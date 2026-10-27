module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenLayer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenRho
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableNormalCyclic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.RankThreeUC.S15 Subgroup

theorem isSolvable_centralizer_layer_three {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hR : CFSG.Open.pRank 3 (CFSG.pCore 3 (StarGroup 3 H)) ≤ 2) :
    Group.IsSolvable ↥(centralizer (CFSG.layer (StarGroup 3 H) : Set (StarGroup 3 H))) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R : Subgroup (StarGroup 3 H) := CFSG.pCore 3 (StarGroup 3 H)
  let L : Subgroup (StarGroup 3 H) := CFSG.layer (StarGroup 3 H)
  let Yc : Subgroup (StarGroup 3 H) := centralizer (L : Set (StarGroup 3 H))
  let Cc : Subgroup (StarGroup 3 H) := centralizer (R : Set (StarGroup 3 H))
  haveI hRn : R.Normal := inferInstance
  haveI hLc : L.Characteristic := CFSG.LocalCores.layer_characteristic
  haveI hLn : L.Normal := inferInstance
  haveI hYcN : Yc.Normal := inferInstance
  haveI hCcN : Cc.Normal := inferInstance
  obtain ⟨ρ, hρ⟩ := exists_hom_GL23_of_pRank_le_two (Y := StarGroup 3 H) R
    (CFSG.pCore_isPGroup (p := 3) (G := StarGroup 3 H)) hR
  let g : ↥Yc →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) := ρ.comp Yc.subtype
  have hker : IsPGroup 3 ↥g.ker := by
    change ∀ x : ↥g.ker, ∃ k, x ^ 3 ^ k = 1
    intro x
    have hxρ : ρ (x.1 : ↥Yc) = 1 := x.2
    have hxmem : ((x.1 : ↥Yc) : StarGroup 3 H) ∈ ρ.ker := hxρ
    obtain ⟨a, ha⟩ := hρ ⟨MulAut.conjNormal (H := R) ((x.1 : ↥Yc) : StarGroup 3 H),
      ⟨(x.1 : ↥Yc), hxmem, rfl⟩⟩
    have ha' : (MulAut.conjNormal (H := R) ((x.1 : ↥Yc) : StarGroup 3 H)) ^ 3 ^ a = 1 := by
      simpa using congrArg Subtype.val ha
    have hconj1 : MulAut.conjNormal (H := R)
        (((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a) = 1 := by
      rw [map_pow (MulAut.conjNormal (H := R)) ((x.1 : ↥Yc) : StarGroup 3 H) (3 ^ a)]
      exact ha'
    have hcent : ((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a ∈ Cc := by
      rw [Subgroup.mem_centralizer_iff]
      intro r hr
      have h1 := congrArg
        (fun σ : MulAut ↥R => (σ ⟨r, hr⟩ : StarGroup 3 H)) hconj1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc r * ((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a
          = (((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a * r *
              (((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a)⁻¹) *
              ((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a := by rw [h1]
        _ = ((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a * r := by group
    have hRY : Yc ⊓ Cc ≤ R := by
      have h' := cStarL_inf_centralizer_le_pCore Nat.prime_three H
      rwa [cStarL_eq_centralizer_layer Nat.prime_three H] at h'
    have hyR : ((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a ∈ R :=
      hRY ⟨Yc.pow_mem x.1.2 _, hcent⟩
    obtain ⟨c, hc⟩ := (CFSG.pCore_isPGroup (p := 3) (G := StarGroup 3 H)).exists_orderOf_eq_pow
      ⟨_, hyR⟩
    have hc' : orderOf (((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ a) = 3 ^ c :=
      (Subgroup.orderOf_coe ⟨_, hyR⟩).trans hc
    have hamb : ((x.1 : ↥Yc) : StarGroup 3 H) ^ 3 ^ (a + c) = 1 := by
      rw [pow_add, pow_mul, ← hc', pow_orderOf_eq_one]
    refine ⟨a + c, ?_⟩
    exact Subtype.ext (Subtype.ext
      (by simpa only [Subgroup.coe_pow, Subgroup.coe_one] using hamb))
  haveI : Group.IsNilpotent ↥g.ker := hker.isNilpotent
  haveI : Group.IsSolvable ↥g.ker := inferInstance
  haveI : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable
      (ZMod 3) (Or.inr (by rw [Nat.card_zmod]))
  refine Group.isSolvable_of_ker_le_range g.ker.subtype g ?_
  rw [Subgroup.range_subtype]

theorem isPSolvable_d1PlusCore {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (K : Subgroup (StarGroup p H))
    (hs : Group.IsSolvable ↥(centralizer (K : Set (StarGroup p H)))) :
    CFSG.HallHigman.IsPSolvable p ↥(CFSG.AGLEmbedding.d1PlusCore p H K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let X : Subgroup G := CFSG.AGLEmbedding.d1PlusCore p H K
  let Cc : Subgroup (StarGroup p H) := centralizer (K : Set (StarGroup p H))
  let core : Subgroup ↥H := primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' core
  have hXH : X ≤ H := Subgroup.map_subtype_le _
  have hXC : ∀ x : ↥X, π (Subgroup.inclusion hXH x) ∈ Cc := by
    intro x
    obtain ⟨h, hh, heq⟩ := Subgroup.mem_map.mp
      (show x.1 ∈ ((Cc).comap π).map H.subtype from x.2)
    have hx : Subgroup.inclusion hXH x = h := Subtype.ext (by simpa using heq.symm)
    rw [hx]
    exact Subgroup.mem_comap.mp hh
  let φ : ↥X →* ↥Cc := (π.comp (Subgroup.inclusion hXH)).codRestrict Cc hXC
  have hkerle : (φ.ker).map (Subgroup.inclusion hXH) ≤ core := by
    rintro _ ⟨x, hx, rfl⟩
    have hx1 : (φ x).1 = 1 := by rw [MonoidHom.mem_ker.mp hx]; rfl
    rw [← QuotientGroup.eq_one_iff]
    exact hx1
  have hdvd : Nat.card φ.ker ∣ Nat.card core := by
    have hcard : Nat.card ((φ.ker).map (Subgroup.inclusion hXH)) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective (K := φ.ker) (f := Subgroup.inclusion hXH)
        (Subgroup.inclusion_injective hXH)
    rw [← hcard]
    exact Subgroup.card_dvd_of_le hkerle
  have hcop : Nat.Coprime p (Nat.card φ.ker) :=
    (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥H)).coprime_dvd_right hdvd
  have hsol : Group.IsSolvable (↥X ⧸ φ.ker) := by
    haveI : Group.IsSolvable ↥Cc := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange φ).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange φ).injective
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.isPSolvable_of_normal_coprime_quotient_solvable
    φ.ker hcop hsol

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
