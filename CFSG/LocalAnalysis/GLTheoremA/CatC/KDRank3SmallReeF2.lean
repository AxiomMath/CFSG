module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KDRank3SmallReeF2Core

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeF2

open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeF2Core CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeBorel
open CFSG.LieType.Ree CFSG.ComponentClassification.LiteratureLocal.SmallRee
open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallAbs (SmallF2 centralInvol exists_ne_one_centralInvol mem_centralInvol)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem finiteReeAut_zero_eq : ReeTag.G2.finiteReeAut K 0 = ReeTag.G2.finiteExceptionalAut K := by
  rw [CFSG.RankThree.finiteReeAut_eq_pow 0]
  simp

theorem frob_F0_hyp (g : ReeTag.G2.reeGamma K 1) :
    CFSG.RankThree.reeGammaToAdjoint 1 ((frobeniusΓ ^ 2) g) =
      ReeTag.G2.finiteReeAut K 0 (CFSG.RankThree.reeGammaToAdjoint 1 g) := by
  rw [finiteReeAut_zero_eq]
  exact frob_two_apply g

theorem mul_conj_eq (F : MulAut (ReeTag.G2.reeGamma K 1)) (x : ReeTag.G2.reeGamma K 1) :
    F * MulAut.conj x = MulAut.conj (F x) * F := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem conj_conj_eq (δ : MulAut (ReeTag.G2.reeGamma K 1)) (y : ReeTag.G2.reeGamma K 1) :
    MulAut.conj δ (MulAut.conj y) = MulAut.conj (δ y) := by
  ext z
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem frob_two_fix_iff (hK : Nat.card K = 3 ^ (2 * 1 + 1)) (x : ReeTag.G2.reeGamma K 1) :
    (frobeniusΓ ^ 2 : MulAut (ReeTag.G2.reeGamma K 1)) x = x ↔ frobeniusΓ x = x := by
  have hF3 : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K 1)) ^ 3 = 1 := by
    simpa using frobeniusΓ_pow hK
  constructor
  · intro h
    have h4 : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K 1)) ^ 4 = frobeniusΓ := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hF3, one_mul, pow_one]
    calc frobeniusΓ x = ((frobeniusΓ : MulAut (ReeTag.G2.reeGamma K 1)) ^ 4) x := by rw [h4]
      _ = (frobeniusΓ ^ 2 : MulAut (ReeTag.G2.reeGamma K 1)) ((frobeniusΓ ^ 2) x) := by
          rw [← MulAut.mul_apply, ← pow_add]
      _ = x := by rw [h, h]
  · intro h
    rw [sq, MulAut.mul_apply, h, h]

theorem exists_conj_F0 (hK : Nat.card K = 3 ^ (2 * 1 + 1))
    (E : Subgroup (MulAut (ReeTag.G2.reeGamma K 1))) (hE : IsElemAbelian 3 E)
    (hnot : ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K 1)) :
    ∃ δ : MulAut (ReeTag.G2.reeGamma K 1),
      (frobeniusΓ ^ 2 : MulAut (ReeTag.G2.reeGamma K 1)) ∈ E.map (MulAut.conj δ).toMonoidHom := by
  obtain ⟨b, hbE, hbI⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨g, k, hk⟩ := exists_eq_conj_mul_frobeniusΓ_pow (by norm_num) hK b
  have hF3 : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K 1)) ^ 3 = 1 := by
    simpa using frobeniusΓ_pow hK
  have hkmod : (frobeniusΓ : MulAut (ReeTag.G2.reeGamma K 1)) ^ k =
      frobeniusΓ ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3]
    rw [pow_add, pow_mul, hF3, one_pow, one_mul]
  rw [hkmod] at hk
  have hr : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hx : ∃ x : ReeTag.G2.reeGamma K 1, MulAut.conj x * (frobeniusΓ ^ 2 : MulAut _) ∈ E := by
    generalize k % 3 = r at hk hr
    interval_cases r
    · exfalso
      apply hbI
      rw [hk, pow_zero, mul_one]
      exact ⟨g, rfl⟩
    · refine ⟨g * frobeniusΓ g, ?_⟩
      have e : MulAut.conj (g * frobeniusΓ g) * (frobeniusΓ ^ 2 : MulAut _) = b * b := by
        rw [hk, pow_one]
        ext y
        simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, sq]
      rw [e]
      exact E.mul_mem hbE hbE
    · refine ⟨g, ?_⟩
      rw [← hk]
      exact hbE
  obtain ⟨x, hxE⟩ := hx
  have hβ : (MulAut.conj x * (frobeniusΓ ^ 2 : MulAut _)) ^ 3 = 1 := hE.2 _ hxE
  obtain ⟨δ, hδ⟩ := CFSG.RankThree.exists_conj_eq_of_finiteReeAut (K := K) (a := 1) (b := 0) (p := 3) hK
    (by norm_num) (by norm_num) (frobeniusΓ ^ 2 : MulAut _) frob_F0_hyp x hβ
  refine ⟨δ, Subgroup.mem_map.2 ⟨MulAut.conj x * (frobeniusΓ ^ 2 : MulAut _), hxE, ?_⟩⟩
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact hδ

theorem card_comap_inner (hK : Nat.card K = 3 ^ (2 * 1 + 1))
    (T : Subgroup (MulAut (ReeTag.G2.reeGamma K 1)))
    (hT : T ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K 1)) :
    Nat.card (T.comap (MulAut.conj : ReeTag.G2.reeGamma K 1 →* MulAut (ReeTag.G2.reeGamma K 1))) =
      Nat.card T := by
  have hinj : Function.Injective (MulAut.conj : ReeTag.G2.reeGamma K 1 →* MulAut (ReeTag.G2.reeGamma K 1)) :=
    fun x y h => conj_inj hK h
  have e : (MulAut.conj : ReeTag.G2.reeGamma K 1 →* MulAut (ReeTag.G2.reeGamma K 1)).range ⊓ T = T :=
    inf_eq_right.2 hT
  rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, e]

theorem map_conj_comm {E : Subgroup (MulAut (ReeTag.G2.reeGamma K 1))} (hE : IsElemAbelian 3 E)
    (δ : MulAut (ReeTag.G2.reeGamma K 1)) {a b : MulAut (ReeTag.G2.reeGamma K 1)}
    (ha : a ∈ E.map (MulAut.conj δ).toMonoidHom) (hb : b ∈ E.map (MulAut.conj δ).toMonoidHom) :
    a * b = b * a := by
  obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b0, hb0, rfl⟩ := Subgroup.mem_map.1 hb
  rw [← map_mul, ← map_mul, isElemAbelian_commute hE ha0 hb0]

theorem map_conj_pow3 {E : Subgroup (MulAut (ReeTag.G2.reeGamma K 1))} (hE : IsElemAbelian 3 E)
    (δ : MulAut (ReeTag.G2.reeGamma K 1)) {a : MulAut (ReeTag.G2.reeGamma K 1)}
    (ha : a ∈ E.map (MulAut.conj δ).toMonoidHom) : a ^ 3 = 1 := by
  obtain ⟨a0, ha0, rfl⟩ := Subgroup.mem_map.1 ha
  rw [← map_pow, hE.2 a0 ha0, map_one]

theorem smallF2_gamma (hK : Nat.card K = 3 ^ (2 * 1 + 1))
    (E : Subgroup (MulAut (ReeTag.G2.reeGamma K 1))) (hE : IsElemAbelian 3 E)
    (hnot : ¬ E ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K 1))
    (hE0 : Nat.card ↥(E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (ReeTag.G2.reeGamma K 1)) = 3 ^ 2) :
    SmallF2 (ReeTag.G2.reeGamma K 1) E := by
  haveI : Finite (ModGL ReeTag.G2.tag K) := finite_modGL
  haveI : Finite (ReeTag.G2.reeGamma K 1) := Subtype.finite
  haveI : Finite (MulAut (ReeTag.G2.reeGamma K 1)) := MulEquiv.finite_left
  intro W hW hWi hcent
  by_contra hWne
  obtain ⟨x, hx, hx1⟩ := exists_ne_one_centralInvol hW hWne
  obtain ⟨hxW, -, hx2⟩ := mem_centralInvol.1 hx
  obtain ⟨y, rfl⟩ := hWi hxW
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hy2 : y * y = 1 := conj_inj hK (by rw [map_mul, map_one, ← sq]; exact hx2)
  obtain ⟨δ, hδ⟩ := exists_conj_F0 hK E hE hnot
  set T₁ : Subgroup (MulAut (ReeTag.G2.reeGamma K 1)) :=
    (E ⊓ CFSG.ComponentClassification.OuterAutomorphisms.inner (ReeTag.G2.reeGamma K 1)).map
      (MulAut.conj δ).toMonoidHom with hT₁
  have hT₁le : T₁ ≤ E.map (MulAut.conj δ).toMonoidHom :=
    Subgroup.map_mono inf_le_left
  have hT₁inner : T₁ ≤ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (ReeTag.G2.reeGamma K 1) := by
    intro t ht
    obtain ⟨s, ⟨-, hs⟩, rfl⟩ := Subgroup.mem_map.1 ht
    obtain ⟨z, rfl⟩ := hs
    exact ⟨δ z, (conj_conj_eq δ z).symm⟩
  set X : Subgroup (ReeTag.G2.reeGamma K 1) := T₁.comap MulAut.conj with hXdef
  have hmemX : ∀ x : ReeTag.G2.reeGamma K 1, x ∈ X ↔ MulAut.conj x ∈ T₁ := fun x => Iff.rfl
  have hF0E : (frobeniusΓ ^ 2 : MulAut (ReeTag.G2.reeGamma K 1)) ∈ E.map (MulAut.conj δ).toMonoidHom := hδ
  have hX0 : X ≤ gam0 := by
    intro x hx
    have hxT := (hmemX x).1 hx
    have hc := map_conj_comm hE δ hF0E (hT₁le hxT)
    rw [mul_conj_eq] at hc
    have hc' : MulAut.conj ((frobeniusΓ ^ 2 : MulAut (ReeTag.G2.reeGamma K 1)) x) =
        MulAut.conj x := mul_right_cancel hc
    rw [mem_gam0, ← frob_two_fix_iff hK]
    exact conj_inj hK hc'
  have hX9 : Nat.card X = 9 := by
    rw [hXdef, card_comap_inner hK T₁ hT₁inner, hT₁, Subgroup.card_map_of_injective
      (MulAut.conj δ).injective, hE0]
    norm_num
  have hX3 : ∀ x ∈ X, x ^ 3 = 1 := by
    intro x hx
    apply conj_inj hK
    rw [map_pow, map_one]
    exact map_conj_pow3 hE δ (hT₁le ((hmemX x).1 hx))
  have hXy : ∀ x ∈ X, x * δ y = δ y * x := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 ((hmemX x).1 hx)
    have hsx' : MulAut.conj δ s = MulAut.conj x := hsx
    have hsc := Subgroup.mem_centralizer_iff.1 (hcent hs) (MulAut.conj y) hxW
    have h1 : MulAut.conj δ (MulAut.conj y * s) = MulAut.conj δ (s * MulAut.conj y) := by rw [hsc]
    rw [map_mul, map_mul, conj_conj_eq, hsx'] at h1
    have h2 : MulAut.conj (x * δ y) = MulAut.conj (δ y * x) := by
      rw [map_mul, map_mul]
      exact h1.symm
    exact conj_inj hK h2
  exact f2_core hK X hX0 hX9 hX3 (y := δ y) (by rw [← map_mul, hy2, map_one])
    (fun h => hy1 (δ.injective (by rw [h, map_one]))) hXy

end CFSG.LocalAnalysis.GLTheoremA.KDRank3SmallReeF2
