module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25Main
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HU34
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25HEquiv
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitF5B4Four

public section

namespace CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification
  CFSG.ComponentClassification.FooteLit CFSG.ComponentClassification.FooteLit.F5
  CFSG.ComponentClassification.Asc76X CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.EvenSporadicStandard.Finkelstein77.Lemma25Proof

variable {G : Type} [Group G]

theorem isDihedral_of_fourgroup [Finite G]
    {x : G} (hx : orderOf x = 4) (hwc : WeaklyClosedInNormalizer (zpowers x)) {w t : G}
    (hd : Datum {u | IsConj (x ^ 2) u} 0 w t)
    (hsic : ∀ s ∈ normalizer ((dsub w t : Subgroup G) : Set G), IsConj (x ^ 2) s → s ∈ dsub w t)
    {P : Subgroup G} (hP : IsSylowOf 2 P (normalClosure ((dsub w t : Subgroup G) : Set G))) :
    AschbacherTheorem3.IsDihedralTwoGroup P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := dsub w t with hDdef
  have hdih : AschbacherTheorem3.IsDihedralTwoGroup D :=
    ⟨2, le_rfl, by simpa using hd.nonempty_mulEquiv_dihedral⟩
  have hD4 : Nat.card D = 4 := by
    obtain ⟨e⟩ := hd.nonempty_mulEquiv_dihedral
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    norm_num
  have hDexp : ∀ g ∈ D, g * g = 1 := mul_self_eq_one_of_dihedral_four hdih hD4
  have hcl : ∀ y ∈ normalizer (D : Set G), y ∉ D → orderOf y = 2 →
      ∀ d ∈ D, orderOf d = 2 → ∀ g : G, g⁻¹ * y * g ≠ d := by
    intro y hyN hyD hy2 d hdD hd2 g hg
    have hd2' : d * d = 1 := hDexp d hdD
    have hd1 : d ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hd2
      omega
    have hdC : IsConj (x ^ 2) d := hd.inv_mem d hdD hd2' hd1
    have hyC : IsConj (x ^ 2) y := by
      have : y = g * d * g⁻¹ := by rw [← hg]; group
      rw [this]
      exact isConj_conj g hdC
    exact hyD (hsic y hyN hyC)
  obtain ⟨S, hS, hDS⟩ := exists_isSylowOf_ge_of_le (le_top : D ≤ ⊤) (isPGroup_of_mul_self hDexp)
  have hSN : S ≤ normalizer (D : Set G) :=
    le_normalizer_of_involutionClosed hDexp hcl hS.isPGroup hDS
  have hwcD : ∀ g : G, rightConjugate D g ≤ S → rightConjugate D g = D := by
    intro g hg
    refine eq_of_le_of_card_ge ?_
      (card_map_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
        (MulAut.conj g⁻¹).injective).ge
    rintro _ ⟨d, hd', rfl⟩
    have h1 : (MulAut.conj g⁻¹).toMonoidHom d ∈ S := hg ⟨d, hd', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h1 ⊢
    exact conj_mem_of_mem_normalizer hDexp hcl hd' (hSN h1)
  rcases hallFusionThm32 G S D hS hDS hD4 (isElemAbelian_of_mul_self hDexp) hwcD with
    h1 | he | h1
  · obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf h1 hP.le hP.isPGroup
    have hle : P.map (MulAut.conj k⁻¹).toMonoidHom ≤ D := by
      rintro _ ⟨a, ha, rfl⟩
      simpa using hk a ha
    have hcard : Nat.card D ≤ Nat.card (P.map (MulAut.conj k⁻¹).toMonoidHom) := by
      rw [card_map_of_injective (MulAut.conj k⁻¹).injective, hP.card_eq, h1.card_eq]
    exact isDihedral_of_mulEquiv ((mulEquivConj P k).trans
      (MulEquiv.subgroupCongr (eq_of_le_of_card_ge hle hcard))) hdih
  · exfalso
    obtain ⟨e⟩ := he
    set N : Subgroup G := normalClosure (D : Set G) with hN
    have hNnormal : N.Normal := normalClosure_normal
    have hDN : D ≤ N := fun d hd' => subset_normalClosure hd'
    have hSnil : Group.IsNilpotent ↥S := hS.isPGroup.isNilpotent
    have hDS' : (D.subgroupOf S).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hDS).mpr hSN
    have hne : D.subgroupOf S ≠ ⊥ := by
      intro h
      have h1 : Nat.card (D.subgroupOf S) = 1 := by rw [h]; simp
      have h4 : Nat.card (D.subgroupOf S) = 4 :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDS).toEquiv).trans hD4
      omega
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
    have haD : ((a : ↥S) : G) ∈ D := (Subgroup.mem_inf.mp a.2).1
    have haC : (a : ↥S) ∈ Subgroup.center ↥S := (Subgroup.mem_inf.mp a.2).2
    set z₀ : G := ((a : ↥S) : G) with hz₀
    have hz₀1 : z₀ ≠ 1 := fun h => ha1 (Subtype.ext (Subtype.ext h))
    have hz₀cent : ∀ s ∈ S, s * z₀ = z₀ * s := fun s hs =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp haC ⟨s, hs⟩)
    have hz₀C : IsConj (x ^ 2) z₀ := hd.inv_mem z₀ haD (hDexp z₀ haD) hz₀1
    have hSC : S ≤ centralizer ({z₀} : Set G) := fun s hs =>
      mem_centralizer_singleton_iff.mpr (hz₀cent s hs)
    obtain ⟨y, hxy, hy2, hSy⟩ := exists_datum hx hwc hz₀C hS.isPGroup hSC
    have hyo : orderOf y = 4 := by rw [orderOf_eq_of_isConj hxy, hx]
    obtain ⟨t₁, ht₁D, ht₁z, ht₁1⟩ := Hall32.exists_mem_ne_ne hD4 z₀ 1
    have ht₁C : IsConj (x ^ 2) t₁ := hd.inv_mem t₁ ht₁D (hDexp t₁ ht₁D) ht₁1
    have hnc : ¬ (t₁ * y = y * t₁) := by
      intro hcomm
      exact ht₁z ((eq_sq_of_commute_conj hx hwc hxy ht₁C hcomm).trans hy2)
    have hKN : (⊤ : Subgroup G) ≤ normalizer (N : Set G) := by
      rw [Subgroup.normalizer_eq_top]
    have hTX : IsSylowOf 2 (S ⊓ N) N := hS.inf_of_le_normalizer le_top hKN
    have hmem : t₁ ∈ ⁅S ⊓ N, S ⊓ N⁆ :=
      mem_commutator_of_psu3 e hTX ⟨hDS ht₁D, hDN ht₁D⟩ (hDexp t₁ ht₁D)
    have hmem' : t₁ ∈ ⁅S, S⁆ := Subgroup.commutator_mono inf_le_left inf_le_left hmem
    exact hnc (mem_centralizer_singleton_iff.mp
      (commutator_le_centralizer_of_normalizer hyo hSy hmem'))
  · exact ⟨3, by norm_num, by simpa using h1 P hP⟩

end CFSG.EvenSporadicStandard.Finkelstein77.Lemma25HProof
