module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L67Red
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L66In

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec67_fstar_of_isConj [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    {y : G} (hty : IsConj t y) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer ({y} : Set G)) ∧ InFStar K := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hty
  have hSc := hS.conjugate c⁻¹
  rw [inv_inv, hc] at hSc
  exact ⟨CFSG.conjugate L c⁻¹, hSc.component, inFStar_of_inF hSc.inF⟩

theorem sec67_fstar_of_layer [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {y : G} (hy2 : orderOf y = 2)
    (hyt : y ∈ centralizer ({t} : Set G))
    (hsh : IsOmega5 (layerCent L y) ∨ IsL29 (layerCent L y) ∨ IsU33 (layerCent L y) ∨
      IsL3Eps3 (layerCent L y)) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer ({y} : Set G)) ∧ InFStar K := by
  let X : Subgroup G := layerCent L y
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS
  have hXL : IsComponentIn X (L ⊓ centralizer ({y} : Set G)) :=
    isComponentIn_layerCent hsh
  have hXc : IsComponentIn X (centralizer ({t, y} : Set G)) := by
    rw [centralizer_pair_eq_inf t y]
    exact IsComponentIn.of_normal_inf_centralizer hS.component.le hnorm hXL
  have hcomm : t * y = y * t := (Subgroup.mem_centralizer_singleton_iff.mp hyt).symm
  have hXstar : InFStar X := by
    rcases hsh with h | h | h | h
    · exact inFStar_of_inF ⟨hXc.isQuasisimple, Or.inl (Or.inl h)⟩
    · exact Or.inr ⟨hXc.isQuasisimple, Or.inl h⟩
    · exact Or.inr ⟨hXc.isQuasisimple, Or.inr (Or.inr (Or.inr h))⟩
    · exact inFStar_of_isL3Eps3 hXL h
  obtain ⟨K, hK, hXle⟩ := hS.lBalance t y hS.involution hy2 hcomm X hXc
  exact ⟨K, hK, hS.a2 t y hS.involution hy2 hcomm X K hXc hK hXle hXstar⟩

theorem sec67_inner_case [Finite G] (h66 : Asc82Lemma66) (h82 : Asc82Lemma82) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L) {y : G}
    (hy2 : orderOf y = 2) (hyt : y ∈ centralizer ({t} : Set G)) (hyne : y ≠ t) (hyL : y ∉ L)
    (hin : InnerOn L y) : IsConj t y := by
  obtain ⟨v, hvL, hv2, hcase⟩ := sec66_inner_decomp h82 hS hL6 hy2 hyt hyne hin
  rcases hcase with hsv | hsv
  · exact absurd (hsv.symm ▸ hvL) hyL
  · have hvt : v * t = t * v :=
      Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hvL)
    rw [hsv, hvt]
    exact h66 G t L hS hL6 v hv2 hvL

theorem sec67_outer_case [Finite G] (h36 : Asc82Lemma36) (hM : Asc82Tab6M) {t : G}
    {L : Subgroup G} (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L)
    (hi3 : ∀ y : G, orderOf y = 2 → (∃ α : ℤˣ, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y)
    {y : G} (hy2 : orderOf y = 2) (hyt : y ∈ centralizer ({t} : Set G)) (hout : ¬ InnerOn L y) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer ({y} : Set G)) ∧ InFStar K := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have hnorm : ∀ c ∈ centralizer ({t} : Set G), CFSG.conjugate L c = L :=
    conjugate_eq_self_of_lemma36 h36 hS
  have hyN : y ∈ normalizer (L : Set G) := mem_normalizer_of_conjugate_eq (hnorm y hyt)
  by_cases hlay : layerCent L y = ⊥
  · rcases (hM.layer_trivial G L hLM y hy2 hyN).mp hlay with h4 | ⟨α, hα⟩
    · exact absurd ((hM.inner_iff G L hLM y hy2 hyN).mpr h4).1 hout
    · exact sec67_fstar_of_isConj hS (hi3 y hy2 ⟨α, hα⟩)
  · rcases hM.classify G L hLM y hy2 hyN with hc | h4p | h4m | hρ | h1 | h3 | hγ
    · exact absurd (Subgroup.mem_sup_right hc) hout
    · exact absurd ((hM.inner_iff G L hLM y hy2 hyN).mpr h4p).1 hout
    · have h4m' : IsL29 (layerCent L y) := hM.layer_i4m G L hLM y hy2 hyN h4m
      exact sec67_fstar_of_layer h36 hS hy2 hyt (Or.inr (Or.inl h4m'))
    · have hρ' : IsU33 (layerCent L y) := hM.layer_rho G L hLM y hy2 hyN hρ
      exact sec67_fstar_of_layer h36 hS hy2 hyt (Or.inr (Or.inr (Or.inl hρ')))
    · have h1' : IsOmega5 (layerCent L y) := hM.layer_i1 G L hLM y hy2 hyN h1
      exact sec67_fstar_of_layer h36 hS hy2 hyt (Or.inl h1')
    · exact absurd ((hM.layer_trivial G L hLM y hy2 hyN).mpr (Or.inr h3)) hlay
    · have hγ' : IsL29 (layerCent L y) := hM.layer_gamma G L hLM y hy2 hyN hγ
      exact sec67_fstar_of_layer h36 hS hy2 hyt (Or.inr (Or.inl hγ'))

theorem sec67_comm_case [Finite G] (h36 : Asc82Lemma36) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hM : Asc82Tab6M) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L)
    (hi3 : ∀ y : G, orderOf y = 2 → (∃ α : ℤˣ, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y)
    {y : G} (hy2 : orderOf y = 2) (hyt : y ∈ centralizer ({t} : Set G)) (hyL : y ∉ L) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer ({y} : Set G)) ∧ InFStar K := by
  by_cases hyeq : y = t
  · rw [hyeq]
    exact sec67_fstar_of_isConj hS (IsConj.refl t)
  · by_cases hin : InnerOn L y
    · exact sec67_fstar_of_isConj hS (sec67_inner_case h66 h82 hS hL6 hy2 hyt hyeq hyL hin)
    · exact sec67_outer_case h36 hM hS hL6 hi3 hy2 hyt hin

theorem sec67_exists_fstar [Finite G] (h36 : Asc82Lemma36) (h66 : Asc82Lemma66)
    (h82 : Asc82Lemma82) (hM : Asc82Tab6M) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) (hL6 : IsOmega6Minus L)
    (hi3 : ∀ y : G, orderOf y = 2 → (∃ α : ℤˣ, InducesTypeSome L y 6 (-1) 3 α) → IsConj t y)
    {z : G} (hz2 : orderOf z = 2) (hzL : z ∈ L) {y : G} (hy2 : orderOf y = 2)
    (hyN : y ∈ normalizer (L : Set G)) (hyz : ∀ l ∈ L, l⁻¹ * z * l ≠ y) :
    ∃ K : Subgroup G, IsComponentIn K (centralizer ({y} : Set G)) ∧ InFStar K := by
  have hLM : IsOm6M L := ⟨hS.component.isQuasisimple, hL6⟩
  have htC : t ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS.component.le hx)
  obtain ⟨v, hvC, hvy⟩ := sec67_reduce (h82 G t L hS hL6) hS.involution htC hy2 hyN
  have hyL : y ∉ L := by
    intro hyLin
    obtain ⟨h, hh, hyh⟩ := hM.inv_one_class G L hLM z y hzL hyLin hz2 hy2
    exact hyz h⁻¹ (L.inv_mem hh) (by rw [inv_inv]; exact hyh.symm)
  have hS₁ : Sec3SettingLB G (v * t * v⁻¹) L := by
    have h := hS.conjugate v⁻¹
    rw [inv_inv, sec67_conjugate_eq_of_centralizer
      ((centralizer (L : Set G)).inv_mem hvC)] at h
    exact h
  have ht1conj : IsConj t (v * t * v⁻¹) := isConj_iff.mpr ⟨v, rfl⟩
  have hi3₁ : ∀ y' : G, orderOf y' = 2 →
      (∃ α : ℤˣ, InducesTypeSome L y' 6 (-1) 3 α) →
      IsConj (v * t * v⁻¹) y' := by
    intro y' hy'2 hy'type
    exact ht1conj.symm.trans (hi3 y' hy'2 hy'type)
  have hyC : y ∈ centralizer ({v * t * v⁻¹} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hvy
  exact sec67_comm_case h36 h66 h82 hM hS₁ hL6 hi3₁ hy2 hyC hyL

end CFSG.OddStandard.SmallF3.Omega
