module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNFCert
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHNRow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobFactor
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHNLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHNPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocHNSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Out1SlimEquiv

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore

theorem overgroup_transfer {Y G : Type} [Group Y] [Group G] (Φ : Y ≃* G) {u : Y}
    {K : Subgroup Y}
    (h : ∀ X' : Subgroup G, K.map Φ.toMonoidHom ≤ X' →
      X' ≤ centralizer ({Φ u} : Set G) ∨ X' = ⊤)
    (X : Subgroup Y) (hKX : K ≤ X) : X ≤ centralizer ({u} : Set Y) ∨ X = ⊤ := by
  rcases h (X.map Φ.toMonoidHom) (Subgroup.map_mono hKX) with h1 | h1
  · left
    intro x hx
    have hx' : Φ x ∈ X.map Φ.toMonoidHom := ⟨x, hx, rfl⟩
    have := mem_centralizer_singleton_iff.1 (h1 hx')
    rw [mem_centralizer_singleton_iff]
    apply Φ.injective
    rw [map_mul, map_mul]
    exact this
  · right
    rw [eq_top_iff]
    intro y _
    have hy : Φ y ∈ X.map Φ.toMonoidHom := by rw [h1]; trivial
    obtain ⟨x, hx, hxy⟩ := hy
    have : x = y := Φ.injective hxy
    rwa [← this]

theorem map_le_centralizer_of_commute {Y G : Type} [Group Y] [Group G] (Φ : Y ≃* G) {u : Y}
    {K : Subgroup Y} (hKu : ∀ k ∈ K, k * u = u * k) :
    K.map Φ.toMonoidHom ≤ centralizer ({Φ u} : Set G) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [mem_centralizer_singleton_iff]
  show Φ k * Φ u = Φ u * Φ k
  rw [← map_mul, ← map_mul, hKu k hk]

theorem card_map_mulEquiv {Y G : Type} [Group Y] [Group G] (Φ : Y ≃* G) (K : Subgroup Y) :
    Nat.card ↥(K.map Φ.toMonoidHom) = Nat.card K :=
  Nat.card_congr (K.equivMapOfInjective Φ.toMonoidHom Φ.injective).symm.toEquiv

theorem exists_mulEquiv_of_isConj {Y G : Type} [Group Y] [Group G] (Ψ : Y ≃* G) {u : Y} {a : G}
    (h : IsConj a (Ψ u)) : ∃ Φ : Y ≃* G, Φ u = a := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨Ψ.trans (MulAut.conj c⁻¹), ?_⟩
  show c⁻¹ * Ψ u * c⁻¹⁻¹ = a
  rw [← hc]
  group

theorem overgroup_of_model {Y G : Type} [Group Y] [Group G] [Finite G] (Ψ : Y ≃* G) (a t : G)
    (hconj : ∀ g : G, orderOf g = 2 → IsConj a g ∨ IsConj t g)
    (hct : Nat.card ↥(centralizer ({t} : Set G)) < 88704000)
    (hov : ∀ K : Subgroup G, K ≤ centralizer ({a} : Set G) → Nat.card K = 88704000 →
      ∀ X : Subgroup G, K ≤ X → X ≤ centralizer ({a} : Set G) ∨ X = ⊤)
    {u : Y} {K : Subgroup Y} (hu2 : orderOf u = 2) (hKu : ∀ k ∈ K, k * u = u * k)
    (hcard : Nat.card K = 88704000) (X : Subgroup Y) (hKX : K ≤ X) :
    X ≤ centralizer ({u} : Set Y) ∨ X = ⊤ := by
  have hu' : orderOf (Ψ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hu2
  rcases hconj _ hu' with hc | hc
  · obtain ⟨Φ, hΦu⟩ := exists_mulEquiv_of_isConj Ψ hc
    refine overgroup_transfer Φ (fun X' hX' => ?_) X hKX
    rw [hΦu]
    have hKc := map_le_centralizer_of_commute Φ hKu
    rw [hΦu] at hKc
    exact hov _ hKc (by rw [card_map_mulEquiv, hcard]) X' hX'
  · exfalso
    have h1 := card_centralizer_eq_of_isConj hc
    have h2 := Subgroup.card_le_of_le (map_le_centralizer_of_commute Ψ hKu)
    rw [card_map_mulEquiv, hcard, ← h1] at h2
    omega

section Centralizer


theorem card_centralizer_aJ : Nat.card ↥(centralizer ({aJ} : Set ↥JH)) = 177408000 := by
  obtain ⟨E, hE, hi⟩ := hnShape_aJ
  have h1 := card_eq_of_double_cover hE.card_center hE.quotient
  have h2 := Subgroup.card_mul_index E
  rw [h1, hi] at h2
  omega

end Centralizer

section Simple


theorem card_JH : Nat.card ↥JH = 273030912000000 := by
  rw [← Nat.card_congr hnEquivJ.toEquiv]
  exact CFSG.Sporadic.HN.card_HN

theorem isSimpleGroup_JH : IsSimpleGroup ↥JH :=
  @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HN.isSimpleGroup_HN hnEquivJ.symm

theorem JH_index_ne_two (X : Subgroup ↥JH) : X.index ≠ 2 := by
  intro hX
  have := isSimpleGroup_JH
  have : X.Normal := Subgroup.normal_of_index_eq_two hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with h | h
  · rw [h, Subgroup.index_bot, card_JH] at hX
    omega
  · rw [h, Subgroup.index_top] at hX
    omega

end Simple

section Overgroups


theorem hnOvergroup_aJ {K : Subgroup ↥JH} (hKC : K ≤ centralizer ({aJ} : Set ↥JH))
    (hcard : Nat.card K = 88704000) :
    ∀ X : Subgroup ↥JH, K ≤ X → X ≤ centralizer ({aJ} : Set ↥JH) ∨ X = ⊤ := by
  have hC := card_centralizer_aJ
  have hidx : (K.subgroupOf (centralizer ({aJ} : Set ↥JH))).index = 2 := by
    have h := Subgroup.card_mul_index (K.subgroupOf (centralizer ({aJ} : Set ↥JH)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv, hcard, hC] at h
    omega
  have := finite_JH
  exact hnf_overgroup (hnfOrbitData_JH hC card_JH) JH_index_ne_two hKC hidx

end Overgroups

section Fact


theorem hnOvergroupFact : HNOvergroupFact := by
  intro Y _ hY u K hu2 hKu hcard X hKX
  have hfin := finite_JH
  obtain ⟨Ψ⟩ := exists_mulEquiv_JH_of_isSporadic hY
  have hct : Nat.card ↥(centralizer ({t4J} : Set ↥JH)) < 88704000 := by
    rw [card_CJ_t4]
    norm_num
  exact @overgroup_of_model Y ↥JH _ inferInstance hfin Ψ aJ t4J
    (fun _ hg => isConj_aJ_or_t4J hg) hct (fun _ hK hc => hnOvergroup_aJ hK hc) u K hu2 hKu
    hcard X hKX

end Fact

end CFSG.EvenSporadicStandard.Solomon78
