module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.SylowData

public section

namespace CFSG.EvenSporadicStandard.TwoSuz

open Subgroup
open CFSG.Sporadic.SuzOddCore (suzM suzEquivM suzM_card_chain)
open CFSG.Sporadic.Recognition.SuzMultiplier (SuzCover)
open scoped commutatorElement

section Transfer

variable {Λ Γ : Type*} [Group Λ] [Group Γ]

theorem map_comap_of_le (ψ : Λ →* Γ) {S : Subgroup Γ} (hS : S ≤ ψ.range) :
    (S.comap ψ).map ψ = S := by
  rw [Subgroup.map_comap_eq]
  exact inf_eq_right.2 hS

theorem InnerData.of_model (ψ : Λ →* Γ) (hψ : Function.Injective ψ) {z : Λ} {S J : Subgroup Γ}
    {x₁ x₂ : Γ} (hz : ψ z ∈ S) (hSr : S ≤ ψ.range) (hJr : J ≤ ψ.range)
    (hS : Nat.card S = 2 ^ 14) (hSJ : S ≤ J) (hx₁ : x₁ ∈ S) (hx₂ : x₂ ∈ S)
    (hc₁ : ∀ j ∈ J, j * x₁ = x₁ * j) (hc₂ : ∀ j ∈ J, j * x₂ = x₂ * j) (hJ : J ≤ ⁅J, J⁆)
    (hcov : ∀ s ∈ S, s * s = 1 → s ≠ 1 → s ≠ ψ z →
      ∃ g ∈ ψ.range, g * s * g⁻¹ = x₁ ∨ g * s * g⁻¹ = x₂)
    (h1056 : rootCount S (ψ z) = 1056) (h1 : rootCount S x₁ ≠ 1056)
    (h2 : rootCount S x₂ ≠ 1056) : InnerData Λ z := by
  obtain ⟨a₁, ha₁⟩ := hSr hx₁
  obtain ⟨a₂, ha₂⟩ := hSr hx₂
  have hmapS := map_comap_of_le ψ hSr
  have hmapJ := map_comap_of_le ψ hJr
  refine ⟨S.comap ψ, J.comap ψ, a₁, a₂, ?_, hz, Subgroup.comap_mono hSJ, by
    rw [Subgroup.mem_comap, ha₁]; exact hx₁, by rw [Subgroup.mem_comap, ha₂]; exact hx₂, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective hψ, hmapS, hS]
  · intro j hj
    refine hψ ?_
    rw [map_mul, map_mul, ha₁]
    exact hc₁ _ hj
  · intro j hj
    refine hψ ?_
    rw [map_mul, map_mul, ha₂]
    exact hc₂ _ hj
  · intro j hj
    have hj' : ψ j ∈ ⁅J, J⁆ := hJ hj
    have e : (⁅J.comap ψ, J.comap ψ⁆).map ψ = ⁅J, J⁆ := by
      rw [Subgroup.map_commutator, hmapJ]
    rw [← e] at hj'
    obtain ⟨c, hc, hcj⟩ := Subgroup.mem_map.1 hj'
    rwa [← hψ hcj]
  · intro s hs hss hs1 hsz
    have hs' : ψ s ∈ S := hs
    obtain ⟨g, ⟨g', rfl⟩, hg⟩ := hcov (ψ s) hs' (by rw [← map_mul, hss, map_one])
      (fun h' => hs1 (hψ (by rw [h', map_one]))) (fun h' => hsz (hψ h'))
    refine ⟨g', ?_⟩
    rcases hg with hg | hg
    · exact Or.inl (hψ (by rw [map_mul, map_mul, map_inv, hg, ha₁]))
    · exact Or.inr (hψ (by rw [map_mul, map_mul, map_inv, hg, ha₂]))
  · have := rootCount_map hψ (S.comap ψ) z
    rw [hmapS, h1056] at this
    exact this.symm
  · intro h'
    apply h1
    have := rootCount_map hψ (S.comap ψ) a₁
    rw [hmapS, ha₁] at this
    rw [this]
    exact h'
  · intro h'
    apply h2
    have := rootCount_map hψ (S.comap ψ) a₂
    rw [hmapS, ha₂] at this
    rw [this]
    exact h'

end Transfer

section Setup

theorem exists_surjection_ker_eq' {L Y : Type*} [Group L] [Group Y] {N : Subgroup L} [N.Normal]
    (f : L ⧸ N ≃* Y) : ∃ q : L →* Y, Function.Surjective q ∧ q.ker = N := by
  refine ⟨f.toMonoidHom.comp (QuotientGroup.mk' N),
    f.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  rw [map_eq_one_iff _ f.injective, QuotientGroup.eq_one_iff]

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem card_of_setup (h : Setup G L z) : Nat.card L = 896690995200 := by
  obtain ⟨e₀⟩ := h.quot
  have e : (↥L ⧸ center ↥L) ≃* suzM := e₀.trans suzEquivM
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center ↥L), Nat.card_congr e.toEquiv,
    suzM_card_chain, h.card_center]

theorem exists_embedding_of_setup (h : Setup G L z) :
    ∃ ψ : ↥L →* GL12, Function.Injective ψ ∧ ψ ⟨z, h.zmem⟩ = -1 ∧
      ψ.range = (rho : SuzCover →* GL12).range := by
  obtain ⟨e₀⟩ := h.quot
  have e : (↥L ⧸ center ↥L) ≃* suzM := e₀.trans suzEquivM
  obtain ⟨q, hq, hqker⟩ := exists_surjection_ker_eq' e
  have hcenter : center ↥L = zpowers (⟨z, h.zmem⟩ : ↥L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [h.center_map, MonoidHom.map_zpowers]
    rfl
  have ht2 : orderOf (⟨z, h.zmem⟩ : ↥L) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact h.z_order
  have : Group.IsPerfect ↥L := Group.isPerfect_def.2 h.perfect
  obtain ⟨φ, ψ, hφ, hψ, -, hψφ, hψt⟩ :=
    exists_embedding q hq ht2 (hqker.trans hcenter) hcenter.symm.le
  refine ⟨ψ, hψ, hψt, ?_⟩
  rw [← hψφ, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hφ, Subgroup.map_top]


theorem innerData_of_setup (h : Setup G L z) : InnerData ↥L (⟨z, h.zmem⟩ : ↥L) := by
  obtain ⟨ψ, hψ, hz, hr⟩ := exists_embedding_of_setup h
  obtain ⟨S, J, x₁, x₂, hSL, hJL, hS, hzS, hSJ, hx₁, hx₂, hc₁, hc₂, hJ, hcov, h1056, h1, h2⟩ :=
    model_inner
  have hSL' : S ≤ ψ.range := by rw [hr]; exact hSL
  have hJL' : J ≤ ψ.range := by rw [hr]; exact hJL
  refine InnerData.of_model ψ hψ ?_ hSL' hJL' hS hSJ hx₁ hx₂ hc₁ hc₂ hJ ?_ ?_ h1 h2
  · rw [hz]; exact hzS
  · rw [hz]
    intro s hs hss hs1 hsz
    obtain ⟨g, hg, hg'⟩ := hcov s hs hss hs1 hsz
    exact ⟨g, by rw [hr]; exact hg, hg'⟩
  · rw [hz]; exact h1056

theorem twoSuzNoSwapInner : TwoSuzNoSwapInner :=
  twoSuzNoSwapInner_of_data (fun _ _ _ _ _ h => card_of_setup h) (fun _ _ _ _ _ h =>
    innerData_of_setup h)

end Setup

end CFSG.EvenSporadicStandard.TwoSuz
