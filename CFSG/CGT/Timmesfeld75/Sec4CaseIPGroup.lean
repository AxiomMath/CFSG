module

public import CFSG.CGT.Timmesfeld75.WeaklyClosed

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_closure_ne {S R : Subgroup G} (hS : IsPGroup 2 S) {Δ : Set G}
    (hΔS : Δ ⊆ S) (hΔ : ∀ s ∈ S, ∀ d ∈ Δ, s * d * s⁻¹ ∈ Δ) (hRS : R ≤ S)
    (hR : Subgroup.closure (Δ ∩ (R : Set G)) = R) (hne : Subgroup.closure Δ ≠ R) :
    ∃ x ∈ Δ, x ∈ Subgroup.normalizer (R : Set G) ∧ x ∉ R := by
  by_contra hbad
  have hbad' : ∀ x ∈ Δ, x ∈ Subgroup.normalizer (R : Set G) → x ∈ R := fun x hx hxN => by
    by_contra hxR
    exact hbad ⟨x, hx, hxN, hxR⟩
  have key : ∀ U : Subgroup G, R ≤ U → U ≤ S → (∀ d ∈ Δ, d ∈ U → d ∈ R) →
      ∀ d ∈ Δ, d ∈ R := by
    intro U
    induction U using WellFoundedGT.induction with
    | ind U ih =>
      intro hRU hUS hΔU
      by_cases hUS' : U = S
      · exact fun d hd => hΔU d hd (hUS' ▸ hΔS hd)
      · obtain ⟨y, hyS, hyN, hyU⟩ := exists_mem_normalizer_not_mem_of_pGroup hS hUS hUS'
        have hU'N : U ⊔ Subgroup.zpowers y ≤ Subgroup.normalizer (U : Set G) :=
          sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hyN)
        have hU'S : U ⊔ Subgroup.zpowers y ≤ S :=
          sup_le hUS ((Subgroup.zpowers_le).2 hyS)
        have hlt : U < U ⊔ Subgroup.zpowers y :=
          lt_of_le_of_ne le_sup_left fun h =>
            hyU (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        refine ih _ hlt (hRU.trans le_sup_left) hU'S ?_
        intro δ hδ hδU'
        have hδN : δ ∈ Subgroup.normalizer (U : Set G) := hU'N hδU'
        have hRδ : ∀ x ∈ R, δ * x * δ⁻¹ ∈ R := by
          intro x hx
          rw [← hR] at hx
          refine Subgroup.closure_induction (p := fun x _ => δ * x * δ⁻¹ ∈ R) ?_ ?_ ?_ ?_ hx
          · rintro d ⟨hdΔ, hdR⟩
            exact hΔU _ (hΔ δ (hΔS hδ) d hdΔ) ((Subgroup.mem_normalizer_iff.1 hδN d).1
              (hRU hdR))
          · simp
          · intro a b _ _ ha hb
            have e : δ * (a * b) * δ⁻¹ = (δ * a * δ⁻¹) * (δ * b * δ⁻¹) := by group
            rw [e]
            exact R.mul_mem ha hb
          · intro a _ ha
            have e : δ * a⁻¹ * δ⁻¹ = (δ * a * δ⁻¹)⁻¹ := by group
            rw [e]
            exact R.inv_mem ha
        have hle : conjSubgroup δ R ≤ R := by
          rintro _ ⟨x, hx, rfl⟩
          exact hRδ x hx
        exact hbad' δ hδ (mem_normalizer_of_conjSubgroup_eq (conjSubgroup_eq_of_le hle))
  have hΔR := key R le_rfl hRS fun d _ hd => hd
  apply hne
  refine le_antisymm ((Subgroup.closure_le R).2 hΔR) ?_
  rw [← hR]
  exact Subgroup.closure_mono Set.inter_subset_left

end CFSG.CGT.Timmesfeld75
