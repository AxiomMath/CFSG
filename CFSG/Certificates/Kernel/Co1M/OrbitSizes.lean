
module

public import CFSG.Certificates.Kernel.Co1M.OrbitSizesBase

public import CFSG.Certificates.Kernel.Co1M.OrbitCheckOf
public import CFSG.Sporadic.Co1.Module.FormsBase1

public section

namespace CFSG.KC.Co1Orb

open CFSG.Blueprint CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 CFSG.KC.PairCount

theorem checks_v₃_v₄
    (h2 : orbitCheck 2 98280 [4096, 1] = true) {u₃ u₄ : Vec24} (hu₃ : u₃ ∈ orb co1Act v₂)
    (hw₃ : v₂ + u₃ ∈ orb co1Act v₃) (H₃ : Finset Vec24)
    (hH₃ : ∀ h ∈ H₃, ∃ x, co1Act x v₂ = v₂ ∧ co1Act x u₃ = h) (hk₃ : 47104 ≤ H₃.card)
    (hc₃ : ((orb co1Act v₂).filter fun a => v₂ + u₃ + a ∈ orb co1Act v₂).card ≤ 552)
    (hu₄ : u₄ ∈ orb co1Act v₂) (hw₄ : v₂ + u₄ ∈ orb co1Act v₄) (H₄ : Finset Vec24)
    (hH₄ : ∀ h ∈ H₄, ∃ x, co1Act x v₂ = v₂ ∧ co1Act x u₄ = h) (hk₄ : 46575 ≤ H₄.card)
    (hc₄ : ((orb co1Act v₂).filter fun a => v₂ + u₄ + a ∈ orb co1Act v₂).card ≤ 552) :
    orbitCheck 4096 8386560 [1] = true ∧ orbitCheck 1 8292375 [] = true := by
  have n2 : (MulAction.orbit Jmat v₂).ncard = 98280 := by
    rw [← toVecD_v₂]
    exact ncard_orbit_of_check h2
  have l3 := lower_bound hu₃ hw₃ H₃ hH₃ hk₃ hc₃
  have l4 := lower_bound hu₄ hw₄ H₄ hH₄ hk₄ hc₄
  rw [orb_card, orb_card, n2] at l3 l4
  have n3 : 8386560 ≤ (MulAction.orbit Jmat v₃).ncard := by omega
  have n4 : 8292375 ≤ (MulAction.orbit Jmat v₄).ncard := by omega
  have h32 : v₃ ∉ MulAction.orbit Jmat v₂ := by
    rw [← toVecD_v₃, ← toVecD_v₂]
    exact not_mem_orbit_of_check h2 (by simp) (by norm_num)
  have h42 : v₄ ∉ MulAction.orbit Jmat v₂ := by
    rw [← toVecD_v₄, ← toVecD_v₂]
    exact not_mem_orbit_of_check h2 (by simp) (by norm_num)
  have h43 : v₄ ∉ MulAction.orbit Jmat v₃ := by
    rintro ⟨g, hg⟩
    have hg' : g • v₃ = v₄ := hg
    have e := q₀_smul g v₃
    rw [hg', q₀_v₃, q₀_v₄] at e
    exact absurd e (by decide)
  have d32 := disjoint_orbit h32
  have d42 := disjoint_orbit h42
  have d43 := disjoint_orbit h43
  set O₂ := MulAction.orbit Jmat v₂
  set O₃ := MulAction.orbit Jmat v₃
  set O₄ := MulAction.orbit Jmat v₄
  have z2 := zero_not_mem_orbit v₂_ne_zero
  have z3 := zero_not_mem_orbit v₃_ne_zero
  have z4 := zero_not_mem_orbit v₄_ne_zero
  have hU : (({0} ∪ O₂) ∪ O₃ ∪ O₄).ncard = 1 + O₂.ncard + O₃.ncard + O₄.ncard := by
    rw [Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
    · rw [Set.disjoint_singleton_left]
      exact z2
    · rw [Set.disjoint_union_left, Set.disjoint_singleton_left]
      exact ⟨z3, d32.symm⟩
    · rw [Set.disjoint_union_left, Set.disjoint_union_left, Set.disjoint_singleton_left]
      exact ⟨⟨z4, d42.symm⟩, d43.symm⟩
  have hle : (({0} ∪ O₂) ∪ O₃ ∪ O₄).ncard ≤ 2 ^ 24 := by
    rw [← card_vec24, ← Nat.card_eq_fintype_card, ← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _)
  have e3 : O₃.ncard = 8386560 := by omega
  have e4 : O₄.ncard = 8292375 := by omega
  refine ⟨orbitCheck_of_ncard (by norm_num) (by norm_num) (by rw [toVecD_v₃]; exact e3) ?_,
    orbitCheck_of_ncard (by norm_num) (by norm_num) (by rw [toVecD_v₄]; exact e4) (by simp)⟩
  intro w hw _
  have : w = 1 := by simpa using hw
  subst this
  rw [toVecD_v₄, toVecD_v₃]
  exact h43

end CFSG.KC.Co1Orb

end
