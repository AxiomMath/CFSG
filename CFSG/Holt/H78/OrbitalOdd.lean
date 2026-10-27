module

public import CFSG.Holt.H78.SectionsStar
public import CFSG.CGT.PushingUpLit.A78.SimsOrbital

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.CGT.PushingUpLit.A78

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω] [Finite Ω]
  [FaithfulSMul G Ω]

theorem eq_bot_of_le_stabilizer_inf_fixingSubgroup (hG : IsStarGroup G Ω) [IsPreprimitive G Ω]
    {α β : Ω} {Γ : Set Ω} (hβΓ : β ∈ Γ) (hβα : β ≠ α)
    (hΓ : ∀ g ∈ stabilizer G α, ∀ ω ∈ Γ, g • ω ∈ Γ) {S : Subgroup G} (hS : IsPGroup 2 S)
    (hSΓ : S ≤ stabilizer G α ⊓ fixingSubgroup G Γ) : S = ⊥ := by
  have hαF : α ∈ fixSet Ω S := mem_fixSet_iff_le_stabilizer.mpr (hSΓ.trans inf_le_left)
  have hΓF : Γ ⊆ fixSet Ω S := fun ω hω s hs =>
    (mem_fixingSubgroup_iff G).mp (Subgroup.mem_inf.mp (hSΓ hs)).2 ω hω
  let E : Ω → Ω → Prop := fun a b => ∃ g : G, g • α = a ∧ g⁻¹ • b ∈ Γ
  have hE : Sims.Invariant G E := fun h a b ⟨g, hga, hgb⟩ =>
    ⟨h * g, by rw [mul_smul, hga], by rwa [mul_inv_rev, mul_smul, inv_smul_smul]⟩
  have hstep : ∀ a b, a ∈ fixSet Ω S → E a b → b ∈ fixSet Ω S := by
    rintro a b ha ⟨g, hga, hgb⟩
    obtain ⟨c, hcS, hca⟩ := hG.exists_centralizer_smul_eq_of_mem_fixSet hS hαF ha
    have hcg : c⁻¹ * g ∈ stabilizer G α := by
      rw [mem_stabilizer_iff, mul_smul, hga, ← hca, inv_smul_smul]
    have h1 : c⁻¹ • b ∈ Γ := by
      have h := hΓ _ hcg _ hgb
      rwa [mul_smul, smul_inv_smul] at h
    have h2 := smul_mem_fixSet_of_mem_normalizer (Subgroup.centralizer_le_normalizer _ hcS)
      (hΓF h1)
    rwa [smul_inv_smul] at h2
  have : Nontrivial Ω := ⟨⟨α, β, hβα.symm⟩⟩
  obtain ⟨g, hg⟩ := exists_smul_eq G α β
  have hgen : stabilizer G α ⊔ Subgroup.zpowers g = ⊤ := by
    refine (IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive G α).2 _
      (lt_of_le_of_ne le_sup_left fun h => hβα ?_)
    have hgα : g ∈ stabilizer G α := h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
    rw [← hg, mem_stabilizer_iff.mp hgα]
  have hEg : E α (g • α) := ⟨1, one_smul G α, by rw [inv_one, one_smul, hg]; exact hβΓ⟩
  have hall : ∀ x : Ω, x ∈ fixSet Ω S := fun x => by
    have hreach := (Sims.eqvGen_iff_reflTransGen hE α x).mp
      (Sims.connected_of_stabilizer_sup hE hEg hgen x)
    induction hreach with
    | refl => exact hαF
    | tail _ hbc ih => exact hstep _ _ ih hbc
  exact Sims.eq_bot_of_fixes_all fun s hs x => hall x s hs

theorem odd_card_stabilizer_inf_fixingSubgroup (hG : IsStarGroup G Ω) [IsPreprimitive G Ω]
    {α β : Ω} {Γ : Set Ω} (hβΓ : β ∈ Γ) (hβα : β ≠ α)
    (hΓ : ∀ g ∈ stabilizer G α, ∀ ω ∈ Γ, g • ω ∈ Γ) :
    Odd (Nat.card ↥(stabilizer G α ⊓ fixingSubgroup G Γ)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.even_or_odd (Nat.card ↥(stabilizer G α ⊓ fixingSubgroup G Γ)) with h | h
  · obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
      (G := ↥(stabilizer G α ⊓ fixingSubgroup G Γ)) 2 h.two_dvd
    have hx' : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
    have h1 := eq_bot_of_le_stabilizer_inf_fixingSubgroup hG hβΓ hβα hΓ
      (isPGroup_zpowers_of_orderOf_eq_two hx') (Subgroup.zpowers_le.mpr x.2)
    have hx1 : (x : G) = 1 := Subgroup.zpowers_eq_bot.mp h1
    rw [hx1, orderOf_one] at hx'
    exact absurd hx' (by decide)
  · exact h

theorem lemma_3_4 (hG : IsStarGroup G Ω) [IsPreprimitive G Ω] {α : Ω} {Γ : Set Ω}
    (hΓ : ∃ β ∈ Γ, β ≠ α ∧ Γ = orbit ↥(stabilizer G α) β) :
    Odd (Nat.card ↥(stabilizer G α ⊓ fixingSubgroup G Γ)) := by
  obtain ⟨β, hβΓ, hβα, rfl⟩ := hΓ
  refine odd_card_stabilizer_inf_fixingSubgroup hG hβΓ hβα fun g hg ω hω => ?_
  obtain ⟨k, rfl⟩ := hω
  exact ⟨⟨g, hg⟩ * k, mul_smul _ _ _⟩

end CFSG.Holt.H78
