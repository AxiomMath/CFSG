module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.GF2Type.SmithTypeE.E8

theorem commutator_iSup_iSup_le {G : Type*} [Group G] {ι κ : Type*} (A : ι → Subgroup G)
    (B : κ → Subgroup G) (N : Subgroup G)
    (hA : (⨆ i, A i) ≤ Subgroup.normalizer (N : Set G))
    (hB : (⨆ j, B j) ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ i j, ⁅A i, B j⁆ ≤ N) :
    ⁅(⨆ i, A i), (⨆ j, B j)⁆ ≤ N := by
  open scoped commutatorElement in
  rw [Subgroup.commutator_le]
  have step1 : ∀ i, ∀ a ∈ A i, ∀ b ∈ ⨆ j, B j, ⁅a, b⁆ ∈ N := by
    intro i a ha b hb
    induction hb using Subgroup.iSup_induction' with
    | hp j b hb => exact h i j (Subgroup.commutator_mem_commutator ha hb)
    | h1 => simp
    | hmul b b' hb hb' ihb ihb' =>
      have hid : ⁅a, b * b'⁆ = ⁅a, b⁆ * (b * ⁅a, b'⁆ * b⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [hid]
      exact N.mul_mem ihb ((Subgroup.mem_normalizer_iff.mp (hB hb) _).mp ihb')
  intro a ha b hb
  induction ha using Subgroup.iSup_induction' with
  | hp i a ha => exact step1 i a ha b hb
  | h1 => simp
  | hmul a a' ha ha' iha iha' =>
    have hid : ⁅a * a', b⁆ = a * ⁅a', b⁆ * a⁻¹ * ⁅a, b⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [hid]
    exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hA ha) _).mp iha') iha

theorem card_inf_le_two_mul {G : Type*} [Group G] [Finite G] (X H N : Subgroup G) (hNH : N ≤ H)
    (c : G) (hc : ∀ h ∈ H, h ∈ N ∨ ∃ n ∈ N, h = c * n) :
    Nat.card ↥(X ⊓ H) ≤ 2 * Nat.card ↥(X ⊓ N) := by
  by_cases hXH : X ⊓ H ≤ N
  · have hle : X ⊓ H ≤ X ⊓ N := le_inf inf_le_left hXH
    have := Subgroup.card_le_of_le hle
    omega
  · obtain ⟨a, haXH, haN⟩ := SetLike.not_le_iff_exists.1 hXH
    obtain ⟨haX, haH⟩ := Subgroup.mem_inf.1 haXH
    obtain ⟨na, hna, hacn⟩ : ∃ n ∈ N, a = c * n := (hc a haH).resolve_left haN
    have hsub : ((X ⊓ H : Subgroup G) : Set G) ⊆
        ((X ⊓ N : Subgroup G) : Set G) ∪ (fun x => a * x) '' ((X ⊓ N : Subgroup G) : Set G) := by
      intro b hb
      obtain ⟨hbX, hbH⟩ := Subgroup.mem_inf.1 hb
      rcases hc b hbH with hbN | ⟨nb, hnb, hbcn⟩
      · exact Or.inl (Subgroup.mem_inf.2 ⟨hbX, hbN⟩)
      · have hab : a⁻¹ * b = na⁻¹ * nb := by
          rw [hacn, hbcn]
          simp [mul_assoc]
        refine Or.inr ⟨a⁻¹ * b, Subgroup.mem_inf.2 ⟨X.mul_mem (X.inv_mem haX) hbX, ?_⟩, ?_⟩
        · rw [hab]
          exact N.mul_mem (N.inv_mem hna) hnb
        · simp
    calc Nat.card ↥(X ⊓ H)
        = ((X ⊓ H : Subgroup G) : Set G).ncard := Nat.card_coe_set_eq _
      _ ≤ (((X ⊓ N : Subgroup G) : Set G) ∪
            (fun x => a * x) '' ((X ⊓ N : Subgroup G) : Set G)).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ ((X ⊓ N : Subgroup G) : Set G).ncard +
            ((fun x => a * x) '' ((X ⊓ N : Subgroup G) : Set G)).ncard :=
          Set.ncard_union_le _ _
      _ = 2 * Nat.card ↥(X ⊓ N) := by
          have h2 : ((X ⊓ N : Subgroup G) : Set G).ncard = Nat.card ↥(X ⊓ N) :=
            (Nat.card_coe_set_eq _).symm
          rw [Set.ncard_image_of_injective _ (mul_right_injective a), h2]
          omega

theorem card_inf_eq_of_inf_le {G : Type*} [Group G] [Finite G] (X H N : Subgroup G) (hNH : N ≤ H)
    (h : X ⊓ H ≤ N) : Nat.card ↥(X ⊓ H) = Nat.card ↥(X ⊓ N) := by
  have hEq : X ⊓ H = X ⊓ N := le_antisymm (le_inf inf_le_left h) (inf_le_inf_left X hNH)
  rw [hEq]

end CFSG.GF2Type.SmithTypeE.E8
