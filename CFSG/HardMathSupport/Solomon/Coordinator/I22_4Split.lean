module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_4Basic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

variable {Ω : Type*} [Group Ω]

theorem i224_mem_sup_of_comm {P Q : Subgroup Ω} (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x) {z : Ω}
    (hz : z ∈ P ⊔ Q) : ∃ x ∈ P, ∃ y ∈ Q, z = x * y := by
  let T : Subgroup Ω :=
    { carrier := {z | ∃ x ∈ P, ∃ y ∈ Q, z = x * y}
      mul_mem' := by
        rintro _ _ ⟨x, hx, y, hy, rfl⟩ ⟨x', hx', y', hy', rfl⟩
        refine ⟨x * x', P.mul_mem hx hx', y * y', Q.mul_mem hy hy', ?_⟩
        have h := hc x' hx' y hy
        calc x * y * (x' * y') = x * (y * x') * y' := by group
          _ = x * (x' * y) * y' := by rw [← h]
          _ = x * x' * (y * y') := by group
      one_mem' := ⟨1, P.one_mem, 1, Q.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        refine ⟨x⁻¹, P.inv_mem hx, y⁻¹, Q.inv_mem hy, ?_⟩
        have h := hc x⁻¹ (P.inv_mem hx) y⁻¹ (Q.inv_mem hy)
        calc (x * y)⁻¹ = y⁻¹ * x⁻¹ := by group
          _ = x⁻¹ * y⁻¹ := h.symm }
  have hP : P ≤ T := fun x hx => ⟨x, hx, 1, Q.one_mem, by simp⟩
  have hQ : Q ≤ T := fun y hy => ⟨1, P.one_mem, y, hy, by simp⟩
  exact (sup_le hP hQ) hz

section Elem

variable {p : ℕ} [Fact p.Prime] {B A : Subgroup Ω}

private theorem comm_of_le {B P Q : Subgroup Ω} (hB : CFSG.Open.IsElemAbelian p B) (hP : P ≤ B)
    (hQ : Q ≤ B) : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hB.1.is_comm.comm (⟨x, hP hx⟩ : ↥B) ⟨y, hQ hy⟩)

theorem i224_exists_complement (hB : CFSG.Open.IsElemAbelian p B) (hAB : A ≤ B) :
    ∃ C : Subgroup Ω, C ≤ B ∧ A ⊓ C = ⊥ ∧ A ⊔ C = B ∧ Nat.card B = Nat.card A * Nat.card C := by
  obtain ⟨C, hCB, hd, hs⟩ := i224_exists_compl hB hAB
  refine ⟨C, hCB, hd, hs, ?_⟩
  have := i224_card_sup (comm_of_le hB hAB hCB) hd
  rw [hs] at this
  exact this

theorem i224_split (hB : CFSG.Open.IsElemAbelian p B) (hAB : A ≤ B) {s : Ω} (hs : s ∈ B)
    (hsA : s ∉ A) :
    (∃ R : Subgroup Ω, R ≤ B ∧ A ⊓ R = ⊥ ∧ (∀ g ∈ R, s⁻¹ * g ∉ A) ∧
      Nat.card B = p * (Nat.card A * Nat.card R)) ∧
    (∃ R : Subgroup Ω, R ≤ B ∧ A ⊓ R = ⊥ ∧ s ∈ R ∧ Nat.card B = Nat.card A * Nat.card R) := by
  set S : Subgroup Ω := Subgroup.zpowers s with hS
  have hSB : S ≤ B := (Subgroup.zpowers_le).2 hs
  have hs1 : s ≠ 1 := fun h => hsA (h ▸ A.one_mem)
  have hsp : orderOf s = p := orderOf_eq_prime (hB.2 s hs) hs1
  have hScard : Nat.card S = p := by rw [hS, Nat.card_zpowers, hsp]
  have hAS : A ⊓ S = ⊥ := by
    haveI : Fact (Nat.card ↥S).Prime := ⟨hScard ▸ Fact.out⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((A ⊓ S).subgroupOf S) with h | h
    · rw [eq_bot_iff]
      intro x hx
      have hxS : x ∈ S := hx.2
      have : (⟨x, hxS⟩ : ↥S) ∈ (A ⊓ S).subgroupOf S := hx
      rw [h, Subgroup.mem_bot] at this
      have h1 : x = 1 := congrArg Subtype.val this
      rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      apply hsA
      have : (⟨s, Subgroup.mem_zpowers s⟩ : ↥S) ∈ (A ⊓ S).subgroupOf S := by
        rw [h]; exact Subgroup.mem_top _
      exact this.1
  have hcAS : ∀ x ∈ A, ∀ y ∈ S, x * y = y * x := comm_of_le hB hAB hSB
  have hVcard : Nat.card ↥(A ⊔ S) = Nat.card A * p := by
    rw [i224_card_sup hcAS hAS, hScard]
  have hVB : A ⊔ S ≤ B := sup_le hAB hSB
  obtain ⟨R₃, hR₃B, hVR, hVsup, hBcard⟩ := i224_exists_complement hB hVB
  rw [hVcard] at hBcard
  have hAR : A ⊓ R₃ = ⊥ := by
    rw [eq_bot_iff, ← hVR]
    exact inf_le_inf_right _ le_sup_left
  refine ⟨⟨R₃, hR₃B, hAR, ?_, ?_⟩, ?_⟩
  · intro g hg ha
    have hgV : g ∈ A ⊔ S := by
      have : g = s * (s⁻¹ * g) := by group
      rw [this]
      exact (A ⊔ S).mul_mem (Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
        (Subgroup.mem_sup_left ha)
    have : g ∈ (A ⊔ S) ⊓ R₃ := ⟨hgV, hg⟩
    rw [hVR, Subgroup.mem_bot] at this
    rw [this] at ha
    apply hsA
    have : s = (s⁻¹ * 1)⁻¹ := by group
    rw [this]
    exact A.inv_mem ha
  · rw [hBcard]; ring
  · have hSR : S ⊓ R₃ = ⊥ := by
      rw [eq_bot_iff, ← hVR]
      exact inf_le_inf_right _ le_sup_right
    have hcSR : ∀ x ∈ S, ∀ y ∈ R₃, x * y = y * x := comm_of_le hB hSB hR₃B
    refine ⟨S ⊔ R₃, sup_le hSB hR₃B, ?_, Subgroup.mem_sup_left (Subgroup.mem_zpowers s), ?_⟩
    · rw [eq_bot_iff]
      intro x ⟨hxA, hxR⟩
      obtain ⟨u, hu, r, hr, rfl⟩ := i224_mem_sup_of_comm hcSR hxR
      have hrV : r ∈ (A ⊔ S) ⊓ R₃ := by
        refine ⟨?_, hr⟩
        have : r = u⁻¹ * (u * r) := by group
        rw [this]
        exact (A ⊔ S).mul_mem ((A ⊔ S).inv_mem (Subgroup.mem_sup_right hu))
          (Subgroup.mem_sup_left hxA)
      rw [hVR, Subgroup.mem_bot] at hrV
      rw [hrV, mul_one] at hxA ⊢
      have : u ∈ A ⊓ S := ⟨hxA, hu⟩
      rw [hAS, Subgroup.mem_bot] at this
      rw [this]
      exact Subgroup.one_mem _
    · rw [i224_card_sup hcSR hSR, hScard]
      rw [hBcard]; ring

end Elem

end CFSG.HardMathSupport.Solomon.Coordinator
