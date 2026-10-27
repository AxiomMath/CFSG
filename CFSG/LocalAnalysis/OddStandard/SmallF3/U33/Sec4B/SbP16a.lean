module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbC414Grp

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

structure Setting16 {G : Type} [Group G] (Q Y : Subgroup G) (τ ω : G) : Prop where
  normal : Q.Normal
  comm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a
  mem_Y : ∀ a, a ∈ Y ↔ a ∈ Q ∧ a ^ 2 = 1
  card_Q : Nat.card Q = 64
  card_Y : Nat.card Y = 16
  exists_sq : ∃ a ∈ Q, a ^ 2 ≠ 1
  tau_sq : τ ^ 2 = 1
  om_sq : ω ^ 2 = 1
  tau_om : τ * ω = ω * τ
  tau_inv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹
  om_cent_Y : ∀ a ∈ Y, ω * a = a * ω
  comm_om : ∀ q ∈ Q, ω * q * ω⁻¹ * q⁻¹ ∈ Y
  cent_om : ∀ a ∈ Q, ω * a = a * ω → a ∈ Y
  cent_omtau : ∀ a ∈ Q, (ω * τ) * a = a * (ω * τ) → a ∈ Y
  invol_om : ∀ q ∈ Q, (ω * q) ^ 2 = 1 → q ∈ Y
  invol_omtau : ∀ q ∈ Q, (ω * τ * q) ^ 2 = 1 → q ∈ Y
  gen : Q ⊔ closure ({τ, ω} : Set G) = ⊤

namespace Setting16

variable {G : Type} [Group G] [Finite G] {Q Y : Subgroup G} {τ ω : G}

theorem tau_inv_eq (h : Setting16 Q Y τ ω) : τ⁻¹ = τ := by
  have h2 : τ * τ = 1 := by rw [← pow_two]; exact h.tau_sq
  exact inv_eq_of_mul_eq_one_right h2

theorem om_inv_eq (h : Setting16 Q Y τ ω) : ω⁻¹ = ω := by
  have h2 : ω * ω = 1 := by rw [← pow_two]; exact h.om_sq
  exact inv_eq_of_mul_eq_one_right h2

theorem Y_le_Q (h : Setting16 Q Y τ ω) : Y ≤ Q := by
  intro a ha
  exact ((h.mem_Y a).mp ha).1

theorem tau_mul (h : Setting16 Q Y τ ω) {a : G} (ha : a ∈ Q) : τ * a = a⁻¹ * τ := by
  calc τ * a = τ * a * τ⁻¹ * τ := by group
    _ = a⁻¹ * τ := by rw [h.tau_inv a ha]

theorem om_conj_Y (h : Setting16 Q Y τ ω) {a : G} (ha : a ∈ Y) : ω * a * ω = a := by
  have hω : ω * ω = 1 := by rw [← pow_two]; exact h.om_sq
  calc ω * a * ω = a * ω * ω := by rw [h.om_cent_Y a ha]
    _ = a := by rw [mul_assoc, hω, mul_one]

theorem mem_closure_pair_iff (h : Setting16 Q Y τ ω) {x : G} :
    x ∈ closure ({τ, ω} : Set G) ↔ x = 1 ∨ x = τ ∨ x = ω ∨ x = τ * ω := by
  have hττ : τ * τ = 1 := by rw [← pow_two]; exact h.tau_sq
  have hωω : ω * ω = 1 := by rw [← pow_two]; exact h.om_sq
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hττ
  have hωinv : ω⁻¹ = ω := inv_eq_of_mul_eq_one_right hωω
  have hτQ : ∀ y, (y = 1 ∨ y = τ ∨ y = ω ∨ y = τ * ω) →
      (τ * y = 1 ∨ τ * y = τ ∨ τ * y = ω ∨ τ * y = τ * ω) := by
    intro y hy
    rcases hy with hy | hy | hy | hy
    · right; left; subst hy; rw [mul_one]
    · left; subst hy; rw [hττ]
    · right; right; right; subst hy; rfl
    · right; right; left; subst hy; rw [← mul_assoc, hττ, one_mul]
  have hωQ : ∀ y, (y = 1 ∨ y = τ ∨ y = ω ∨ y = τ * ω) →
      (ω * y = 1 ∨ ω * y = τ ∨ ω * y = ω ∨ ω * y = τ * ω) := by
    intro y hy
    rcases hy with hy | hy | hy | hy
    · right; right; left; subst hy; rw [mul_one]
    · right; right; right; subst hy; exact h.tau_om.symm
    · left; subst hy; rw [hωω]
    · right; left; subst hy; rw [← mul_assoc, h.tau_om.symm, mul_assoc, hωω, mul_one]
  constructor
  · intro hx
    refine Subgroup.closure_induction_left
      (p := fun x _ => x = 1 ∨ x = τ ∨ x = ω ∨ x = τ * ω) ?_ ?_ ?_ hx
    · exact Or.inl rfl
    · intro a ha y hy hyQ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hτQ y hyQ
      · exact hωQ y hyQ
    · intro a ha y hy hyQ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · rw [hτinv]; exact hτQ y hyQ
      · rw [hωinv]; exact hωQ y hyQ
  · rintro (rfl | rfl | rfl | rfl)
    · exact (closure ({τ, ω} : Set G)).one_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact (closure ({τ, ω} : Set G)).mul_mem
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

theorem cosets (h : Setting16 Q Y τ ω) (x : G) :
    ∃ q ∈ Q, x = q ∨ x = q * τ ∨ x = q * ω ∨ x = q * (τ * ω) := by
  haveI := h.normal
  have hx : x ∈ Q ⊔ closure ({τ, ω} : Set G) := by
    rw [h.gen]
    exact Subgroup.mem_top x
  rcases Subgroup.mem_sup_of_normal_left.mp hx with ⟨q, hq, z, hz, hqz⟩
  rcases (h.mem_closure_pair_iff).mp hz with h1 | h1 | h1 | h1
  · exact ⟨q, hq, Or.inl (by rw [← hqz, h1, mul_one])⟩
  · exact ⟨q, hq, Or.inr (Or.inl (by rw [← hqz, h1]))⟩
  · exact ⟨q, hq, Or.inr (Or.inr (Or.inl (by rw [← hqz, h1])))⟩
  · exact ⟨q, hq, Or.inr (Or.inr (Or.inr (by rw [← hqz, h1])))⟩

theorem tau_not_mem (h : Setting16 Q Y τ ω) : τ ∉ Q := by
  intro hτQ
  obtain ⟨a, haQ, ha2⟩ := h.exists_sq
  have hcomm : τ * a = a * τ := h.comm τ hτQ a haQ
  have h1 : τ * a * τ⁻¹ = a := by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have h2 : a = a⁻¹ := h1.symm.trans (h.tau_inv a haQ)
  have h3 : a * a = 1 := (congrArg (fun x => a * x) h2).trans (mul_inv_cancel a)
  exact ha2 (by rw [pow_two]; exact h3)

theorem om_not_mem (h : Setting16 Q Y τ ω) : ω ∉ Q := by
  intro hωQ
  have hQY : Q ≤ Y := fun a ha => h.cent_om a ha (h.comm a ha ω hωQ).symm
  have hcardle : Nat.card Q ≤ Nat.card Y := Subgroup.card_le_of_le hQY
  rw [h.card_Q, h.card_Y] at hcardle
  norm_num at hcardle

theorem tau_om_not_mem (h : Setting16 Q Y τ ω) : τ * ω ∉ Q := by
  intro hmem
  have hωτ_mem : ω * τ ∈ Q := by rw [← h.tau_om]; exact hmem
  have hQY : Q ≤ Y := fun a ha => h.cent_omtau a ha (h.comm (ω * τ) hωτ_mem a ha)
  have hcardle : Nat.card Q ≤ Nat.card Y := Subgroup.card_le_of_le hQY
  rw [h.card_Q, h.card_Y] at hcardle
  norm_num at hcardle

theorem card_le (h : Setting16 Q Y τ ω) : Nat.card G ≤ 4 * Nat.card Q := by
  have hsurj : Function.Surjective
      (fun p : Q × Fin 4 => (p.1 : G) * ![1, τ, ω, τ * ω] p.2) := by
    rintro x
    obtain ⟨q, hq, hx⟩ := h.cosets x
    rcases hx with hx | hx | hx | hx
    · exact ⟨(⟨q, hq⟩, 0), by simp [hx]⟩
    · exact ⟨(⟨q, hq⟩, 1), by simp [hx]⟩
    · exact ⟨(⟨q, hq⟩, 2), by simp [hx]⟩
    · exact ⟨(⟨q, hq⟩, 3), by simp [hx]⟩
  have h1 : Nat.card G ≤ Nat.card (Q × Fin 4) := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_fin] at h1
  omega

theorem index_le (h : Setting16 Q Y τ ω) : Q.index ≤ 4 := by
  haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have hcard := Subgroup.card_mul_index Q
  have hle := h.card_le
  rw [← hcard, mul_comm 4 (Nat.card Q)] at hle
  exact Nat.le_of_mul_le_mul_left hle hpos

theorem sup_Q_eq_top (h : Setting16 Q Y τ ω) {A : Subgroup G} (hA : 64 ≤ Nat.card A)
    (hAQ : Nat.card ↥(A ⊓ Q) ≤ 16) : A ⊔ Q = ⊤ := by
  haveI := h.normal
  have hrelA : (A ⊓ Q).relIndex A = Q.relIndex A := by
    rw [inf_comm]
    exact Subgroup.inf_relIndex_right Q A
  have hcardA : (A ⊓ Q).relIndex A * Nat.card ↥(A ⊓ Q) = Nat.card A := by
    have hh := Subgroup.relIndex_mul_card (H := A ⊓ Q) (K := A)
    rwa [inf_of_le_left inf_le_left] at hh
  have hr4 : 4 ≤ Q.relIndex A := by
    rw [← hrelA]
    have hle : (A ⊓ Q).relIndex A * Nat.card ↥(A ⊓ Q) ≤ (A ⊓ Q).relIndex A * 16 :=
      Nat.mul_le_mul_left _ hAQ
    rw [hcardA] at hle
    have h64 : 4 * 16 ≤ (A ⊓ Q).relIndex A * 16 := by
      rw [show (4 : ℕ) * 16 = 64 by norm_num]
      exact le_trans hA hle
    exact Nat.le_of_mul_le_mul_right h64 (by norm_num)
  have hcard_sup : Nat.card ↥(A ⊔ Q) = Q.relIndex (A ⊔ Q) * Nat.card Q := by
    have hh := Subgroup.relIndex_mul_card (H := Q) (K := A ⊔ Q)
    rw [inf_of_le_left le_sup_right] at hh
    exact hh.symm
  have hrelsup : Q.relIndex (A ⊔ Q) = Q.relIndex A := Subgroup.relIndex_sup_right A Q
  have hge : 256 ≤ Nat.card ↥(A ⊔ Q) := by
    rw [hcard_sup, hrelsup, h.card_Q]
    calc (256 : ℕ) = 4 * 64 := by norm_num
      _ ≤ Q.relIndex A * 64 := Nat.mul_le_mul_right _ hr4
  have hleG : Nat.card ↥(A ⊔ Q) ≤ Nat.card G := Subgroup.card_le_card_group (A ⊔ Q)
  have hG : Nat.card G ≤ 256 := by
    have hh := h.card_le
    rw [h.card_Q] at hh
    norm_num at hh
    exact hh
  have hEq : Nat.card ↥(A ⊔ Q) = Nat.card G := le_antisymm hleG (by omega)
  exact Subgroup.eq_top_of_card_eq (A ⊔ Q) hEq

theorem sq_mul_tau (h : Setting16 Q Y τ ω) {q : G} (hq : q ∈ Q) : (q * τ) ^ 2 = 1 := by
  have hτ : τ * τ = 1 := by rw [← pow_two]; exact h.tau_sq
  rw [pow_two]
  calc (q * τ) * (q * τ) = q * (τ * q * τ⁻¹) * (τ * τ) := by group
    _ = q * q⁻¹ * 1 := by rw [h.tau_inv q hq, hτ]
    _ = 1 := by simp

theorem sq_tau_mul (h : Setting16 Q Y τ ω) {q : G} (hq : q ∈ Q) : (τ * q) ^ 2 = 1 := by
  have hτ : τ * τ = 1 := by rw [← pow_two]; exact h.tau_sq
  have hτinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hconj : τ * q * τ = q⁻¹ := by simpa [hτinv] using h.tau_inv q hq
  rw [pow_two]
  calc (τ * q) * (τ * q) = (τ * q * τ) * q := by group
    _ = q⁻¹ * q := by rw [hconj]
    _ = 1 := by simp

end Setting16

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
