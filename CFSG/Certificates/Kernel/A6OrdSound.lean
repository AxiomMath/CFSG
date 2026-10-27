module

public import Certificates.Data.Kernel.A6OrdK
public import CFSG.Certificates.Kernel.ONanA6Sound
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3A6Data

public section

namespace CFSG.KC.A6Ord

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.LQT.P CFSG.QuasithinUnique

local notation "P10" => A6Facts.P10

theorem h10 : (10 : ℕ) ≤ 32 := by norm_num

theorem powFrom_sound (σ δ : P10) :
    ∀ (n : ℕ) (π : P10), powFrom (code σ) (code δ) n (code π) = true → ∃ k < n, δ = π * σ ^ k := by
  intro n
  induction n with
  | zero => exact fun _ h => absurd h Bool.false_ne_true
  | succ n ih =>
    intro π h
    have e : powFrom (code σ) (code δ) (n + 1) (code π) =
        orB (Nat.beq (code π) (code δ)) (powFrom (code σ) (code δ) n (mul 10 (code π) (code σ))) :=
      rfl
    rw [e, orB_iff, beq_code h10, code_mul h10] at h
    rcases h with h | h
    · exact ⟨0, Nat.succ_pos n, by rw [h, pow_zero, mul_one]⟩
    · obtain ⟨k, hk, hd⟩ := ih (π * σ) h
      exact ⟨k + 1, Nat.succ_lt_succ hk, by rw [hd, pow_succ', mul_assoc]⟩

theorem pow8_sound {σ δ : P10} (h : pow8 (code σ) (code δ) = true) : ∃ k < 8, δ = σ ^ k := by
  unfold pow8 at h
  rw [code_one] at h
  obtain ⟨k, hk, hd⟩ := powFrom_sound σ δ 8 1 h
  exact ⟨k, hk, by rw [hd, one_mul]⟩

theorem img_img (σ δ : P10) : img (code δ) (img (code σ) 0) = ((δ * σ) 0 : ℕ) := by
  have h1 : img (code σ) 0 = (σ 0 : ℕ) := img_code h10 σ 0
  rw [h1, img_code h10 δ (σ 0)]
  rfl

theorem centB_sound {σ δ : P10} (hc : δ * σ = σ * δ) (h : centB (code σ) (code δ) = true) :
    ∃ k < 8, δ = σ ^ k := by
  unfold centB at h
  rw [img_img, img_img, hc, code_mul h10, code_mul h10, hc] at h
  simp only [orB_iff, notB_iff, Nat.beq_refl, not_true_eq_false, false_or] at h
  exact pow8_sound h

theorem ord_sound {L : List ℕ} (hL : ∀ x ∈ A6Models.autA6, code x ∈ L) {σ : P10}
    (h : ord26081 L (code σ) = true) :
    (σ ^ 16 = 1 → σ ^ 8 = 1) ∧
      (σ ^ 8 = 1 → σ ^ 4 ≠ 1 → ∀ δ ∈ A6Models.autA6, δ * σ = σ * δ → ∃ k < 8, δ = σ ^ k) := by
  unfold ord26081 at h
  simp only [letB_eq, code_mul h10, code_one] at h
  have e4 : σ * σ * (σ * σ) = σ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have e8 : σ ^ 4 * σ ^ 4 = σ ^ 8 := by rw [← pow_add]
  have e16 : σ ^ 8 * σ ^ 8 = σ ^ 16 := by rw [← pow_add]
  rw [e4, e8, e16] at h
  simp only [andB_iff, orB_iff, notB_iff, beq_code h10] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun h16 => ?_, fun h8 h4 δ hδ hc => ?_⟩
  · rcases h1 with h1 | h1
    · exact absurd h16 h1
    · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact absurd h8 h2
    · exact absurd h2 h4
    · exact centB_sound hc ((allL_iff _ _).1 h2 _ (hL δ hδ))

theorem a6OrdData_of {L : List ℕ} (hL : ∀ x ∈ A6Models.autA6, code x ∈ L)
    (hk : chk26081 L = true) : CFSG.EvenSporadicStandard.Fin76b.A6OrdData := by
  intro c hc
  obtain ⟨σ, hσ, rfl⟩ := CFSG.KC.ONanA6.of_mem_autL hc
  obtain ⟨F1, F2⟩ := ord_sound hL ((allL_iff _ _).1 hk _ (hL σ hσ))
  simp only [← A6Facts.code_pow, ← A6Facts.code_one]
  refine ⟨fun h16 => ?_, fun h8 h4 d hd hcomm => ?_⟩
  · rw [F1 (A6Facts.code_injective h16)]
  · obtain ⟨δ, hδ, rfl⟩ := CFSG.KC.ONanA6.of_mem_autL hd
    rw [← A6Facts.code_mul, ← A6Facts.code_mul] at hcomm
    obtain ⟨k, hk8, hk⟩ := F2 (A6Facts.code_injective h8)
      (fun e => h4 (by rw [e])) δ hδ (A6Facts.code_injective hcomm)
    exact ⟨k, hk8, by rw [hk]⟩

end CFSG.KC.A6Ord
