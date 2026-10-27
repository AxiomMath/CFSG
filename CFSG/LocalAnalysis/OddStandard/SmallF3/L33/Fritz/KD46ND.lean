module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7ND
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NMat
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46NQ1

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {R : Subgroup X}

namespace Inst

variable (I : Inst S)

theorem ui_mat (H : Hyp S R) : I.Mat I.ui xCols := by
  have huT := I.ui_mem_TE
  have hc : ∀ {g : X}, g ∈ S.B → I.ui * g * I.ui⁻¹ = g := fun hg => by
    rw [← (KD46.central_of_mem_B S) hg huT]; group
  refine Mat.mk (I.R_le H (H.le huT)) ?_ ?_ ?_ ?_
  · rw [hc (subset_closure (by simp))]; simp [xCols, sigCols, wV]
  · rw [I.ui_conj_yi]; simp [xCols, sigCols, wV]
  · rw [hc (subset_closure (by simp))]; simp [xCols, sigCols, wV]
  · rw [hc I.ki_mem_B]; simp [xCols, sigCols, wV]

theorem card_oddTwoCoreIn (H : Hyp S R) :
    (Nat.card (A7Base.oddTwoCoreIn (normalizer (I.E : Set X)))).factorization 2 = 7 := by
  rw [I.oddTwoCoreIn_eq H, card_map_of_injective (subtype_injective _), I.factorization_Pre H]

theorem exists_d_normalizer (H : Hyp S R) {S₁ : Subgroup X}
    (hS₁N : S₁ ≤ normalizer (I.E : Set X)) (hS₁ : Nat.card S₁ = 256)
    (hS₁C : S₁ ⊓ centralizer (I.E : Set X) = I.E) :
    ∃ d, I.Mat d dCols ∧ d ∈ normalizer
      ((S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) := by
  set N := normalizer (I.E : Set X) with hN
  set P := A7Base.oddTwoCoreIn N with hP
  set Q₁ := S₁ ⊓ P with hQ₁
  obtain ⟨hQcard, -, hreal⟩ := I.Q₁_props H hS₁N hS₁ hS₁C
  obtain ⟨d₀, hd₀, hd₀c⟩ := I.exists_d_cols
  have hd₀M : I.Mat d₀ dCols := ⟨hd₀.1, hd₀c⟩
  set Q' := Q₁.map (MulAut.conj d₀).toMonoidHom with hQ'
  have hQP : Q₁ ≤ P := inf_le_right
  have hQ'P : Q' ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    exact conj_mem_oddTwoCoreIn' hd₀.1 (hQP hq)
  have hfac := I.card_oddTwoCoreIn H
  have hQ'card : Nat.card Q' = 128 := by
    rw [hQ', card_map_of_injective (MulAut.conj d₀).injective, hQcard]
  obtain ⟨h, hhP, hh⟩ := exists_conj_eq_of_card_eq hQ'P hQP
    (by rw [hQ'card, hfac]; rfl) (by rw [hQcard, hfac]; rfl)
  obtain ⟨q, hq, hqh⟩ := hreal h hhP
  refine ⟨q⁻¹ * h * d₀, hd₀M.central_mul hqh, ?_⟩
  · refine mem_normalizer_of_conj_mem fun p hp => ?_
    have h1 : h * (d₀ * p * d₀⁻¹) * h⁻¹ ∈ Q₁ := by
      rw [← hh]
      exact ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    have h2 : q⁻¹ * (h * (d₀ * p * d₀⁻¹) * h⁻¹) * q⁻¹⁻¹ ∈ Q₁ :=
      mul_mem (mul_mem (inv_mem hq) h1) (by rw [inv_inv]; exact hq)
    have e : q⁻¹ * h * d₀ * p * (q⁻¹ * h * d₀)⁻¹ =
        q⁻¹ * (h * (d₀ * p * d₀⁻¹) * h⁻¹) * q⁻¹⁻¹ := by group
    rw [e]
    exact h2

variable {I} in
theorem Mat.pow_three_mul_add_one {n : X} {c : Fin 4 → V4} (h : I.Mat n c)
    (hc : ∀ i, comp c (comp c c) i = bas i) (k : ℕ) : I.Mat (n ^ (3 * k + 1)) c := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have h3 : I.Mat (n ^ 3) bas := by
      have := h.mul (h.mul h)
      rwa [show comp c (comp c c) = bas from funext hc, ← pow_three] at this
    have := ih.mul h3
    rw [show comp c bas = c from funext fun i => lin_bas c i, ← pow_add] at this
    rwa [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by ring]

theorem exists_d₁₁ (H : Hyp S R) {S₁ : Subgroup X} (hTS : R ≤ S₁)
    (hS₁N : S₁ ≤ normalizer (I.E : Set X)) (hS₁ : Nat.card S₁ = 256)
    (hS₁C : S₁ ⊓ centralizer (I.E : Set X) = I.E) :
    ∃ d, I.Mat d dCols ∧
      d ∈ normalizer ((S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) ∧
      (∃ a : ℕ, d ^ (3 ^ a) = 1) ∧ I.ui * d * I.ui⁻¹ = d⁻¹ := by
  obtain ⟨d₀, hd₀, hd₀Q⟩ := I.exists_d_normalizer H hS₁N hS₁ hS₁C
  have huM := I.ui_mat H
  have hu2 : I.ui * I.ui = 1 := by rw [← pow_two]; exact I.ui_sq
  have huinv : I.ui⁻¹ = I.ui := inv_eq_of_mul_eq_one_right hu2
  have huS : I.ui ∈ S₁ := hTS (H.le I.ui_mem_TE)
  have huQ : I.ui ∈
      normalizer ((S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) := by
    refine mem_normalizer_of_conj_mem fun q hq => mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem (mul_mem huS (mem_inf.mp hq).1) (inv_mem huS)
    · exact conj_mem_oddTwoCoreIn' (hS₁N huS) (mem_inf.mp hq).2
  obtain ⟨d₂, hd₂⟩ : ∃ d₂, d₂ = d₀ * I.ui * d₀⁻¹ * I.ui⁻¹ := ⟨_, rfl⟩
  have hd₂M : I.Mat d₂ ddCols := by
    have := ((hd₀.mul huM).mul (hd₀.inv dCols_ddCols)).mul (huM.inv xCols_xCols)
    rwa [show comp (comp (comp dCols xCols) ddCols) xCols = ddCols from funext d₂_cols,
      ← hd₂] at this
  have hd₂inv : I.ui * d₂ * I.ui⁻¹ = d₂⁻¹ := by
    rw [hd₂, huinv]
    calc I.ui * (d₀ * I.ui * d₀⁻¹ * I.ui) * I.ui = I.ui * d₀ * I.ui * d₀⁻¹ * (I.ui * I.ui) := by
          group
      _ = I.ui * d₀ * I.ui * d₀⁻¹ := by rw [hu2, mul_one]
      _ = (d₀ * I.ui * d₀⁻¹ * I.ui)⁻¹ := by simp only [mul_inv_rev, inv_inv, huinv, mul_assoc]
  have hd₂Q : d₂ ∈
      normalizer ((S₁ ⊓ A7Base.oddTwoCoreIn (normalizer (I.E : Set X)) : Subgroup X) : Set X) := by
    rw [hd₂]
    exact mul_mem (mul_mem (mul_mem hd₀Q huQ) (inv_mem hd₀Q)) (inv_mem huQ)
  obtain ⟨a, r, hr3, hr⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos d₂).ne' 3 (by norm_num)
  have hpow : d₂ ^ (3 ^ a * r) = 1 := by rw [← hr]; exact pow_orderOf_eq_one d₂
  obtain ⟨m, hm2, hm⟩ : ∃ m : ℕ, m % 3 = 2 ∧ d₂ ^ (3 ^ a * m) = 1 := by
    rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h1 | h2
    · refine ⟨2 * r, by omega, ?_⟩
      rw [show 3 ^ a * (2 * r) = 3 ^ a * r * 2 by ring, pow_mul, hpow, one_pow]
    · exact ⟨r, h2, hpow⟩
  refine ⟨d₂ ^ m, ?_, pow_mem hd₂Q m, ⟨a, ?_⟩, ?_⟩
  · have h1 := (hd₂M.pow_three_mul_add_one ddCols_cube (m / 3)).mul hd₂M
    rwa [show comp ddCols ddCols = dCols from funext ddCols_sq, ← pow_succ,
      show 3 * (m / 3) + 1 + 1 = m by omega] at h1
  · rw [← pow_mul, mul_comm, hm]
  · rw [← conj_pow, hd₂inv, inv_pow]

end Inst

end CFSG.OddStandard.SmallF3.L33.KD.KD46
