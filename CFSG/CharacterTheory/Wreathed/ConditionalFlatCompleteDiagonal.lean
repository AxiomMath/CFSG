module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteFrame
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

@[expose] def CoreAt {I : Type*} (i₀ i₁ i₂ i₃ i₄ : I) (δ₀ δ₁ δ₂ δ₃ δ₄ : ℤ) (a : Fin 3)
    (v : I → ℤ) : Prop :=
  v i₀ = δ₀ * caseZ0 a ∧ v i₁ = -(δ₁ * caseZ0 a) ∧ v i₂ = δ₂ * caseZ2 a ∧
    v i₃ = -(δ₃ * caseZ2 a) ∧ v i₄ = δ₄ * caseW a

@[expose] def pairA : Fin 2 → Fin 4 := ![0, 2]

@[expose] def pairB : Fin 2 → Fin 4 := ![1, 3]

@[expose] def PairAt {I : Type*} (q : Fin 4 → I) (η : Fin 4 → ℤ) (v : I → ℤ) (e : Fin 2)
    (σ : ℤ) : Prop :=
  v (q (pairA e)) = σ * η (pairA e) ∧ v (q (pairB e)) = -(σ * η (pairB e)) ∧
    v (q (pairA (1 - e))) = 0 ∧ v (q (pairB (1 - e))) = 0

theorem pairAt_zero {I : Type*} {q : Fin 4 → I} {η : Fin 4 → ℤ} {v : I → ℤ} {σ : ℤ}
    (h0 : v (q 0) = σ * η 0) (h1 : v (q 1) = -(σ * η 1)) (h2 : v (q 2) = 0)
    (h3 : v (q 3) = 0) : PairAt q η v 0 σ :=
  ⟨h0, h1, h2, h3⟩

theorem pairAt_one {I : Type*} {q : Fin 4 → I} {η : Fin 4 → ℤ} {v : I → ℤ} {σ : ℤ}
    (h0 : v (q 0) = 0) (h1 : v (q 1) = 0) (h2 : v (q 2) = σ * η 2)
    (h3 : v (q 3) = -(σ * η 3)) : PairAt q η v 1 σ :=
  ⟨h2, h3, h0, h1⟩

theorem one_le_mul_self_of_odd' {x : ℤ} (hx : Odd x) : 1 ≤ x * x := by
  obtain ⟨t, rfl⟩ := hx
  rcases le_or_gt 0 t with h | h <;> nlinarith

theorem eq_zero_of_sum_mul_self_eq_zero' {I : Type*} {S : Finset I} {v : I → ℤ}
    (h : ∑ i ∈ S, v i * v i = 0) {i : I} (hi : i ∈ S) : v i = 0 :=
  mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun j _ => mul_self_nonneg (v j)).mp h
    i hi)

theorem exists_unit_of_sum_mul_self_eq_one {I : Type*} [DecidableEq I] {S : Finset I}
    {v : I → ℤ} (h : ∑ i ∈ S, v i * v i = 1) :
    ∃ ξ ∈ S, (v ξ = 1 ∨ v ξ = -1) ∧ ∀ i ∈ S, i ≠ ξ → v i = 0 := by
  have hne : ∃ ξ ∈ S, v ξ ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero fun i hi => by rw [hc i hi, mul_zero]] at h
    exact absurd h (by norm_num)
  obtain ⟨ξ, hξ, hξ0⟩ := hne
  have hsplit := Finset.add_sum_erase S (fun i => v i * v i) hξ
  have hrest : 0 ≤ ∑ i ∈ S.erase ξ, v i * v i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hpos : 1 ≤ v ξ * v ξ := by
    rcases lt_or_gt_of_ne hξ0 with h' | h' <;> nlinarith
  have h1 : v ξ * v ξ = 1 := by linarith
  have h0 : ∑ i ∈ S.erase ξ, v i * v i = 0 := by linarith
  refine ⟨ξ, hξ, ?_, fun i hi hiξ =>
    eq_zero_of_sum_mul_self_eq_zero' h0 (Finset.mem_erase.mpr ⟨hiξ, hi⟩)⟩
  have hb : -1 ≤ v ξ ∧ v ξ ≤ 1 := by constructor <;> nlinarith
  omega

namespace Frame

variable {I H K : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype K]
  {d : I → ℤ} {A : H → I → ℤ} {E : K → I → ℤ} {Ys : I → ℤ} {Y : K → I → ℤ} {C : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : H → I} {q : K → Fin 4 → I} {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ}
  {η : K → Fin 4 → ℤ} {D : ℤ}

section Diagonal

variable (F : Frame d A E Ys Y C i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D)
include F

omit [Fintype I] [Fintype H] [Fintype K] in
theorem sum_single_q_self (k : K) (l₀ : Fin 4) :
    ∑ l, (Pi.single (q k l) (η k l) : I → ℤ) (q k l₀) = η k l₀ := by
  rw [Finset.sum_eq_single l₀]
  · simp
  · intro l _ hl
    rw [Pi.single_apply, ite_eq_right]
    intro h
    exact hl (F.q_inj h).2.symm
  · simp

omit [Fintype I] [Fintype H] [Fintype K] F in
theorem sum_single_q_of_ne (k : K) {i : I} (hi : ∀ l, q k l ≠ i) :
    ∑ l, (Pi.single (q k l) (η k l) : I → ℤ) i = 0 :=
  Finset.sum_eq_zero fun l _ => by rw [Pi.single_apply, ite_eq_right fun h => hi l h.symm]

omit [Fintype I] [Fintype H] [Fintype K] in
theorem sub_E_C (k : K) (i : I) :
    E k i - C i = 2 * ((Pi.single i₁ δ₁ : I → ℤ) i + (Pi.single i₃ δ₃ : I → ℤ) i -
      (Pi.single i₄ δ₄ : I → ℤ) i) + ∑ l, (Pi.single (q k l) (η k l) : I → ℤ) i := by
  rw [F.formE k, F.formC]
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_apply]
  have h4 : (Pi.single i₄ (2 * δ₄) : I → ℤ) i = 2 * (Pi.single i₄ δ₄ : I → ℤ) i := by
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs <;> ring
  rw [h4]
  ring

omit [Fintype K] in
theorem diag_pair (hH : 2 ≤ Fintype.card H) (k : K) {c c' : I → ℤ}
    (hcc : c ⬝ᵥ c = 8) (hc'c' : c' ⬝ᵥ c' = 8) (hcc' : c ⬝ᵥ c' = 6)
    (hcA : ∀ h, c ⬝ᵥ A h = 0) (hc'A : ∀ h, c' ⬝ᵥ A h = 0) (hcYs : c ⬝ᵥ Ys = 0)
    (hc'Ys : c' ⬝ᵥ Ys = 0) (hcC : c ⬝ᵥ C = 6) (hc'C : c' ⬝ᵥ C = 6) (hcE : c ⬝ᵥ E k = 0)
    (hc'E : c' ⬝ᵥ E k = 0) (hcY : c ⬝ᵥ Y k = 0) (hc'Y : c' ⬝ᵥ Y k = 0)
    (hpar : ∀ i, E k i ≡ C i + c i + c' i [ZMOD 2]) :
    ∃ (a : Fin 3) (e : Fin 2) (σ σ' : ℤ), (σ = 1 ∨ σ = -1) ∧ (σ' = 1 ∨ σ' = -1) ∧
      CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a c ∧ CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a c' ∧
      (∀ h, c (p h) = 0 ∧ c' (p h) = 0) ∧
      PairAt (q k) (η k) c e σ ∧ PairAt (q k) (η k) c' (1 - e) σ' ∧
      (∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c' i = c i) ∧
      ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c i * c i = 6 - caseNorm a := by
  set Δ : I → ℤ := c - c' with hΔ
  have hΔpar : ∀ i, Δ i ≡ E k i - C i [ZMOD 2] := by
    intro i
    have h := hpar i
    simp only [hΔ, Pi.sub_apply]
    unfold Int.ModEq at h ⊢
    omega
  have hΔodd : ∀ l, Odd (Δ (q k l)) := by
    intro l
    have h := hΔpar (q k l)
    rw [F.sub_E_C k, F.sum_single_q_self k l] at h
    have hη := F.sη k l
    rw [Int.odd_iff]
    unfold Int.ModEq at h
    rcases hη with hη | hη <;> rw [hη] at h <;> omega
  have hΔeven : ∀ i, (∀ l, q k l ≠ i) → Even (Δ i) := by
    intro i hi
    have h := hΔpar i
    rw [F.sub_E_C k, sum_single_q_of_ne k hi, add_zero] at h
    rw [Int.even_iff]
    unfold Int.ModEq at h
    omega
  have hΔΔ : Δ ⬝ᵥ Δ = 4 := by
    simp only [hΔ, sub_dotProduct, dotProduct_sub]
    rw [dotProduct_comm c' c]
    linarith
  have hsplitΔ := F.sum_split k fun i => Δ i * Δ i
  have hΔvv : Δ ⬝ᵥ Δ = ∑ i, Δ i * Δ i := rfl
  have hq1 := fun l => one_le_mul_self_of_odd' (hΔodd l)
  have hcore0 := mul_self_nonneg (Δ i₀)
  have hcore1 := mul_self_nonneg (Δ i₁)
  have hcore2 := mul_self_nonneg (Δ i₂)
  have hcore3 := mul_self_nonneg (Δ i₃)
  have hcore4 := mul_self_nonneg (Δ i₄)
  have hoddnn : 0 ≤ ∑ h, Δ (p h) * Δ (p h) := Finset.sum_nonneg fun h _ => mul_self_nonneg _
  have hrestnn : 0 ≤ ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), Δ i * Δ i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hq4 : ∑ l, Δ (q k l) * Δ (q k l) = Δ (q k 0) * Δ (q k 0) + Δ (q k 1) * Δ (q k 1) +
      Δ (q k 2) * Δ (q k 2) + Δ (q k 3) * Δ (q k 3) := Fin.sum_univ_four _
  have hq0 := hq1 0
  have hq1' := hq1 1
  have hq2 := hq1 2
  have hq3 := hq1 3
  rw [← hΔvv, hΔΔ, hq4] at hsplitΔ
  have hΔi₀ : Δ i₀ = 0 := mul_self_eq_zero.mp (by linarith)
  have hΔi₁ : Δ i₁ = 0 := mul_self_eq_zero.mp (by linarith)
  have hΔi₂ : Δ i₂ = 0 := mul_self_eq_zero.mp (by linarith)
  have hΔi₃ : Δ i₃ = 0 := mul_self_eq_zero.mp (by linarith)
  have hΔi₄ : Δ i₄ = 0 := mul_self_eq_zero.mp (by linarith)
  have hΔp : ∀ h, Δ (p h) = 0 := fun h =>
    eq_zero_of_sum_mul_self_eq_zero' (v := fun h => Δ (p h)) (S := Finset.univ) (by linarith)
      (Finset.mem_univ h)
  have hΔrest : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), Δ i = 0 := fun i hi =>
    eq_zero_of_sum_mul_self_eq_zero' (by linarith) hi
  have hΔq : ∀ l, Δ (q k l) * Δ (q k l) = 1 := by
    intro l
    fin_cases l <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> linarith
  have hagree : ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c' i = c i := fun i hi => by
    have h := hΔrest i hi
    simp only [hΔ, Pi.sub_apply] at h
    linarith
  have hag₀ : c' i₀ = c i₀ := by
    have h := hΔi₀
    simp only [hΔ, Pi.sub_apply] at h
    linarith
  have hag₁ : c' i₁ = c i₁ := by
    have h := hΔi₁
    simp only [hΔ, Pi.sub_apply] at h
    linarith
  have hag₂ : c' i₂ = c i₂ := by
    have h := hΔi₂
    simp only [hΔ, Pi.sub_apply] at h
    linarith
  have hag₃ : c' i₃ = c i₃ := by
    have h := hΔi₃
    simp only [hΔ, Pi.sub_apply] at h
    linarith
  have hag₄ : c' i₄ = c i₄ := by
    have h := hΔi₄
    simp only [hΔ, Pi.sub_apply] at h
    linarith
  have hagp : ∀ h, c' (p h) = c (p h) := fun h => by
    have h' := hΔp h
    simp only [hΔ, Pi.sub_apply] at h'
    linarith
  have hsplitc := F.sum_split k fun i => c i * c i
  have hsplitc' := F.sum_split k fun i => c' i * c' i
  have hcvv : c ⬝ᵥ c = ∑ i, c i * c i := rfl
  have hc'vv : c' ⬝ᵥ c' = ∑ i, c' i * c' i := rfl
  rw [← hcvv, hcc] at hsplitc
  have hoddc' : ∑ h, c' (p h) * c' (p h) = ∑ h, c (p h) * c (p h) :=
    Finset.sum_congr rfl fun h _ => by rw [hagp h]
  have hrestc' : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c' i * c' i =
      ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c i * c i :=
    Finset.sum_congr rfl fun i hi => by rw [hagree i hi]
  rw [← hc'vv, hc'c', hag₀, hag₁, hag₂, hag₃, hag₄, hoddc', hrestc'] at hsplitc'
  have hs₂eq : ∑ l, c' (q k l) * c' (q k l) = ∑ l, c (q k l) * c (q k l) := by linarith
  have hpairsq : ∀ l, 1 ≤ c (q k l) * c (q k l) + c' (q k l) * c' (q k l) := by
    intro l
    have h := hΔq l
    simp only [hΔ, Pi.sub_apply] at h
    have hx := mul_self_nonneg (c (q k l))
    have hy := mul_self_nonneg (c' (q k l))
    by_contra hlt
    have h1 : c (q k l) * c (q k l) = 0 := by linarith
    have h2 : c' (q k l) * c' (q k l) = 0 := by linarith
    rw [mul_self_eq_zero.mp h1, mul_self_eq_zero.mp h2] at h
    norm_num at h
  have hs₂ : 2 ≤ ∑ l, c (q k l) * c (q k l) := by
    have h := Finset.sum_le_sum fun l (_ : l ∈ Finset.univ) => hpairsq l
    rw [Finset.sum_add_distrib, hs₂eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      at h
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one] at h
    linarith
  obtain ⟨hcp, hc01, hc23, a, e0, e1, e2, e3, e4, hR⟩ :=
    F.column_shape hH k hcA hcYs hcC hcE hcY (by rw [hcc]; linarith)
  obtain ⟨hc'p, hc'01, hc'23, -⟩ :=
    F.column_shape hH k hc'A hc'Ys hc'C hc'E hc'Y (by rw [hc'c', hs₂eq]; linarith)
  have hRnn : 0 ≤ ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c i * c i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hη₀ := sign_mul_self (F.sη k 0)
  have hη₁ := sign_mul_self (F.sη k 1)
  have hη₂ := sign_mul_self (F.sη k 2)
  have hη₃ := sign_mul_self (F.sη k 3)
  have hnormA : caseNorm a = 5 ∨ caseNorm a = 6 := by
    fin_cases a <;> simp [caseNorm]
  have hsq : ∀ v : I → ℤ, ∀ l, (η k l * v (q k l)) * (η k l * v (q k l)) =
      v (q k l) * v (q k l) := by
    intro v l
    have h := sign_mul_self (F.sη k l)
    linear_combination (v (q k l) * v (q k l)) * h
  have hs₂c : ∑ l, c (q k l) * c (q k l) = 2 := by
    have e01 : c (q k 1) * c (q k 1) = c (q k 0) * c (q k 0) := by
      rw [← hsq c 0, ← hsq c 1, show η k 1 * c (q k 1) = -(η k 0 * c (q k 0)) by linarith]
      ring
    have e23 : c (q k 3) * c (q k 3) = c (q k 2) * c (q k 2) := by
      rw [← hsq c 2, ← hsq c 3, show η k 3 * c (q k 3) = -(η k 2 * c (q k 2)) by linarith]
      ring
    have hform : ∑ l, c (q k l) * c (q k l) =
        2 * (c (q k 0) * c (q k 0) + c (q k 2) * c (q k 2)) := by
      rw [Fin.sum_univ_four, e01, e23]
      ring
    have hle : ∑ l, c (q k l) * c (q k l) ≤ 3 := by
      rw [hcc] at hR
      rcases hnormA with h | h <;> rw [h] at hR <;> linarith
    clear_value Δ
    generalize ∑ l, c (q k l) * c (q k l) = S at hform hle hs₂ ⊢
    generalize c (q k 0) * c (q k 0) + c (q k 2) * c (q k 2) = X at hform
    omega
  have hs₂c' : ∑ l, c' (q k l) * c' (q k l) = 2 := by rw [hs₂eq, hs₂c]
  have hpc := pair_cases hc01 hc23 (by
    rw [hsq c 0, hsq c 1, hsq c 2, hsq c 3, ← hs₂c, Fin.sum_univ_four])
  have hpc' := pair_cases hc'01 hc'23 (by
    rw [hsq c' 0, hsq c' 1, hsq c' 2, hsq c' 3, ← hs₂c', Fin.sum_univ_four])
  have hrec : ∀ (v : I → ℤ) (l : Fin 4) (s : ℤ), η k l * v (q k l) = s →
      v (q k l) = s * η k l := by
    intro v l s hs
    have h := sign_mul_self (F.sη k l)
    linear_combination η k l * hs - v (q k l) * h
  have hR' : ∑ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k), c i * c i = 6 - caseNorm a := by
    rw [hR, hcc, hs₂c]
    ring
  have hcoreC : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a c := ⟨e0, e1, e2, e3, e4⟩
  have hcoreC' : CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a c' :=
    ⟨hag₀.trans e0, hag₁.trans e1, hag₂.trans e2, hag₃.trans e3, hag₄.trans e4⟩
  have hp' : ∀ h, c (p h) = 0 ∧ c' (p h) = 0 := fun h => ⟨hcp h, hc'p h⟩
  have hodd2 : Odd (c (q k 2) - c' (q k 2)) := hΔodd 2
  have hodd0 : Odd (c (q k 0) - c' (q k 0)) := hΔodd 0
  have hz : ∀ (v : I → ℤ) (l : Fin 4), η k l * v (q k l) = 0 → v (q k l) = 0 := fun v l h =>
    (hrec v l 0 h).trans (zero_mul _)
  rcases hpc with ⟨hy₀, hy₁, hy₂, hy₃⟩ | ⟨hy₀, hy₁, hy₂, hy₃⟩
  ·
    rcases hpc' with ⟨-, -, hy₂', -⟩ | ⟨hy₀', hy₁', hy₂', hy₃'⟩
    · exfalso
      rw [hz c 2 hy₂, hz c' 2 (by rw [hy₂']), sub_zero] at hodd2
      exact absurd hodd2 (by decide)
    · refine ⟨a, 0, η k 0 * c (q k 0), η k 2 * c' (q k 2), hy₀, hy₂', hcoreC, hcoreC', hp',
        pairAt_zero (hrec c 0 _ rfl) ((hrec c 1 _ hy₁).trans (by ring)) (hz c 2 hy₂)
          (hz c 3 hy₃),
        show PairAt (q k) (η k) c' 1 _ from pairAt_one (hz c' 0 hy₀') (hz c' 1 hy₁')
          (hrec c' 2 _ rfl) ((hrec c' 3 _ hy₃').trans (by ring)), hagree, hR'⟩
  ·
    rcases hpc' with ⟨hy₀', hy₁', hy₂', hy₃'⟩ | ⟨hy₀', -, -, -⟩
    · refine ⟨a, 1, η k 2 * c (q k 2), η k 0 * c' (q k 0), hy₂, hy₀', hcoreC, hcoreC', hp',
        pairAt_one (hz c 0 hy₀) (hz c 1 hy₁) (hrec c 2 _ rfl)
          ((hrec c 3 _ hy₃).trans (by ring)),
        show PairAt (q k) (η k) c' 0 _ from pairAt_zero (hrec c' 0 _ rfl)
          ((hrec c' 1 _ hy₁').trans (by ring)) (hz c' 2 hy₂') (hz c' 3 hy₃'),
        hagree, hR'⟩
    · exfalso
      rw [hz c 0 hy₀, hz c' 0 (by rw [hy₀']), sub_zero] at hodd0
      exact absurd hodd0 (by decide)

end Diagonal

end Frame

end CFSG.Wreathed.FlatComplete
