module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YCtx
public import CFSG.Quasithin.H13.L32AC50aPack
public import CFSG.Permutation.FinPackInv

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23.Y6Pack

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin.H13.L32A.C.Alt7Pack

theorem h6 : (6 : ℕ) ≤ 16 := by norm_num

@[expose] def oneY : ℕ := 5517840

theorem enc_oneY : enc (1 : Perm (Fin 6)) = oneY := by decide +kernel

@[expose] def p0C : List ℕ :=
  [5517840, 3490320, 4411920, 5517345, 3489825, 4411425, 5517570, 3490050, 4411650]

theorem p0_fam_ok : allLtK (fun i => allLtK (fun j =>
    memK (mulK 6 (powK 6 oneY 5517345 i) (powK 6 oneY 3490320 j)) p0C) 3) 3 = true := by
  decide +kernel

theorem p0_surj_ok : ∀ c ∈ p0C, ∃ i < 3, ∃ j < 3,
    mulK 6 (powK 6 oneY 5517345 i) (powK 6 oneY 3490320 j) = c := by
  decide +kernel

theorem mem_fam_iff (c1 c2 : Perm (Fin 6)) (h1 : enc c1 = 5517345) (h2 : enc c2 = 3490320)
    (x : Perm (Fin 6)) :
    x ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).image (fun p => c1 ^ (p.1 : ℕ) * c2 ^ (p.2 : ℕ)) ↔
      memK (enc x) p0C = true := by
  constructor
  · intro hx
    obtain ⟨⟨i, j⟩, -, rfl⟩ := Finset.mem_image.1 hx
    rw [enc_mul h6, enc_pow h6, enc_pow h6, enc_oneY, h1, h2]
    exact allLtK_iff.1 (allLtK_iff.1 p0_fam_ok i i.isLt) j j.isLt
  · intro hx
    obtain ⟨i, hi, j, hj, e⟩ := p0_surj_ok _ (memK_iff.1 hx)
    rw [← h1, ← h2, ← enc_oneY, ← enc_pow h6, ← enc_pow h6, ← enc_mul h6] at e
    rw [← enc_inj h6 e]
    exact Finset.mem_image.2 ⟨(⟨i, hi⟩, ⟨j, hj⟩), Finset.mem_univ _, rfl⟩

theorem surj_fam (c1 c2 : Perm (Fin 6)) (h1 : enc c1 = 5517345) (h2 : enc c2 = 3490320) :
    ∀ c ∈ p0C, ∃ x ∈ (Finset.univ : Finset (Fin 3 × Fin 3)).image
      (fun p => c1 ^ (p.1 : ℕ) * c2 ^ (p.2 : ℕ)), enc x = c := by
  intro c hc
  obtain ⟨i, hi, j, hj, e⟩ := p0_surj_ok c hc
  refine ⟨c1 ^ i * c2 ^ j, Finset.mem_image.2 ⟨(⟨i, hi⟩, ⟨j, hj⟩), Finset.mem_univ _, rfl⟩, ?_⟩
  rw [enc_mul h6, enc_pow h6, enc_pow h6, enc_oneY, h1, h2]
  exact e

@[expose] noncomputable def conjKY (cg cx : ℕ) : ℕ := mulK 6 (mulK 6 cg cx) (invCK 6 cg)

theorem enc_conjY (g x : Perm (Fin 6)) : enc (g * x * g⁻¹) = conjKY (enc g) (enc x) := by
  rw [conjKY, enc_mul h6, enc_mul h6, enc_inv_invCK h6]

@[expose] def bsP (f : Fin 6 → Fin 6) : Bool :=
  decide (∀ i j : Fin 6, i.val / 3 = j.val / 3 ↔ (f i).val / 3 = (f j).val / 3)

theorem mem_blockStab_K (σ : Perm (Fin 6)) : σ ∈ blockStab ↔ bsP (decK 6 (enc σ)) = true := by
  rw [decK_enc h6, bsP, decide_eq_true_iff]
  exact Iff.rfl

theorem conj_ok : walkK 6 (fun c => allK (fun x => memK (conjKY c x) p0C) p0C ||
    allK (fun x => Nat.beq x oneY || !memK (conjKY c x) p0C) p0C) 6 0 0 0 = true := by
  decide +kernel

theorem norm_ok : walkK 6 (fun c => !allK (fun x => memK (conjKY c x) p0C) p0C ||
    bsP (decK 6 c)) 6 0 0 0 = true := by
  decide +kernel

theorem conj_or_disjoint_of (S : Finset (Perm (Fin 6)))
    (hS : ∀ x, x ∈ S ↔ memK (enc x) p0C = true) (τ : Perm (Fin 6)) :
    (∀ x ∈ S, τ * x * τ⁻¹ ∈ S) ∨ (∀ x ∈ S, x ≠ 1 → τ * x * τ⁻¹ ∉ S) := by
  have h := walkK_sound conj_ok τ
  rw [Bool.or_eq_true, allK_iff, allK_iff] at h
  rcases h with h | h
  · left
    intro x hx
    rw [hS, enc_conjY]
    exact h _ (memK_iff.1 ((hS x).1 hx))
  · right
    intro x hx hx1 hc
    have h1 := h _ (memK_iff.1 ((hS x).1 hx))
    rw [hS, enc_conjY] at hc
    rw [hc, ← enc_oneY, beq_enc_false h6 hx1] at h1
    exact absurd h1 (by decide)

theorem normalizer_le_of (S : Finset (Perm (Fin 6)))
    (hS : ∀ x, x ∈ S ↔ memK (enc x) p0C = true) (hsurj : ∀ c ∈ p0C, ∃ x ∈ S, enc x = c)
    (τ : Perm (Fin 6)) (h : ∀ x ∈ S, τ * x * τ⁻¹ ∈ S) : τ ∈ blockStab := by
  have h1 := walkK_sound norm_ok τ
  have h2 : allK (fun x => memK (conjKY (enc τ) x) p0C) p0C = true := by
    refine allK_iff.2 fun c hc => ?_
    obtain ⟨x, hx, rfl⟩ := hsurj c hc
    rw [← enc_conjY, ← hS]
    exact h x hx
  rw [h2, Bool.not_true, Bool.false_or] at h1
  exact (mem_blockStab_K τ).2 h1

end CFSG.OddStandard.HigherRank.YamadaG23.Y6Pack
