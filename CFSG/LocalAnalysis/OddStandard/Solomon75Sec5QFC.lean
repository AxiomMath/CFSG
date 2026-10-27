module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QH0
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Defs

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

open scoped commutatorElement

section FC

@[expose] def sig0 (n : ℕ) [NeZero n] : Perm (Fin n) := swapsPerm n [(0, 1), (2, 3), (4, 5), (6, 7)]

@[expose] def conjSet {n : ℕ} (H : Subgroup (Perm (Fin n))) (x : Perm (Fin n)) :
    Set (Perm (Fin n)) :=
  {t | ∃ g ∈ H, t = g * x * g⁻¹}

@[expose] noncomputable def Bn (n : ℕ) [NeZero n] : Subgroup (Perm (Fin n)) :=
  if n = 11 then zpowers (swapsPerm n [(8, 9), (9, 10)]) else ⊥

@[expose] def GoodSet (n : ℕ) (Γ : Set (Perm (Fin n))) : Prop :=
  (n ≤ 10 ∧ ∀ g ∈ Γ, g ^ 8 = 1) ∨
    (n = 11 ∧ ∀ a ∈ Γ, ∀ b ∈ Γ, ∀ c ∈ Γ, ∀ d ∈ Γ, ⁅⁅a, b⁆, ⁅c, d⁆⁆ = 1)

variable (n : ℕ) [NeZero n]

@[expose] def FC2 (σ : Perm (Fin n)) : Prop :=
  ∀ x ∈ centralizer ({σ} : Set (Perm (Fin n))), (∃ j : ℕ, x ^ (2 ^ j) = 1) → x ^ 8 = 1

@[expose] def FCR (σ : Perm (Fin n)) : Prop :=
  ∀ x ∈ centralizer ({σ} : Set (Perm (Fin n))), x ^ 8 = 1 → x ∉ zpowers σ →
    (∃ r ∈ Subgroup.closure (conjSet (H0 σ) x ∪ {σ}), r * r = 1 ∧ r ≠ 1 ∧ 4 ≤ fixCount r) ∨
    (∃ S : Set (Perm (Fin n)), S ⊆ conjSet (H0 σ) x ∧
      GoodSet n {g | g ∈ centralizer ({σ} : Set (Perm (Fin n))) ∧ ∀ t ∈ S, ⁅g, t⁆ ∈ Bn n})

@[expose] def FCB (σ : Perm (Fin n)) : Prop :=
  ∀ b ∈ centralizer ({σ} : Set (Perm (Fin n))), Odd (orderOf b) → b ∉ Bn n →
    ∃ g ∈ H0 σ, Even (orderOf (b * (g * b * g⁻¹)))

@[expose] def Wn (σ : Perm (Fin n)) : Subgroup (Perm (Fin n)) :=
  if n ≤ 10 then Subgroup.closure {g | g ∈ H0 σ ∧ Odd (orderOf g)}
  else ⁅⁅H0 σ, H0 σ⁆, ⁅H0 σ, H0 σ⁆⁆

@[expose] def FCO2 (σ : Perm (Fin n)) : Prop :=
  ∃ ι ∈ Wn n σ, ι * ι = 1 ∧ ι ≠ 1 ∧ 4 ≤ fixCount ι

@[expose] def FCAll : Prop := FC2 n (sig0 n) ∧ FCR n (sig0 n) ∧ FCB n (sig0 n) ∧ FCO2 n (sig0 n)

end FC

section Sig0

theorem sig0_val8 : ∀ x : Fin 8, ((sig0 8 x : Fin 8) : ℕ) = if (x : ℕ) < 8 then
    (if (x : ℕ) % 2 = 0 then (x : ℕ) + 1 else (x : ℕ) - 1) else x := by decide

theorem sig0_val9 : ∀ x : Fin 9, ((sig0 9 x : Fin 9) : ℕ) = if (x : ℕ) < 8 then
    (if (x : ℕ) % 2 = 0 then (x : ℕ) + 1 else (x : ℕ) - 1) else x := by decide

theorem sig0_val10 : ∀ x : Fin 10, ((sig0 10 x : Fin 10) : ℕ) = if (x : ℕ) < 8 then
    (if (x : ℕ) % 2 = 0 then (x : ℕ) + 1 else (x : ℕ) - 1) else x := by decide

theorem sig0_val11 : ∀ x : Fin 11, ((sig0 11 x : Fin 11) : ℕ) = if (x : ℕ) < 8 then
    (if (x : ℕ) % 2 = 0 then (x : ℕ) + 1 else (x : ℕ) - 1) else x := by decide

theorem sig0_val (n : ℕ) [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11) (x : Fin n) :
    ((sig0 n x : Fin n) : ℕ) = if (x : ℕ) < 8 then
      (if (x : ℕ) % 2 = 0 then (x : ℕ) + 1 else (x : ℕ) - 1) else x := by
  interval_cases n
  · exact sig0_val8 x
  · exact sig0_val9 x
  · exact sig0_val10 x
  · exact sig0_val11 x

theorem sig0_eq_stdInv (n : ℕ) [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11) :
    sig0 n = stdInv n 4 (by omega) := by
  refine Equiv.ext fun x => ?_
  by_cases hx : (x : ℕ) < 8
  · have hmem : x ∈ Set.range (pairEmb n 4 (by omega)) := by
      refine ⟨(⟨x.val / 2, by omega⟩, ⟨x.val % 2, by omega⟩), ?_⟩
      apply Fin.ext
      show 2 * (x.val / 2) + x.val % 2 = x.val
      omega
    obtain ⟨⟨i, j⟩, rfl⟩ := hmem
    rw [stdInv_apply_pair]
    apply Fin.ext
    rw [sig0_val n hn hn']
    have hi := i.2
    have hj := j.2
    have e1 : ((pairEmb n 4 (by omega) (i, j) : Fin n) : ℕ) = 2 * i.val + j.val := rfl
    have e2 : ((pairEmb n 4 (by omega) (i, Equiv.swap (0 : Fin 2) 1 j) : Fin n) : ℕ) =
        2 * i.val + (Equiv.swap (0 : Fin 2) 1 j).val := rfl
    have e3 : ((Equiv.swap (0 : Fin 2) 1 j : Fin 2) : ℕ) = 1 - j.val := by
      fin_cases j <;> simp
    rw [e1, e2, e3]
    split_ifs <;> omega
  · rw [stdInv_apply_of_notMem]
    · apply Fin.ext
      rw [sig0_val n hn hn']
      simp [hx]
    · rintro ⟨⟨i, j⟩, hij⟩
      apply hx
      have := congrArg Fin.val hij
      have e1 : ((pairEmb n 4 (by omega) (i, j) : Fin n) : ℕ) = 2 * i.val + j.val := rfl
      have hi := i.2
      have hj := j.2
      omega

theorem sig0_spec (n : ℕ) [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11) :
    sig0 n * sig0 n = 1 ∧ (sig0 n).support.card = 8 ∧ sign (sig0 n) = 1 := by
  rw [sig0_eq_stdInv n hn hn']
  have h1 : stdInv n 4 (by omega) * stdInv n 4 (by omega) = (1 : Perm (Fin n)) := stdInv_mul_self
  have h2 : (stdInv n 4 (by omega)).support.card = 8 := card_support_stdInv
  exact ⟨h1, h2, IsoI.sign_eq_one ⟨h1, h2⟩⟩

end Sig0

end CFSG.OddStandard.Solomon75
