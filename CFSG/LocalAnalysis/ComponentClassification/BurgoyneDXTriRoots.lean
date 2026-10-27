module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Triality

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.DX.Tri

open CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinPlus
open CFSG.LieType.Steinberg.SpinFrame CFSG.ClassicalInvolution.G2D4Models.Twin

@[expose] def posList : List (Fin 4 → ℤ) :=
  [![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![1, 1, 0, 0], ![0, 1, 1, 0],
    ![0, 1, 0, 1], ![1, 1, 1, 0], ![1, 1, 0, 1], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 2, 1, 1]]

@[expose] def rootList : List (Fin 4 → ℤ) := posList ++ posList.map (-·)

instance decIsLong (e : Fin 4 → ℤ) : Decidable (IsLong e) := by
  unfold IsLong
  infer_instance

instance decIsRep (p : ChainRep 4) (a b : Fin 4 → ℤ) : Decidable (p.IsRep a b) := by
  unfold ChainRep.IsRep
  infer_instance

theorem isLong_of_mem : ∀ γ ∈ rootList, IsLong (toStdD 4 γ) := by
  decide +kernel

theorem exists_mem_of_long : ∀ (i j : Fin 4), i ≠ j → ∀ s t : Bool,
    ∃ γ ∈ rootList, toStdD 4 γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) := by
  decide +kernel

theorem mem_roots_iff {K : Type} [Field K] (hn : 3 ≤ 4) {γ : Fin 4 → ℤ} :
    γ ∈ (Φ 4 K hn).roots ↔ γ ∈ rootList := by
  rw [Φ_roots, ← isLong_toStdD_iff (by norm_num)]
  constructor
  · rintro ⟨i, j, hij, s, t, h⟩
    obtain ⟨γ', hγ', e⟩ := exists_mem_of_long i j hij s t
    rw [← e] at h
    rw [toStdD_injective 4 h]
    exact hγ'
  · exact isLong_of_mem γ

@[expose] def piT (γ : Fin 4 → ℤ) : Fin 4 → ℤ := γ ∘ triEquiv.symm

theorem piT_add (α β : Fin 4 → ℤ) : piT (α + β) = piT α + piT β := rfl

theorem piT_neg (α : Fin 4 → ℤ) : piT (-α) = -piT α := rfl

theorem piT_single : ∀ k : Fin 4, piT (Pi.single k 1) = Pi.single (triPerm k) 1 := by
  decide +kernel

theorem piT_mem : ∀ γ ∈ rootList, piT γ ∈ rootList := by
  decide +kernel

theorem piT_piT_piT (γ : Fin 4 → ℤ) : piT (piT (piT γ)) = γ := by
  funext i
  fin_cases i <;> rfl

theorem piT_injective : Function.Injective piT := fun a b h => by
  rw [← piT_piT_piT a, h, piT_piT_piT]

@[expose] def epsT (γ : Fin 4 → ℤ) : ℤ :=
  if γ ∈ ([![1, 1, 0, 0], ![-1, -1, 0, 0], ![0, 1, 0, 1], ![0, -1, 0, -1]] : List (Fin 4 → ℤ))
  then -1 else 1

theorem epsT_mul_self (γ : Fin 4 → ℤ) : epsT γ * epsT γ = 1 := by
  unfold epsT
  split_ifs <;> norm_num

@[expose] def crep (a b : Fin 4 → ℤ) : ChainRep 4 :=
  let j := ((List.finRange 4).find? fun j => a j ≠ 0 ∧ b j ≠ 0).getD 0
  let i := ((List.finRange 4).find? fun i => i ≠ j ∧ a i ≠ 0).getD 0
  let k := ((List.finRange 4).find? fun k => k ≠ j ∧ b k ≠ 0).getD 0
  ⟨i, j, k, decide (0 < a i), decide (0 < a j), decide (0 < b k)⟩

theorem crep_isRep : ∀ α ∈ rootList, ∀ β ∈ rootList, α + β ∈ rootList →
    (crep (toStdD 4 α) (toStdD 4 β)).IsRep (toStdD 4 α) (toStdD 4 β) := by
  decide +kernel

theorem coeff_crep_piT : ∀ α ∈ rootList, ∀ β ∈ rootList, α + β ∈ rootList →
    (crep (toStdD 4 (piT α)) (toStdD 4 (piT β))).coeff * epsT α * epsT β =
      epsT (α + β) * (crep (toStdD 4 α) (toStdD 4 β)).coeff := by
  decide +kernel

theorem commC_piT {α β : Fin 4 → ℤ} (hα : α ∈ rootList) (hβ : β ∈ rootList)
    (hαβ : α + β ∈ rootList) (p q : ℕ × ℕ) :
    commC (piT α) (piT β) p * epsT α * epsT β = epsT (α + β) * commC α β q := by
  have h1 := crep_isRep α hα β hβ hαβ
  have h2 := crep_isRep (piT α) (piT_mem α hα) (piT β) (piT_mem β hβ)
    (by rw [← piT_add]; exact piT_mem _ hαβ)
  rw [commC, commC, chainSign_eq h1, chainSign_eq h2]
  exact coeff_crep_piT α hα β hβ hαβ

end CFSG.ComponentClassification.Burgoyne.DX.Tri
