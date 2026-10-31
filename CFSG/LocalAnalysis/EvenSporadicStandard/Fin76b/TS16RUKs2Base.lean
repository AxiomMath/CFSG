
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RUKs2Check

@[expose] public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.Fin76b.U16

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.PairNative CFSG.EvenSporadicStandard.M24Std.CU43
  CFSG.Sporadic.SmallOddCore

section Inv7

noncomputable def y8Perm : Equiv.Perm (Fin 820) := permOfArr 820 y8Arr

noncomputable def CKs7 : Subgroup (Equiv.Perm (Fin 820)) :=
  U43ExtStar ⊓ centralizer ({rP 4} : Set (Equiv.Perm (Fin 820)))

theorem repCoset_eq_seven : ∀ j < 9, repCoset[j]! = 7 → j = 4 := by decide

end Inv7

theorem allLt_twist_iff {n : ℕ} {w : List (Array ℕ)} {H : Equiv.Perm (Fin n)} (hw : RepW n w H)
    {r r' : Array ℕ} {A B : Equiv.Perm (Fin n)} (hr : Rep n r A) (hr' : Rep n r' B) :
    allLt n (fun i => evR w r[i]! == r'[evR w i]!) = true ↔ H * A = B * H := by
  rw [allLt_iff]
  constructor
  · intro h
    refine Equiv.ext fun x => Fin.ext ?_
    have := h x x.2
    rw [beq_iff_eq] at this
    have e1 : r[(x : ℕ)]! = (A x : ℕ) := hr x
    have e2 : evR w (A x : ℕ) = H (A x) := hw (A x)
    have e3 : evR w (x : ℕ) = H x := hw x
    rw [e1, e2, e3] at this
    have e4 : r'[(H x : ℕ)]! = (B (H x) : ℕ) := hr' (H x)
    rw [e4] at this
    simpa using this
  · intro h i hi
    rw [beq_iff_eq]
    have e1 : r[i]! = (A ⟨i, hi⟩ : ℕ) := hr ⟨i, hi⟩
    have e2 : evR w (A ⟨i, hi⟩ : ℕ) = H (A ⟨i, hi⟩) := hw (A ⟨i, hi⟩)
    have e3 : evR w i = H ⟨i, hi⟩ := hw ⟨i, hi⟩
    have e4 : r'[(H ⟨i, hi⟩ : ℕ)]! = (B (H ⟨i, hi⟩) : ℕ) := hr' (H ⟨i, hi⟩)
    rw [e1, e2, e3, e4]
    have := congrArg (fun F : Equiv.Perm (Fin n) => (F ⟨i, hi⟩ : ℕ)) h
    simpa using this

section Pairs

theorem invRelW_iff {k : ℕ} {v vi : Array ℕ} {V W : Equiv.Perm (Fin 820)} (hv : Rep 820 v V)
    (hvi : Rep 820 vi W) {w : List (Array ℕ)} {g : Equiv.Perm (Fin 820)} (hw : RepW 820 w g) :
    invRelW (tArr k) v vi w = true ↔
      (g * tP k) * (g * tP k) = 1 ∧ (g * tP k) * V = W * (g * tP k) := by
  have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
  unfold invRelW
  rw [Bool.and_eq_true]
  exact and_congr (allLt_sq_iff hH) (allLt_twist_iff hH hv hvi)

def Xi7 (V W : Equiv.Perm (Fin 820)) : Set ↥U43ExtStar :=
  {x | InCos 7 x ∧ (x : Equiv.Perm (Fin 820)) * x = 1 ∧ (x : Equiv.Perm (Fin 820)) * V = W * x}

theorem card_Xi7 {v vi : Array ℕ} {V W : Equiv.Perm (Fin 820)} (hv : Rep 820 v V)
    (hvi : Rep 820 vi W) :
    Nat.card ↥(Xi7 V W) = countW (invRelW (tArr 7) v vi) blocks [] := by
  classical
  have hk7 : (7 : ℕ) < 8 := by norm_num
  have hV7 : InV 7 := Or.inr (Or.inr (Or.inr rfl))
  rw [← card_eq_countW_P (f := invRelW (tArr 7) v vi)
    (Pr := fun g => (g * tP 7) * (g * tP 7) = 1 ∧ (g * tP 7) * V = W * (g * tP 7))
    (fun w g hw _ => invRelW_iff hv hvi hw)]
  refine Nat.card_congr
    { toFun := fun x => ⟨⟨(x.1 : Equiv.Perm (Fin 820)) * (tP 7)⁻¹, x.2.1⟩, by
        have h1 : (x.1 : Equiv.Perm (Fin 820)) * (tP 7)⁻¹ * tP 7 = x.1 := by group
        simpa [h1] using x.2.2⟩
      invFun := fun g => ⟨⟨(g.1 : Equiv.Perm (Fin 820)) * tP 7, g.1.1,
        g.1.2, 7, hk7, hV7, rfl⟩, inCos_mul_tP g.1.2, g.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun g => by
        apply Subtype.ext
        apply Subtype.ext
        simp }

theorem card_cent_Ks2 {v ξ : Array ℕ} {V X : Equiv.Perm (Fin 820)} (hv : Rep 820 v V)
    (hξ : Rep 820 ξ X) :
    Nat.card {x : ↥U43ExtStar // (x : Equiv.Perm (Fin 820)) * V = V * x ∧
      (x : Equiv.Perm (Fin 820)) * X = X * x} = centKs2 v ξ := by
  classical
  rw [card_Ks_pred (fun x => x * V = V * x ∧ x * X = X * x)]
  have h : ∀ k, k < 8 → Nat.card {g : ↥P // (g : Equiv.Perm (Fin 820)) * tP k * V =
      V * ((g : Equiv.Perm (Fin 820)) * tP k) ∧ (g : Equiv.Perm (Fin 820)) * tP k * X =
        X * ((g : Equiv.Perm (Fin 820)) * tP k)} =
      countW (commW (tArr k) [v, ξ]) blocks [] := by
    intro k hk
    rw [card_eq_countW_P (f := commW (tArr k) [v, ξ])
      (Pr := fun g => g * tP k * V = V * (g * tP k) ∧ g * tP k * X = X * (g * tP k))]
    intro w g hw _
    have hH : RepW 820 (tArr k :: w) (g * tP k) := RepW.cons (rep_tArr k) hw
    simp only [commW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact and_congr (allLt_comm_iff hH hv) (allLt_comm_iff hH hξ)
  rw [h 0 (by norm_num), h 2 (by norm_num), h 5 (by norm_num), h 7 (by norm_num)]
  rw [centKs2, vIxL, List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_cons,
    List.foldl_nil, Nat.zero_add]

noncomputable def xiPerm (i : ℕ) : Equiv.Perm (Fin 820) := permOfArr 820 xiArrs[i]!

theorem rep_ks8_inv {j : ℕ} (hj : j < 8) :
    Rep 820 (invCand 820 ks8Reps[j]!) (ks8Perm j)⁻¹ :=
  rep_inv_of_isInvA (rep_ks8 hj) (ks8_facts j hj).1

theorem pair_arith : ∀ i < 3, ks8Cent[5 + i]! = pairNum[i]! * pairCent[i]! := by decide +kernel

noncomputable def d16a : Equiv.Perm (Fin 820) := permOfArr 820 d16A

noncomputable def d16b : Equiv.Perm (Fin 820) := permOfArr 820 d16B

noncomputable def D16sub : Subgroup (Equiv.Perm (Fin 820)) :=
  zpowers d16a ⊔ zpowers d16b

theorem ks8Coset_seven : ∀ j < 8, ks8Coset[j]! = 7 → 5 ≤ j := by decide

theorem pairCent_sixteen : ∀ i < 3, 16 ∣ pairCent[i]! → i = 2 := by decide

noncomputable def Cpair (i : ℕ) : Subgroup (Equiv.Perm (Fin 820)) :=
  U43ExtStar ⊓ centralizer ({ks8Perm (5 + i)} : Set (Equiv.Perm (Fin 820))) ⊓
    centralizer ({xiPerm i} : Set (Equiv.Perm (Fin 820)))

end Pairs

end CFSG.EvenSporadicStandard.Fin76b.U16
