module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4CombSpan

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

@[expose] def heartCoord (w : Fin 8 → ZMod 2) : Fin 6 → ZMod 2 :=
  fun i => w (Fin.castLE (by norm_num) i) + w 7

@[expose] def extPerm (σ : Equiv.Perm (Fin 6)) : Equiv.Perm (Fin 8) :=
  (finSumFinEquiv (m := 6) (n := 2)).permCongr (Equiv.Perm.sumCongr σ 1)

private instance instDecidableIsEvenVec8 (v : Fin 8 → ZMod 2) : Decidable (IsEvenVec v) := by
  unfold IsEvenVec
  infer_instance

private lemma castLE_castSucc_castSucc (i : Fin 6) :
    Fin.castLE (by norm_num : 6 ≤ 8) i = Fin.castSucc (Fin.castSucc i) := rfl

private def heartLift (v : Fin 6 → ZMod 2) : Fin 8 → ZMod 2 :=
  Fin.snoc (Fin.snoc v (∑ i, v i)) 0

private lemma heartLift_even (v : Fin 6 → ZMod 2) : IsEvenVec (heartLift v) := by
  unfold IsEvenVec heartLift
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [add_zero]
  exact CharTwo.add_self_eq_zero _

private lemma heartLift_coord (v : Fin 6 → ZMod 2) : heartCoord (heartLift v) = v := by
  funext i
  simp only [heartCoord, heartLift, castLE_castSucc_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
    Pi.add_apply, Pi.zero_apply]
  exact add_zero (v i)

theorem sec5b_heartCoord_add (v w : Fin 8 → ZMod 2) :
    heartCoord (v + w) = heartCoord v + heartCoord w := by
  funext i
  simp only [heartCoord, Pi.add_apply]
  ring

theorem sec5b_heartCoord_add_one (w : Fin 8 → ZMod 2) : heartCoord (w + 1) = heartCoord w := by
  funext i
  simp only [heartCoord, Pi.add_apply, Pi.one_apply]
  ring_nf
  simp [CharTwo.two_eq_zero]

theorem sec5b_heartCoord_eq_zero {w : Fin 8 → ZMod 2} (hw : IsEvenVec w) :
    heartCoord w = 0 ↔ w = 0 ∨ w = 1 := by
  revert hw
  revert w
  decide +kernel

theorem sec5b_heartCoord_inj {v w : Fin 8 → ZMod 2} (hv : IsEvenVec v) (hw : IsEvenVec w)
    (h : heartCoord v = heartCoord w) : w = v ∨ w = v + 1 := by
  have hvw : IsEvenVec (v + w) := isEvenVec_add hv hw
  have hvv : v + v = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (v i)
  have hker : heartCoord (v + w) = 0 := by
    rw [sec5b_heartCoord_add, h]
    funext i
    simp only [Pi.add_apply, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  rcases (sec5b_heartCoord_eq_zero hvw).mp hker with h0 | h1
  · left
    calc w = 0 + w := (zero_add w).symm
      _ = (v + v) + w := by rw [← hvv]
      _ = v + (v + w) := by rw [add_assoc]
      _ = v + 0 := by rw [h0]
      _ = v := add_zero v
  · right
    calc w = 0 + w := (zero_add w).symm
      _ = (v + v) + w := by rw [← hvv]
      _ = v + (v + w) := by rw [add_assoc]
      _ = v + 1 := by rw [h1]

theorem sec5b_heartCoord_surj (v : Fin 6 → ZMod 2) :
    ∃ w : Fin 8 → ZMod 2, IsEvenVec w ∧ heartCoord w = v :=
  ⟨heartLift v, heartLift_even v, heartLift_coord v⟩

private lemma extPerm_cast (σ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    extPerm σ (Fin.castLE (by norm_num : 6 ≤ 8) i) = Fin.castLE (by norm_num : 6 ≤ 8) (σ i) := by
  revert σ i
  decide +kernel

theorem sec5b_extPerm_apply_six (σ : Equiv.Perm (Fin 6)) : extPerm σ 6 = 6 ∧ extPerm σ 7 = 7 := by
  revert σ
  decide +kernel

theorem sec5b_heartCoord_extPerm (σ : Equiv.Perm (Fin 6)) (w : Fin 8 → ZMod 2) :
    heartCoord (permVec (extPerm σ) w) = permVec σ (heartCoord w) := by
  funext i
  have h1 : (extPerm σ).symm (Fin.castLE (by norm_num : 6 ≤ 8) i)
      = Fin.castLE (by norm_num : 6 ≤ 8) (σ.symm i) := by
    rw [Equiv.symm_apply_eq, extPerm_cast, Equiv.apply_symm_apply]
  have h2 : (extPerm σ).symm 7 = 7 := by
    rw [Equiv.symm_apply_eq]
    exact ((sec5b_extPerm_apply_six σ).2).symm
  simp only [heartCoord, permVec, Function.comp_apply, Pi.add_apply]
  rw [h1, h2]

theorem sec5b_heartCoord_pair_six_seven :
    heartCoord (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1) = 1 := by
  decide +kernel

private lemma permVec_single (σ : Equiv.Perm (Fin 8)) (i : Fin 8) :
    permVec σ (Pi.single i (1 : ZMod 2)) = Pi.single (σ i) 1 := by
  funext j
  simp only [permVec, Function.comp_apply, Pi.single_apply]
  by_cases h : j = σ i
  · have h' : σ.symm j = i := by rw [Equiv.symm_apply_eq]; exact h
    simp [h, h']
  · have h' : σ.symm j ≠ i := fun hh => h ((Equiv.symm_apply_eq σ).mp hh)
    simp [h, h']

private lemma heartCoord_single_pair {a b : Fin 8} (hab : a ≠ b) :
    vecWeight (heartCoord (Pi.single a (1 : ZMod 2) + Pi.single b 1)) = 2 →
      a.val < 6 ∧ b.val < 6 := by
  revert a b
  decide +kernel

theorem sec5b_move_of_heartCoord {σ : Equiv.Perm (Fin 8)}
    (h : vecWeight (heartCoord (permVec σ (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1))) = 2) :
    (σ 6).val < 6 ∧ (σ 7).val < 6 := by
  have hperm : permVec σ (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1)
      = Pi.single (σ 6) 1 + Pi.single (σ 7) 1 := by
    rw [show permVec σ (Pi.single 6 (1 : ZMod 2) + Pi.single 7 1)
          = permVec σ (Pi.single 6 1) + permVec σ (Pi.single 7 1) from rfl,
      permVec_single, permVec_single]
  rw [hperm] at h
  have hne : σ 6 ≠ σ 7 := by
    intro hh
    have h67 : (6 : Fin 8) = 7 := σ.injective hh
    exact absurd h67 (by decide)
  exact heartCoord_single_pair hne h

end CFSG.OddStandard.SmallF3.Omega
