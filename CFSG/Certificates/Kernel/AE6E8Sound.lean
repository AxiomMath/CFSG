module

public import Certificates.Data.Kernel.AE6E8.Defs
public import CFSG.Certificates.Kernel.AE6TriSound

public section

namespace CFSG.KC.AE6E8

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Tri CFSG.KS.Raw

variable {G : List Nat} {g : Nat → Equiv.Perm (Fin 360)}

theorem sumOK_sound (hG : GRep G g) {S W : Nat → Nat} {VL : List Nat}
    {a : Nat → Equiv.Perm (Fin 16)} (hW : ∀ j < VL.length, Orb.PRep 16 5 (W j) (a j))
    {s : Nat → Equiv.Perm (Fin 376)} (hS : ∀ j < VL.length, Orb.PRep 376 9 (S j) (s j))
    (h : sumOK S W G VL = true) :
    ∀ j < VL.length, s j = finSumFinEquiv.permCongr
      (Equiv.sumCongr (a j) (g (VL.getD j 0))) := by
  intro j hj
  unfold sumOK at h
  have e := allIx_getD 0 h j hj
  rw [Orb.bAnd_eq, Bool.and_eq_true, Orb.allN_iff, Orb.allN_iff] at e
  refine Equiv.ext fun z => Fin.ext ?_
  obtain ⟨u, rfl⟩ := (finSumFinEquiv (m := 16) (n := 360)).surjective z
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, ← hS j hj]
  cases u with
  | inl x =>
    simp only [Equiv.sumCongr_apply, Sum.map_inl]
    change pg 9 (mask 9) (S j) x = (a j x : Nat)
    rw [← hW j hj x]
    exact Nat.eq_of_beq_eq_true (e.1 x x.2)
  | inr b =>
    simp only [Equiv.sumCongr_apply, Sum.map_inr]
    change pg 9 (mask 9) (S j) (16 + b) = 16 + (g (VL.getD j 0) b : Nat)
    rw [← hG _ b]
    exact Nat.eq_of_beq_eq_true (e.2 b b.2)

theorem wSel_lt (T : Nat → Nat) {j : Nat} (hj : j < 7) : wSel T j = T j := by
  unfold wSel
  rw [Orb.nIf_eq, if_pos (by rw [Nat.blt_eq]; exact hj)]

theorem wSel_ge (T : Nat → Nat) {j : Nat} (hj : 7 ≤ j) : wSel T j = piP := by
  unfold wSel
  rw [Orb.nIf_eq, if_neg (by rw [Nat.blt_eq]; omega)]

theorem notB_eq' (b : Bool) : notB b = !b := by cases b <;> rfl

theorem q8OK_sound (hG : GRep G g) {w₁ w₂ : List Nat} (h : q8OK G w₁ w₂ = true) :
    wv g w₁ * wv g w₁ ≠ 1 ∧ wv g w₁ * wv g w₁ * (wv g w₁ * wv g w₁) = 1 ∧
      wv g w₂ * wv g w₂ = wv g w₁ * wv g w₁ ∧
      wv g w₁ * wv g w₂ * (wv g w₁ * wv g w₂) = wv g w₁ * wv g w₁ ∧ wv g w₂ ≠ wv g w₁ ∧
      wv g w₂ ≠ wv g w₁ * wv g w₁ * wv g w₁ := by
  unfold q8OK at h
  rw [Orb.strictB_eq, Orb.strictB_eq, Orb.strictB_eq] at h
  simp only [Orb.bAnd_eq, Bool.and_eq_true, notB_eq', Bool.not_eq_true'] at h
  rw [Orb.strictB_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hx := prep_wv hG w₁
  have hy := prep_wv hG w₂
  have hxx := prep_pmN hx hx
  have hxy := prep_pmN hx hy
  have hid : Orb.PRep 360 9 (pidn 360 9) 1 := prep_pidn'
  refine ⟨fun e => ?_, (eqN_iff (prep_pmN hxx hxx) hid).1 h2, (eqN_iff (prep_pmN hy hy) hxx).1 h3,
    (eqN_iff (prep_pmN hxy hxy) hxx).1 h4, fun e => ?_, fun e => ?_⟩
  · rw [(eqN_iff hxx hid).2 e] at h1
    exact Bool.false_ne_true h1.symm
  · rw [(eqN_iff hy hx).2 e] at h5
    exact Bool.false_ne_true h5.symm
  · rw [(eqN_iff hy (prep_pmN hxx hx)).2 e] at h6
    exact Bool.false_ne_true h6.symm

end CFSG.KC.AE6E8

end
