module

public import Certificates.Data.Kernel.GH74Tab.Defs

public section

namespace CFSG.KC.GH74Tab

open CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

theorem vget_ofFn {α : Type*} {m : ℕ} (f : Fin m → α) (i : Fin m) : (Vector.ofFn f).get i = f i := by
  simp [Vector.get]
  rfl

variable {n : ℕ} [NeZero n]

theorem mkTab_mulT_idx (i j : Fin 64) :
    (mkTab n).mulT i j = mkIdx n ((mkTab n).el.get i * (mkTab n).el.get j) := by
  simp only [Tab.mulT, mkTab, mkIdx, vget_ofFn]

theorem mkTab_inv_idx (i : Fin 64) : (mkTab n).inv.get i = mkIdx n ((mkTab n).el.get i)⁻¹ := by
  simp only [mkTab, mkIdx, vget_ofFn]

theorem mkTab_one_idx : (mkTab n).one = mkIdx n 1 := rfl

theorem mkTab_x0i_idx : (mkTab n).x0i = mkIdx n (x0 n) := rfl

variable (D : Dat)

theorem transOK_spec (h : transOK D n = true) :
    (∀ i j : Fin 64, (mkTab n).el.get (f64 (mul D i j)) = (mkTab n).el.get i * (mkTab n).el.get j) ∧
    (∀ k : Fin 64, mkIdx n ((mkTab n).el.get k) = k) ∧
    (mkTab n).el.get (f64 D.one) = 1 ∧ (mkTab n).el.get (f64 D.x0) = x0 n ∧
    (∀ i : Fin 64, (mkTab n).el.get (f64 (g6 D.I i)) = ((mkTab n).el.get i)⁻¹) ∧
    (∀ i : Fin 64, (mkTab n).isQ.get i = bit D.Q i) ∧
    (∀ i : Fin 64, (mkTab n).cls.get i = g6 D.C i) := by
  simp only [transOK, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hm, hi⟩, h1⟩, hx⟩, hinv⟩, hq⟩, hc⟩ := h
  exact ⟨hm, hi, h1, hx, hinv, hq, hc⟩

theorem mulT_eq (h : transOK D n = true) (i j : Fin 64) :
    (mkTab n).mulT i j = f64 (mul D i j) := by
  obtain ⟨hm, hi, -⟩ := transOK_spec D h
  rw [mkTab_mulT_idx, ← hm i j, hi]

theorem inv_eq (h : transOK D n = true) (i : Fin 64) : (mkTab n).inv.get i = f64 (g6 D.I i) := by
  obtain ⟨-, hi, -, -, hinv, -⟩ := transOK_spec D h
  rw [mkTab_inv_idx, ← hinv i, hi]

theorem one_eq (h : transOK D n = true) : (mkTab n).one = f64 D.one := by
  obtain ⟨-, hi, h1, -⟩ := transOK_spec D h
  rw [mkTab_one_idx, ← h1, hi]

theorem x0i_eq (h : transOK D n = true) : (mkTab n).x0i = f64 D.x0 := by
  obtain ⟨-, hi, -, hx, -⟩ := transOK_spec D h
  rw [mkTab_x0i_idx, ← hx, hi]

theorem isQ_eq (h : transOK D n = true) (i : Fin 64) : (mkTab n).isQ.get i = bit D.Q i :=
  (transOK_spec D h).2.2.2.2.2.1 i

theorem cls_eq (h : transOK D n = true) (i : Fin 64) : (mkTab n).cls.get i = g6 D.C i :=
  (transOK_spec D h).2.2.2.2.2.2 i

end CFSG.KC.GH74Tab

end
