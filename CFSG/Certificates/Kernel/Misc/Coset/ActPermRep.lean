module

public import CFSG.Certificates.Kernel.Misc.Coset.ActPermSound
public import CFSG.Certificates.Kernel.Misc.Coset.ActSound

public section

namespace CFSG.KC.MiscCoset.Act

theorem exists_rep {A : ℕ → ℕ} {m N : ℕ} {rels : List (List ℕ)}
    (h : ∀ x < N, pointOK A m N rels x = true) : ∃ σ : Fin m → Equiv.Perm (Fin N), Rep A m N σ := by
  have hl : ∀ x : Fin N, LetOK A m N x.val := fun x => (pointOK_spec (h x.val x.isLt)).1
  let σ : Fin m → Equiv.Perm (Fin N) := fun g =>
    { toFun := fun x => ⟨step A (m + m) x.val (g.val + g.val), (hl x).1 _ (by omega)⟩
      invFun := fun x => ⟨step A (m + m) x.val (g.val + g.val + 1), (hl x).1 _ (by omega)⟩
      left_inv := fun x => Fin.ext ((hl x).2 g.val g.isLt).1
      right_inv := fun x => Fin.ext ((hl x).2 g.val g.isLt).2 }
  refine ⟨σ, fun g x => ⟨?_, ?_⟩⟩
  · change A (x.val * (m + m) + 2 * g.val) = step A (m + m) x.val (g.val + g.val)
    rw [show 2 * g.val = g.val + g.val by omega]
    rfl
  · change A (x.val * (m + m) + (2 * g.val + 1)) = step A (m + m) x.val (g.val + g.val + 1)
    rw [show 2 * g.val = g.val + g.val by omega]
    rfl

theorem relsAt_of_pointOK {A : ℕ → ℕ} {m N : ℕ} {rels : List (List ℕ)} {x : ℕ}
    (h : pointOK A m N rels x = true) : relsAt A (Nat.add m m) rels x = true := by
  simp only [pointOK, andB_eq, Bool.and_eq_true] at h
  exact h.2.2

end CFSG.KC.MiscCoset.Act

end
