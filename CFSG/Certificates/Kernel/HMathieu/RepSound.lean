module

public import CFSG.Certificates.Kernel.HMathieu.NormalSound

public section

namespace CFSG.KC.HMathieu

open CFSG.KC.Enum CFSG.KS CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

variable {T : PT 24} [hT : Fact (T.check = true)] {E invL P : List Nat}

theorem exists_pk_idx (H : Packed T E) {k : Nat} (hk : k < E.length) :
    ∃ g : T.Elem, pk E g = E.getD k 0 := by
  refine ⟨T.elemEquiv.symm ⟨k, by rw [n_eq H]; exact hk⟩, ?_⟩
  unfold pk
  simp [PT.elemEquiv]

theorem conj_el_of_pk (H : Packed T E) (I : InvData T E invL P) (hid : E.getD 0 0 = pidn 24 5)
    (g : T.Elem) {y z : Nat} (hy : y ≤ T.invols.length) (hz : z ≤ T.invols.length)
    (h : conjP (pk E g) (P.getD y 0) = P.getD z 0) :
    MulAut.conj g (el T.invols y) = el T.invols z := by
  rw [← pk_el H I hy, ← pk_el H I hz, conjP, ← pk_mul H, ← pk_inv H hid, ← pk_mul H] at h
  exact eq_of_pk H h

theorem exists_conj_of_row (H : Packed T E) (I : InvData T E invL P)
    (hid : E.getD 0 0 = pidn 24 5) {k : Nat} (hk : k < E.length) (z : Nat → Nat)
    (hz : ∀ y < T.invols.length, z y ≤ T.invols.length)
    (h : ∀ y < T.invols.length, conjP (E.getD k 0) (P.getD y 0) = P.getD (z y) 0) :
    ∃ g : T.Elem, ∀ y < T.invols.length, MulAut.conj g (el T.invols y) = el T.invols (z y) := by
  obtain ⟨g, hg⟩ := exists_pk_idx H hk
  exact ⟨g, fun y hy => conj_el_of_pk H I hid g hy.le (hz y hy) (by rw [hg]; exact h y hy)⟩

end CFSG.KC.HMathieu

end
