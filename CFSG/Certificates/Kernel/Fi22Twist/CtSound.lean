module

public import Certificates.Data.Kernel.Fi22Twist.Ct
public import CFSG.Certificates.Kernel.Fi22Twist.DjSound

public section

namespace CFSG.KS.Fi22Twist

open CFSG.KC.Enum CFSG.KC.Fi22Twist CFSG.KS.E27Lie

theorem ctK_comm {G T : ℕ} {g t : Equiv.Perm (Fin 3510)} (hg : PRep 3510 12 (MonoidHom.id _) G g)
    (ht : PRep 3510 12 (MonoidHom.id _) T t) (h : ctK G T = true) : g * t = t * g := by
  unfold ctK at h
  refine pt_ext fun i hi => ?_
  have e := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec h i hi)
  rw [ap_eq ht hi, ap_eq hg (pt_lt _ t hi), ap_eq hg hi, ap_eq ht (pt_lt _ g hi)] at e
  rw [pt_mul, pt_mul]
  exact e

end CFSG.KS.Fi22Twist

end
