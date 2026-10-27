module

public import Certificates.Data.Kernel.Bounds.TableZ
public import CFSG.Certificates.Kernel.Misc.Coset.PG
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Group
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib

public section

namespace CFSG.Certificates.KB.ZSound

open CFSG.Certificates.KB CFSG.Certificates.KB.Sound

section Grp

variable {G : Type*} [Group G]

@[reducible] def cenComm (G : Type*) [Group G] : CommGroup (Subgroup.center G) :=
  { (inferInstance : Group (Subgroup.center G)) with
    mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.1 b.2 a) }

attribute [local instance] cenComm

variable {z : ℕ → G} {nZ : ℕ} {hc : ∀ k < nZ, ∀ g : G, z k * g = g * z k}

variable {z : ℕ → G} {nZ : ℕ} {hc : ∀ k < nZ, ∀ g : G, z k * g = g * z k}

end Grp

end CFSG.Certificates.KB.ZSound

namespace CFSG.Certificates.KB

open CFSG.Certificates.KB.ZSound CFSG.Certificates.KB.Sound

attribute [local instance] ZSound.cenComm

end CFSG.Certificates.KB
