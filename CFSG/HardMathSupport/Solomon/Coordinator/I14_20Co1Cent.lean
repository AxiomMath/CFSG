module

public import Certificates.Certificate13504

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.I1420

open CFSG.Sporadic.Co1Schreier

@[expose] noncomputable def yE : ↥GA :=
  ⟨Certificates.y13Co1, getD_mem_of_forall (dagG_mem (fun g hg => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with h | h
    · rw [h]; exact A₁_mem
    · rw [h]; exact A₂_mem) _) 3⟩

theorem yE_coe : (yE : GL24) = Certificates.y13Co1 := by
  unfold yE
  rfl


theorem yE_pow_thirteen : yE ^ 13 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, yE_coe]
  exact Certificates.certificate13504.1

theorem yE_ne_one : yE ≠ 1 := by
  intro h
  apply Certificates.certificate13504.2.1
  rw [← yE_coe, h, Subgroup.coe_one]

theorem no_order_five_of_commute_y13 (c : ↥GA) (hc : c * yE = yE * c) (h5 : c ^ 5 = 1) :
    c = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_one]
  refine Certificates.certificate13504.2.2 c c.2 ?_ ?_
  · rw [← yE_coe, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hc]
  · rw [← Subgroup.coe_pow, h5, Subgroup.coe_one]

end CFSG.HardMathSupport.Solomon.Coordinator.I1420
