module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourA9
public import CFSG.Alternating.Multipliers.OddKernel

public section

namespace CFSG.CGT.PushingUpLit.CGT6

theorem a9Center : A9Center := by
  intro K _ _ hK ⟨e⟩ hodd
  have : Group.IsPerfect K := hK.1
  let η : K →* alternatingGroup (Fin (7 + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hη : Function.Surjective η :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = Subgroup.center K := by
    ext k
    rw [MonoidHom.mem_ker]
    show e (QuotientGroup.mk' (Subgroup.center K) k) = 1 ↔ k ∈ Subgroup.center K
    rw [map_eq_one_iff e e.injective]
    exact QuotientGroup.eq_one_iff k
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (P := K) (m := 7) (by norm_num) η
    hη (hker ▸ le_rfl) (hker ▸ hodd)
  rw [hker] at h1
  exact (Subgroup.card_eq_one).mp h1

end CFSG.CGT.PushingUpLit.CGT6
