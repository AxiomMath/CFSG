module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Data.Finset.Attr
public import Mathlib.GroupTheory.QuotientGroup.Defs

public section

namespace CFSG.GroupTheory

variable {H : Type*} [Group H]

theorem le_or_sup_eq_top_of_normal_of_isSimpleGroup_quotient {N K : Subgroup H} [N.Normal]
    [K.Normal] (hsimple : IsSimpleGroup (H ⧸ N)) : K ≤ N ∨ K ⊔ N = ⊤ := by
  let π : H →* H ⧸ N := QuotientGroup.mk' N
  haveI : (K.map π).Normal :=
    (inferInstance : K.Normal).map π (QuotientGroup.mk'_surjective N)
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.map π) with hbot | htop
  · left
    have h : K ≤ π.ker := (Subgroup.map_eq_bot_iff K).mp hbot
    rwa [QuotientGroup.ker_mk'] at h
  · right
    have h := congrArg (Subgroup.comap π) htop
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h

end CFSG.GroupTheory

end
