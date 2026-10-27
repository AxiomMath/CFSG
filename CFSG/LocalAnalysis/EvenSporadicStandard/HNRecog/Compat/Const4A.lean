module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpConst4A

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'} {α : G → G'}

theorem const_4A (hC : Cover4A) (hW : Wit4A) (h : F5Std a z) (h' : F5Std a' z')
    (hα : IsIsoOn (Gx a) (Gx a') α)
    (F : Fam a α) (hF : Arranged a F) {x : G} (hx : x ∈ orb4A a z a) {t t' : G}
    (ht : t ∈ InvIn (Gxy a x)) (ht' : t' ∈ InvIn (Gxy a x)) : F.app t x = F.app t' x := by
  obtain ⟨d, hd⟩ := cp_exists_perp_4A h hx
  exact bookkeep_two F h.typ.orderOf_a ⟨1, (Gx a).one_mem, by simp⟩ (cp_isInvReps_4A hC h hx hd)
    (fun r hr r' hr' => (cp_4A_step hW h h' hα F hF hx hd hr).trans
      (cp_4A_step hW h h' hα F hF hx hd hr').symm) t ht t' ht'

end CFSG.EvenSporadicStandard.HNRecog.Section4
