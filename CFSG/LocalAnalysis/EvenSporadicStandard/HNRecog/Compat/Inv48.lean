module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Compat.CpFourA

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

variable {G G' : Type} [Group G] [Group G'] {a z : G} {a' z' : G'}

theorem fam_4A (hC : Cover4A) (h : F5Std a z) (h' : F5Std a' z') {b : G} (hb : IsConj a b)
    {β : G → G'}
    (hb' : IsConj a' (β b)) (hβ : IsIsoOn (Gx b) (Gx (β b)) β) (F : Fam b β) {y : G}
    (hy : y ∈ orb4A a z b) {t t' : G} (ht : t ∈ InvIn (Gxy b y)) (ht' : t' ∈ InvIn (Gxy b y)) :
    (F.app t y = F.app t' y ∨ F.app t y = F.app t' (b * y * b⁻¹)) ∧
      (ConjIn (Gxy b y) t' t → F.app t y = F.app t' y) :=
  cp_fam_4A_base hC (h.of_isConj hb (IsConj.refl z)) (h'.of_isConj hb' (IsConj.refl z')) hβ F
    ⟨hb.symm.trans hy.1, hy.2⟩ ht ht'

end CFSG.EvenSporadicStandard.HNRecog.Section4
