module

public import Mathlib.Algebra.Group.Conj

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

@[expose] def Vert {G : Type} [Group G] (P : G → G → Prop) (a z : G) : Prop :=
  ∀ x w : G, IsConj a x → IsConj z w → P x w

theorem Vert.self {G : Type} [Group G] {P : G → G → Prop} {a z : G} (h : Vert P a z) : P a z :=
  h a z (IsConj.refl a) (IsConj.refl z)

theorem Vert.of_isConj {G : Type} [Group G] {P : G → G → Prop} {a z x w : G}
    (h : Vert P a z) (hx : IsConj a x) (hw : IsConj z w) : Vert P x w :=
  fun x' w' hx' hw' => h x' w' (hx.trans hx') (hw.trans hw')

end CFSG.EvenSporadicStandard.HNRecog.Section3
