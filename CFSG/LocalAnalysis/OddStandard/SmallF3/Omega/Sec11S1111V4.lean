module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec11L114A

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec11_V4_mem {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t) {x : G} :
    x ∈ zpowers t ⊔ zpowers z ↔ x = 1 ∨ x = t ∨ x = z ∨ x = t * z :=
  sec11L114_pair_mem ht2 hz2 htz

theorem sec11_V4_card {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t)
    (ht1 : t ≠ 1) (hz1 : z ≠ 1) (hne : t ≠ z) : Nat.card ↥(zpowers t ⊔ zpowers z) = 4 :=
  sec11L114_pair_card ht2 hz2 htz ht1 hz1 hne

theorem sec11_V4_isDih2 {t z : G} (ht2 : t * t = 1) (hz2 : z * z = 1) (htz : t * z = z * t)
    (ht1 : t ≠ 1) (hz1 : z ≠ 1) (hne : t ≠ z) : IsDih2 (zpowers t ⊔ zpowers z) :=
  sec11L114_pair_isDih2 ht2 hz2 htz ht1 hz1 hne

end CFSG.OddStandard.SmallF3.Omega
