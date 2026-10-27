module

public import CFSG.LocalAnalysis.EvenBN.G2.LocalQDefs
public import CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.LocalAnalysis.EvenBN.Common (CosetData)
open CFSG.LocalAnalysis.SymplecticFourStandard.BothTrivialClosure (BarM barMap barSub)
open CFSG.LocalAnalysis.EvenBN.Common.RankOneLayerRadical (normalClosureInNormalizer)
open scoped commutatorElement Pointwise

section Defs

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] noncomputable def yamadaK₁ (d : G2Data L K) : Subgroup G :=
  ⁅L ⊓ normalizer (d.U : Set G), L ⊓ normalizer (d.U : Set G)⁆

@[expose] noncomputable def yamadaK₂ (d : G2Data L K) : Subgroup G :=
  ⁅L ⊓ normalizer (d.Y : Set G), L ⊓ normalizer (d.Y : Set G)⁆

@[expose] noncomputable def yamadaN₁ (d : G2Data L K) (t : G) : Subgroup G :=
  normalClosureInNormalizer (yamadaD₇ d t) (yamadaK₁ d)

@[expose] noncomputable def yamadaN₂ (d : G2Data L K) (t : G) : Subgroup G :=
  normalClosureInNormalizer (yamadaM₆ d t) (yamadaK₂ d)

open Classical in
@[expose] noncomputable def yamadaT₁ (d : G2Data L K) (t : G) : BarM (yamadaD₇ d t) :=
  if ht : t ∈ normalizer (yamadaD₇ d t : Set G) then barMap (yamadaD₇ d t) ⟨t, ht⟩ else 1

open Classical in
@[expose] noncomputable def yamadaT₂ (d : G2Data L K) (t : G) : BarM (yamadaM₆ d t) :=
  if ht : t ∈ normalizer (yamadaM₆ d t : Set G) then barMap (yamadaM₆ d t) ⟨t, ht⟩ else 1

noncomputable abbrev yamadaBarK₁ (d : G2Data L K) (t : G) : Subgroup (BarM (yamadaD₇ d t)) :=
  barSub (yamadaD₇ d t) (yamadaK₁ d)

noncomputable abbrev yamadaBarP₁ (d : G2Data L K) (t : G) : Subgroup (BarM (yamadaD₇ d t)) :=
  barSub (yamadaD₇ d t) (yamadaP d t)

noncomputable abbrev yamadaBarN₁ (d : G2Data L K) (t : G) : Subgroup (BarM (yamadaD₇ d t)) :=
  barSub (yamadaD₇ d t) (yamadaN₁ d t)

noncomputable abbrev yamadaBarK₂ (d : G2Data L K) (t : G) : Subgroup (BarM (yamadaM₆ d t)) :=
  barSub (yamadaM₆ d t) (yamadaK₂ d)

noncomputable abbrev yamadaBarP₂ (d : G2Data L K) (t : G) : Subgroup (BarM (yamadaM₆ d t)) :=
  barSub (yamadaM₆ d t) (yamadaP d t)

noncomputable abbrev yamadaBarN₂ (d : G2Data L K) (t : G) : Subgroup (BarM (yamadaM₆ d t)) :=
  barSub (yamadaM₆ d t) (yamadaN₂ d t)

theorem yamadaT₁_eq (d : G2Data L K) {t : G} (ht : t ∈ normalizer (yamadaD₇ d t : Set G)) :
    yamadaT₁ d t = barMap (yamadaD₇ d t) ⟨t, ht⟩ :=
  dif_pos ht

theorem yamadaT₂_eq (d : G2Data L K) {t : G} (ht : t ∈ normalizer (yamadaM₆ d t : Set G)) :
    yamadaT₂ d t = barMap (yamadaM₆ d t) ⟨t, ht⟩ :=
  dif_pos ht

theorem yamadaK₁_le_yamadaN₁ (d : G2Data L K) (t : G) : yamadaK₁ d ≤ yamadaN₁ d t :=
  le_sup_left.trans
    (Common.RankOneLayerRadical.sup_le_normalClosureInNormalizer (yamadaD₇ d t) (yamadaK₁ d))

theorem yamadaD₇_le_yamadaN₁ (d : G2Data L K) (t : G) : yamadaD₇ d t ≤ yamadaN₁ d t :=
  le_sup_right.trans
    (Common.RankOneLayerRadical.sup_le_normalClosureInNormalizer (yamadaD₇ d t) (yamadaK₁ d))

theorem yamadaK₂_le_yamadaN₂ (d : G2Data L K) (t : G) : yamadaK₂ d ≤ yamadaN₂ d t :=
  le_sup_left.trans
    (Common.RankOneLayerRadical.sup_le_normalClosureInNormalizer (yamadaM₆ d t) (yamadaK₂ d))

theorem yamadaM₆_le_yamadaN₂ (d : G2Data L K) (t : G) : yamadaM₆ d t ≤ yamadaN₂ d t :=
  le_sup_right.trans
    (Common.RankOneLayerRadical.sup_le_normalClosureInNormalizer (yamadaM₆ d t) (yamadaK₂ d))

theorem yamadaN₁_le_normalizer (d : G2Data L K) (t : G)
    (hK : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G)) :
    yamadaN₁ d t ≤ normalizer (yamadaD₇ d t : Set G) :=
  Common.RankOneLayerRadical.normalClosureInNormalizer_le_normalizer hK

theorem yamadaN₂_le_normalizer (d : G2Data L K) (t : G)
    (hK : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G)) :
    yamadaN₂ d t ≤ normalizer (yamadaM₆ d t : Set G) :=
  Common.RankOneLayerRadical.normalClosureInNormalizer_le_normalizer hK

end Defs

section Bar

variable
  {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

theorem barSub_yamadaN₁ (d : G2Data L K) (t : G)
    (hK : yamadaK₁ d ≤ normalizer (yamadaD₇ d t : Set G)) :
    barSub (yamadaD₇ d t) (yamadaN₁ d t) =
      normalClosure (barSub (yamadaD₇ d t) (yamadaK₁ d) : Set (BarM (yamadaD₇ d t))) :=
  Common.RankOneLayerRadical.barSub_normalClosureInNormalizer hK

theorem barSub_yamadaN₂ (d : G2Data L K) (t : G)
    (hK : yamadaK₂ d ≤ normalizer (yamadaM₆ d t : Set G)) :
    barSub (yamadaM₆ d t) (yamadaN₂ d t) =
      normalClosure (barSub (yamadaM₆ d t) (yamadaK₂ d) : Set (BarM (yamadaM₆ d t))) :=
  Common.RankOneLayerRadical.barSub_normalClosureInNormalizer hK

end Bar

section Identify

variable
  {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

theorem yamadaK₁_eq (d : G2Data L K) (hK : 4 ≤ Nat.card K) : yamadaK₁ d = d.D ⊔ d.leviA := by
  rw [yamadaK₁, (d.yamada_3_13_2_G).1, ← (d.yamada_3_13_2_G).2.1]
  exact (d.yamada_3_13_4_G hK).1

theorem yamadaK₂_eq (d : G2Data L K) (hK : 4 ≤ Nat.card K) : yamadaK₂ d = d.M ⊔ d.leviB := by
  rw [yamadaK₂, (d.yamada_3_13_3_G).1, ← (d.yamada_3_13_3_G).2.2.1]
  exact (d.yamada_3_13_4_G hK).2.2.1

end Identify

end CFSG.LocalAnalysis.EvenBN.G2
