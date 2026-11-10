module

public import CFSG.GH74.QTGen4.DSGen4.L34Generic
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabC
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabD
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabE
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
public import CFSG.GH74.QTGen4.DSGen4.OpenLeavesAmal

public section

namespace CFSG.GH74.QTGen4.DSGen4.L34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

noncomputable abbrev mdlM1 : Subgroup (projectiveSL 3 (GaloisField 2 2)) :=
  Subgroup.normalizer ((CFSG.QuasithinUnique.Fin257.L3.V2 :
    Subgroup (projectiveSL 3 (GaloisField 2 2))) : Set (projectiveSL 3 (GaloisField 2 2)))

noncomputable abbrev mdlM2 : Subgroup (projectiveSL 3 (GaloisField 2 2)) :=
  Subgroup.normalizer ((CFSG.QuasithinUnique.Fin257.L3.V1 :
    Subgroup (projectiveSL 3 (GaloisField 2 2))) : Set (projectiveSL 3 (GaloisField 2 2)))

@[expose] noncomputable def mdlPSL : L34Model where
  Y := projectiveSL 3 (GaloisField 2 2)
  T0 := projUnitriangular 3 (GaloisField 2 2)
  M1 := mdlM1
  M2 := mdlM2
  lie := isLieOverTwo_psl3_four
  pair := isYAmalgamPair_of_borelData
    (CFSG.Quasithin.H13.F431.L3.borelData_swap
      (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := GaloisField 2 2)))
    (CFSG.Quasithin.H13.F431.L3.no_normal_two_subgroup (F := GaloisField 2 2))

theorem mdl_T0_le : projUnitriangular 3 (GaloisField 2 2) ≤ mdlM1 ⊓ mdlM2 := by
  have h : projUnitriangular 3 (GaloisField 2 2) ≤
      Subgroup.normalizer ((projUnitriangular 3 (GaloisField 2 2) :
        Subgroup (projectiveSL 3 (GaloisField 2 2))) : Set (projectiveSL 3 (GaloisField 2 2))) :=
    Subgroup.le_normalizer
  rwa [normalizer_U_eq_inf_V] at h

theorem mdl_card_T0 : Nat.card ↥(projUnitriangular 3 (GaloisField 2 2)) = 64 :=
  card_projUnitriangular_four natCard_gf4

theorem mdl_card_B0 : Nat.card ↥(mdlM1 ⊓ mdlM2) = 192 :=
  card_normalizer_inf_V natCard_gf4

theorem mdl_normalizer_T0 :
    Subgroup.normalizer ((projUnitriangular 3 (GaloisField 2 2) :
      Subgroup (projectiveSL 3 (GaloisField 2 2))) : Set (projectiveSL 3 (GaloisField 2 2))) =
      mdlM1 ⊓ mdlM2 :=
  normalizer_U_eq_inf_V

theorem mdl_sylow1 : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 (GaloisField 2 2)) mdlM1 :=
  CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U_normalizer (mdl_T0_le.trans inf_le_left)

theorem mdl_sylow2 : CFSG.QuasithinUnique.IsSylowTwoOf (projUnitriangular 3 (GaloisField 2 2)) mdlM2 :=
  CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U_normalizer (mdl_T0_le.trans inf_le_right)

theorem mdl_quot1 : CFSG.Quasithin.IsL2Quot 2 (CFSG.Quasithin.oTwoQuot ↥mdlM1) :=
  isL2Quot_normalizer_V2 natCard_gf4

theorem mdl_quot2 : CFSG.Quasithin.IsL2Quot 2 (CFSG.Quasithin.oTwoQuot ↥mdlM2) :=
  isL2Quot_normalizer_V1 natCard_gf4

theorem mdl_charTwo1 : CFSG.QuasithinUnique.CharTwo mdlM1 :=
  (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := GaloisField 2 2)).charTwo₂

theorem mdl_charTwo2 : CFSG.QuasithinUnique.CharTwo mdlM2 :=
  (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := GaloisField 2 2)).charTwo₁

theorem mdl_elem1 : CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 mdlM1) := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V2]
  exact CFSG.QuasithinUnique.Fin257.L3.isElemAbelian_V2

theorem mdl_elem2 : CFSG.Open.IsElemAbelian 2 (CFSG.Open.pCoreOf 2 mdlM2) := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V1]
  exact CFSG.QuasithinUnique.Fin257.L3.isElemAbelian_V1

theorem mdl_card1 : Nat.card ↥(CFSG.Open.pCoreOf 2 mdlM1) = 16 := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V2, card_V2, natCard_gf4] <;> norm_num

theorem mdl_card2 : Nat.card ↥(CFSG.Open.pCoreOf 2 mdlM2) = 16 := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V1, card_V1, natCard_gf4] <;> norm_num

theorem mdl_ne : CFSG.Open.pCoreOf 2 mdlM1 ≠ CFSG.Open.pCoreOf 2 mdlM2 := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V2, CFSG.QuasithinUnique.Fin257.L3.core_V1]
  exact CFSG.QuasithinUnique.Fin257.L3.V1_ne_V2.symm

theorem mdl_le1 : CFSG.Open.pCoreOf 2 mdlM1 ≤ projUnitriangular 3 (GaloisField 2 2) := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V2]
  exact CFSG.QuasithinUnique.Fin257.L3.V2_le_U

theorem mdl_le2 : CFSG.Open.pCoreOf 2 mdlM2 ≤ projUnitriangular 3 (GaloisField 2 2) := by
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V1]
  exact CFSG.QuasithinUnique.Fin257.L3.V1_le_U

theorem mdl_only : ∀ E : Subgroup (projectiveSL 3 (GaloisField 2 2)),
    E ≤ projUnitriangular 3 (GaloisField 2 2) → CFSG.Open.IsElemAbelian 2 E →
      Nat.card ↥E = 16 → E = CFSG.Open.pCoreOf 2 mdlM1 ∨ E = CFSG.Open.pCoreOf 2 mdlM2 := by
  intro E hE hab hcard
  rw [CFSG.QuasithinUnique.Fin257.L3.core_V2, CFSG.QuasithinUnique.Fin257.L3.core_V1]
  exact only_E16 natCard_gf4 E hE hab hcard

theorem mdl_facts : L34ModelFacts mdlPSL where
  T0_le := mdl_T0_le
  card_T0 := mdl_card_T0
  card_B0 := mdl_card_B0
  normalizer_T0 := mdl_normalizer_T0
  sylow1 := mdl_sylow1
  sylow2 := mdl_sylow2
  quot1 := mdl_quot1
  quot2 := mdl_quot2
  charTwo1 := mdl_charTwo1
  charTwo2 := mdl_charTwo2
  elem1 := mdl_elem1
  elem2 := mdl_elem2
  card1 := mdl_card1
  card2 := mdl_card2
  nat1 := natSec_normalizer_V2 natCard_gf4
  nat2 := natSec_normalizer_V1 natCard_gf4
  ne := mdl_ne
  le1 := mdl_le1
  le2 := mdl_le2
  only := mdl_only

end CFSG.GH74.QTGen4.DSGen4.L34

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

theorem leafL34Model : LeafL34Model :=
  Nonempty.intro ⟨L34.mdlPSL, L34.mdl_facts⟩

end CFSG.GH74.QTGen4.DSGen4

end
