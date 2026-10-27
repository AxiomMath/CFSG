module

public import CFSG.Fischer.Classification.Unitary.Model
public import CFSG.LargeExtraspecial.S12InspP4Ord
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.Open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LieType.Universal.Unitary
open CFSG.Blueprint.Fischer (K)

namespace S12InspP5

theorem card_PG_eq {m : ℕ} (hm : 3 ≤ m) :
    Nat.card (PG m) = Nat.card (CFSG.Assembly.LowTwoRank.StatedProj
      (CFSG.Assembly.LowTwoRank.StatedSU m (2 ^ 1) K)) := by
  have h := SUid_eq_statedSU (F := K) (p := 2) (f := 1) card_K m
  show (center (SUid frob m)).index =
    ((CFSG.Assembly.LowTwoRank.StatedScalars (Fin m) K).subgroupOf
      (CFSG.Assembly.LowTwoRank.StatedSU m (2 ^ 1) K)).index
  rw [center_SUid hm, ← h]

theorem card_PG_four : Nat.card (PG 4) = 25920 := by
  rw [card_PG_eq (by norm_num), CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    Nat.prime_two le_rfl card_K (by norm_num)]
  decide

theorem card_PG_five : Nat.card (PG 5) = 13685760 := by
  rw [card_PG_eq (by norm_num), CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    Nat.prime_two le_rfl card_K (by norm_num)]
  decide

end S12InspP5

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_Xbar12_of_psu {g : G} {m : ℕ}
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    Nat.card (S.Xbar12 g) = Nat.card (PG m) := by
  obtain ⟨φ, -⟩ := fischerCentralQuotientModel_iff_U2.1 hmod
  exact Nat.card_congr (φ.trans (u2Equiv m)).toEquiv

theorem false_of_psu_five {g : G}
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 5 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 5 x y)
      (fischerTransvections (fischerHermitianF4 5)
        fun v => v ≠ 0 ∧ fischerHermitianF4 5 v v = 0)) : False := by
  have h10 : 2 ^ 10 ∣ Nat.card (S.Xbar12 g) := by
    rw [card_Xbar12_of_psu hmod, S12InspP5.card_PG_five]
    norm_num
  have := le_seven_of_two_pow_dvd_card_Xbar12 hP h10
  omega

theorem false_of_psu_four_of_section {g : G}
    (hP : ∀ P : Subgroup S.Mbar, IsPGroup 2 P → Nat.card P ≤ 2 ^ 7)
    (hsec : ∀ N : Subgroup S.Mbar, N.Normal → 20160 ∣ Nat.card N ∨ 20160 ∣ N.index)
    (hmod : fischerCentralQuotientModel (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4)
        fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0)) : False := by
  have hc : Nat.card (S.Xbar12 g) = 25920 := by
    rw [card_Xbar12_of_psu hmod, S12InspP5.card_PG_four]
  exact false_of_section (g := g) hP hsec (by rw [hc]; norm_num) (by rw [hc]; norm_num)

end Setting

end CFSG.LargeExtraspecial
