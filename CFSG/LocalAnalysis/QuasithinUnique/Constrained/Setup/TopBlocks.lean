module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftOrigImages
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.TopMain

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Layer CFSG.QuasithinUnique.Setup.Layer.Actor
  CFSG.QuasithinUnique.Setup.Offender
open scoped LinearAlgebra.Projectivization

@[expose] def NaturalCanonicalLin2Blocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (hS : EvenSL2Setting X R M V n F), CharTwo X →
    (∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ X ≤ Subgroup.normalizer (Rc : Set G)) →
    autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
    ∀ (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), IsCompList (autOn X V) r Lc →
      EvenSL2BlockOutput X R V hS.reduced.2.1 n r Lc

@[expose] def DeletedCanonicalAlt5Blocks : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X R M V : Subgroup G) (n : ℕ) (F : Type) [Field F]
    (hS : EvenSL2Setting X R M V n F), CharTwo X →
    (∀ Rc : Subgroup G, Rc ≠ ⊥ → Rc ≤ baum R → (Rc.subgroupOf (baum R)).Characteristic →
      ¬ X ≤ Subgroup.normalizer (Rc : Set G)) → n = 2 →
    ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V →
    ∀ (r : ℕ) (Lc : Fin r → Subgroup (MulAut V)), IsCompList (autOn X V) r Lc →
      EvenSL2BlockOutput X R V hS.reduced.2.1 n r Lc

section Main

variable {G : Type} [Group G] [Finite G]

theorem n_eq_two_of_not_le
    {X R M V : Subgroup G} {n : ℕ} {F : Type} [Field F]
    (hS : EvenSL2Setting X R M V n F) {r : ℕ} {Lc : Fin r → Subgroup (MulAut V)}
    (hLc : IsCompList (autOn X V) r Lc)
    (hle : ¬ autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V) : n = 2 := by
  classical
  have hFfin : Finite F := Nat.finite_of_card_ne_zero (by rw [hS.card_eq]; positivity)
  let _ : Fintype F := Fintype.ofFinite F
  let _ : Fintype (ℙ F (Fin 2 → F)) := Fintype.ofFinite _
  let _ : DecidableEq (ℙ F (Fin 2 → F)) := Classical.decEq _
  obtain ⟨⟨W, hW1, hW2, hW3, θ, hmax, himg⟩⟩ := even_SL2_original_images hS hLc
  have hbridge := even_SL2_original_bridge hS hLc
  rcases hmax.offenders.family.alternatives with ⟨hnat, -⟩ | ⟨hdel, -⟩
  · exfalso
    apply hle
    have h1 := (himg.natural hnat).2.1.1
    have h2 : (autOn (oddOrderSubgroup X) V).map (binPsi θ).toMonoidHom =
        oddGen ((autOn X V).map (binPsi θ).toMonoidHom) := by
      rw [hbridge.K_eq]
      exact map_closure_odd (binPsi θ) (autOn X V)
    rw [← h2] at h1
    exact (Subgroup.map_le_map_iff_of_injective (binPsi θ).injective).1 h1
  · exact hdel.n_eq

theorem actual_block_production_of_canonical
    (hNat : NaturalCanonicalLin2Blocks)
    (hDel : DeletedCanonicalAlt5Blocks) : EvenSL2ActualBlockProduction := by
  intro G _ _ X R M V n F _ hS hchar hno r Lc hLc
  by_cases hle : autOn (thompsonJ R) V ≤ autOn (oddOrderSubgroup X) V
  · exact hNat G X R M V n F hS hchar hno hle r Lc hLc
  · exact hDel G X R M V n F hS hchar hno (n_eq_two_of_not_le hS hLc hle) hle r Lc hLc

end Main

end CFSG.QuasithinUnique.Setup.Lift

namespace CFSG.QuasithinUnique.Setup.Top

open CFSG.Quasithin CFSG.SectionRank CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.Family CFSG.QuasithinUnique.Setup.Lift

theorem minParabolicBlocks_of_canonical
    (hSolv : SolvableA3Family)
    (hNat : NaturalCanonicalLin2Blocks) (hDel : DeletedCanonicalAlt5Blocks)
    (hSQT : NonsolvableActionSQT) (hone : OneQuasisimpleResidualProp)
    (hfam : FamilyRestrictionProp) (hA6 : NoAlt6Component) (hU33 : NoPSU33Component)
    (hU32 : NoEvenUnitaryThreeComponent) (hTri : NoTrialityOrLargeReeComponent)
    (hG2 : NoG2OrTitsComponent) (hL3 : X7a.ActualLinearThreeSelfDualSections)
    (hSp4 : X7b.ActualSymplecticFourData) : MinParabolicBlocks :=
  minParabolicBlocks_of_clusters hSolv (actual_block_production_of_canonical hNat hDel) hSQT hone
    hfam hA6 hU33 hU32 hTri hG2 hL3 hSp4

end CFSG.QuasithinUnique.Setup.Top
