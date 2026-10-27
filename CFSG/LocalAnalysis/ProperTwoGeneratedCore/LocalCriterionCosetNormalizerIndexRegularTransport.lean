module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexModelRegular
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexFixedOrbit

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u v w x

theorem regularOn_of_equivariant_equiv {L : Type u} [Group L]
    {Omega : Type v} {Lambda : Type w} [MulAction L Omega] [MulAction L Lambda]
    (A : Subgroup L) (e : Omega ≃ Lambda)
    (he : ∀ a : L, ∀ omega : Omega, e (a • omega) = a • e omega)
    (X : Set Omega) (Y : Set Lambda) (hXY : ∀ omega, omega ∈ X ↔ e omega ∈ Y)
    (hreg : IsRegularOn A Y) : IsRegularOn A X := by
  intro a b ha hb
  obtain ⟨r, hr, huniq⟩ := hreg ((hXY a).mp ha) ((hXY b).mp hb)
  refine ⟨r, ?_, ?_⟩
  · apply e.injective
    rw [he]
    exact hr
  · intro s hs
    apply huniq s
    rw [← he, hs]

@[expose, instance_reducible] def cosetFixedSetInverseRightAction
    {G : Type u} [Group G] (H L : Subgroup G) (u : G)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G)) :
    MulAction L (cosetFixedSet H u) :=
  pointInvariantSetInverseRightAction H L (cosetFixedSet H u)
    (fun a ha omega homega =>
      point_centralizer_preserves_cosetFixedSet H u a (hLC ha) (omega := omega) homega)

theorem cosetFixedSetInverseRightAction_smul
    {G : Type u} [Group G] (H L : Subgroup G) (u : G)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (a : L) (omega : cosetFixedSet H u) :
    letI := cosetFixedSetInverseRightAction H L u hLC
    ((a • omega : cosetFixedSet H u) : pointRightCosetSpace H) =
      pointRightCosetMul H omega.val (a : G)⁻¹ := rfl

theorem point_sylow_offBase_orbit_of_full_model_identification
    {G : Type u} {F : Type v} [Group G] [Group F] [Finite G] [Finite F]
    (H L : Subgroup G) (u : G) (huH : u ∈ H)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (f : L →* F) (hf : Function.Surjective f) (hodd : Odd (Nat.card f.ker))
    (B : Subgroup F) (hB : IsBorelSubgroup B) (hmodel : IsSimpleBenderGroup F)
    (e : cosetFixedSet H u ≃ F ⧸ B)
    (hbase : e ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr huH⟩ =
      QuotientGroup.mk 1)
    (he : letI := cosetFixedSetInverseRightAction H L u hLC
      ∀ a : L, ∀ omega : cosetFixedSet H u, e (a • omega) = f a • e omega)
    (R : Sylow 2 (B.comap f)) :
    ∀ beta ∈ cosetFixedSet H u, beta ≠ rightCosetMk H 1 →
      ∀ omega ∈ cosetFixedSet H u, omega ≠ rightCosetMk H 1 →
        ∃ r : ((R : Subgroup (B.comap f)).map (B.comap f).subtype),
          pointRightCosetMul H beta ((r : L) : G) = omega := by
  let := cosetFixedSetInverseRightAction H L u hLC
  let A : Subgroup L := (R : Subgroup (B.comap f)).map (B.comap f).subtype
  have hreg : letI : MulAction L (F ⧸ B) := MulAction.compHom (F ⧸ B) f
      IsRegularOn A {omega : F ⧸ B | omega ≠ QuotientGroup.mk 1} :=
    simpleBender_borel_preimage_sylow_regular f hf hodd B hB hmodel R
  intro beta hbeta hb omega homega ho
  let b : cosetFixedSet H u := ⟨beta, hbeta⟩
  let o : cosetFixedSet H u := ⟨omega, homega⟩
  have heb : e b ≠ QuotientGroup.mk 1 := by
    intro h
    have hh := e.injective (h.trans hbase.symm)
    exact hb (congrArg Subtype.val hh)
  have heo : e o ≠ QuotientGroup.mk 1 := by
    intro h
    have hh := e.injective (h.trans hbase.symm)
    exact ho (congrArg Subtype.val hh)
  obtain ⟨r, hr, _⟩ := hreg heb heo
  have hs : ((r : L) • b : cosetFixedSet H u) = o := by
    apply e.injective
    rw [he]
    exact hr
  refine ⟨r⁻¹, ?_⟩
  have hv := congrArg Subtype.val hs
  change pointRightCosetMul H beta ((r : L) : G)⁻¹ = omega at hv
  simpa only [Subgroup.coe_inv] using hv

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
