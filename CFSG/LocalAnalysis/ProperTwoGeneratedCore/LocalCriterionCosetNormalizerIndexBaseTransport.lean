module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexRegularTransport

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u v

theorem borel_preimage_eq_original_point_stabilizer
    {G : Type u} {F : Type v} [Group G] [Group F]
    (H L : Subgroup G) (u : G) (huH : u ∈ H)
    (hLC : L ≤ Subgroup.centralizer ({u} : Set G))
    (f : L →* F) (B : Subgroup F) (e : cosetFixedSet H u ≃ F ⧸ B)
    (hbase : e ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr huH⟩ =
      QuotientGroup.mk 1)
    (he : letI := cosetFixedSetInverseRightAction H L u hLC
      ∀ a : L, ∀ omega : cosetFixedSet H u, e (a • omega) = f a • e omega) :
    B.comap f = H.subgroupOf L := by
  let := cosetFixedSetInverseRightAction H L u hLC
  let alpha : cosetFixedSet H u :=
    ⟨rightCosetMk H 1, (point_right_base_fixed_iff H u).mpr huH⟩
  ext a
  change f a ∈ B ↔ (a : G) ∈ H
  have hfix : f a ∈ B ↔ f a • (QuotientGroup.mk 1 : F ⧸ B) = QuotientGroup.mk 1 := by
    calc
      _ ↔ f a ∈ MulAction.stabilizer F (QuotientGroup.mk 1 : F ⧸ B) :=
        Iff.of_eq (congrArg (fun C : Subgroup F => f a ∈ C)
          (MulAction.stabilizer_quotient B).symm)
      _ ↔ _ := MulAction.mem_stabilizer_iff
  rw [hfix, ← hbase, ← he, e.injective.eq_iff]
  change (⟨pointRightCosetMul H (rightCosetMk H 1) (a : G)⁻¹, _⟩ :
    cosetFixedSet H u) = alpha ↔ (a : G) ∈ H
  rw [Subtype.ext_iff]
  exact (point_right_base_fixed_iff H (a : G)⁻¹).trans H.inv_mem_iff

theorem point_centralizer_offBase_orbit_of_full_model_identification
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
    (beta : pointRightCosetSpace H) (hbeta : beta ∈ cosetFixedSet H u)
    (hb : beta ≠ rightCosetMk H 1) :
    ∀ omega ∈ cosetFixedSet H u, omega ≠ rightCosetMk H 1 →
      ∃ a : (Subgroup.centralizer ({u} : Set G) ⊓ H : Subgroup G),
        pointRightCosetMul H beta (a : G) = omega := by
  have hpre := borel_preimage_eq_original_point_stabilizer H L u huH hLC f B e hbase he
  let R : Sylow 2 (B.comap f) := Sylow.nonempty.some
  have horbit := point_sylow_offBase_orbit_of_full_model_identification H L u huH hLC
    f hf hodd B hB hmodel e hbase he R beta hbeta hb
  intro omega homega ho
  obtain ⟨r, hr⟩ := horbit omega homega ho
  have hrpre : (r : L) ∈ B.comap f :=
    Subgroup.map_subtype_le (R : Subgroup (B.comap f)) r.property
  have hrH : ((r : L) : G) ∈ H := by
    exact (show B.comap f ≤ H.subgroupOf L from hpre.le) hrpre
  exact ⟨⟨((r : L) : G), ⟨hLC (r : L).property, hrH⟩⟩, hr⟩

theorem point_centralizer_index_of_full_model_identification
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
    (beta : pointRightCosetSpace H) (hbeta : beta ∈ cosetFixedSet H u)
    (hb : beta ≠ rightCosetMk H 1) :
    (pairPointStabilizer H beta).relIndex
        (Subgroup.centralizer ({u} : Set G) ⊓ H) = Nat.card (cosetFixedSet H u) - 1 := by
  exact point_centralizer_index_of_full_offBase_orbit H _ inf_le_right u huH inf_le_left
    beta hb hbeta (point_centralizer_offBase_orbit_of_full_model_identification
      H L u huH hLC f hf hodd B hB hmodel e hbase he beta hbeta hb)

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
