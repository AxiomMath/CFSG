module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.D4Comm
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private theorem mul_cyc_of_commute {G : Type*} [Group G] {a b c : G} (hab : Commute a b)
    (hac : Commute a c) : b * c * a = a * b * c := by
  rw [mul_assoc, ← hac.eq, ← mul_assoc, ← hab.eq]

private abbrev idx0 : Fin TwistTag.D4.tag.rank := ⟨0, by decide⟩
private abbrev idx1 : Fin TwistTag.D4.tag.rank := ⟨1, by decide⟩
private abbrev idx3 : Fin TwistTag.D4.tag.rank := ⟨3, by decide⟩

private theorem rootA0_eq_single : rootA0 = Pi.single idx0 1 := by decide
private theorem rootA1_eq_single : rootA1 = Pi.single idx1 1 := by decide
private theorem rootA3_eq_single : rootA3 = Pi.single idx3 1 := by decide

private theorem perm_idx0 : TwistTag.D4.perm idx0 = idx1 := by decide
private theorem perm_idx1 : TwistTag.D4.perm idx1 = idx3 := by decide
private theorem perm_idx3 : TwistTag.D4.perm idx3 = idx0 := by decide

section ShortRoots

variable {K : Type} [Field K] (σ : K ≃+* K)

private theorem twistHom_pinnedX_single (i : Fin TwistTag.D4.tag.rank) (c : K) :
    twistHom TwistTag.D4 K σ.toRingHom (pinnedX TwistTag.D4.tag K (Pi.single i 1) c) =
      pinnedX TwistTag.D4.tag K (Pi.single (TwistTag.D4.perm i) 1) (σ c) := by
  rw [pinnedX_single, pinnedX_single, twistHom_xUnit]
  rfl

private theorem units_map_pinnedX (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K α c) =
      pinnedX TwistTag.D4.tag K α (σ c) := by
  refine Units.ext ?_
  rw [Units.coe_map]
  exact entrywise_pinnedX σ.toRingHom α c

end ShortRoots

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem pinnedX_short_mem {t : K} (ht : σ t = t) :
    pinnedX TwistTag.D4.tag K rootA0 t * pinnedX TwistTag.D4.tag K rootA1 t *
        pinnedX TwistTag.D4.tag K rootA3 t ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
  rw [rootA0_eq_single, rootA1_eq_single, rootA3_eq_single]
  have hU : ∀ i : Fin TwistTag.D4.tag.rank,
      pinnedX TwistTag.D4.tag K (Pi.single i 1) t ∈ posUnipotent TwistTag.D4.tag K := fun i =>
    pinnedX_mem_rootSpan (S := {α : Fin TwistTag.D4.tag.rank → ℤ |
        IsRoot TwistTag.D4.tag α ∧ 0 < height α})
      (show Pi.single i (1 : ℤ) ∈ {α : Fin TwistTag.D4.tag.rank → ℤ |
          IsRoot TwistTag.D4.tag α ∧ 0 < height α} from
        ⟨isRoot_single _ _, by rw [height_single]; norm_num⟩) t
  have c01 : Commute (pinnedX TwistTag.D4.tag K (Pi.single idx0 1) t)
      (pinnedX TwistTag.D4.tag K (Pi.single idx1 1) t) :=
    commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.D4) K (isRoot_single _ _)
      (isRoot_single _ _) (by decide) t t
  have c03 : Commute (pinnedX TwistTag.D4.tag K (Pi.single idx0 1) t)
      (pinnedX TwistTag.D4.tag K (Pi.single idx3 1) t) :=
    commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.D4) K (isRoot_single _ _)
      (isRoot_single _ _) (by decide) t t
  have hF : twistHom TwistTag.D4 K σ.toRingHom
      (pinnedX TwistTag.D4.tag K (Pi.single idx0 1) t *
        pinnedX TwistTag.D4.tag K (Pi.single idx1 1) t *
        pinnedX TwistTag.D4.tag K (Pi.single idx3 1) t) =
      pinnedX TwistTag.D4.tag K (Pi.single idx0 1) t *
        pinnedX TwistTag.D4.tag K (Pi.single idx1 1) t *
        pinnedX TwistTag.D4.tag K (Pi.single idx3 1) t := by
    rw [map_mul, map_mul, twistHom_pinnedX_single, twistHom_pinnedX_single,
      twistHom_pinnedX_single, ht, perm_idx0, perm_idx1, perm_idx3]
    exact mul_cyc_of_commute c01 c03
  rw [graphFixedPosUnipotent, Subgroup.mem_inf, mem_twistedFixedGroup_iff_twistHom]
  exact ⟨mul_mem (mul_mem (hU idx0) (hU idx1)) (hU idx3),
    mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _) (pinnedX_mem_adjointGroup _ _))
      (pinnedX_mem_adjointGroup _ _), hF⟩

@[expose] noncomputable def shortElt {t : K} (ht : σ t = t) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
  ⟨pinnedX TwistTag.D4.tag K rootA0 t * pinnedX TwistTag.D4.tag K rootA1 t *
      pinnedX TwistTag.D4.tag K rootA3 t,
    le_sup_left (a := graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom)
      (pinnedX_short_mem hf hK σ hσ ht)⟩

theorem coe_shortElt {t : K} (ht : σ t = t) :
    ((shortElt hf hK σ hσ ht : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K rootA0 t * pinnedX TwistTag.D4.tag K rootA1 t *
        pinnedX TwistTag.D4.tag K rootA3 t := rfl

theorem fieldActor_shortElt {t : K} (ht : σ t = t) :
    fieldActor (t := TwistTag.D4) σ σ (shortElt hf hK σ hσ ht) = shortElt hf hK σ hσ ht := by
  refine Subtype.ext ?_
  rw [coe_fieldActor, coe_shortElt, map_mul, map_mul, units_map_pinnedX, units_map_pinnedX,
    units_map_pinnedX, ht]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
