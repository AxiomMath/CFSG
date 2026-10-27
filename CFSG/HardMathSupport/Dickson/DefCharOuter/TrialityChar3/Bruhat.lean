module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.BruhatCaseA
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.BruhatCaseB
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem exists_bruhat_factor (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ∃ (w : WeylGroup TwistTag.D4.tag) (b u : ModGL TwistTag.D4.tag K),
      weylTwist TwistTag.D4 w = w ∧ b ∈ graphFixedBorel TwistTag.D4 K σ.toRingHom ∧
      u ∈ graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom w ∧
      (g : ModGL TwistTag.D4.tag K) =
        b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u := by
  have hΓ : (g : ModGL TwistTag.D4.tag K) ∈ twistedFixedGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom g.2
  have hadj : (g : ModGL TwistTag.D4.tag K) ∈
      (adjointGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) :=
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.D4 K σ.toRingHom).1 hΓ).1
  rw [adjointGroup_eq_iUnion_bruhatCell] at hadj
  obtain ⟨w, hgw⟩ := Set.mem_iUnion.1 hadj
  obtain ⟨hδ, b, hb, u, hu, hbu⟩ :=
    exists_fixed_bruhat_factor (σ := σ.toRingHom) σ.surjective hΓ hgw
  exact ⟨w, b, u, hδ, hb, hu, hbu.symm⟩

theorem fieldActor_eq_of_conj_mul_fixed {c : K} (hc : σ c = c) (hc0 : c ≠ 0)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc * fieldActor (t := TwistTag.D4) σ σ g *
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc)⁻¹ = g) :
    fieldActor (t := TwistTag.D4) σ σ g = g := by
  obtain ⟨w, b, u, hw, hb, hu, hgbu⟩ := exists_bruhat_factor hf hK σ hσ g
  by_cases hinv : rootD ∈ inversionSet w
  · exact (bruhat_caseA hf hK σ hσ hc hc0 g hg hw hb hu hgbu hinv).elim
  · exact bruhat_caseB hf hK σ hσ hc hc0 g hg hw hb hu hgbu hinv

theorem fixSubgroup_conj_mul_fieldActor_eq {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    fixSubgroup (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
        fieldActor (t := TwistTag.D4) σ σ) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) ⊓
        Subgroup.centralizer {longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc} := by
  set z := longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc
  ext g
  constructor
  · intro hg
    have hg' : z * fieldActor (t := TwistTag.D4) σ σ g * z⁻¹ = g := hg
    have hδ : fieldActor (t := TwistTag.D4) σ σ g = g :=
      fieldActor_eq_of_conj_mul_fixed hf hK σ hσ hc hc0 g hg'
    rw [hδ] at hg'
    refine Subgroup.mem_inf.2 ⟨(CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup).2 hδ,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    calc g * z = z * g * z⁻¹ * z := by rw [hg']
      _ = z * g := by group
  · intro hg
    obtain ⟨hδ, hcomm⟩ := Subgroup.mem_inf.1 hg
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup] at hδ
    have hcomm' := Subgroup.mem_centralizer_singleton_iff.1 hcomm
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, MulAut.mul_apply,
      MulAut.conj_apply, hδ, ← hcomm', mul_inv_cancel_right]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
