module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Cov

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem bruhat_caseA {c : K} (hc : σ c = c) (hc0 : c ≠ 0)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg : longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc * fieldActor (t := TwistTag.D4) σ σ g *
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc)⁻¹ = g)
    {w : WeylGroup TwistTag.D4.tag} (hw : weylTwist TwistTag.D4 w = w) {b u : ModGL TwistTag.D4.tag K}
    (hb : b ∈ graphFixedBorel TwistTag.D4 K σ.toRingHom)
    (hu : u ∈ graphFixedInversionUnipotent TwistTag.D4 K σ.toRingHom w)
    (hgbu : (g : ModGL TwistTag.D4.tag K) =
      b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w * u)
    (hinv : rootD ∈ inversionSet w) : False := by
  obtain ⟨z, hzdef⟩ : ∃ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      z = longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc := ⟨_, rfl⟩
  rw [← hzdef] at hg
  have hzM : (z : ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K rootD c := by
    subst hzdef
    rfl
  have hEg : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) =
      (z : ModGL TwistTag.D4.tag K)⁻¹ * (g : ModGL TwistTag.D4.tag K) *
        (z : ModGL TwistTag.D4.tag K) := by
    have h1 := congrArg (fun x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
      (x : ModGL TwistTag.D4.tag K)) hg
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_fieldActor] at h1
    calc Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K)
        = (z : ModGL TwistTag.D4.tag K)⁻¹ * ((z : ModGL TwistTag.D4.tag K) *
            Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.D4.tag K) *
              (z : ModGL TwistTag.D4.tag K)⁻¹) * (z : ModGL TwistTag.D4.tag K) := by group
      _ = (z : ModGL TwistTag.D4.tag K)⁻¹ * (g : ModGL TwistTag.D4.tag K) *
            (z : ModGL TwistTag.D4.tag K) := by rw [h1]
  have hmain : Units.map (entrywiseHom σ.toRingHom) b *
      canonicalRep (coxeterSystem TwistTag.D4.tag) K w * Units.map (entrywiseHom σ.toRingHom) u =
      (z : ModGL TwistTag.D4.tag K)⁻¹ * b * canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
        (u * (z : ModGL TwistTag.D4.tag K)) := by
    have h2 : Units.map (entrywiseHom σ.toRingHom) b *
        canonicalRep (coxeterSystem TwistTag.D4.tag) K w *
          Units.map (entrywiseHom σ.toRingHom) u =
        (z : ModGL TwistTag.D4.tag K)⁻¹ * (g : ModGL TwistTag.D4.tag K) *
          (z : ModGL TwistTag.D4.tag K) := by
      rw [← hEg, hgbu, map_mul, map_mul, entrywise_canonicalRep σ w]
    rw [h2, hgbu]
    group
  have hbB : b ∈ borelGroup TwistTag.D4.tag K := (Subgroup.mem_inf.1 hb).1
  have huR : u ∈ rootSpan TwistTag.D4.tag K (inversionSet w) := (Subgroup.mem_inf.1 hu).1
  have hzR : (z : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K (inversionSet w) := by
    rw [hzM]
    exact pinnedX_mem_rootSpan hinv c
  have hIB : rootSpan TwistTag.D4.tag K (inversionSet w) ≤ borelGroup TwistTag.D4.tag K :=
    (rootSpan_le_posUnipotent fun _ h => inversionSet_pos (w := w) h).trans le_sup_right
  have hEb : Units.map (entrywiseHom σ.toRingHom) b ∈ borelGroup TwistTag.D4.tag K :=
    entrywise_mem_borelGroup (σ := σ) hbB
  have hEu : Units.map (entrywiseHom σ.toRingHom) u ∈
      rootSpan TwistTag.D4.tag K (inversionSet w) :=
    entrywise_mem_rootSpan (σ := σ) huR
  have hzb : (z : ModGL TwistTag.D4.tag K)⁻¹ * b ∈ borelGroup TwistTag.D4.tag K :=
    mul_mem (inv_mem (hIB hzR)) hbB
  have huz : u * (z : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K (inversionSet w) :=
    mul_mem huR hzR
  have hp : (Units.map (entrywiseHom σ.toRingHom) b, Units.map (entrywiseHom σ.toRingHom) u) ∈
      (borelGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) ×ˢ
        (rootSpan TwistTag.D4.tag K (inversionSet w) : Set (ModGL TwistTag.D4.tag K)) :=
    Set.mk_mem_prod hEb hEu
  have hq : ((z : ModGL TwistTag.D4.tag K)⁻¹ * b, u * (z : ModGL TwistTag.D4.tag K)) ∈
      (borelGroup TwistTag.D4.tag K : Set (ModGL TwistTag.D4.tag K)) ×ˢ
        (rootSpan TwistTag.D4.tag K (inversionSet w) : Set (ModGL TwistTag.D4.tag K)) :=
    Set.mk_mem_prod hzb huz
  have hinj := (bijOn_bruhatCell (K := K) w).2.1 hp hq hmain
  have hEu' : Units.map (entrywiseHom σ.toRingHom) u = u * (z : ModGL TwistTag.D4.tag K) :=
    congrArg Prod.snd hinj
  have huP : u ∈ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedInversionUnipotent_le_graphFixedPosUnipotent (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) w hu
  obtain ⟨uC, huCdef⟩ : ∃ uC : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (uC : ModGL TwistTag.D4.tag K) = u :=
    ⟨⟨u, graphFixedPosUnipotent_le_graphFixedRootGroup (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) huP⟩, rfl⟩
  have huC : (uC : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [huCdef]
    exact huP
  have h0B : longElt hf hK σ hσ (Or.inl rfl) 0 (map_zero σ) = 1 :=
    Subtype.ext (pinnedX_zero TwistTag.D4.tag K rootB)
  have h0C : longElt hf hK σ hσ (Or.inr (Or.inl rfl)) 0 (map_zero σ) = 1 :=
    Subtype.ext (pinnedX_zero TwistTag.D4.tag K rootC)
  have hfix : fieldActor (t := TwistTag.D4) σ σ uC = uC * (longElt hf hK σ hσ (Or.inl rfl) 0
      (map_zero σ) * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) 0 (map_zero σ) *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) := by
    simp only [h0B, h0C, one_mul]
    apply Subtype.ext
    rw [coe_fieldActor, Subgroup.coe_mul, huCdef, ← hzdef]
    exact hEu'
  obtain ⟨-, -, hc'⟩ := fieldActor_eq_mul_long_imp hf hK σ hσ uC huC 0 0 c (map_zero σ)
    (map_zero σ) hc hfix
  exact hc0 hc'

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
