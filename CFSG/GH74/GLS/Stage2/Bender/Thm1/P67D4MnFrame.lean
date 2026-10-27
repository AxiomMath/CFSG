module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4DiagLang
public import CFSG.RankThree.Chevalley.SteinbergCBTrialityOpposition
public import CFSG.RankThree.Chevalley.SteinbergCFTrialityToralRoots
public import CFSG.RankThree.PartOne.KGD.D4Frame

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Commute

variable {L : Type} [Field L]

theorem diagramMap_comm_canonicalRep {w : WeylGroup TwistTag.D4.tag}
    (hw : w ∈ relWeylTwist TwistTag.D4) :
    diagramMap TwistTag.D4 L * canonicalRep (coxeterSystem TwistTag.D4.tag) L w =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w * diagramMap TwistTag.D4 L := by
  obtain ⟨-, hΓ⟩ := Subgroup.mem_inf.1
    (canonicalRep_mem_graphFixedMonomial TwistTag.D4 L (RingHom.id L) hw)
  obtain ⟨-, hfix⟩ := (mem_twistedFixedGroup_iff_twistHom _ _ _).1 hΓ
  rw [twistHom_apply] at hfix
  have h1 : Units.map (entrywiseHom (RingHom.id L))
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L w) =
      canonicalRep (coxeterSystem TwistTag.D4.tag) L w := Units.ext (entrywise_id _)
  rw [h1] at hfix
  exact mul_inv_eq_iff_eq_mul.1 hfix

theorem diagramMap_comm_trialityOpposition :
    diagramMap TwistTag.D4 L * trialityOpposition L =
      trialityOpposition L * diagramMap TwistTag.D4 L := by
  have ho := diagramMap_comm_canonicalRep (L := L)
    (TwistTag.D4.orbitReflection_mem ⟨0, by decide⟩)
  have hm := diagramMap_comm_canonicalRep (L := L)
    (TwistTag.D4.orbitReflection_mem ⟨1, by decide⟩)
  have ho' : Commute (diagramMap TwistTag.D4 L) (trialityOuterRep L) := ho
  have hm' : Commute (diagramMap TwistTag.D4 L) (trialityMiddleRep L) := hm
  have ha : Commute (diagramMap TwistTag.D4 L) (trialityOppositionShift L) := hm'.mul_right ho'
  exact ho'.mul_right ((ha.mul_right hm').mul_right ha.inv_right)

theorem twistHom_diagramMap (Fr : L →+* L) :
    twistHom TwistTag.D4 L Fr (diagramMap TwistTag.D4 L) = diagramMap TwistTag.D4 L := by
  rw [twistHom_apply, units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_diagramMap]
  group

theorem twistHom_conj_diagramMap_inv (Fr : L →+* L) (x : ModGL TwistTag.D4.tag L) :
    twistHom TwistTag.D4 L Fr ((diagramMap TwistTag.D4 L)⁻¹ * x * diagramMap TwistTag.D4 L) =
      (diagramMap TwistTag.D4 L)⁻¹ * twistHom TwistTag.D4 L Fr x * diagramMap TwistTag.D4 L := by
  rw [map_mul, map_mul, map_inv, twistHom_diagramMap]

theorem d4Minus_exists_frame [IsAlgClosed L] (p : ℕ) [Fact p.Prime] [CharP L p] (hp2 : p ≠ 2)
    {f : ℕ} (hf : 1 ≤ f) :
    ∃ g₀ : ModGL TwistTag.D4.tag L, g₀ ∈ adjointGroup TwistTag.D4.tag L ∧
      diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L ∧
      twistHom TwistTag.D4 L (iterateFrobenius L p f) g₀ = g₀ * trialityOpposition L := by
  have hzC : trialityOpposition L ∈ adjointGroup TwistTag.D4.tag L :=
    monomialSubgroup_le_adjointGroup' trialityOpposition_mem_monomialSubgroup
  have hz : trialityOpposition L ∈
      graphCentralizer TwistTag.D4.tag L (diagramMap TwistTag.D4 L) :=
    Subgroup.mem_inf.2 ⟨hzC, Subgroup.mem_centralizer_singleton_iff.2
      diagramMap_comm_trialityOpposition.symm⟩
  obtain ⟨g, hg, hgz⟩ := D4_diagram_centralizer_Lang p hp2 L hf (trialityOpposition L) hz
  obtain ⟨hgC, hgP⟩ := Subgroup.mem_inf.1 hg
  have hgP' : diagramMap TwistTag.D4 L * g = g * diagramMap TwistTag.D4 L :=
    (Subgroup.mem_centralizer_singleton_iff.1 hgP).symm
  refine ⟨g, hgC, hgP', ?_⟩
  rw [twistHom_apply]
  have h1 : Units.map (entrywiseHom (iterateFrobenius L p f)) g = g * trialityOpposition L := by
    rw [← hgz]
    group
  have h2 : diagramMap TwistTag.D4 L * (g * trialityOpposition L) =
      (g * trialityOpposition L) * diagramMap TwistTag.D4 L := by
    rw [← mul_assoc, hgP', mul_assoc, diagramMap_comm_trialityOpposition, ← mul_assoc]
  rw [h1, h2, mul_inv_cancel_right]

end Commute

section Psi

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {L : Type} [Field L] [Algebra K L]

def d4MinusPsi (σ : K ≃+* K) (L : Type) [Field L] [Algebra K L]
    (g₀ : ModGL TwistTag.D4.tag L) :
    graphFixedRootGroup TwistTag.D4 K σ.toRingHom →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj g₀⁻¹).toMonoidHom.comp (triEmb K σ L)

omit
  [Finite K] in
theorem d4MinusPsi_apply (g₀ : ModGL TwistTag.D4.tag L)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    d4MinusPsi σ L g₀ y = g₀⁻¹ * triEmb K σ L y * g₀ := by
  simp only [d4MinusPsi, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]

omit
  [Finite K] in
theorem d4MinusPsi_injective (g₀ : ModGL TwistTag.D4.tag L) :
    Function.Injective (d4MinusPsi σ L g₀) := by
  intro a b h
  rw [d4MinusPsi_apply, d4MinusPsi_apply] at h
  have h1 : g₀⁻¹ * triEmb K σ L a = g₀⁻¹ * triEmb K σ L b := mul_right_cancel h
  have h2 : triEmb K σ L a = triEmb K σ L b := mul_left_cancel h1
  exact triEmb_injective h2

omit
  [Finite K] in
theorem d4MinusPsi_mem_adjointGroup {g₀ : ModGL TwistTag.D4.tag L}
    (hg₀ : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    d4MinusPsi σ L g₀ y ∈ adjointGroup TwistTag.D4.tag L := by
  rw [d4MinusPsi_apply]
  exact mul_mem (mul_mem (inv_mem hg₀) (triEmb_mem_adjointGroup y)) hg₀

theorem triEmb_fieldActor (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L))
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    triEmb K σ L (fieldActor (t := TwistTag.D4) σ σ y) =
      (diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L y * diagramMap TwistTag.D4 L := by
  have h1 : triEmb K σ L (fieldActor (t := TwistTag.D4) σ σ y) =
      Units.map (entrywiseHom Fr) (triEmb K σ L y) := by
    rw [triEmb_apply, triEmb_apply, coe_fieldActor, units_map_entrywiseHom_eq_baseChangeGL,
      units_map_entrywiseHom_eq_baseChangeGL, CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL,
      CFSG.LieType.Chevalley.baseChangeGL_baseChangeGL, hcomm]
  have h2 := triEmb_fixed Fr hcomm y
  rw [twistHom_apply] at h2
  rw [h1]
  calc Units.map (entrywiseHom Fr) (triEmb K σ L y) =
      (diagramMap TwistTag.D4 L)⁻¹ * (diagramMap TwistTag.D4 L *
        Units.map (entrywiseHom Fr) (triEmb K σ L y) * (diagramMap TwistTag.D4 L)⁻¹) *
          diagramMap TwistTag.D4 L := by group
    _ = _ := by rw [h2]

theorem d4MinusPsi_fieldActor {g₀ : ModGL TwistTag.D4.tag L} (Fr : L →+* L)
    (hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L))
    (hP : diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L)
    (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    d4MinusPsi σ L g₀ (fieldActor (t := TwistTag.D4) σ σ y) =
      (diagramMap TwistTag.D4 L)⁻¹ * d4MinusPsi σ L g₀ y * diagramMap TwistTag.D4 L := by
  rw [d4MinusPsi_apply, d4MinusPsi_apply, triEmb_fieldActor Fr hcomm]
  have h1 : g₀⁻¹ * (diagramMap TwistTag.D4 L)⁻¹ = (diagramMap TwistTag.D4 L)⁻¹ * g₀⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, hP]
  have h2 : diagramMap TwistTag.D4 L * g₀ = g₀ * diagramMap TwistTag.D4 L := hP
  calc g₀⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * triEmb K σ L y * diagramMap TwistTag.D4 L) * g₀
      = (g₀⁻¹ * (diagramMap TwistTag.D4 L)⁻¹) * triEmb K σ L y *
          (diagramMap TwistTag.D4 L * g₀) := by group
    _ = _ := by rw [h1, h2]; group

omit [Finite K] in
theorem d4MinusPsi_mem_range_iff {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {g₀ : ModGL TwistTag.D4.tag L}
    (hg₀C : g₀ ∈ adjointGroup TwistTag.D4.tag L)
    (hg₀ : twistHom TwistTag.D4 L Fr g₀ = g₀ * trialityOpposition L)
    (x : ModGL TwistTag.D4.tag L) :
    x ∈ (d4MinusPsi σ L g₀).range ↔ x ∈ adjointGroup TwistTag.D4.tag L ∧
      trialityOpposition L * twistHom TwistTag.D4 L Fr x * (trialityOpposition L)⁻¹ = x := by
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by simp [hσ, hFr, map_pow]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨d4MinusPsi_mem_adjointGroup hg₀C y, ?_⟩
    rw [d4MinusPsi_apply, map_mul, map_mul, map_inv, hg₀, triEmb_fixed Fr hcomm y]
    group
  · rintro ⟨hxC, hx⟩
    have hu : g₀ * x * g₀⁻¹ ∈ (triEmb K σ L).range := by
      rw [triEmb_range hℓ hf hK hσ Fr hFr]
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg₀C hxC) (inv_mem hg₀C), ?_⟩
      change twistHom TwistTag.D4 L Fr (g₀ * x * g₀⁻¹) = g₀ * x * g₀⁻¹
      rw [map_mul, map_mul, map_inv, hg₀]
      calc g₀ * trialityOpposition L * twistHom TwistTag.D4 L Fr x *
            (g₀ * trialityOpposition L)⁻¹ =
          g₀ * (trialityOpposition L * twistHom TwistTag.D4 L Fr x *
            (trialityOpposition L)⁻¹) * g₀⁻¹ := by group
        _ = g₀ * x * g₀⁻¹ := by rw [hx]
    obtain ⟨y, hy⟩ := hu
    refine ⟨y, ?_⟩
    rw [d4MinusPsi_apply, hy]
    group

end Psi

end CFSG.GH74.GLS.Stage2.Bender.Thm1
