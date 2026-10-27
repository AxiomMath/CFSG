module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.CentEquiv
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2NoL2
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.G2Weyl
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Bruhat
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.FieldActorFixed
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.TriD4Aux.Three
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.G2Subgroup
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.D4G2All
public import CFSG.RankThree.PartOne.KGD.D4T36Core
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4OutG2
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.Core

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.GH74.GLS.Stage2.Bender.Thm1
open CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
open CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
open CFSG.RankThree.PartTwo.KFacts
open CFSG.ComponentClassification.UnbalancedCatalog

set_option linter.unusedSectionVars false


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem three_le_card_fixSubfield : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
  rw [ENat.card_eq_coe_natCard,
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ]
  exact_mod_cast Nat.le_self_pow (by omega) 3

omit hf hK hσ in
@[expose] def fixToImage (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) →* ↥(trialityFieldImage σ σ) where
  toFun x := ⟨(x.1 : ModGL TwistTag.D4.tag K),
    (d4_mem_trialityFieldImage_self_iff σ hσ3 x.1).2 (mem_fixSubgroup.1 x.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit hf hK hσ in
theorem fixToImage_bijective (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    Function.Bijective (fixToImage σ hσ3) := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · have h' := congrArg (fun z : ↥(trialityFieldImage σ σ) => (z : ModGL TwistTag.D4.tag K)) h
    exact Subtype.ext (Subtype.ext h')
  · have hy : (y : ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      d4_trialityFieldImage_self_le σ y.2
    refine ⟨⟨⟨_, hy⟩, mem_fixSubgroup.2 ?_⟩, rfl⟩
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 ⟨_, hy⟩).1 y.2

omit hf hK hσ in
@[expose] def fixEquivImage (hσ3 : ∀ c, σ (σ (σ c)) = c) :
    ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(trialityFieldImage σ σ) :=
  MulEquiv.ofBijective (fixToImage σ hσ3) (fixToImage_bijective σ hσ3)

omit hf hK hσ in
@[expose] def rootToImage (σ : K ≃+* K) :
    ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ))) →*
      ↥(trialityFieldImage σ σ) where
  toFun g := ⟨baseChangeGL (fixSubfield σ).subtype (g.1 : ModGL TwistTag.D4.tag (fixSubfield σ)), by
    show _ ∈ (graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom).map _
    rw [fixSubfieldRestrict_toRingHom_eq_id]
    exact ⟨g.1, g.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

omit hf hK hσ in
theorem rootToImage_bijective (σ : K ≃+* K) : Function.Bijective (rootToImage σ) := by
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · exact Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))
  · have hy := y.2
    change _ ∈ (graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom).map _ at hy
    rw [fixSubfieldRestrict_toRingHom_eq_id] at hy
    obtain ⟨g, hg, hgy⟩ := hy
    exact ⟨⟨g, hg⟩, Subtype.ext hgy⟩

omit hf hK hσ in
@[expose] def imageEquivRoot (σ : K ≃+* K) :
    ↥(trialityFieldImage σ σ) ≃*
      ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ))) :=
  (MulEquiv.ofBijective (rootToImage σ) (rootToImage_bijective σ)).symm

omit hf hK hσ in
theorem baseChangeGL_imageEquivRoot (y : ↥(trialityFieldImage σ σ)) :
    baseChangeGL (fixSubfield σ).subtype
      ((imageEquivRoot σ y : ↥(graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
        (RingHom.id (fixSubfield σ)))) : ModGL TwistTag.D4.tag (fixSubfield σ)) =
      (y : ModGL TwistTag.D4.tag K) := by
  have h := (MulEquiv.ofBijective (rootToImage σ) (rootToImage_bijective σ)).apply_symm_apply y
  exact congrArg Subtype.val h

omit hf hK hσ in
@[expose] def rootEquivG2 (k : Type) [Field k] [Finite k] (hk3 : (3 : ℕ∞) ≤ ENat.card k) :
    ↥(graphFixedRootGroup TwistTag.D4 k (RingHom.id k)) ≃* ↥(adjointGroup Tag.G2 k) :=
  (MulEquiv.subgroupCongr (d4_twistedFixedGroup_id_eq_graphFixedRootGroup (K := k))).symm.trans
    (d4FixedG2EquivAll k hk3)

@[expose] def fixEquivG2 :
    ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) ≃* ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
  (fixEquivImage σ (ringEquiv_cube_apply_eq hK hσ)).trans
    ((imageEquivRoot σ).trans (rootEquivG2 (fixSubfield σ) (three_le_card_fixSubfield hf hK σ hσ)))

theorem longElt_mem_fix {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) {c : K} (hc : σ c = c) :
    longElt hf hK σ hσ hγ c hc ∈ fixSubgroup (fieldActor (t := TwistTag.D4) σ σ) := by
  rw [mem_fixSubgroup]
  apply Subtype.ext
  have hmap : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K γ c) =
      pinnedX TwistTag.D4.tag K γ c := by
    rw [show Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K γ c) =
        pinnedX TwistTag.D4.tag K γ (σ c) from
      Units.ext (entrywise_pinnedX σ.toRingHom γ c), hc]
  rw [coe_fieldActor]
  exact hmap

omit hf hK hσ in
theorem coe_rootEquivG2 (k : Type) [Field k] [Finite k] (hk3 : (3 : ℕ∞) ≤ ENat.card k)
    (g : ↥(graphFixedRootGroup TwistTag.D4 k (RingHom.id k))) :
    ((rootEquivG2 k hk3 g : ↥(adjointGroup Tag.G2 k)) : ModGL Tag.G2 k) =
      d4FixedToG2 k ⟨(g : ModGL TwistTag.D4.tag k),
        graphFixedRootGroup_le TwistTag.D4 k (RingHom.id k) g.2⟩ := by
  show ((d4FixedG2EquivAll k hk3 ((MulEquiv.subgroupCongr
    (d4_twistedFixedGroup_id_eq_graphFixedRootGroup (K := k))).symm g) : ↥(adjointGroup Tag.G2 k)) :
      ModGL Tag.G2 k) = _
  rw [coe_d4FixedG2EquivAll]
  rfl

theorem fixEquivG2_longElt_rootB (c₀ : fixSubfield σ) :
    ((fixEquivG2 hf hK σ hσ ⟨longElt hf hK σ hσ (Or.inl rfl) (c₀ : K) c₀.2,
        longElt_mem_fix hf hK σ hσ (Or.inl rfl) c₀.2⟩ : ↥(adjointGroup Tag.G2 (fixSubfield σ))) :
      ModGL Tag.G2 (fixSubfield σ)) = xUnit Tag.G2 (fixSubfield σ) ⟨0, by decide⟩ c₀ := by
  have hσ3 := ringEquiv_cube_apply_eq hK hσ
  set x : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) :=
    ⟨longElt hf hK σ hσ (Or.inl rfl) (c₀ : K) c₀.2,
      longElt_mem_fix hf hK σ hσ (Or.inl rfl) c₀.2⟩ with hx
  have hy₁ : ((fixEquivImage σ hσ3 x : ↥(trialityFieldImage σ σ)) : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K rootB (c₀ : K) := rfl
  set g := imageEquivRoot σ (fixEquivImage σ hσ3 x) with hg
  have hg' : (g : ModGL TwistTag.D4.tag (fixSubfield σ)) =
      pinnedX TwistTag.D4.tag (fixSubfield σ) rootB c₀ := by
    apply baseChangeGL_injective (fixSubfield σ).subtype
    rw [hg, baseChangeGL_imageEquivRoot, hy₁, baseChangeGL_pinnedX]
    rfl
  show ((rootEquivG2 (fixSubfield σ) (three_le_card_fixSubfield hf hK σ hσ) g :
    ↥(adjointGroup Tag.G2 (fixSubfield σ))) : ModGL Tag.G2 (fixSubfield σ)) = _
  rw [coe_rootEquivG2]
  have hword : TwistTag.D4.orbitWord (g2FoldedIndex (⟨0, by decide⟩ : Fin Tag.G2.rank)) =
      [⟨2, by decide⟩] := by decide
  have hB : rootB = Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) (1 : ℤ) := by decide
  have hgg : (⟨(g : ModGL TwistTag.D4.tag (fixSubfield σ)),
      graphFixedRootGroup_le TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ)) g.2⟩ :
      ↥(twistedFixedGroup TwistTag.D4 (fixSubfield σ) (RingHom.id (fixSubfield σ)))) =
      ⟨g2OrbitXUnit (fixSubfield σ) ⟨0, by decide⟩ c₀,
        g2OrbitXUnit_mem ⟨0, by decide⟩ c₀⟩ := by
    apply Subtype.ext
    show (g : ModGL TwistTag.D4.tag (fixSubfield σ)) = g2OrbitXUnit (fixSubfield σ) ⟨0, by decide⟩ c₀
    rw [hg', hB, pinnedX_single, g2OrbitXUnit, hword]
    simp
  rw [hgg, d4FixedToG2_g2OrbitXUnitAll]

theorem exists_conj_g2Top {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    ∃ (h : ↥(adjointGroup Tag.G2 (fixSubfield σ))) (c'' : fixSubfield σ), c'' ≠ 0 ∧
      fixEquivG2 hf hK σ hσ ⟨longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc,
        longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc⟩ =
        h * g2Top (fixSubfield σ) c'' * h⁻¹ := by
  classical
  obtain ⟨n, ε, hnfix, hε, hconj⟩ := exists_weyl_rootB_to_rootD hf hK σ hσ
  have hεε : ε * ε = 1 := by rcases hε with rfl | rfl <;> simp
  have hεc : σ (ε * c) = ε * c := by rcases hε with rfl | rfl <;> simp [hc]
  set c₀ : fixSubfield σ := ⟨ε * c, hεc⟩ with hc₀
  set nJ : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) := ⟨n, mem_fixSubgroup.2 hnfix⟩
    with hnJ
  set xB : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) :=
    ⟨longElt hf hK σ hσ (Or.inl rfl) (c₀ : K) c₀.2,
      longElt_mem_fix hf hK σ hσ (Or.inl rfl) c₀.2⟩ with hxB
  set zJ : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ σ)) :=
    ⟨longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc,
      longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc⟩ with hzJ
  have hz : zJ = nJ * xB * nJ⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    show pinnedX TwistTag.D4.tag K rootD c =
      (n : ModGL TwistTag.D4.tag K) * pinnedX TwistTag.D4.tag K rootB (ε * c) *
        (n : ModGL TwistTag.D4.tag K)⁻¹
    rw [hconj (ε * c), ← mul_assoc, hεε, one_mul]
  have hExB : fixEquivG2 hf hK σ hσ xB =
      ⟨pinnedX Tag.G2 (fixSubfield σ) g2a c₀, pinnedX_mem_adjointGroup g2a c₀⟩ := by
    apply Subtype.ext
    rw [fixEquivG2_longElt_rootB hf hK σ hσ c₀]
    show xUnit Tag.G2 (fixSubfield σ) ⟨0, by decide⟩ c₀ = pinnedX Tag.G2 (fixSubfield σ) g2a c₀
    rw [g2a_eq_single, pinnedX_single]
    rfl
  set w : WeylGroup Tag.G2 := simple Tag.G2 g2ia * simple Tag.G2 g2ir with hw
  have hwa : w • g2a = g2c := by
    simp only [hw, mul_smul, simple_smul]
    exact List.ofFn_injective (by decide +kernel)
  obtain ⟨ε', hε'ε', hconj'⟩ :=
    exists_canonicalRep_mul_pinnedX_mul_inv (τ := Tag.G2) (fixSubfield σ) w isRoot_g2a
  set nW : ↥(adjointGroup Tag.G2 (fixSubfield σ)) :=
    ⟨canonicalRep (coxeterSystem Tag.G2) (fixSubfield σ) w,
      canonicalRep_mem_adjointGroup (coxeterSystem Tag.G2) (fixSubfield σ) w⟩ with hnW
  have hXa : (⟨pinnedX Tag.G2 (fixSubfield σ) g2a c₀, pinnedX_mem_adjointGroup g2a c₀⟩ :
      ↥(adjointGroup Tag.G2 (fixSubfield σ))) = nW⁻¹ * g2Top (fixSubfield σ) (ε' * c₀) * nW := by
    apply Subtype.ext
    have h1 := hconj' c₀
    rw [hwa] at h1
    show pinnedX Tag.G2 (fixSubfield σ) g2a c₀ =
      (canonicalRep (coxeterSystem Tag.G2) (fixSubfield σ) w)⁻¹ *
        pinnedX Tag.G2 (fixSubfield σ) g2c (ε' * c₀) *
        canonicalRep (coxeterSystem Tag.G2) (fixSubfield σ) w
    rw [← h1]
    group
  have hε'0 : ε' ≠ 0 := fun h => by simp [h] at hε'ε'
  have hc₀0 : c₀ ≠ 0 := by
    intro h
    have h' : ε * c = 0 := congrArg Subtype.val h
    have hε0 : ε ≠ 0 := fun h0 => by simp [h0] at hεε
    exact hc0 ((mul_eq_zero.1 h').resolve_left hε0)
  refine ⟨fixEquivG2 hf hK σ hσ nJ * nW⁻¹, ε' * c₀, mul_ne_zero hε'0 hc₀0, ?_⟩
  show fixEquivG2 hf hK σ hσ zJ = _
  rw [hz, map_mul, map_mul, map_inv, hExB, hXa]
  group

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
