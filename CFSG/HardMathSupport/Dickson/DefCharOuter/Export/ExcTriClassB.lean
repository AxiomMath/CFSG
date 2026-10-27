module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Shapes
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2NoComp
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.TransportTop

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.HardMathSupport.Dickson.Sec6.I923
  CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux

theorem exc_mulAut_mul_conj {G : Type*} [Group G] (β : MulAut G) (x : G) :
    β * MulAut.conj x = MulAut.conj (β x) * β :=
  MulEquiv.ext fun y => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]

theorem exc_conj_injective {G : Type*} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := congrArg (fun φ : MulAut G => φ y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hZ] at this
  exact this


theorem exc_baseChange_mem_posUnipotent {τ : Tag} {k L : Type} [Field k] [Field L] (ι : k →+* L)
    {x : ModGL τ k} (hx : x ∈ posUnipotent τ k) : baseChangeGL ι x ∈ posUnipotent τ L := by
  have h : (posUnipotent τ k).map (baseChangeGL ι) ≤ posUnipotent τ L := by
    rw [Subgroup.map_le_iff_le_comap, posUnipotent, rootSpan_eq_closure, Subgroup.closure_le]
    rintro _ ⟨α, hα, d, rfl⟩
    show baseChangeGL ι (pinnedX τ k α d) ∈ posUnipotent τ L
    rw [baseChangeGL_pinnedX]
    exact pinnedX_mem_rootSpan (K := L) (S := {α | IsRoot τ α ∧ 0 < height α}) hα (ι d)
  exact h (Subgroup.mem_map_of_mem _ hx)

section ClassB

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

theorem exc_cent_classB {c : K} (hc : σ c = c) (hc0 : c ≠ 0)
    (w : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hw : Nat.Coprime 3 (orderOf w))
    (hwβ : w * (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
      fieldActor (t := TwistTag.D4) σ σ) =
      (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
      fieldActor (t := TwistTag.D4) σ σ) * w)
    (hfix : ∀ x ∈ fixSubgroup (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
      fieldActor (t := TwistTag.D4) σ σ), w x = x) :
    w ∈ innerAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hσ3 : ∀ c, σ (σ (σ c)) = c := ringEquiv_cube_apply_eq hK hσ
  obtain ⟨-, hex, ⟨Θ, hΘ, -, hker, -⟩, -, -, -, -, -⟩ :=
    odd_triality_exact_automorphism_normal_form Nat.prime_three (by norm_num) hf K hK σ hσ
  set z := longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc with hzdef
  set δ₀ := fieldActor (t := TwistTag.D4) σ σ with hδ₀
  have hzJ : z ∈ fixSubgroup δ₀ := R2Aux.longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc
  have hzC : z ∈ fixSubgroup (MulAut.conj z * δ₀) := by
    rw [fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
    exact Subgroup.mem_inf.2 ⟨hzJ, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hwz : w z = z := hfix z hzC
  have hwδ : w * δ₀ = δ₀ * w := by
    have h1 : w * MulAut.conj z = MulAut.conj z * w := by
      rw [exc_mulAut_mul_conj, hwz]
    have h2 : MulAut.conj z * (w * δ₀) = MulAut.conj z * (δ₀ * w) := by
      calc MulAut.conj z * (w * δ₀) = (MulAut.conj z * w) * δ₀ := by rw [mul_assoc]
        _ = (w * MulAut.conj z) * δ₀ := by rw [h1]
        _ = w * (MulAut.conj z * δ₀) := by rw [mul_assoc]
        _ = (MulAut.conj z * δ₀) * w := hwβ
        _ = MulAut.conj z * (δ₀ * w) := by rw [mul_assoc]
    exact mul_left_cancel h2
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  have hinj := exc_conj_injective hZ
  have hcommδ : ∀ φ : K ≃+* K, fieldActor (t := TwistTag.D4) σ φ * δ₀ =
      δ₀ * fieldActor σ φ := fun φ => by
    rw [hδ₀, ← fieldActor_mul (t := TwistTag.D4), ← fieldActor_mul (t := TwistTag.D4),
      (commute_ringEquiv_of_finite φ σ).eq]
  obtain ⟨⟨g, φ⟩, hgφ, -⟩ := hex w
  have hw' : w = MulAut.conj g * fieldActor (t := TwistTag.D4) σ φ := hgφ
  have hgJ : (g : ModGL TwistTag.D4.tag K) ∈ trialityFieldImage σ σ := by
    have hβδ : δ₀ * w = w * δ₀ := hwδ.symm
    rw [hw'] at hβδ
    have e1 : MulAut.conj (δ₀ g) * (δ₀ * fieldActor (t := TwistTag.D4) σ φ) =
        MulAut.conj g * (δ₀ * fieldActor (t := TwistTag.D4) σ φ) := by
      calc MulAut.conj (δ₀ g) * (δ₀ * fieldActor (t := TwistTag.D4) σ φ) =
          δ₀ * (MulAut.conj g * fieldActor (t := TwistTag.D4) σ φ) := by
            rw [← mul_assoc, ← exc_mulAut_mul_conj, mul_assoc]
        _ = MulAut.conj g * fieldActor (t := TwistTag.D4) σ φ * δ₀ := hβδ
        _ = MulAut.conj g * (δ₀ * fieldActor (t := TwistTag.D4) σ φ) := by
          rw [mul_assoc, hcommδ]
    exact (d4_mem_trialityFieldImage_self_iff σ hσ3 g).2 (hinj (mul_right_cancel e1))
  have hJC := d4_trialityFieldImage_self_le σ
  have hιinj : Function.Injective
      (baseChangeGL (τ := TwistTag.D4.tag) (fixSubfield σ).subtype) := baseChangeGL_injective _
  obtain ⟨g', hg', hgg'⟩ := hgJ
  have hσ₀1 : fixSubfieldRestrict σ σ = 1 := RingEquiv.ext fun x => Subtype.ext (by
    rw [coe_fixSubfieldRestrict]
    exact x.2)
  have hσ₀3 : fixSubfieldRestrict σ σ ^ TwistTag.D4.order = 1 := by
    show fixSubfieldRestrict σ σ ^ 3 = 1
    rw [hσ₀1, one_pow]
  have hfixQ : ∀ j' : graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
      (fixSubfieldRestrict σ σ).toRingHom,
      (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) ∈ graphFixedParabolicRadical TwistTag.D4
        (fixSubfield σ) (fixSubfieldRestrict σ σ).toRingHom ∅ →
      (g' : ModGL TwistTag.D4.tag (fixSubfield σ)) *
        Units.map (entrywiseHom (fixSubfieldRestrict φ σ).toRingHom)
          (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) *
        (g' : ModGL TwistTag.D4.tag (fixSubfield σ))⁻¹ =
      (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) := by
    intro j' hj'
    have hj'J : baseChangeGL (fixSubfield σ).subtype
        (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) ∈ trialityFieldImage σ σ :=
      ⟨j', j'.2, rfl⟩
    have hjU : (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) ∈ posUnipotent TwistTag.D4.tag
        (fixSubfield σ) :=
      (Subgroup.mem_inf.1 (graphFixedParabolicRadical_le TwistTag.D4 (fixSubfield σ)
        (fixSubfieldRestrict σ σ).toRingHom ∅ hj')).1
    have hjUK := exc_baseChange_mem_posUnipotent (fixSubfield σ).subtype hjU
    have hcomm : baseChangeGL (fixSubfield σ).subtype
        (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) * pinnedX TwistTag.D4.tag K rootD c =
        pinnedX TwistTag.D4.tag K rootD c * baseChangeGL (fixSubfield σ).subtype
          (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) :=
      (commute_pinnedX_rootD_of_mem_posUnipotent hf hK σ hσ hjUK c).eq
    have hy : (⟨_, hJC hj'J⟩ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ∈
        fixSubgroup (MulAut.conj z * δ₀) := by
      rw [fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
      exact Subgroup.mem_inf.2 ⟨mem_fixSubgroup.2 (Subtype.ext
          (by rw [coe_fieldActor]; exact (d4_mem_trialityFieldImage_self_iff σ hσ3 _).1 hj'J
            |> fun h => congrArg Subtype.val h)),
        Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext hcomm)⟩
    have h1 := congrArg Subtype.val (hfix _ hy)
    rw [hw'] at h1
    change (g : ModGL TwistTag.D4.tag K) * Units.map (entrywiseHom φ.toRingHom)
      (baseChangeGL (fixSubfield σ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield σ))) *
        (g : ModGL TwistTag.D4.tag K)⁻¹ =
      baseChangeGL (fixSubfield σ).subtype (j' : ModGL TwistTag.D4.tag (fixSubfield σ)) at h1
    rw [← hgg', entrywise_baseChangeGL_fixSubfieldRestrict, ← map_inv, ← map_mul,
      ← map_mul] at h1
    exact hιinj h1
  have hne : (∅ : Set (Fin TwistTag.D4.foldedTag.rank)) ≠ Set.univ := by
    haveI : Nonempty (Fin TwistTag.D4.foldedTag.rank) := ⟨⟨0, by decide⟩⟩
    exact Set.empty_ne_univ
  have hrig := (diagram_fixed_parabolic_radical_diagonal_field_pointwise_rigidity
    TwistTag.D4 (fixSubfield σ) (fixSubfieldRestrict σ σ) hσ₀3 hne).2.1 (g' : ModGL TwistTag.D4.tag (fixSubfield σ)) hg'
    (1 : Fin TwistTag.D4.tag.rank → (fixSubfield σ)ˣ)
    (fun i => by simp) (fixSubfieldRestrict φ σ)
    (by rw [hσ₀1, mul_one, one_mul])
    (MulAut.conj (⟨g', hg'⟩ : graphFixedRootGroup TwistTag.D4 (fixSubfield σ)
        (fixSubfieldRestrict σ σ).toRingHom) *
      fieldActor (t := TwistTag.D4) (fixSubfieldRestrict σ σ) (fixSubfieldRestrict φ σ))
    (fun x => by
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_fieldActor, rootDiagUnit_one, mul_one, one_mul, inv_one])
    (fun x hx => Subtype.ext (by
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
        coe_fieldActor]
      exact hfixQ x hx))
  have hψ1 := hrig.1
  have hφσ : ∀ x, σ x = x → φ x = x := fun x hx => by
    have h2 := congrArg (fun ψ : fixSubfield σ ≃+* fixSubfield σ => (ψ ⟨x, hx⟩ : K)) hψ1
    exact h2
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
    (CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed hφσ)
  have hσ3' : σ ^ 3 = 1 := RingEquiv.ext fun c => by simpa [pow_succ, RingAut.mul_apply] using hσ3 c
  have hΘw : Θ w = φ := hΘ w g φ hgφ
  have hΘ3 : Θ w ^ 3 = 1 := by
    rw [hΘw, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ3', one_zpow]
  have hdvd1 : orderOf (Θ w) ∣ orderOf w := orderOf_map_dvd Θ w
  have hdvd2 : orderOf (Θ w) ∣ 3 := orderOf_dvd_of_pow_eq_one hΘ3
  have hone : orderOf (Θ w) = 1 :=
    Nat.eq_one_of_dvd_coprimes hw.symm hdvd1 hdvd2
  have hΘ1 : Θ w = 1 := orderOf_eq_one_iff.1 hone
  have hmem : w ∈ Θ.ker := hΘ1
  rw [hker] at hmem
  exact hmem

theorem exc_noComponent_classB {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    ∀ A : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      ¬ GLAPComponent 3 (fixSubgroup (MulAut.conj
        (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
          fieldActor (t := TwistTag.D4) σ σ)) A := by
  classical
  haveI := finite_graphFixedRootGroup_D4 σ
  haveI : Finite (adjointGroup Tag.G2 (fixSubfield σ)) := generated_group_finite Tag.G2 _
  rw [fixSubgroup_conj_mul_fieldActor_eq hf hK σ hσ hc hc0]
  have hzJ := R2Aux.longElt_mem_fix hf hK σ hσ (Or.inr (Or.inr rfl)) hc
  refine R2Aux.noGLAP3_of_equiv
    (R2Aux.infCentralizerEquiv (fixSubgroup (fieldActor (t := TwistTag.D4) σ σ))
      (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) hzJ (R2Aux.fixEquivG2 hf hK σ hσ)) ?_
  obtain ⟨h, c'', hc'', hE⟩ := R2Aux.exists_conj_g2Top hf hK σ hσ hc hc0
  rw [hE]
  refine R2Aux.noGLAP3_centralizer_conj h _ ?_
  have hcard : Nat.card (fixSubfield σ) = 3 ^ f :=
    CFSG.RankThree.PartOne.KGD.card_fixSubfield_cube Nat.prime_three hf hK σ hσ
  haveI : CharP (fixSubfield σ) 3 := inferInstance
  exact R2Aux.noGLAP3_centralizer_g2Top (K := fixSubfield σ)
    (by rw [hcard]; exact Nat.le_self_pow (by omega) 3) hc''

theorem outerCentData_three_classB {c : K} (hc : σ c = c) (hc0 : c ≠ 0) :
    OuterCentData 3 (MulAut.conj (longElt hf hK σ hσ (Or.inr (Or.inr rfl)) c hc) *
      fieldActor (t := TwistTag.D4) σ σ) :=
  OuterCentData.ofNoComponent (exc_noComponent_classB hf hK σ hσ hc hc0)
    (fun _ => glaPPrimeCoreOf_fixSubgroup_conj_mul_fieldActor hf hK σ hσ hc hc0)
    (fun _ w hw hwβ hfix => exc_cent_classB hf hK σ hσ hc hc0 w hw hwβ hfix)

end ClassB

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
