module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Outer
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwistedE6
public import CFSG.LieType.Chevalley.TwistedE6OddNormalForm
public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.Chevalley.FieldGraphFieldPointwise (exists_exactNormalAut_eq_of_fix_regular
  regularElt coe_regularElt regularElt_mem_posUnipotent rootCoord_regularElt
  regularElt_mem_graphFixedRootGroup eq_one_of_exactNormalAut_zero_fix exactNormalAut_one_zero_eq
  entrywiseAdjointAut_adjX)

theorem fixSubfieldRestrict_one_toRingHom {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    (fixSubfieldRestrict (1 : K ≃+* K) σ).toRingHom = RingHom.id (fixSubfield σ) :=
  RingHom.ext fun _ => Subtype.ext rfl


variable {K : Type} [Field K] [Finite K]

omit
  [Finite K] in
@[expose] def twE6F4Image (σ : K ≃+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  (twistedFixedGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _)).map
    (baseChangeGL (fixSubfield σ).subtype)

theorem twE6F4Image_le (σ : K ≃+* K) :
    twE6F4Image σ ≤ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ⊓
      entrywiseFixedGroup TwistTag.E6.tag σ := by
  have h := map_baseChangeGL_twistedFixedGroup_le TwistTag.E6 (1 : K ≃+* K) σ
  rw [fixSubfieldRestrict_one_toRingHom] at h
  exact h

theorem twE6F4Image_normal (σ : K ≃+* K) :
    ((twE6F4Image σ).subgroupOf (twistedFixedGroup TwistTag.E6 K (RingHom.id K) ⊓
      entrywiseFixedGroup TwistTag.E6.tag σ)).Normal := by
  have h := map_baseChangeGL_twistedFixedGroup_normal TwistTag.E6 (1 : K ≃+* K) σ
  rw [fixSubfieldRestrict_one_toRingHom] at h
  exact h

omit [Finite K] in
theorem twE6F4Image_le_graphFixedRootGroup (σ : K ≃+* K) :
    twE6F4Image σ ≤ graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
  map_baseChangeGL_le_graphFixedRootGroup (k := fixSubfield σ) (K := K) (σ := σ.toRingHom)
    fun c => c.2

omit [Finite K] in
theorem xUnit_mem_twE6F4Image (σ : K ≃+* K) {i : Fin TwistTag.E6.tag.rank}
    (hi : TwistTag.E6.perm i = i) {c : K} (hc : σ c = c) :
    xUnit TwistTag.E6.tag K i c ∈ twE6F4Image σ := by
  refine ⟨xUnit TwistTag.E6.tag (fixSubfield σ) i ⟨c, hc⟩,
    mem_twistedFixedGroup_id_iff.2 ⟨xUnit_mem_adjointGroup i _, ?_⟩, baseChangeGL_xUnit _ i _⟩
  rw [← mul_inv_eq_iff_eq_mul, diagramMap_mul_xUnit_mul_inv TwistTag.E6 _ i _, hi]

omit [Finite K] in
theorem regularElt_mem_twE6F4Image (σ : K ≃+* K) :
    (regularElt K : ModGL TwistTag.E6.tag K) ∈ twE6F4Image σ := by
  refine ⟨regularElt (fixSubfield σ), graphFixedRootGroup_le _ _ _
    (regularElt_mem_graphFixedRootGroup (RingHom.id _)), ?_⟩
  rw [coe_regularElt (K := fixSubfield σ), coe_regularElt (K := K), map_list_prod, List.map_map]
  refine congrArg List.prod (List.map_congr_left fun i _ => ?_)
  rw [Function.comp_apply, baseChangeGL_xUnit, map_one]

omit [Finite K] in
theorem canonicalRep_mem_twE6F4Image (σ : K ≃+* K) {w : WeylGroup TwistTag.E6.tag}
    (hw : w ∈ relWeylTwist TwistTag.E6) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K w ∈ twE6F4Image σ :=
  ⟨canonicalRep (coxeterSystem TwistTag.E6.tag) (fixSubfield σ) w, graphFixedRootGroup_le _ _ _
    (canonicalRep_mem_graphFixedRootGroup hw), baseChangeGL_canonicalRep _ w⟩

theorem isSimpleGroup_twE6F4Image (hK : ringChar K ≠ 2) (σ : K ≃+* K) :
    IsSimpleGroup (twE6F4Image σ) ∧ ∃ a b : twE6F4Image σ, a * b ≠ b * a := by
  have hk2 := ringChar_fixSubfield_ne_two hK σ
  obtain ⟨hsimp, hnab, -⟩ := odd_diagram_field_fixed_p_components TwistTag.E6 (fixSubfield σ) hk2 1
  have h1 : (1 : fixSubfield σ ≃+* fixSubfield σ).toRingHom = RingHom.id _ :=
    RingHom.ext fun _ => rfl
  have hs : graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (1 : fixSubfield σ ≃+* _).toRingHom =
      twistedFixedGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) := by
    rw [h1]
    exact (e6_twistedFixedGroup_id_eq_graphFixedRootGroup _).symm
  let e₁ : graphFixedRootGroup TwistTag.E6 (fixSubfield σ) (1 : fixSubfield σ ≃+* _).toRingHom ≃*
      twistedFixedGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) :=
    MulEquiv.subgroupCongr hs
  let e₂ : twistedFixedGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _) ≃* twE6F4Image σ :=
    (twistedFixedGroup TwistTag.E6 (fixSubfield σ) (RingHom.id _)).equivMapOfInjective _
      (baseChangeGL_injective _)
  let e := e₁.trans e₂
  have := hsimp
  refine ⟨MulEquiv.isSimpleGroup e.symm, ?_⟩
  obtain ⟨a, b, hab⟩ := hnab
  exact ⟨e a, e b, fun h => hab (e.injective (by rw [map_mul, map_mul, h]))⟩

theorem eq_one_of_odd_fix_twE6F4Image {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f))
    {β : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)} (hβ : Odd (orderOf β))
    (hfix : ∀ x : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (x : ModGL TwistTag.E6.tag K) ∈ twE6F4Image σ → β x = x) : β = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hσσ : σ * σ = 1 := by
    refine RingEquiv.ext fun c => ?_
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, show p ^ f * p ^ f = Fintype.card K by
      rw [← Nat.card_eq_fintype_card, hK, sq]]
    exact FiniteField.pow_card c
  obtain ⟨-, -, -, -, -, hΔ, hδ, hNF, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  obtain ⟨g, u, δ, hβeq⟩ := hNF β
  set d := rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) with hd
  have hβapp : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (β h : ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag K) *
          (d * Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag K) * d⁻¹) *
            (g : ModGL TwistTag.E6.tag K)⁻¹ := by
    intro h
    rw [hβeq, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hΔ, hδ]
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le _ _ _ g.2).1
  set β' := MulAut.conj (⟨g, hgC⟩ : adjointGroup TwistTag.E6.tag K) *
    rootDiagAut TwistTag.E6.tag K (compatDiag TwistTag.E6 σ.toRingHom u) *
      entrywiseAdjointAut TwistTag.E6.tag δ with hβ'def
  have hβ'app : ∀ x : adjointGroup TwistTag.E6.tag K, (β' x : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) *
        (d * Units.map (entrywiseHom δ.toRingHom) (x : ModGL TwistTag.E6.tag K) * d⁻¹) *
          (g : ModGL TwistTag.E6.tag K)⁻¹ := by
    intro x
    rw [hβ'def, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut, coe_entrywiseAdjointAut]
  have hC : ∀ y ∈ graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      y ∈ adjointGroup TwistTag.E6.tag K := fun y hy => (graphFixedRootGroup_le _ _ _ hy).1
  have hres : ∀ h : graphFixedRootGroup TwistTag.E6 K σ.toRingHom,
      (β h : ModGL TwistTag.E6.tag K) = β' ⟨h, hC _ h.2⟩ := by
    intro h
    rw [hβapp, hβ'app]
  have hJfix : ∀ x : adjointGroup TwistTag.E6.tag K,
      (x : ModGL TwistTag.E6.tag K) ∈ twE6F4Image σ → β' x = x := by
    intro x hx
    have hx0 := twE6F4Image_le_graphFixedRootGroup σ hx
    have h1 := congrArg Subtype.val (hfix ⟨x, hx0⟩ hx)
    rw [hres] at h1
    exact Subtype.ext h1
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem TwistTag.E6.tag).length
  obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.E6
  rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
  have hn₀ := canonicalRep_mem_twE6F4Image σ hw₁
  have hu := regularElt_mem_twE6F4Image (K := K) σ
  obtain ⟨a, φ, v, hβ'eq⟩ := exists_exactNormalAut_eq_of_fix_regular (τ := TwistTag.E6.tag)
    (Or.inl rfl) hw₀
    (n₀ := ⟨_, canonicalRep_mem_adjointGroup _ K w₀⟩) (u := regularElt K) (β := β') rfl
    regularElt_mem_posUnipotent (fun j => by rw [rootCoord_regularElt]; exact one_ne_zero)
    (hJfix _ hu) (hJfix _ (mul_mem (mul_mem hn₀ hu) (inv_mem hn₀)))
  have hv : (v : ℕ) = 0 ∨ (v : ℕ) = 1 := by
    have h := v.isLt
    change (v : ℕ) < 2 at h
    omega
  have hP : ∀ x : adjointGroup TwistTag.E6.tag K, (x : ModGL TwistTag.E6.tag K) ∈ twE6F4Image σ →
      exactNormalAut TwistTag.E6.tag K 1 1 1 x = x := by
    intro x hx
    have hxP := (mem_twistedFixedGroup_id_iff.1 (twE6F4Image_le σ hx).1).2
    refine Subtype.ext ?_
    rw [coe_exactNormalAut, rootDiagUnit_one]
    change 1 * diagramMap TwistTag.E6 K ^ 1 * Units.map (entrywiseHom (RingHom.id K)) _ *
      (diagramMap TwistTag.E6 K ^ 1)⁻¹ * 1⁻¹ = _
    rw [pow_one, one_mul, inv_one, mul_one, show Units.map (entrywiseHom (RingHom.id K))
      (x : ModGL TwistTag.E6.tag K) = x from Units.ext (entrywise_id _), hxP,
      mul_inv_cancel_right]
  have hmul : exactNormalAut TwistTag.E6.tag K a φ 0 * exactNormalAut TwistTag.E6.tag K 1 1 1 =
      exactNormalAut TwistTag.E6.tag K a φ 1 := by
    have h1 : (fun j => a j * Units.map φ.toRingHom.toMonoidHom
        ((1 : Fin TwistTag.E6.tag.rank → Kˣ) ((exactPerm TwistTag.E6.tag 0).symm j))) = a := by
      funext j
      simp
    rw [exactNormalAut_mul, h1, mul_one, zero_add]
  have hN0 : ∀ x : adjointGroup TwistTag.E6.tag K, (x : ModGL TwistTag.E6.tag K) ∈ twE6F4Image σ →
      exactNormalAut TwistTag.E6.tag K a φ 0 x = x := by
    intro x hx
    have h1 := hJfix x hx
    rw [hβ'eq] at h1
    rcases hv with hv | hv
    · rwa [hv] at h1
    · rw [hv, ← hmul, MulAut.mul_apply, hP x hx] at h1
      exact h1
  obtain rfl := eq_one_of_exactNormalAut_zero_fix (hN0 _ hu)
  have hφ : φ ∈ Subgroup.zpowers σ := by
    refine CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed fun c hc => ?_
    have h1 := hN0 (adjX TwistTag.E6.tag K ⟨1, by decide⟩ c)
      (xUnit_mem_twE6F4Image σ (by decide) hc)
    rw [exactNormalAut_one_zero_eq, entrywiseAdjointAut_adjX] at h1
    exact adjX_injective _ h1
  have hφφ : φ * φ = 1 := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hσσ, one_zpow]
  have hsq : β' * β' = 1 := by
    rw [hβ'eq, exactNormalAut_mul, ← exactNormalAut_mod, hφφ]
    have h0 : ((v : ℕ) + (v : ℕ)) % exactE TwistTag.E6.tag = 0 := by
      change ((v : ℕ) + (v : ℕ)) % 2 = 0
      omega
    have h1 : (fun j => (1 : Fin TwistTag.E6.tag.rank → Kˣ) j *
        Units.map φ.toRingHom.toMonoidHom
          ((1 : Fin TwistTag.E6.tag.rank → Kˣ) ((exactPerm TwistTag.E6.tag v).symm j))) = 1 := by
      funext j
      simp
    rw [h0, h1, exactNormalAut_one_zero_eq, entrywiseAdjointAut_one]
  have hβ2 : β * β = 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.one_apply, hres]
    have e : (⟨(β h : ModGL TwistTag.E6.tag K), hC _ (β h).2⟩ : adjointGroup TwistTag.E6.tag K) =
        β' ⟨h, hC _ h.2⟩ := Subtype.ext (hres h)
    rw [e, ← MulAut.mul_apply, hsq, MulAut.one_apply]
  exact eq_one_of_odd_of_mem_zpowers (α := β) (by rw [sq]; exact hβ2) hβ (mem_zpowers β)

theorem burgCoreFor_twistedE6_graph {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) :
    BurgCoreFor (fieldActor (t := TwistTag.E6) σ σ) := by
  classical
  have hK2 : ringChar K ≠ 2 := by
    have : CharP K p := LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
      (show 1 ≤ f * 2 by omega) (by rw [hK, ← pow_mul])
    rw [ringChar.eq K p]
    exact hp2
  obtain ⟨-, -, -, -, -, -, -, -, -, hσP, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form hp hp2 hf K hK σ hσ
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  set J := (twE6F4Image σ).subgroupOf C₀ with hJ
  have hMC₀ := twE6F4Image_le_graphFixedRootGroup σ
  have hF : ∀ g : C₀, g ∈ fixedSubgroup (fieldActor (t := TwistTag.E6) σ σ) ↔
      diagramMap TwistTag.E6 K * (g : ModGL TwistTag.E6.tag K) =
        (g : ModGL TwistTag.E6.tag K) * diagramMap TwistTag.E6 K := by
    intro g
    change fieldActor σ σ g = g ↔ _
    rw [← Subtype.coe_inj, hσP, mul_inv_eq_iff_eq_mul]
  have hJq : IsQuasisimple J := by
    obtain ⟨hsimp, hnab⟩ := isSimpleGroup_twE6F4Image hK2 σ
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMC₀).symm
      (LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  refine burgCoreFor_of_normal_quasisimple (exceptional_fixed_center_trivial TwistTag.E6 K σ)
    (J := J) (fun j hj => (hF j).2 (mem_twistedFixedGroup_id_iff.1 (twE6F4Image_le σ hj).1).2)
    (fun g hg j hj => ?_) hJq fun β hβ hfix => eq_one_of_odd_fix_twE6F4Image hp hp2 hf hK σ hσ hβ
      fun x hx => hfix x hx
  have hgP := (hF g).1 hg
  have hgC : (g : ModGL TwistTag.E6.tag K) ∈ adjointGroup TwistTag.E6.tag K :=
    (graphFixedRootGroup_le _ _ _ g.2).1
  have hgσ : Units.map (entrywiseHom σ.toRingHom) (g : ModGL TwistTag.E6.tag K) = g := by
    have h := (graphFixedRootGroup_le _ _ _ g.2).2
    change twistHom TwistTag.E6 K σ.toRingHom g = g at h
    rw [twistHom_apply] at h
    have hPg : diagramMap TwistTag.E6 K * (g : ModGL TwistTag.E6.tag K) *
        (diagramMap TwistTag.E6 K)⁻¹ = g := by rw [hgP, mul_inv_cancel_right]
    exact mul_left_cancel (mul_right_cancel (h.trans hPg.symm))
  have hgY : (g : ModGL TwistTag.E6.tag K) ∈ twistedFixedGroup TwistTag.E6 K (RingHom.id K) ⊓
      entrywiseFixedGroup TwistTag.E6.tag σ :=
    ⟨mem_twistedFixedGroup_id_iff.2 ⟨hgC, hgP⟩, mem_entrywiseFixedGroup.2 ⟨hgC, hgσ⟩⟩
  have hjM : ((j : C₀) : ModGL TwistTag.E6.tag K) ∈ twE6F4Image σ := hj
  have h := (twE6F4Image_normal σ).conj_mem ⟨_, twE6F4Image_le σ hjM⟩ hjM ⟨_, hgY⟩
  rw [mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  exact h

@[expose] def BurgoyneE2TwistedE6NonF4Input : Prop :=
  ∀ (p f : ℕ), p.Prime → p ≠ 2 → 1 ≤ f →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (p ^ f) ^ 2 →
      ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (p ^ f)) →
        ∀ α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), orderOf α = 2 →
          (∀ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
            ψ * α * ψ⁻¹ ≠ fieldActor (t := TwistTag.E6) σ σ) →
          BurgCoreFor α ∨ BurgTorusFor α

theorem burgoyneE2TwistedE6Input_of_nonF4 (h : BurgoyneE2TwistedE6NonF4Input) :
    BurgoyneE2TwistedE6Input := by
  intro p f hp hp2 hf K _ _ hK σ hσ α hα
  by_cases hc : ∃ ψ : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      ψ * α * ψ⁻¹ = fieldActor (t := TwistTag.E6) σ σ
  · obtain ⟨ψ, hψ⟩ := hc
    have hc := (burgCoreFor_twistedE6_graph hp hp2 hf hK σ hσ).conj ψ⁻¹
    rw [← hψ, show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at hc
    exact Or.inl hc
  · push Not at hc
    exact h p f hp hp2 hf K hK σ hσ α hα hc

end CFSG.ComponentClassification.Burgoyne.E2
