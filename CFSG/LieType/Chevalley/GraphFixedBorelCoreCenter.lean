module

public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem graphFixedRootTorus_inf_graphFixedPosUnipotent :
    graphFixedRootTorus t K σ ⊓ graphFixedPosUnipotent t K σ = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxH, hxU⟩ := Subgroup.mem_inf.1 hx
  have h := (triangular_borel_structure.{0, 0} t.tag K).2.2.2.1
  rw [← h]
  exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hxH).1).1,
    (Subgroup.mem_inf.1 hxU).1⟩

theorem graphFixedRootTorus_inf_graphFixedNegUnipotent :
    graphFixedRootTorus t K σ ⊓ graphFixedNegUnipotent t K σ = ⊥ :=
  eq_bot_iff.2 fun x hx => by
    rw [← graphFixedRootBorel_inf_graphFixedNegUnipotent (t := t) (K := K) (σ := σ)]
    exact Subgroup.mem_inf.2 ⟨graphFixedRootTorus_le_graphFixedRootBorel (Subgroup.mem_inf.1 hx).1,
      (Subgroup.mem_inf.1 hx).2⟩

theorem graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent :
    graphFixedRootTorus t K σ ≤
      Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) :=
  graphFixedRootTorus_le_graphFixedRootBorel.trans
    ((Subgroup.normal_subgroupOf_iff_le_normalizer graphFixedPosUnipotent_le_graphFixedRootBorel).1
      graphFixedPosUnipotent_subgroupOf_graphFixedRootBorel_normal)

theorem mem_graphFixedRootTorus_of_mem_normalCore
    {x : graphFixedRootGroup t K σ}
    (hx : x ∈ ((graphFixedRootBorel t K σ).subgroupOf (graphFixedRootGroup t K σ)).normalCore) :
    (x : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hw₀ := mem_relWeylTwist_of_forall_length_le hmax
  set n := canonicalRep (coxeterSystem t.tag) K w₀
  have hnC : n ∈ graphFixedRootGroup t K σ := canonicalRep_mem_graphFixedRootGroup hw₀
  have h1 : (x : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    have := hx 1
    rw [one_mul, inv_one, mul_one] at this
    exact this
  have h2 : (x : ModGL t.tag K) ∈ (graphFixedRootBorel t K σ).map
      (MulAut.conj n).toMonoidHom := by
    have := hx ⟨n⁻¹, inv_mem hnC⟩
    rw [Subgroup.mem_subgroupOf] at this
    refine ⟨n⁻¹ * x * n, ?_, ?_⟩
    · simpa using this
    · simp [MulAut.conj_apply, mul_assoc]
  rw [← graphFixedRootBorel_inf_map_conj hmax]
  exact Subgroup.mem_inf.2 ⟨h1, h2⟩

theorem commute_of_mem_graphFixed_normalCore
    {x : graphFixedRootGroup t K σ}
    (hx : x ∈ ((graphFixedRootBorel t K σ).subgroupOf (graphFixedRootGroup t K σ)).normalCore)
    {S : Subgroup (ModGL t.tag K)} (hS : graphFixedRootTorus t K σ ⊓ S = ⊥)
    (hSn : graphFixedRootTorus t K σ ≤ Subgroup.normalizer (S : Set (ModGL t.tag K)))
    {g : graphFixedRootGroup t K σ} (hg : (g : ModGL t.tag K) ∈ S) : g * x = x * g := by
  set Core := ((graphFixedRootBorel t K σ).subgroupOf (graphFixedRootGroup t K σ)).normalCore
  have hk : x * g * x⁻¹ * g⁻¹ ∈ Core := by
    have h' : g * x⁻¹ * g⁻¹ ∈ Core := (Subgroup.normalCore_normal _).conj_mem _ (inv_mem hx) g
    have := mul_mem hx h'
    simpa [mul_assoc] using this
  have hH := mem_graphFixedRootTorus_of_mem_normalCore hk
  have hxH := mem_graphFixedRootTorus_of_mem_normalCore hx
  have hconj : (x : ModGL t.tag K) * g * (x : ModGL t.tag K)⁻¹ ∈ S :=
    (Subgroup.mem_normalizer_iff.1 (hSn hxH) g).1 hg
  have hkS : ((x * g * x⁻¹ * g⁻¹ : graphFixedRootGroup t K σ) : ModGL t.tag K) ∈ S := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact mul_mem hconj (inv_mem hg)
  have hk1 := Subgroup.mem_inf.2 ⟨hH, hkS⟩
  rw [hS, Subgroup.mem_bot] at hk1
  have hk1' : x * g * x⁻¹ * g⁻¹ = 1 := Subtype.ext hk1
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hk1'
  exact hk1'.symm

theorem fixed_Borel_core_center
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    ((graphFixedRootBorel t K σ.toRingHom).subgroupOf
        (graphFixedRootGroup t K σ.toRingHom)).normalCore =
      Subgroup.center (graphFixedRootGroup t K σ.toRingHom) ∧
    (MulAction.toPermHom (graphFixedRootGroup t K σ.toRingHom)
        (graphFixedRootGroup t K σ.toRingHom ⧸ (graphFixedRootBorel t K σ.toRingHom).subgroupOf
          (graphFixedRootGroup t K σ.toRingHom))).ker =
      Subgroup.center (graphFixedRootGroup t K σ.toRingHom) := by
  set C := graphFixedRootGroup t K σ.toRingHom
  set B := graphFixedRootBorel t K σ.toRingHom
  have hcore : (B.subgroupOf C).normalCore = Subgroup.center C := by
    refine le_antisymm (fun x hx => ?_) ?_
    · refine Subgroup.mem_center_iff.2 fun g => ?_
      let Z : Subgroup (ModGL t.tag K) := Subgroup.centralizer {(x : ModGL t.tag K)}
      have hcomm : ∀ S : Subgroup (ModGL t.tag K), S ≤ C →
          graphFixedRootTorus t K σ.toRingHom ⊓ S = ⊥ →
          graphFixedRootTorus t K σ.toRingHom ≤ Subgroup.normalizer (S : Set (ModGL t.tag K)) →
            S ≤ Z := by
        intro S hSC hS hSn u hu y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact (congrArg Subtype.val
          (commute_of_mem_graphFixed_normalCore hx hS hSn (g := ⟨u, hSC hu⟩) hu)).symm
      have hle : C ≤ Z := sup_le
        (hcomm _ (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
          graphFixedRootTorus_inf_graphFixedPosUnipotent
          graphFixedRootTorus_le_normalizer_graphFixedPosUnipotent)
        (hcomm _ (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ.toRingHom)
          graphFixedRootTorus_inf_graphFixedNegUnipotent
          graphFixedRootTorus_le_normalizer_graphFixedNegUnipotent)
      have hg := hle g.2 (x : ModGL t.tag K) rfl
      exact Subtype.ext hg.symm
    · refine Subgroup.normal_le_normalCore.2 fun z hz => ?_
      rw [Subgroup.mem_subgroupOf]
      have hBC : B ≤ C := graphFixedRootBorel_le t K σ.toRingHom
      have hzN : (z : ModGL t.tag K) ∈
          C ⊓ Subgroup.normalizer (B : Set (ModGL t.tag K)) := by
        refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_normalizer_iff.2 fun b => ?_⟩
        constructor
        · intro hb
          have hc := Subgroup.mem_center_iff.1 hz ⟨b, hBC hb⟩
          have hc' : (z : ModGL t.tag K) * b = b * z := (congrArg Subtype.val hc).symm
          rw [hc', mul_inv_cancel_right]
          exact hb
        · intro hb
          have hb' : b ∈ C := by
            have h2 := mul_mem (mul_mem (inv_mem z.2) (hBC hb)) z.2
            simpa [mul_assoc] using h2
          have hc := Subgroup.mem_center_iff.1 hz ⟨b, hb'⟩
          have hc' : (z : ModGL t.tag K) * b = b * z := (congrArg Subtype.val hc).symm
          rw [hc', mul_inv_cancel_right] at hb
          exact hb
      rw [graphFixedRootGroup_inf_normalizer_graphFixedRootBorel σ.surjective] at hzN
      exact hzN
  exact ⟨hcore, by rw [← Subgroup.normalCore_eq_ker, hcore]⟩

end CFSG.LieType.Chevalley
