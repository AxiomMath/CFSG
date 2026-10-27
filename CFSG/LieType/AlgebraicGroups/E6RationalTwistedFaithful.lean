module

public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.LieType.Chevalley.LangFiniteRootCentralizer

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem mem_normalizer_of_conj_eq {G : Type*} [Group G] {C U : Subgroup G} (hUC : U ≤ C)
    {h s : G} (hh : h ∈ C) (hs : s ∈ Subgroup.normalizer (U : Set G))
    (hconj : ∀ y ∈ C, h * y * h⁻¹ = s * y * s⁻¹) : h ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hs ⊢
  intro n
  constructor
  · intro hn
    rw [hconj n (hUC hn)]
    exact (hs n).1 hn
  · intro hn
    have hnC : n ∈ C := by
      have h' : h⁻¹ * (h * n * h⁻¹) * h ∈ C := mul_mem (mul_mem (inv_mem hh) (hUC hn)) hh
      rwa [show h⁻¹ * (h * n * h⁻¹) * h = n by group] at h'
    rw [hconj n hnC] at hn
    exact (hs n).2 hn

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem graphFixedTorus_le_normalizer_graphFixedPosUnipotent :
    graphFixedTorus t K σ ≤
      Subgroup.normalizer (graphFixedPosUnipotent t K σ : Set (ModGL t.tag K)) := by
  intro h hh
  obtain ⟨hhH, hhΓ⟩ := Subgroup.mem_inf.1 hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hN := Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_posUnipotent hhH) g
  constructor
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hN.1 hgU, mul_mem (mul_mem hhΓ hgΓ) (inv_mem hhΓ)⟩
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hN.2 hgU, ?_⟩
    have e : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hhΓ) hgΓ) hhΓ

theorem graphFixedTorus_le_normalizer_graphFixedNegUnipotent :
    graphFixedTorus t K σ ≤
      Subgroup.normalizer (graphFixedNegUnipotent t K σ : Set (ModGL t.tag K)) := by
  intro h hh
  obtain ⟨hhH, hhΓ⟩ := Subgroup.mem_inf.1 hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hN := Subgroup.mem_normalizer_iff.1 (torusGroup_le_normalizer_negUnipotent hhH) g
  constructor
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    exact Subgroup.mem_inf.2 ⟨hN.1 hgU, mul_mem (mul_mem hhΓ hgΓ) (inv_mem hhΓ)⟩
  · intro hg
    obtain ⟨hgU, hgΓ⟩ := Subgroup.mem_inf.1 hg
    refine Subgroup.mem_inf.2 ⟨hN.2 hgU, ?_⟩
    have e : g = h⁻¹ * (h * g * h⁻¹) * h := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem hhΓ) hgΓ) hhΓ

theorem eq_one_of_mem_torusGroup_of_commute_orbitX
    {z : ModGL t.tag K}
    (hzT : z ∈ torusGroup t.tag K)
    (hz : ∀ a, z * (orbitX t K σ a 1 : ModGL t.tag K) = (orbitX t K σ a 1 : ModGL t.tag K) * z) :
    z = 1 := by
  obtain ⟨l, hl⟩ := exists_torus_characters hzT
  have hsingle : ∀ i : Fin t.tag.rank, (∏ j, l j ^ (Pi.single i 1 : Fin t.tag.rank → ℤ) j : Kˣ) =
      l i := fun i => by
    rw [Finset.prod_eq_single i (fun j _ hji => by rw [Pi.single_eq_of_ne hji, zpow_zero])
      (by simp), Pi.single_eq_same, zpow_one]
  have hl1 : ∀ i, l i = 1 := by
    intro i
    set a := t.orbitIndex i
    have hc' : z * (orbitX t K σ a 1 : ModGL t.tag K) * z⁻¹ = orbitX t K σ a 1 := by
      rw [hz a, mul_inv_cancel_right]
    rw [← orbitXProd_one_eq_orbitX σ] at hc'
    have hconj : z * orbitXProd t a (fun _ => (1 : K)) * z⁻¹ =
        orbitXProd t a fun j => ((l j : Kˣ) : K) := by
      unfold orbitXProd
      rw [← MulAut.conj_apply, map_list_prod, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
      rw [Function.comp_apply, MulAut.conj_apply, ← pinnedX_single,
        (hl _ (isRoot_single _ j)).2, pinnedX_single, hsingle, mul_one]
    rw [hconj] at hc'
    exact Units.ext (eq_of_orbitXProd_eq t hc' i (t.mem_orbit_orbitIndex i))
  have hchar : ∀ α : Fin t.tag.rank → ℤ, (∏ j, l j ^ α j : Kˣ) = 1 := fun α => by
    simp [hl1]
  refine Units.ext (end_ext_of_hVec_rootVec (fun j => ?_) fun α hα => ?_)
  · rw [Units.val_one, Module.End.one_apply]
    exact ((triangular_borel_structure.{0, 0} t.tag K).2.1 _ hzT).1 j
  · rw [Units.val_one, Module.End.one_apply, (hl α hα).1, hchar, Units.val_one, one_smul]

theorem eq_one_of_mem_twistedFixedGroup_of_commute
    (hσ : Function.Surjective σ)
    {z : ModGL t.tag K} (hzΓ : z ∈ twistedFixedGroup t K σ)
    (hz : ∀ y ∈ graphFixedRootGroup t K σ, z * y = y * z) : z = 1 := by
  have hz' : z ∈ (twistedFixedGroup t K σ : Set (ModGL t.tag K)) := hzΓ
  rw [coe_twistedFixedGroup_eq_mul hσ] at hz'
  obtain ⟨s, hs, h, hh, rfl⟩ := hz'
  have hconj : ∀ y ∈ graphFixedRootGroup t K σ, h * y * h⁻¹ = s⁻¹ * y * s⁻¹⁻¹ := fun y hy => by
    have e := hz y hy
    calc h * y * h⁻¹ = s⁻¹ * (s * h * y) * h⁻¹ := by group
      _ = s⁻¹ * (y * (s * h)) * h⁻¹ := by rw [e]
      _ = s⁻¹ * y * s⁻¹⁻¹ := by group
  have hU : h ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨hh, mem_normalizer_of_conj_eq
      (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ) hh
      (graphFixedTorus_le_normalizer_graphFixedPosUnipotent (inv_mem hs)) hconj⟩
  have hV : h ∈ graphFixedOppositeBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedNegUnipotent hσ]
    exact Subgroup.mem_inf.2 ⟨hh, mem_normalizer_of_conj_eq
      (graphFixedNegUnipotent_le_graphFixedRootGroup t K σ) hh
      (graphFixedTorus_le_normalizer_graphFixedNegUnipotent (inv_mem hs)) hconj⟩
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hH : h ∈ graphFixedRootTorus t K σ := by
    rw [← graphFixedRootBorel_inf_map_conj hmax, map_conj_graphFixedRootBorel hmax hσ]
    exact Subgroup.mem_inf.2 ⟨hU, hV⟩
  have hzT : s * h ∈ torusGroup t.tag K :=
    mul_mem (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hH).1).1
  exact eq_one_of_mem_torusGroup_of_commute_orbitX (σ := σ) hzT fun a =>
    hz _ (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
      (orbitX_mem_graphFixedPosUnipotent t σ a 1))

theorem twisted_fixed_group_faithful_action
    (t : TwistTag) {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ t.order) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    (graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) ≤ twistedFixedGroup t L Fr ∧
    twistedFixedGroup t L Fr ≤ adjointGroup t.tag L ⊓ Subgroup.normalizer
      ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :
        Set (ModGL t.tag L)) ∧
    twistedFixedGroup t L Fr ⊓ Subgroup.centralizer
      ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)) :
        Set (ModGL t.tag L)) = ⊥ ∧
    Function.Injective (conjNormalizerHom (twistedFixedGroup t L Fr)
      ((graphFixedRootGroup t K σ).map (baseChangeGL (algebraMap K L)))) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hq : 0 < p ^ f := pow_pos hp.pos f
  have hFrsurj : Function.Surjective Fr := fun y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y hq
    exact ⟨z, by rw [hFr, hz]⟩
  have hH := map_baseChangeGL_graphFixedRootGroup_eq t hp hf K hK σ hσ (algebraMap K L) hFr
    hFrsurj
  rw [hH]
  have hC : ∀ z ∈ twistedFixedGroup t L Fr,
      (∀ y ∈ graphFixedRootGroup t L Fr, z * y = y * z) → z = 1 := fun z hz hc =>
    eq_one_of_mem_twistedFixedGroup_of_commute hFrsurj hz hc
  refine ⟨graphFixedRootGroup_le t L Fr, le_inf (twistedFixedGroup_le_adjointGroup t L Fr)
    (twistedFixedGroup_le_normalizer hFrsurj), ?_, ?_⟩
  · refine eq_bot_iff.2 fun z hz => ?_
    obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.1 hz
    exact (Subgroup.mem_bot).2 (hC z hzR fun y hy => (Subgroup.mem_centralizer_iff.1 hzC y hy).symm)
  · refine (injective_iff_map_eq_one _).2 fun g hg => ?_
    refine Subtype.ext (hC g (Subgroup.mem_inf.1 g.2).1 fun y hy => ?_)
    have e := congrArg Subtype.val (MulEquiv.ext_iff.1 hg ⟨y, hy⟩)
    change (g : ModGL t.tag L) * y * (g : ModGL t.tag L)⁻¹ = y at e
    calc (g : ModGL t.tag L) * y = (g : ModGL t.tag L) * y * (g : ModGL t.tag L)⁻¹ * g := by group
      _ = y * g := by rw [e]

theorem E6_rational_twisted_fixed_group_faithful_action
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (p ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (p ^ f)) :
    (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) ≤
      twistedFixedGroup TwistTag.E6 L Fr ∧
    twistedFixedGroup TwistTag.E6 L Fr ≤ adjointGroup TwistTag.E6.tag L ⊓ Subgroup.normalizer
      ((graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) :
        Set (ModGL TwistTag.E6.tag L)) ∧
    twistedFixedGroup TwistTag.E6 L Fr ⊓ Subgroup.centralizer
      ((graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)) :
        Set (ModGL TwistTag.E6.tag L)) = ⊥ ∧
    Function.Injective (conjNormalizerHom (twistedFixedGroup TwistTag.E6 L Fr)
      ((graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K L)))) :=
  twisted_fixed_group_faithful_action TwistTag.E6 hp hf K hK σ hσ L Fr hFr

end CFSG.LieType.AlgebraicGroups
