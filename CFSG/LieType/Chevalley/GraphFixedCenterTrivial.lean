module

public import CFSG.LieType.Chevalley.GraphFixedBorelSelfNormalizer
public import CFSG.LieType.Chevalley.TorusCoordinates

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem end_ext_of_hVec_rootVec {f g : Module.End K (RootModule τ K)}
    (hh : ∀ j, f (hVec τ K j) = g (hVec τ K j))
    (hr : ∀ α, IsRoot τ α → f (rootVec τ K α) = g (rootVec τ K α)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · rw [← rootVec_eq_single_of_isRoot hα]
    exact hr α hα

theorem exists_torus_characters
    {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    ∃ l : Fin τ.rank → Kˣ, ∀ α, IsRoot τ α →
      (h : Module.End K (RootModule τ K)) (rootVec τ K α) =
          ((∏ j, l j ^ α j : Kˣ) : K) • rootVec τ K α ∧
        ∀ c, h * pinnedX τ K α c * h⁻¹ = pinnedX τ K α (((∏ j, l j ^ α j : Kˣ) : K) * c) := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨⟨i, s⟩, rfl⟩ := hx
    refine ⟨fun j => s ^ τ.cartan i j, fun α hα => ?_⟩
    have e : (∏ j, (s ^ τ.cartan i j) ^ α j : Kˣ) = s ^ (∑ j, τ.cartan i j * α j) := by
      simp_rw [← zpow_mul]
      exact prod_zpow_eq_zpow_sum _ _ s
    rw [e]
    exact ⟨torusElt_rootVec i s hα, fun c => root_torus_conjugation i hα s c⟩
  | one => exact ⟨1, fun α hα => ⟨by simp, fun c => by simp⟩⟩
  | mul x y _ _ hx hy =>
    obtain ⟨l, hl⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨l * m, fun α hα => ⟨?_, fun c => ?_⟩⟩
    · have e : (∏ j, (l * m) j ^ α j : Kˣ) = (∏ j, l j ^ α j) * ∏ j, m j ^ α j := by
        simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
      rw [Units.val_mul, Module.End.mul_apply, (hm α hα).1, map_smul, (hl α hα).1, smul_smul, e,
        Units.val_mul, mul_comm]
    · have e : (∏ j, (l * m) j ^ α j : Kˣ) = (∏ j, l j ^ α j) * ∏ j, m j ^ α j := by
        simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
      calc x * y * pinnedX τ K α c * (x * y)⁻¹ = x * (y * pinnedX τ K α c * y⁻¹) * x⁻¹ := by
            group
        _ = _ := by rw [(hm α hα).2, (hl α hα).2, e, Units.val_mul, mul_assoc]
  | inv x _ hx =>
    obtain ⟨l, hl⟩ := hx
    refine ⟨l⁻¹, fun α hα => ⟨?_, fun c => ?_⟩⟩
    · have e : (∏ j, l⁻¹ j ^ α j : Kˣ) = (∏ j, l j ^ α j)⁻¹ := by
        simp only [Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]
      have h1 := (hl α hα).1
      have h2 : ((x⁻¹ : ModGL τ K) : Module.End K (RootModule τ K))
          ((x : Module.End K (RootModule τ K)) (rootVec τ K α)) = rootVec τ K α := by
        rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Module.End.one_apply]
      rw [h1, map_smul] at h2
      rw [e, Units.val_inv_eq_inv_val]
      calc ((x⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α) =
          ((∏ j, l j ^ α j : Kˣ) : K)⁻¹ • (((∏ j, l j ^ α j : Kˣ) : K) •
            ((x⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (rootVec τ K α)) := by
            rw [smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul]
        _ = _ := by rw [h2]
    · have e : (∏ j, l⁻¹ j ^ α j : Kˣ) = (∏ j, l j ^ α j)⁻¹ := by
        simp only [Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]
      have h1 := (hl α hα).2 ((((∏ j, l j ^ α j : Kˣ)⁻¹ : Kˣ) : K) * c)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
      rw [e, ← h1, inv_inv]
      group

end Torus

variable {t : TwistTag} {K : Type} [Field K] {σ : K →+* K}

theorem mem_graphFixedRootTorus_of_mem_center
    (hσ : Function.Surjective σ)
    {z : graphFixedRootGroup t K σ} (hz : z ∈ Subgroup.center (graphFixedRootGroup t K σ)) :
    (z : ModGL t.tag K) ∈ graphFixedRootTorus t K σ := by
  have hcomm : ∀ x ∈ graphFixedRootGroup t K σ,
      (z : ModGL t.tag K) * x * (z : ModGL t.tag K)⁻¹ = x := fun x hx => by
    have h := Subgroup.mem_center_iff.1 hz ⟨x, hx⟩
    have h' : x * (z : ModGL t.tag K) = (z : ModGL t.tag K) * x := congrArg Subtype.val h
    rw [← h', mul_inv_cancel_right]
  have hcomm' : ∀ x ∈ graphFixedRootGroup t K σ,
      (z : ModGL t.tag K)⁻¹ * x * (z : ModGL t.tag K) = x := fun x hx => by
    calc (z : ModGL t.tag K)⁻¹ * x * (z : ModGL t.tag K) =
          (z : ModGL t.tag K)⁻¹ * ((z : ModGL t.tag K) * x * (z : ModGL t.tag K)⁻¹) *
            (z : ModGL t.tag K) := by rw [hcomm x hx]
      _ = x := by group
  have hzB : (z : ModGL t.tag K) ∈ graphFixedRootBorel t K σ := by
    rw [← graphFixedRootGroup_inf_normalizer_graphFixedPosUnipotent hσ]
    refine Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_normalizer_iff.2 fun x =>
      ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · rw [hcomm x (graphFixedPosUnipotent_le_graphFixedRootGroup t K σ hx)]
      exact hx
    · have hxC := graphFixedPosUnipotent_le_graphFixedRootGroup t K σ hx
      have e : x = (z : ModGL t.tag K)⁻¹ * ((z : ModGL t.tag K) * x * (z : ModGL t.tag K)⁻¹) *
          (z : ModGL t.tag K) := by group
      rw [e, hcomm' _ hxC]
      exact hx
  obtain ⟨w₀, hmax⟩ := Finite.exists_max (coxeterSystem t.tag).length
  have hn : canonicalRep (coxeterSystem t.tag) K w₀ ∈ graphFixedRootGroup t K σ :=
    canonicalRep_mem_graphFixedRootGroup (mem_relWeylTwist_of_forall_length_le hmax)
  have hzmap : (z : ModGL t.tag K) ∈ (graphFixedRootBorel t K σ).map
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K w₀)).toMonoidHom := by
    refine ⟨z, hzB, ?_⟩
    change canonicalRep (coxeterSystem t.tag) K w₀ * (z : ModGL t.tag K) *
      (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ = z
    have h := hcomm _ hn
    calc canonicalRep (coxeterSystem t.tag) K w₀ * (z : ModGL t.tag K) *
          (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ =
          ((z : ModGL t.tag K) * canonicalRep (coxeterSystem t.tag) K w₀ *
            (z : ModGL t.tag K)⁻¹) * (z : ModGL t.tag K) *
              (canonicalRep (coxeterSystem t.tag) K w₀)⁻¹ := by rw [h]
      _ = z := by group
  rw [← graphFixedRootBorel_inf_map_conj hmax]
  exact Subgroup.mem_inf.2 ⟨hzB, hzmap⟩

theorem center_graphFixedRootGroup_eq_bot
    (hσ : Function.Surjective σ) :
    Subgroup.center (graphFixedRootGroup t K σ) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzH := mem_graphFixedRootTorus_of_mem_center hσ hz
  have hzT : (z : ModGL t.tag K) ∈ torusGroup t.tag K :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hzH).1).1
  obtain ⟨l, hl⟩ := exists_torus_characters hzT
  have hsingle : ∀ i : Fin t.tag.rank, (∏ j, l j ^ (Pi.single i 1 : Fin t.tag.rank → ℤ) j : Kˣ) =
      l i := fun i => by
    rw [Finset.prod_eq_single i (fun j _ hji => by rw [Pi.single_eq_of_ne hji, zpow_zero])
      (by simp), Pi.single_eq_same, zpow_one]
  have hl1 : ∀ i, l i = 1 := by
    intro i
    set a := t.orbitIndex i
    have hx : (orbitX t K σ a 1 : ModGL t.tag K) ∈ graphFixedRootGroup t K σ :=
      graphFixedPosUnipotent_le_graphFixedRootGroup t K σ
        (orbitX_mem_graphFixedPosUnipotent t σ a 1)
    have hc := Subgroup.mem_center_iff.1 hz ⟨_, hx⟩
    have hc' : (z : ModGL t.tag K) * (orbitX t K σ a 1 : ModGL t.tag K) *
        (z : ModGL t.tag K)⁻¹ = orbitX t K σ a 1 := by
      have h' : (orbitX t K σ a 1 : ModGL t.tag K) * (z : ModGL t.tag K) =
          (z : ModGL t.tag K) * (orbitX t K σ a 1 : ModGL t.tag K) := congrArg Subtype.val hc
      rw [← h', mul_inv_cancel_right]
    rw [← orbitXProd_one_eq_orbitX σ] at hc'
    have hconj : (z : ModGL t.tag K) * orbitXProd t a (fun _ => (1 : K)) *
        (z : ModGL t.tag K)⁻¹ = orbitXProd t a fun j => ((l j : Kˣ) : K) := by
      unfold orbitXProd
      rw [← MulAut.conj_apply, map_list_prod, List.map_map]
      refine congrArg List.prod (List.map_congr_left fun j _ => ?_)
      rw [Function.comp_apply, MulAut.conj_apply, ← pinnedX_single,
        (hl _ (isRoot_single _ j)).2, pinnedX_single, hsingle, mul_one]
    rw [hconj] at hc'
    have h := eq_of_orbitXProd_eq t hc' i (t.mem_orbit_orbitIndex i)
    exact Units.ext h
  have hchar : ∀ α : Fin t.tag.rank → ℤ, (∏ j, l j ^ α j : Kˣ) = 1 := fun α => by
    simp [hl1]
  refine Subtype.ext (Units.ext (end_ext_of_hVec_rootVec (fun j => ?_) fun α hα => ?_))
  · rw [Subgroup.coe_one, Units.val_one, Module.End.one_apply]
    exact ((triangular_borel_structure.{0, 0} t.tag K).2.1 _ hzT).1 j
  · rw [Subgroup.coe_one, Units.val_one, Module.End.one_apply, (hl α hα).1, hchar, Units.val_one,
      one_smul]

theorem exceptional_fixed_center_trivial
    (t : TwistTag) (K : Type) [Field K] (σ : K ≃+* K) :
    Subgroup.center (graphFixedRootGroup t K σ.toRingHom) = ⊥ :=
  center_graphFixedRootGroup_eq_bot σ.surjective

end CFSG.LieType.Chevalley
