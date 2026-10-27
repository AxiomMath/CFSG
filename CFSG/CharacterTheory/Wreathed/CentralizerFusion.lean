module

public import CFSG.CharacterTheory.Wreathed.SimpleFusion
public import CFSG.CharacterTheory.Wreathed.QuaternionFocal

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical commutatorElement Pointwise
open BenderSuzuki.External BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

@[expose] def involutionCentralizer (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : Subgroup G :=
  Subgroup.centralizer {wreathModelHom S e (Original.x (2 ^ n))}

theorem sylow_le_involutionCentralizer (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (S : Subgroup G) ≤ involutionCentralizer n S e := by
  have hx : Original.x (2 ^ n) ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  have h := congrArg (wreathModelHom S e)
    (Subgroup.mem_center_iff.mp hx (e ⟨g, hg⟩))
  rw [map_mul, map_mul] at h
  have he : wreathModelHom S e (e ⟨g, hg⟩) = g :=
    congrArg Subtype.val (e.symm_apply_apply ⟨g, hg⟩)
  rwa [he] at h

@[expose] def centralizerSylow (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (involutionCentralizer n S e) :=
  S.subtype (sylow_le_involutionCentralizer n hn S e)

theorem centralizerSylow_coe (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) =
      (S : Subgroup G).subgroupOf (involutionCentralizer n S e) :=
  Sylow.coe_subtype _ _

@[expose] def centralizerCoordinates (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerSylow n hn S e ≃* Wreath (2 ^ n) :=
  (Subgroup.subgroupOfEquivOfLe (sylow_le_involutionCentralizer n hn S e)).trans e

theorem centralizerModelHom_comp (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (involutionCentralizer n S e).subtype.comp
      (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)) =
        wreathModelHom S e := rfl

theorem centralizerModelHom_coe (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) (w : Wreath (2 ^ n)) :
    (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) w : G) =
      wreathModelHom S e w := rfl

@[expose] def modelY {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) : Subgroup G :=
  (Original.Y m).map (wreathModelHom S e)

theorem modelY_le_sylow {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    modelY S e ≤ (S : Subgroup G) := by
  rw [← wreathModelHom_range S e]
  exact Subgroup.map_le_range (f := wreathModelHom S e) (H := Original.Y m)

@[expose] def centralizerQuaternion (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (involutionCentralizer n S e) :=
  modelY (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)

theorem centralizerQuaternion_map (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerQuaternion n hn S e).map (involutionCentralizer n S e).subtype =
      modelY S e := by
  rw [centralizerQuaternion, modelY, Subgroup.map_map, centralizerModelHom_comp]
  rfl

theorem centralizerQuaternion_le_sylow (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerQuaternion n hn S e ≤ (centralizerSylow n hn S e :
      Subgroup (involutionCentralizer n S e)) := modelY_le_sylow _ _

@[expose] def centralInvolution (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) : involutionCentralizer n S e :=
  ⟨wreathModelHom S e (Original.x (2 ^ n)),
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem centralInvolution_mem_center (n : ℕ) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    centralInvolution n S e ∈ Subgroup.center (involutionCentralizer n S e) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp g.property

theorem centralizerModelHom_x (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
      (Original.x (2 ^ n)) = centralInvolution n S e := rfl

theorem centralizerBaseNormalizerQuotient_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    let P := centralizerSylow n hn S e
    let f := centralizerCoordinates n hn S e
    Nat.card (Subgroup.normalizer (modelBase P f : Set (involutionCentralizer n S e)) ⧸
      (Subgroup.centralizer (modelBase P f : Set (involutionCentralizer n S e))).subgroupOf
        (Subgroup.normalizer (modelBase P f : Set (involutionCentralizer n S e)))) = 2 := by
  let P := centralizerSylow n hn S e
  let f := centralizerCoordinates n hn S e
  let j := wreathModelHom P f
  rcases modelBaseNormalizerQuotient_alternatives n (by omega) P f with htwo | hsix
  · exact htwo
  · have hx : j (Original.x (2 ^ n)) ∈ modelBase P f := by
      apply Subgroup.mem_map.mpr
      refine ⟨Original.x (2 ^ n), ?_, rfl⟩
      rw [Original.x_eq, element_mem_base]
    have hx2 : j (Original.x2 (2 ^ n)) ∈ modelBase P f := by
      apply Subgroup.mem_map.mpr
      refine ⟨Original.x2 (2 ^ n), ?_, rfl⟩
      rw [Original.x2_eq, element_mem_base]
    have hxorder : orderOf (j (Original.x (2 ^ n))) = 2 := by
      rw [orderOf_injective j (wreathModelHom_injective P f)]
      exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
    have hx2order : orderOf (j (Original.x2 (2 ^ n))) = 2 := by
      rw [orderOf_injective j (wreathModelHom_injective P f)]
      exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.2.1
    obtain ⟨g, _, hconj⟩ := modelBaseNormalizer_involutions_transitive n (by omega) P f
      hsix _ _ hx hx2 hxorder hx2order
    have hc : j (Original.x (2 ^ n)) ∈ Subgroup.center (involutionCentralizer n S e) :=
      centralInvolution_mem_center n S e
    rw [Subgroup.mem_center_iff.mp hc g, mul_assoc, mul_inv_cancel, mul_one] at hconj
    have heq := wreathModelHom_injective P f hconj
    exact ((wreath_center_involution_and_quaternion_coordinates n hn).distinct_classes.1
      (heq ▸ IsConj.refl _)).elim

theorem centralizer_original_center_weakly_closed [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (v : Wreath (2 ^ n)) (hv : v ∈ Original.Z (2 ^ n))
    (g : involutionCentralizer n S e)
    (hg : g⁻¹ * wreathModelHom (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) v * g ∈
        (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))) :
    g⁻¹ * wreathModelHom (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) v * g =
        wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) v := by
  let P := centralizerSylow n hn S e
  let f := centralizerCoordinates n hn S e
  let H := Subgroup.zpowers (wreathModelHom P f v)
  have hvH : wreathModelHom P f v ∈ H := Subgroup.mem_zpowers _
  have hHS : H ≤ (P : Subgroup (involutionCentralizer n S e)) :=
    Subgroup.zpowers_le.mpr (f.symm v).property
  have hgH : rightConjugate H g ≤ (P : Subgroup (involutionCentralizer n S e)) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg
  obtain ⟨a, hchain, _, hag⟩ := wreathed_fusion_decomposition P n hn f H hHS g hgH
  exact (hag _ hvH).symm.trans
    (wreathedFusionDecomposition_fixes_original_center_of_base_order_two n hn P f
      (centralizerBaseNormalizerQuotient_order_two n hn S e) H v hv hvH hchain)

theorem original_Q_le_Y (n : ℕ) : Original.Q (2 ^ n) ≤ Original.Y (2 ^ n) := by
  rw [Original.Q]
  apply (Subgroup.closure_le _).mpr
  intro q hq
  rcases Set.mem_insert_iff.mp hq with rfl | hq
  · exact (Original.Y _).pow_mem (Subgroup.subset_closure (by simp)) _
  · rw [Set.mem_singleton_iff] at hq
    rw [hq]
    exact Subgroup.subset_closure (by simp)

theorem modelQ_le_modelY (n : ℕ) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelQ S e ≤ modelY S e := Subgroup.map_mono (original_Q_le_Y n)

theorem sylow_le_modelY_normalizer (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (S : Subgroup G) ≤ Subgroup.normalizer (modelY S e : Set G) := by
  let : (Original.Y (2 ^ n)).Normal :=
    (wreath_center_involution_and_quaternion_coordinates n hn).quaternion_quotient.choose
  have h := Subgroup.le_normalizer_map (H := Original.Y (2 ^ n)) (wreathModelHom S e)
  rw [Subgroup.normalizer_eq_top, Subgroup.map_top, wreathModelHom_range S e] at h
  exact h

theorem modelYInSylow_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ((modelY S e).subgroupOf (S : Subgroup G)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (modelY_le_sylow S e)).mpr
    (sylow_le_modelY_normalizer n hn S e)

theorem modelV_eq_modelCenter_sup_modelQ (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelV S e = modelCenter S e ⊔ modelQ S e := by
  unfold modelV
  rw [(wreath_center_involution_and_quaternion_coordinates n hn).central_product,
    Subgroup.map_sup]
  rfl

theorem modelVNormalizer_difference_mem_modelQ [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g v : G) (hg : g ∈ Subgroup.normalizer (modelV S e : Set G))
    (hv : v ∈ modelV S e) : (g⁻¹ * v * g) * v⁻¹ ∈ modelQ S e := by
  have hnQ : modelCenter S e ≤ Subgroup.normalizer (modelQ S e : Set G) := by
    have hCV : modelCenter S e ≤ modelV S e := by
      rw [modelV_eq_modelCenter_sup_modelQ n hn S e]
      exact le_sup_left
    exact hCV.trans ((modelV S e).le_normalizer.trans
      (modelVNormalizer_normalizes_modelQ n hn S e))
  have hvprod : v ∈ (modelCenter S e : Set G) * (modelQ S e : Set G) := by
    have hv' := hv
    rw [modelV_eq_modelCenter_sup_modelQ n hn S e] at hv'
    change v ∈ ((modelCenter S e ⊔ modelQ S e : Subgroup G) : Set G) at hv'
    rwa [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnQ] at hv'
  obtain ⟨z, hz, q, hq, rfl⟩ := hvprod
  have hfix : g⁻¹ * z * g = z := by
    obtain ⟨w, hw, rfl⟩ := hz
    simpa only [inv_inv] using modelVNormalizer_centralizes_original_center n hn S e g⁻¹
      ((Subgroup.normalizer (modelV S e : Set G)).inv_mem hg) w hw
  have hqconj : g⁻¹ * q * g ∈ modelQ S e :=
    (Subgroup.mem_normalizer_iff''.mp (modelVNormalizer_normalizes_modelQ n hn S e hg) q).mp hq
  have hdiff : (g⁻¹ * q * g) * q⁻¹ ∈ modelQ S e :=
    (modelQ S e).mul_mem hqconj ((modelQ S e).inv_mem hq)
  have hzdiff : z * ((g⁻¹ * q * g) * q⁻¹) * z⁻¹ ∈ modelQ S e :=
    (Subgroup.mem_normalizer_iff.mp (hnQ hz) _).mp hdiff
  convert hzdiff using 1
  calc
    (g⁻¹ * (z * q) * g) * (z * q)⁻¹ =
        (g⁻¹ * z * g) * (g⁻¹ * q * g) * q⁻¹ * z⁻¹ := by group
    _ = z * (g⁻¹ * q * g) * q⁻¹ * z⁻¹ := by rw [hfix]
    _ = z * ((g⁻¹ * q * g) * q⁻¹) * z⁻¹ := by group

theorem modelVNormalizer_le_involutionCentralizer [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer (modelV S e : Set G) ≤ involutionCentralizer n S e := by
  have hx : wreathModelHom S e (Original.x (2 ^ n)) ∈ modelCenter S e :=
    Subgroup.mem_map.mpr ⟨Original.x _,
      (Original.Z _).pow_mem (Subgroup.mem_zpowers _) _, rfl⟩
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact (Subgroup.mem_centralizer_iff.mp
    (modelVNormalizer_le_center_centralizer n hn S e hg) _ hx).symm

theorem modelY_eq_centralizerQuaternion_subgroupOf (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerQuaternion n hn S e = (modelY S e).subgroupOf (involutionCentralizer n S e) := by
  apply Subgroup.map_injective (involutionCentralizer n S e).subtype_injective
  rw [centralizerQuaternion_map, Subgroup.map_subgroupOf_eq_of_le
    ((modelY_le_sylow S e).trans (sylow_le_involutionCentralizer n hn S e))]

theorem sylow_derived_eq_model_rotation (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ⁅(S : Subgroup G), (S : Subgroup G)⁆ =
      Subgroup.zpowers (wreathModelHom S e (Original.r (2 ^ n))) := by
  rw [← wreathModelHom_range S e, ← map_commutator_eq, Original.derived_eq,
    MonoidHom.map_zpowers]

theorem sylow_derived_le_modelY (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ modelY S e := by
  rw [← wreathModelHom_range S e, ← map_commutator_eq]
  apply Subgroup.map_mono
  rw [Original.derived_eq]
  apply Subgroup.zpowers_le.mpr
  exact Subgroup.subset_closure (by simp)

theorem model_sylow_conjugation_difference_mem_Y (n : ℕ)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s v : G) (hs : s ∈ (S : Subgroup G)) (hv : v ∈ (S : Subgroup G)) :
    (s⁻¹ * v * s) * v⁻¹ ∈ modelY S e := by
  apply sylow_derived_le_modelY n S e
  have h := Subgroup.commutator_mem_commutator ((S : Subgroup G).inv_mem hs) hv
  simpa only [commutatorElement_def, inv_inv] using h

theorem model_v_conjugate_normalizer_difference_mem_Y [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : S) (h v : G)
    (hh : h ∈ Subgroup.normalizer (rightConjugate (modelV S e) (s : G) : Set G))
    (hv : v ∈ rightConjugate (modelV S e) (s : G)) :
    (h⁻¹ * v * h) * v⁻¹ ∈ modelY S e := by
  have hhmap : h ∈ rightConjugate
      (Subgroup.normalizer (modelV S e : Set G)) (s : G) := by
    simpa only [rightConjugate, normalizer_conjBy] using hh
  obtain ⟨a, ha, hha⟩ := Subgroup.mem_map.mp hhmap
  change (s : G)⁻¹ * a * ((s : G)⁻¹)⁻¹ = h at hha
  simp only [inv_inv] at hha
  subst h
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hv
  have hdiff : (a⁻¹ * q * a) * q⁻¹ ∈ modelY S e :=
    modelQ_le_modelY n S e (modelVNormalizer_difference_mem_modelQ n hn S e a q ha hq)
  have hconj : (s : G)⁻¹ * ((a⁻¹ * q * a) * q⁻¹) * (s : G) ∈ modelY S e :=
    (Subgroup.mem_normalizer_iff''.mp
      (sylow_le_modelY_normalizer n hn S e s.property) _).mp hdiff
  convert hconj using 1
  change ((s : G)⁻¹ * a * (s : G))⁻¹ *
    ((s : G)⁻¹ * q * ((s : G)⁻¹)⁻¹) * ((s : G)⁻¹ * a * (s : G)) *
    ((s : G)⁻¹ * q * ((s : G)⁻¹)⁻¹)⁻¹ = _
  group

theorem wreathedFusionStep_difference_mem_Y_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (T : Subgroup G) (hTS : T ≤ (S : Subgroup G))
    (h : G) (hstep : WreathedFusionStep (S : Subgroup G) e T h)
    (v : G) (hv : v ∈ T) : (h⁻¹ * v * h) * v⁻¹ ∈ modelY S e := by
  rcases hstep with ⟨rfl, hh⟩ | ⟨hT, hh⟩ | ⟨⟨s, hT⟩, hh⟩
  · exact model_sylow_conjugation_difference_mem_Y n S e h v hh hv
  · rw [ambient_original_base_eq_modelBase] at hT
    subst T
    obtain ⟨s, hs, _, hsh⟩ := modelBaseNormalizer_order_two_step_replacement S e hcard h hh
    rw [← hsh _ hv]
    exact model_sylow_conjugation_difference_mem_Y n S e s v hs (hTS hv)
  · rw [ambient_original_v_eq_modelV] at hT
    subst T
    exact model_v_conjugate_normalizer_difference_mem_Y n hn S e s h v hh hv

theorem wreathedFusionDecomposition_difference_mem_Y_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (P : Subgroup G) {g : G}
    (hchain : WreathedFusionDecomposition (S : Subgroup G) e P g) :
    ∀ v ∈ P, (g⁻¹ * v * g) * v⁻¹ ∈ modelY S e := by
  induction hchain with
  | one => intro v _; simp only [inv_one, one_mul, mul_one, mul_inv_cancel, Subgroup.one_mem]
  | @tail g h T _ hTS hcur hstep ih =>
      intro v hv
      have hcurv : g⁻¹ * v * g ∈ T := hcur
        (Subgroup.mem_map.mpr ⟨v, hv, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
      have hstepdiff := wreathedFusionStep_difference_mem_Y_of_base_order_two n hn S e
        hcard T hTS h hstep _ hcurv
      have hprod := (modelY S e).mul_mem hstepdiff (ih v hv)
      convert hprod using 1
      group

theorem modelY_contains_conjugate_difference_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (x y : G) (hx : x ∈ (S : Subgroup G)) (hy : y ∈ (S : Subgroup G))
    (hxy : IsConj x y) : y * x⁻¹ ∈ modelY S e := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  let P := Subgroup.zpowers x
  have hxP : x ∈ P := Subgroup.mem_zpowers _
  have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hx
  have hgP : rightConjugate P a⁻¹ ≤ (S : Subgroup G) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ha] using hy
  obtain ⟨g, hchain, _, hga⟩ := wreathed_fusion_decomposition S n hn e P hPS a⁻¹ hgP
  have hdiff := wreathedFusionDecomposition_difference_mem_Y_of_base_order_two
    n hn S e hcard P hchain x hxP
  have hgy : g⁻¹ * x * g = y := by simpa only [inv_inv, ha] using hga x hxP
  rwa [hgy] at hdiff

theorem modelY_contains_focal_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2) :
    (S : Subgroup G).focalSubgroup ≤ modelY S e := by
  rw [Subgroup.focalSubgroup_eq_closure_isConj]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
  have hxyinv : IsConj x⁻¹ y⁻¹ := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    refine isConj_iff.mpr ⟨c, ?_⟩
    rw [← hc]
    group
  have hdiff := modelY_contains_conjugate_difference_of_base_order_two n hn S e hcard
    x⁻¹ y⁻¹ ((S : Subgroup G).inv_mem hx) ((S : Subgroup G).inv_mem hy) hxyinv
  have hinv := (modelY S e).inv_mem hdiff
  change x⁻¹ * y ∈ modelY S e
  convert hinv using 1
  group

theorem centralizer_focal_le_quaternion [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)).focalSubgroup ≤
      centralizerQuaternion n hn S e :=
  modelY_contains_focal_of_base_order_two n hn _ _
    (centralizerBaseNormalizerQuotient_order_two n hn S e)

theorem centralizerModelV_eq_subgroupOf (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) =
      (modelV S e).subgroupOf (involutionCentralizer n S e) := by
  apply Subgroup.map_injective (involutionCentralizer n S e).subtype_injective
  rw [modelV, Subgroup.map_map, centralizerModelHom_comp,
    Subgroup.map_subgroupOf_eq_of_le
      ((modelV_le_sylow S e).trans (sylow_le_involutionCentralizer n hn S e))]
  rfl

theorem centralizerVNormalizer_eq_subgroupOf [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer
      (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e)) =
      (Subgroup.normalizer (modelV S e : Set G)).subgroupOf
        (involutionCentralizer n S e) := by
  rw [centralizerModelV_eq_subgroupOf, Subgroup.subgroupOf_normalizer_eq
    ((modelV_le_sylow S e).trans (sylow_le_involutionCentralizer n hn S e))]

@[expose] def centralizerVNormalizerEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer
      (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e)) ≃*
      Subgroup.normalizer (modelV S e : Set G) :=
  (MulEquiv.subgroupCongr (centralizerVNormalizer_eq_subgroupOf n hn S e)).trans
    (Subgroup.subgroupOfEquivOfLe (modelVNormalizer_le_involutionCentralizer n hn S e))

theorem centralizerVNormalizerEquiv_coe [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer
      (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e))) :
    (centralizerVNormalizerEquiv n hn S e g).val = g.val.val := by
  unfold centralizerVNormalizerEquiv
  rw [MulEquiv.trans_apply, Subgroup.subgroupOfEquivOfLe_apply_coe]
  exact congrArg Subtype.val (MulEquiv.subgroupCongr_apply _ g)

theorem centralizerVAction_eq [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (g : Subgroup.normalizer
      (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e))) :
    modelVAction (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) g =
      modelVAction S e (centralizerVNormalizerEquiv n hn S e g) := by
  apply MulEquiv.ext
  intro v
  apply Subtype.ext
  apply wreathModelHom_injective S e
  have hleft := congrArg (involutionCentralizer n S e).subtype
    (modelVAction_coe (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) g v)
  rw [map_mul, map_mul, map_inv] at hleft
  change wreathModelHom S e
      (modelVAction (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) g v).val =
    g.val.val * wreathModelHom S e v.val * g.val.val⁻¹ at hleft
  rw [modelVAction_coe, centralizerVNormalizerEquiv_coe]
  exact hleft

theorem centralizerVQuotientAction_eq [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    modelVQuotientAction (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) =
      (modelVQuotientAction S e).comp (centralizerVNormalizerEquiv n hn S e).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  change CFSG.FiveTransitive.CharacteristicAutomorphism.quotient
      (Subgroup.center (Original.V (2 ^ n)))
      (modelVAction (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) g) = _
  rw [centralizerVAction_eq]
  rfl

theorem centralizerVQuotientAction_range [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (modelVQuotientAction (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e)).range = (modelVQuotientAction S e).range := by
  rw [centralizerVQuotientAction_eq, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (centralizerVNormalizerEquiv n hn S e).surjective,
    Subgroup.map_top]

@[expose] def centralizerVNormalizerQuotientEquiv [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup.normalizer
      (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e)) ⧸
      modelVInnerCentralizer (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) ≃*
        Subgroup.normalizer (modelV S e : Set G) ⧸ modelVInnerCentralizer S e :=
  (modelVNormalizerQuotientEquiv n hn _ _).trans
    ((MulEquiv.subgroupCongr (centralizerVQuotientAction_range n hn S e)).trans
      (modelVNormalizerQuotientEquiv n hn S e).symm)

theorem centralizerVNormalizerQuotient_sym3_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (Subgroup.normalizer
      (modelV (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) :
        Set (involutionCentralizer n S e)) ⧸
      modelVInnerCentralizer (centralizerSylow n hn S e) (centralizerCoordinates n hn S e) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨e3⟩ := modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e
  exact ⟨(centralizerVNormalizerQuotientEquiv n hn S e).trans e3⟩

theorem modelY_le_focal_of_v_sym3 [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hsix : Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3))) :
    modelY S e ≤ (S : Subgroup G).focalSubgroup := by
  obtain ⟨g, _, _, horder⟩ := modelVNormalizer_exists_odd_three_power_actor n hn S e hsix
  have hQ : modelQ S e ≤ (S : Subgroup G).focalSubgroup :=
    modelQ_le_focal_of_order_three n hn S e g horder (S : Subgroup G)
      ((modelQ_le_modelY n S e).trans (modelY_le_sylow S e))
  have hr : wreathModelHom S e (Original.r (2 ^ n)) ∈
      (S : Subgroup G).focalSubgroup := by
    apply (S : Subgroup G).commutator_le_focalSubgroup
    rw [sylow_derived_eq_model_rotation]
    exact Subgroup.mem_zpowers _
  have hd : wreathModelHom S e (Original.d (2 ^ n)) ∈
      (S : Subgroup G).focalSubgroup := by
    apply hQ
    exact Subgroup.mem_map.mpr ⟨Original.d _, Subgroup.subset_closure (by simp), rfl⟩
  rw [modelY, Subgroup.map_le_iff_le_comap, Original.Y]
  apply (Subgroup.closure_le _).mpr
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · exact hr
  · rw [Set.mem_singleton_iff] at hv
    rw [hv]
    exact hd

theorem centralizer_focal_eq_quaternion_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)).focalSubgroup =
      centralizerQuaternion n hn S e := by
  apply le_antisymm (centralizer_focal_le_quaternion n hn S e)
  exact modelY_le_focal_of_v_sym3 n hn _ _
    (centralizerVNormalizerQuotient_sym3_of_simple hnonab n hn S e)

theorem centralizer_focal_map_eq_modelY_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ((centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)).focalSubgroup).map
      (involutionCentralizer n S e).subtype = modelY S e := by
  rw [centralizer_focal_eq_quaternion_of_simple hnonab, centralizerQuaternion_map]

theorem centralizer_original_center_weakly_closed_ambient [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (u g : G) (hu : u ∈ modelCenter S e) (hg : g ∈ involutionCentralizer n S e)
    (hconj : g⁻¹ * u * g ∈ (S : Subgroup G)) : g⁻¹ * u * g = u := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  let gN : involutionCentralizer n S e := ⟨g, hg⟩
  have hconjN : gN⁻¹ * wreathModelHom (centralizerSylow n hn S e)
      (centralizerCoordinates n hn S e) v * gN ∈
        (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) := by
    rw [centralizerSylow_coe]
    exact hconj
  exact congrArg Subtype.val
    (centralizer_original_center_weakly_closed n hn S e v hv gN hconjN)

theorem centralizer_fusion_difference_mem_quaternion [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (P : Subgroup (involutionCentralizer n S e)) {g : involutionCentralizer n S e}
    (hchain : WreathedFusionDecomposition
      (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e))
      (centralizerCoordinates n hn S e) P g) :
    ∀ v ∈ P, (g⁻¹ * v * g) * v⁻¹ ∈ centralizerQuaternion n hn S e :=
  wreathedFusionDecomposition_difference_mem_Y_of_base_order_two n hn _ _
    (centralizerBaseNormalizerQuotient_order_two n hn S e) P hchain

end CFSG.Wreathed
