module

public import CFSG.CharacterTheory.Wreathed.Fusion
public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ConjugationFamily
public import CFSG.CharacterTheory.Wreathed.ActualLocalActions
public import CFSG.CharacterTheory.Semidihedral.InvolutionFusion
public import CFSG.LocalAnalysis.RankTwoShapes.CentralMovement

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical
open BenderSuzuki.External BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem ambient_original_base_eq_modelBase {n : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ambientWreathSubgroup (S : Subgroup G) e (Original.U (2 ^ n)) = modelBase S e := by
  rw [ambientWreathSubgroup, Original.U_eq, Subgroup.map_map]
  rfl

theorem ambient_original_v_eq_modelV {n : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    ambientWreathSubgroup (S : Subgroup G) e (Original.V (2 ^ n)) = modelV S e := by
  rw [ambientWreathSubgroup, Subgroup.map_map]
  rfl

theorem model_center_sylow_conjugation (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (v : Wreath (2 ^ n)) (hv : v ∈ Original.Z (2 ^ n))
    (s : G) (hs : s ∈ (S : Subgroup G)) :
    s⁻¹ * wreathModelHom S e v * s = wreathModelHom S e v := by
  have hcentral : v ∈ Subgroup.center (Wreath (2 ^ n)) := by
    rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact hv
  let sS : S := ⟨s, hs⟩
  have hfs : wreathModelHom S e (e sS) = s :=
    congrArg Subtype.val (e.symm_apply_apply sS)
  have hcomm : s * wreathModelHom S e v = wreathModelHom S e v * s := by
    have h := congrArg (wreathModelHom S e)
      (Subgroup.mem_center_iff.mp hcentral (e sS))
    rwa [map_mul, map_mul, hfs] at h
  calc
    s⁻¹ * wreathModelHom S e v * s = s⁻¹ * (wreathModelHom S e v * s) :=
      mul_assoc _ _ _
    _ = s⁻¹ * (s * wreathModelHom S e v) := by rw [← hcomm]
    _ = wreathModelHom S e v := by group

theorem model_v_conjugate_normalizer_center_fixed [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : S) (h : G)
    (hh : h ∈ Subgroup.normalizer (rightConjugate (modelV S e) (s : G) : Set G))
    (v : Wreath (2 ^ n)) (hv : v ∈ Original.Z (2 ^ n)) :
    h⁻¹ * wreathModelHom S e v * h = wreathModelHom S e v := by
  have hhmap : h ∈ rightConjugate
      (Subgroup.normalizer (modelV S e : Set G)) (s : G) := by
    simpa only [rightConjugate, normalizer_conjBy] using hh
  obtain ⟨a, ha, hha⟩ := Subgroup.mem_map.mp hhmap
  change (s : G)⁻¹ * a * ((s : G)⁻¹)⁻¹ = h at hha
  simp only [inv_inv] at hha
  subst h
  have hsfix := model_center_sylow_conjugation n hn S e v hv (s : G) s.property
  have has : a⁻¹ * wreathModelHom S e v * a = wreathModelHom S e v := by
    simpa only [inv_inv] using modelVNormalizer_centralizes_original_center n hn S e a⁻¹
      ((Subgroup.normalizer (modelV S e : Set G)).inv_mem ha) v hv
  have hsfix' : (s : G) * wreathModelHom S e v * (s : G)⁻¹ =
      wreathModelHom S e v := by
    simpa only [inv_inv] using model_center_sylow_conjugation n hn S e v hv (s : G)⁻¹
      ((S : Subgroup G).inv_mem s.property)
  calc
    ((s : G)⁻¹ * a * (s : G))⁻¹ * wreathModelHom S e v *
        ((s : G)⁻¹ * a * (s : G)) =
      (s : G)⁻¹ * (a⁻¹ * ((s : G) * wreathModelHom S e v * (s : G)⁻¹) * a) *
        (s : G) := by group
    _ = (s : G)⁻¹ * (a⁻¹ * wreathModelHom S e v * a) * (s : G) := by rw [hsfix']
    _ = (s : G)⁻¹ * wreathModelHom S e v * (s : G) := by rw [has]
    _ = wreathModelHom S e v := hsfix

theorem wreathedFusionStep_fixes_original_center_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (T : Subgroup G) (h : G) (hstep : WreathedFusionStep (S : Subgroup G) e T h)
    (v : Wreath (2 ^ n)) (hv : v ∈ Original.Z (2 ^ n))
    (hvT : wreathModelHom S e v ∈ T) :
    h⁻¹ * wreathModelHom S e v * h = wreathModelHom S e v := by
  rcases hstep with ⟨rfl, hh⟩ | ⟨hT, hh⟩ | ⟨⟨s, hT⟩, hh⟩
  · exact model_center_sylow_conjugation n hn S e v hv h hh
  · rw [ambient_original_base_eq_modelBase] at hT
    subst T
    obtain ⟨s, hs, _, hsh⟩ := modelBaseNormalizer_order_two_step_replacement S e hcard h hh
    rw [← hsh _ hvT]
    exact model_center_sylow_conjugation n hn S e v hv s hs
  · rw [ambient_original_v_eq_modelV] at hT
    subst T
    exact model_v_conjugate_normalizer_center_fixed n hn S e s h hh v hv

theorem wreathedFusionDecomposition_fixes_original_center_of_base_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) = 2)
    (P : Subgroup G) (v : Wreath (2 ^ n)) (hv : v ∈ Original.Z (2 ^ n))
    (hvP : wreathModelHom S e v ∈ P) {g : G}
    (hchain : WreathedFusionDecomposition (S : Subgroup G) e P g) :
    g⁻¹ * wreathModelHom S e v * g = wreathModelHom S e v := by
  induction hchain with
  | one => simp
  | @tail g h T _ _ hcur hstep ih =>
      have hvT : wreathModelHom S e v ∈ T := by
        rw [← ih]
        apply hcur
        exact Subgroup.mem_map.mpr ⟨_, hvP, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
      calc
        (g * h)⁻¹ * wreathModelHom S e v * (g * h) =
            h⁻¹ * (g⁻¹ * wreathModelHom S e v * g) * h := by group
        _ = h⁻¹ * wreathModelHom S e v * h := by rw [ih]
        _ = wreathModelHom S e v :=
          wreathedFusionStep_fixes_original_center_of_base_order_two n hn S e hcard
            T h hstep v hv hvT

@[expose] def finiteSimpleCarrier (G : Type u) [Finite G] : Type := Fin (Nat.card G)

theorem simple_central_sylow_involution_movement_universe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (S : Sylow 2 G)
    (z : S) (hzZ : z ∈ Subgroup.center (S : Subgroup G)) (hz : orderOf z = 2) :
    ∃ g : G, g⁻¹ * (z : G) * g ∈ (S : Subgroup G) ∧ g⁻¹ * (z : G) * g ≠ z := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype G := Fintype.ofFinite G
  let f : finiteSimpleCarrier G ≃ G :=
    (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)).symm
  let : Group (finiteSimpleCarrier G) := f.group
  let E : finiteSimpleCarrier G ≃* G := f.mulEquiv
  let : Finite (finiteSimpleCarrier G) := Finite.of_equiv G f.symm
  let : IsSimpleGroup (finiteSimpleCarrier G) := E.isSimpleGroup
  let T : Sylow 2 (finiteSimpleCarrier G) :=
    S.mapSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hT : (T : Subgroup (finiteSimpleCarrier G)) =
      (S : Subgroup G).map E.symm.toMonoidHom := Sylow.coe_mapSurjective _ S
  let F : S ≃* T :=
    ((S : Subgroup G).equivMapOfInjective E.symm.toMonoidHom E.symm.injective).trans
      (MulEquiv.subgroupCongr hT.symm)
  have hF (a : S) : E (F a).val = a.val := E.apply_symm_apply a.val
  have hzT : F z ∈ Subgroup.center (T : Subgroup (finiteSimpleCarrier G)) := by
    rw [← Subgroup.map_center_eq F]
    exact Subgroup.mem_map.mpr ⟨z, hzZ, rfl⟩
  have hnonabT : ∃ a b : finiteSimpleCarrier G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨E.symm a, E.symm b, ?_⟩
    intro h
    apply hab
    have heq := congrArg E h
    simpa only [map_mul, MulEquiv.apply_symm_apply] using heq
  obtain ⟨g, hg, hne⟩ := CFSG.RankTwoShapes.simple_central_sylow_involution_movement
    hnonabT T (F z) hzT ((F.orderOf_eq z).trans hz)
  refine ⟨E g, ?_, ?_⟩
  · have hgmap : g⁻¹ * (F z).val * g ∈ (S : Subgroup G).map E.symm.toMonoidHom :=
      hT ▸ hg
    obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp hgmap
    have heq' : a = E (g⁻¹ * (F z).val * g) :=
      (E.apply_symm_apply a).symm.trans (congrArg E heq)
    simp only [map_mul, map_inv, hF] at heq'
    exact heq' ▸ ha
  · intro h
    apply hne
    apply E.injective
    simpa only [map_mul, map_inv, hF] using h

theorem modelBaseNormalizer_order_ne_two_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G))) ≠ 2 := by
  intro hcard
  let x0 := Original.x (2 ^ n)
  let x : S := e.symm x0
  have hxval : x.val = wreathModelHom S e x0 := rfl
  have hxZ : x0 ∈ Original.Z (2 ^ n) := by
    exact (Original.Z (2 ^ n)).pow_mem (Subgroup.mem_zpowers _) _
  have hxcentral : x ∈ Subgroup.center (S : Subgroup G) := by
    rw [← Subgroup.map_center_eq e.symm]
    refine Subgroup.mem_map.mpr ⟨x0, ?_, rfl⟩
    rw [(wreath_center_involution_and_quaternion_coordinates n hn).center]
    exact hxZ
  have hxorder : orderOf x = 2 :=
    (e.symm.orderOf_eq x0).trans
      (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1
  obtain ⟨g, hg, hne⟩ := simple_central_sylow_involution_movement_universe
    hnonab S x hxcentral hxorder
  let P := Subgroup.zpowers (x : G)
  have hxP : (x : G) ∈ P := Subgroup.mem_zpowers _
  have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr x.property
  have hgP : rightConjugate P g ≤ (S : Subgroup G) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hg
  obtain ⟨h, hchain, _, hhg⟩ := wreathed_fusion_decomposition S n hn e P hPS g hgP
  have hfix := wreathedFusionDecomposition_fixes_original_center_of_base_order_two
    n hn S e hcard P x0 hxZ hxP hchain
  exact hne ((hhg _ hxP).symm.trans hfix)

theorem modelBaseNormalizerQuotient_sym3_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) :=
  (modelBaseNormalizerQuotient_alternatives n (by omega) S e).resolve_left
    (modelBaseNormalizer_order_ne_two_of_simple hnonab n hn S e)

@[expose] def modelSwapProjection {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    S →* Multiplicative (ZMod 2) := RegularWreathProduct.rightHom.comp e.toMonoidHom

theorem modelSwap_inv_mul_cancel (a : Multiplicative (ZMod 2)) : a⁻¹ * a = 1 := by
  apply Multiplicative.toAdd.injective
  change -a.toAdd + a.toAdd = 0
  exact neg_add_cancel a.toAdd

theorem modelSwapProjection_ker {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    (modelSwapProjection S e).ker = (modelBase S e).subgroupOf (S : Subgroup G) := by
  ext x
  change e x ∈ baseSubgroup m ↔ x.val ∈ modelBase S e
  constructor
  · intro hx
    exact Subgroup.mem_map.mpr ⟨e x, hx,
      congrArg Subtype.val (e.symm_apply_apply x)⟩
  · rintro ⟨w, hw, heq⟩
    have hS : e.symm w = x := Subtype.ext heq
    have he : w = e x := (e.apply_symm_apply w).symm.trans (congrArg e hS)
    exact he ▸ hw

instance modelBaseInSylow_normal {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) :
    ((modelBase S e).subgroupOf (S : Subgroup G)).Normal := by
  rw [← modelSwapProjection_ker]
  infer_instance

@[expose] def modelSwapValue {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m) (x : G) :
    Multiplicative (ZMod 2) :=
  if hx : x ∈ (S : Subgroup G) then modelSwapProjection S e ⟨x, hx⟩ else 1

theorem modelSwapValue_eq_projection {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (x : G) (hx : x ∈ (S : Subgroup G)) :
    modelSwapValue S e x = modelSwapProjection S e ⟨x, hx⟩ := by
  simp only [modelSwapValue, dite_eq_left hx]

theorem modelSwapValue_eq_one_iff {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (x : G) (hx : x ∈ (S : Subgroup G)) :
    modelSwapValue S e x = 1 ↔ x ∈ modelBase S e := by
  rw [modelSwapValue_eq_projection S e x hx]
  change (⟨x, hx⟩ : S) ∈ (modelSwapProjection S e).ker ↔ _
  rw [modelSwapProjection_ker]
  rfl

theorem modelSwapValue_sylow_conjugation {m : ℕ} (S : Sylow 2 G) (e : S ≃* Wreath m)
    (s x : G) (hs : s ∈ (S : Subgroup G)) (hx : x ∈ (S : Subgroup G)) :
    modelSwapValue S e (s⁻¹ * x * s) = modelSwapValue S e x := by
  have hy : s⁻¹ * x * s ∈ (S : Subgroup G) :=
    (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hs) hx) hs
  rw [modelSwapValue_eq_projection S e _ hy, modelSwapValue_eq_projection S e _ hx]
  change modelSwapProjection S e ((⟨s, hs⟩ : S)⁻¹ * ⟨x, hx⟩ * ⟨s, hs⟩) = _
  rw [map_mul, map_mul, map_inv]
  rw [mul_comm ((modelSwapProjection S e ⟨s, hs⟩)⁻¹), mul_assoc]
  rw [modelSwap_inv_mul_cancel, mul_one]

theorem model_v_conjugate_normalizer_step_replacement [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2)
    (s : S) (h : G)
    (hh : h ∈ Subgroup.normalizer (rightConjugate (modelV S e) (s : G) : Set G)) :
    ∃ t : G, t ∈ (S : Subgroup G) ∧
      ∀ x ∈ rightConjugate (modelV S e) (s : G), t⁻¹ * x * t = h⁻¹ * x * h := by
  have hhmap : h ∈ rightConjugate
      (Subgroup.normalizer (modelV S e : Set G)) (s : G) := by
    simpa only [rightConjugate, normalizer_conjBy] using hh
  obtain ⟨a, ha, hha⟩ := Subgroup.mem_map.mp hhmap
  change (s : G)⁻¹ * a * ((s : G)⁻¹)⁻¹ = h at hha
  simp only [inv_inv] at hha
  subst h
  obtain ⟨b, hbS, _, hba⟩ := modelVNormalizer_order_two_step_replacement n hn S e hcard a ha
  refine ⟨(s : G)⁻¹ * b * (s : G), ?_, ?_⟩
  · exact (S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem s.property) hbS) s.property
  · rintro x ⟨v, hv, rfl⟩
    change ((s : G)⁻¹ * b * (s : G))⁻¹ *
      ((s : G)⁻¹ * v * ((s : G)⁻¹)⁻¹) * ((s : G)⁻¹ * b * (s : G)) =
      ((s : G)⁻¹ * a * (s : G))⁻¹ *
        ((s : G)⁻¹ * v * ((s : G)⁻¹)⁻¹) * ((s : G)⁻¹ * a * (s : G))
    simp only [inv_inv]
    calc
      _ = (s : G)⁻¹ * (b⁻¹ * v * b) * (s : G) := by group
      _ = (s : G)⁻¹ * (a⁻¹ * v * a) * (s : G) := by rw [hba v hv]
      _ = _ := by group

theorem wreathedFusionStep_preserves_swap_of_v_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2)
    (T : Subgroup G) (hTS : T ≤ (S : Subgroup G))
    (h : G) (hstep : WreathedFusionStep (S : Subgroup G) e T h)
    (x : G) (hx : x ∈ T) :
    modelSwapValue S e (h⁻¹ * x * h) = modelSwapValue S e x := by
  rcases hstep with ⟨rfl, hh⟩ | ⟨hT, hh⟩ | ⟨⟨s, hT⟩, hh⟩
  · exact modelSwapValue_sylow_conjugation S e h x hh hx
  · rw [ambient_original_base_eq_modelBase] at hT
    subst T
    have hy : h⁻¹ * x * h ∈ modelBase S e := (Subgroup.mem_normalizer_iff''.mp hh x).mp hx
    exact ((modelSwapValue_eq_one_iff S e _ (hTS hy)).mpr hy).trans
      ((modelSwapValue_eq_one_iff S e _ (hTS hx)).mpr hx).symm
  · rw [ambient_original_v_eq_modelV] at hT
    subst T
    obtain ⟨t, ht, htx⟩ := model_v_conjugate_normalizer_step_replacement n hn S e hcard s h hh
    rw [← htx x hx]
    exact modelSwapValue_sylow_conjugation S e t x ht (hTS hx)

theorem wreathedFusionDecomposition_preserves_swap_of_v_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2)
    (P : Subgroup G) (hPS : P ≤ (S : Subgroup G)) {g : G}
    (hchain : WreathedFusionDecomposition (S : Subgroup G) e P g) :
    ∀ x ∈ P, g⁻¹ * x * g ∈ (S : Subgroup G) ∧
      modelSwapValue S e (g⁻¹ * x * g) = modelSwapValue S e x := by
  induction hchain with
  | one =>
      intro x hx
      simp only [inv_one, one_mul, mul_one]
      exact ⟨hPS hx, trivial⟩
  | @tail g h T _ hTS hcur hstep ih =>
      intro x hx
      have hyT : g⁻¹ * x * g ∈ T := hcur
        (Subgroup.mem_map.mpr ⟨x, hx, by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩)
      have hfinal : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
      rw [hfinal]
      refine ⟨hTS ((Subgroup.mem_normalizer_iff''.mp
        (wreathedFusionStep_mem_normalizer hstep) _).mp hyT), ?_⟩
      exact (wreathedFusionStep_preserves_swap_of_v_order_two n hn S e hcard T hTS
        h hstep _ hyT).trans (ih x hx).2

theorem modelSwapValue_conjugate_eq_of_v_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2)
    (x y : G) (hx : x ∈ (S : Subgroup G)) (hy : y ∈ (S : Subgroup G))
    (hxy : IsConj x y) : modelSwapValue S e x = modelSwapValue S e y := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  let P := Subgroup.zpowers x
  have hxP : x ∈ P := Subgroup.mem_zpowers _
  have hPS : P ≤ (S : Subgroup G) := Subgroup.zpowers_le.mpr hx
  have hgP : rightConjugate P a⁻¹ ≤ (S : Subgroup G) := by
    rw [rightConjugate, Subgroup.conjBy, MonoidHom.map_zpowers]
    apply Subgroup.zpowers_le.mpr
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ha] using hy
  obtain ⟨g, hchain, _, hga⟩ := wreathed_fusion_decomposition S n hn e P hPS a⁻¹ hgP
  have hpres := (wreathedFusionDecomposition_preserves_swap_of_v_order_two
    n hn S e hcard P hPS hchain x hxP).2
  have hgy : g⁻¹ * x * g = y := by simpa only [inv_inv, ha] using hga x hxP
  rw [hgy] at hpres
  exact hpres.symm

theorem model_base_contains_focal_of_v_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2) :
    (S : Subgroup G).focalSubgroup ≤ modelBase S e := by
  rw [Subgroup.focalSubgroup_eq_closure_isConj]
  apply (Subgroup.closure_le (modelBase S e)).2
  rintro _ ⟨x, hx, y, hy, hxy, rfl⟩
  have hxyP : modelSwapProjection S e (⟨x, hx⟩ : S) =
      modelSwapProjection S e (⟨y, hy⟩ : S) := by
    simpa only [modelSwapValue_eq_projection S e _ hx,
      modelSwapValue_eq_projection S e _ hy] using
        modelSwapValue_conjugate_eq_of_v_order_two n hn S e hcard x y hx hy hxy
  have hdiff : (⟨x, hx⟩ : S)⁻¹ * ⟨y, hy⟩ ∈ (modelSwapProjection S e).ker := by
    change modelSwapProjection S e ((⟨x, hx⟩ : S)⁻¹ * ⟨y, hy⟩) = 1
    rw [map_mul, map_inv, hxyP, modelSwap_inv_mul_cancel]
  rw [modelSwapProjection_ker] at hdiff
  exact hdiff

theorem modelBaseSylowQuotient_conjugate_eq_of_v_order_two [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hcard : Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) = 2)
    (x y : S) (hxy : IsConj (x : G) (y : G)) :
    QuotientGroup.mk' ((modelBase S e).subgroupOf (S : Subgroup G)) x =
      QuotientGroup.mk' ((modelBase S e).subgroupOf (S : Subgroup G)) y := by
  have hpres : modelSwapProjection S e x = modelSwapProjection S e y := by
    have H := modelSwapValue_conjugate_eq_of_v_order_two n hn S e hcard x y
      x.property y.property hxy
    rw [modelSwapValue_eq_projection S e _ x.property,
      modelSwapValue_eq_projection S e _ y.property] at H
    convert H using 1
  apply QuotientGroup.eq_iff_div_mem.mpr
  rw [← modelSwapProjection_ker]
  change modelSwapProjection S e (x / y) = 1
  rw [div_eq_mul_inv, map_mul, map_inv, hpres, mul_comm, modelSwap_inv_mul_cancel]

theorem commutator_eq_top_of_nonabelian_simple [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  have hnormal : (commutator G).Normal := inferInstance
  rcases hnormal.eq_bot_or_eq_top with h | h
  · have hcomm := isMulCommutative_iff.mp ((commutator_eq_bot_iff G).mp h)
    obtain ⟨a, b, hab⟩ := hnonab
    exact (hab (hcomm a b)).elim
  · exact h

theorem modelBase_proper_in_sylow {n : ℕ}
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) : modelBase S e ≠ (S : Subgroup G) := by
  intro h
  have hz : wreathModelHom S e (Original.z (2 ^ n)) ∈ modelBase S e :=
    h ▸ (e.symm (Original.z (2 ^ n))).property
  obtain ⟨w, hw, heq⟩ := Subgroup.mem_map.mp hz
  have he : w = Original.z (2 ^ n) := wreathModelHom_injective S e heq
  rw [he, Original.z, element_mem_base] at hw
  exact one_ne_zero hw

theorem modelVNormalizer_order_ne_two_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e) ≠ 2 := by
  intro hcard
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : (S : Subgroup G).focalSubgroup = S := by
    rw [← Subgroup.commutator_inf_eq_focalSubgroup S,
      commutator_eq_top_of_nonabelian_simple hnonab, top_inf_eq]
  have hle : (S : Subgroup G) ≤ modelBase S e := by
    rw [← hF]
    exact model_base_contains_focal_of_v_order_two n hn S e hcard
  exact modelBase_proper_in_sylow S e (le_antisymm (modelBase_le_sylow S e) hle)

theorem modelVNormalizerQuotient_sym3_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)) :=
  (modelVNormalizerQuotient_alternatives n hn S e).resolve_left
    (modelVNormalizer_order_ne_two_of_simple hnonab n hn S e)

theorem modelBase_involutions_conjugate_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (x y : G) (hx : x ∈ modelBase S e) (hy : y ∈ modelBase S e)
    (hxorder : orderOf x = 2) (hyorder : orderOf y = 2) : IsConj x y := by
  obtain ⟨g, _, h⟩ := modelBaseNormalizer_involutions_transitive n (by omega) S e
    (modelBaseNormalizerQuotient_sym3_of_simple hnonab n hn S e) x y hx hy hxorder hyorder
  exact isConj_iff.mpr ⟨g, h⟩

theorem model_original_x_isConj_x2_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) := by
  have hstructure := wreath_center_involution_and_quaternion_coordinates n hn
  apply modelBase_involutions_conjugate_of_simple hnonab n hn S e
  · exact Subgroup.mem_map.mpr ⟨Original.x (2 ^ n), by simp, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨Original.x2 (2 ^ n), by simp, rfl⟩
  · exact (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      hstructure.involution_orders.1
  · exact (orderOf_injective _ (wreathModelHom_injective S e) _).trans
      hstructure.involution_orders.2.1

theorem model_original_x_isConj_swap_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) := by
  obtain ⟨g, _, h⟩ := modelVNormalizer_swap_fusion n hn S e
    (modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e)
  have hxx2 := model_original_x_isConj_x2_of_simple hnonab n hn S e
  rcases h with h | h
  · exact hxx2.trans (isConj_iff.mpr ⟨g, h⟩).symm
  · have hx2t : IsConj (Original.x2 (2 ^ n))
        (Original.t (2 ^ n) ^ (2 ^ n / 2)) :=
      (wreath_center_involution_and_quaternion_coordinates n hn).x2_class _ |>.mpr
        (Or.inr rfl)
    exact (hxx2.trans ((wreathModelHom S e).map_isConj hx2t)).trans
      (isConj_iff.mpr ⟨g, h⟩).symm

theorem model_involution_isConj_original_x_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (w : Wreath (2 ^ n)) (hw : orderOf w = 2) :
    IsConj (wreathModelHom S e w) (wreathModelHom S e (Original.x (2 ^ n))) := by
  rcases (wreath_center_involution_and_quaternion_coordinates n hn).involution_classes w hw
      with h | h | h
  · exact (wreathModelHom S e).map_isConj h.symm
  · exact ((wreathModelHom S e).map_isConj h.symm).trans
      (model_original_x_isConj_x2_of_simple hnonab n hn S e).symm
  · exact ((wreathModelHom S e).map_isConj h.symm).trans
      (model_original_x_isConj_swap_of_simple hnonab n hn S e).symm

theorem ambient_involution_isConj_original_x_of_simple [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (x : G) (hx : orderOf x = 2) :
    IsConj x (wreathModelHom S e (Original.x (2 ^ n))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; norm_num)
  obtain ⟨y, hxy⟩ :=
    CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow S x hxp
  have hyG : orderOf (y : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hyorder : orderOf (e y) = 2 :=
    (e.orderOf_eq y).trans ((Subgroup.orderOf_coe y).symm.trans hyG)
  have hyx := model_involution_isConj_original_x_of_simple hnonab n hn S e (e y) hyorder
  have hyactual : wreathModelHom S e (e y) = (y : G) :=
    congrArg Subtype.val (e.symm_apply_apply y)
  rw [hyactual] at hyx
  exact hxy.trans hyx

theorem all_involutions_conjugate_of_simple_wreathed [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 2) : IsConj x y :=
  (ambient_involution_isConj_original_x_of_simple hnonab n hn S e x hx).trans
    (ambient_involution_isConj_original_x_of_simple hnonab n hn S e y hy).symm

theorem simple_wreathed_one_involution_class_and_local_S3 [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nonempty (Subgroup.normalizer (modelBase S e : Set G) ⧸
      (Subgroup.centralizer (modelBase S e : Set G)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
    Nonempty (Subgroup.normalizer (modelV S e : Set G) ⧸
      modelVInnerCentralizer S e ≃* Equiv.Perm (Fin 3)) ∧
    (∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) ∧
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.x2 (2 ^ n))) ∧
    IsConj (wreathModelHom S e (Original.x (2 ^ n)))
      (wreathModelHom S e (Original.z (2 ^ n))) :=
  ⟨modelBaseNormalizerQuotient_sym3_of_simple hnonab n hn S e,
    modelVNormalizerQuotient_sym3_of_simple hnonab n hn S e,
    all_involutions_conjugate_of_simple_wreathed hnonab n hn S e,
    model_original_x_isConj_x2_of_simple hnonab n hn S e,
    model_original_x_isConj_swap_of_simple hnonab n hn S e⟩

end CFSG.Wreathed
