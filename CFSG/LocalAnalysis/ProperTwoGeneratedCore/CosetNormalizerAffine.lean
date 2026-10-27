module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCosetTransitivity
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexUnitCoordinates
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexCentralFusion

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.CosetNormalizer

open CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
open CFSG.ShultStronglyClosedTI CFSG.BenderSuzuki.PFAppendixIII
open scoped IsMulCommutative

variable {G : Type*} [Group G]

theorem mul_self_eq_one_of_orderOf_eq_two {u : G} (hu : orderOf u = 2) : u * u = 1 := by
  rw [← pow_two, ← hu, pow_orderOf_eq_one]

theorem commute_of_mem_centralizer {U : Subgroup G} {u : G}
    (huC : u ∈ Subgroup.centralizer (U : Set G)) : ∀ x ∈ U, Commute u x :=
  fun x hx => (Subgroup.mem_centralizer_iff.mp huC x hx).symm

theorem centralizer_inf_normalizer_le_normalizer_coset (U : Subgroup G) (u : G) :
    Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) := by
  rintro g ⟨hgu, hgU⟩
  have hgu' : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hgu
  have hconj : ∀ v : G, g * (u * v) * g⁻¹ = u * (g * v * g⁻¹) := fun v => by
    rw [← mul_assoc g u, hgu']
    group
  intro x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨g * v * g⁻¹, (Subgroup.mem_normalizer_iff.mp hgU v).mp hv, (hconj v).symm⟩
  · rintro ⟨w, hw, hwx⟩
    change u * w = g * x * g⁻¹ at hwx
    refine ⟨g⁻¹ * w * g, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgU) w).mp hw
      simpa only [inv_inv, SetLike.mem_coe] using this
    · change u * (g⁻¹ * w * g) = x
      have hgu'' : g⁻¹ * u = u * g⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgu', mul_inv_cancel_right]
      calc u * (g⁻¹ * w * g) = (u * g⁻¹) * w * g := by group
        _ = (g⁻¹ * u) * w * g := by rw [hgu'']
        _ = g⁻¹ * (u * w) * g := by group
        _ = x := by rw [hwx]; group

theorem mem_closure_singleton_sup_iff {U : Subgroup G} {u : G} (hu : u * u = 1)
    (hcentral : ∀ x ∈ U, Commute u x) {x : G} :
    x ∈ Subgroup.closure ({u} : Set G) ⊔ U ↔ x ∈ U ∨ x ∈ (fun v : G => u * v) '' (U : Set G) := by
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hcomm : ∀ x : G, u * x ∈ U → u * x = x * u := fun x hx => by
    have h := (hcentral _ hx).eq
    calc u * x = u * (u * (u * x)) := by rw [← mul_assoc u u, hu, one_mul]
      _ = u * ((u * x) * u) := by rw [h]
      _ = x * u := by rw [← mul_assoc, ← mul_assoc, hu, one_mul]
  let S : Subgroup G :=
    { carrier := {x | x ∈ U ∨ u * x ∈ U}
      mul_mem' := by
        rintro x y (hx | hx) (hy | hy)
        · exact Or.inl (U.mul_mem hx hy)
        · refine Or.inr ?_
          have : u * (x * y) = x * (u * y) := by
            rw [← mul_assoc, (hcentral x hx).eq, mul_assoc]
          rw [this]
          exact U.mul_mem hx hy
        · refine Or.inr ?_
          rw [← mul_assoc]
          exact U.mul_mem hx hy
        · refine Or.inl ?_
          have : x * y = (u * x) * (u * y) := by
            rw [hcomm x hx, mul_assoc, ← mul_assoc u u, hu, one_mul]
          rw [this]
          exact U.mul_mem hx hy
      one_mem' := Or.inl U.one_mem
      inv_mem' := by
        rintro x (hx | hx)
        · exact Or.inl (U.inv_mem hx)
        · refine Or.inr ?_
          have : u * x⁻¹ = (u * x)⁻¹ := by
            rw [hcomm x hx, mul_inv_rev, huinv]
          rw [this]
          exact U.inv_mem hx }
  constructor
  · intro hx
    have hle : Subgroup.closure ({u} : Set G) ⊔ U ≤ S := by
      refine sup_le ?_ fun y hy => Or.inl hy
      rw [Subgroup.closure_le, Set.singleton_subset_iff]
      exact Or.inr (by rw [hu]; exact U.one_mem)
    rcases hle hx with hxU | hxU
    · exact Or.inl hxU
    · exact Or.inr ⟨u * x, hxU, show u * (u * x) = x by rw [← mul_assoc, hu, one_mul]⟩
  · rintro (hx | ⟨v, hv, rfl⟩)
    · exact Subgroup.mem_sup_right hx
    · exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.subset_closure (Set.mem_singleton u)))
        (Subgroup.mem_sup_right hv)

@[expose] def cosetNormalizerAffineHom (U : Subgroup G) [IsElementaryAbelian 2 U] (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G)) →*
      (Additive U ≃ᵃ[ZMod 2] Additive U) where
  toFun n :=
    { toEquiv := Additive.toMul.trans ((unitCoordinatePerm U u n).trans Additive.ofMul)
      linear := (MulEquiv.toAdditive (unitLinearConjugation U u hu hcentral n)).toLinearEquiv
        (ZMod.map_smul _)
      map_vadd' := fun p v => by
        change Additive.ofMul (unitCoordinatePerm U u n (Additive.toMul v * Additive.toMul p)) =
          Additive.ofMul (unitLinearConjugation U u hu hcentral n (Additive.toMul v) *
            unitCoordinatePerm U u n (Additive.toMul p))
        congr 1
        rw [unitCoordinatePerm_displacement_mul_conjugation U u hu hcentral n,
          unitCoordinatePerm_displacement_mul_conjugation U u hu hcentral n (Additive.toMul p),
          map_mul, ← mul_assoc, ← mul_assoc, mul_comm' (unitCoordinatePerm U u n 1)] }
  map_one' := by
    refine AffineEquiv.ext fun x => ?_
    change Additive.ofMul (unitCoordinatePerm U u 1 (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' n m := by
    refine AffineEquiv.ext fun x => ?_
    change Additive.ofMul (unitCoordinatePerm U u (n * m) (Additive.toMul x)) =
      Additive.ofMul (unitCoordinatePerm U u n (unitCoordinatePerm U u m (Additive.toMul x)))
    rw [map_mul]
    rfl

theorem cosetNormalizerAffineHom_apply (U : Subgroup G) [IsElementaryAbelian 2 U] (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x)
    (n : Subgroup.normalizer ((fun x : G => u * x) '' (U : Set G))) (v : U) :
    Additive.toMul (cosetNormalizerAffineHom U u hu hcentral n (Additive.ofMul v)) =
      unitCoordinatePerm U u n v :=
  rfl

theorem cosetNormalizerAffineHom_ker (U : Subgroup G) [IsElementaryAbelian 2 U] (u : G)
    (hu : u * u = 1) (hcentral : ∀ x ∈ U, Commute u x) :
    (cosetNormalizerAffineHom U u hu hcentral).ker = (unitCoordinatePerm U u).ker := by
  ext n
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  constructor
  · intro h
    refine Equiv.ext fun v => ?_
    have := congrArg (fun e : Additive U ≃ᵃ[ZMod 2] Additive U =>
      Additive.toMul (e (Additive.ofMul v))) h
    exact this
  · intro h
    refine AffineEquiv.ext fun x => ?_
    change Additive.ofMul (unitCoordinatePerm U u n (Additive.toMul x)) = x
    rw [h]
    rfl

theorem involution_coset_normalizer_affine_action (U : Subgroup G) [IsElementaryAbelian 2 U]
    (_hU : U ≠ ⊥) {u : G} (huC : u ∈ Subgroup.centralizer (U : Set G)) (_huU : u ∉ U)
    (hu : orderOf u = 2) :
    Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ≤
        Subgroup.normalizer ((Subgroup.closure ({u} : Set G) ⊔ U : Subgroup G) : Set G) ∧
      Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ≤
        Subgroup.normalizer (U : Set G) ∧
      (∀ n : G, (n ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ∧
          ∀ x ∈ (fun v : G => u * v) '' (U : Set G), n * x * n⁻¹ = x) ↔
        n ∈ Subgroup.centralizer ((Subgroup.closure ({u} : Set G) ⊔ U : Subgroup G) : Set G)) ∧
      (∃ φ : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) →*
          (Additive U ≃ᵃ[ZMod 2] Additive U),
        φ.ker = (Subgroup.centralizer
            ((Subgroup.closure ({u} : Set G) ⊔ U : Subgroup G) : Set G)).subgroupOf
          (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) ∧
        Function.Injective (QuotientGroup.kerLift φ) ∧
        ∀ (n : Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G))) (v : U),
          (n : G) * (u * v) * (n : G)⁻¹ = u * ((Additive.toMul (φ n (Additive.ofMul v)) : U) : G)) ∧
      Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)) ⊓
          Subgroup.centralizer ({u} : Set G) =
        Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.normalizer (U : Set G) := by
  have hu1 := mul_self_eq_one_of_orderOf_eq_two hu
  have hcentral := commute_of_mem_centralizer huC
  have hNU := involution_translate_normalizer_le_unit_normalizer U u hu1 hcentral
  have hCE : Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer (U : Set G) =
      Subgroup.centralizer ((Subgroup.closure ({u} : Set G) ⊔ U : Subgroup G) : Set G) := by
    rw [← unit_translate_entire_centralizer, centralizer_translate_eq_generated_centralizer]
  refine ⟨?_, hNU, ?_, ⟨cosetNormalizerAffineHom U u hu1 hcentral, ?_,
    QuotientGroup.kerLift_injective _, fun n v => ?_⟩, ?_⟩
  · have h := Subgroup.normalizer_le_normalizer_closure ((fun v : G => u * v) '' (U : Set G))
    rwa [closure_translate_eq_sup] at h
  · intro n
    rw [← centralizer_translate_eq_generated_centralizer]
    constructor
    · rintro ⟨-, hfix⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      calc x * n = n * x * n⁻¹ * n := by rw [hfix x hx]
        _ = n * x := by group
    · intro hn
      refine ⟨Subgroup.centralizer_le_normalizer _ hn, fun x hx => ?_⟩
      rw [← Subgroup.mem_centralizer_iff.mp hn x hx]
      group
  · rw [cosetNormalizerAffineHom_ker, unitCoordinatePerm_ker, hCE]
  · rw [cosetNormalizerAffineHom_apply, unitCoordinatePerm_apply, mul_inv_cancel_left]
  · apply le_antisymm
    · rintro n ⟨hnN, hnu⟩
      exact ⟨hnu, hNU hnN⟩
    · intro n hn
      exact ⟨centralizer_inf_normalizer_le_normalizer_coset U u hn, hn.1⟩

theorem mem_involutionPointClass_iff {z w : G} : w ∈ involutionPointClass z ↔ IsConj z w := by
  rw [isConj_iff]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp only [rightConjugateElem, inv_inv]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c⁻¹, by simp only [rightConjugateElem, inv_inv]⟩

theorem involution_coset_normalizer_fusion_transitivity [Finite G] (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : U ≠ ⊥) {u : G} (huC : u ∈ Subgroup.centralizer (U : Set G))
    (huU : u ∉ U) (hu : orderOf u = 2) (T : Sylow 2 (Subgroup.centralizer ({u} : Set G)))
    (hΩ : Subgroup.closure {x : G | x ∈ (T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype ∧ orderOf x = 2} =
      Subgroup.closure ({u} : Set G) ⊔ U)
    (hclass : conjugatesOf u ∩ (((T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
        (Subgroup.centralizer ({u} : Set G)).subtype : Subgroup G) : Set G) =
      (fun v : G => u * v) '' (U : Set G))
    (hfusion : ∃ (S : Sylow 2 G) (z : G) (hzS : z ∈ (S : Subgroup G)),
      (⟨z, hzS⟩ : (S : Subgroup G)) ∈ Subgroup.center (S : Subgroup G) ∧
        ∀ v ∈ U, v ≠ 1 → IsConj z v)
    (htrans : ∀ v ∈ U, ∀ w ∈ U, v ≠ 1 → w ≠ 1 →
      ∃ g ∈ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.normalizer (U : Set G),
        g * v * g⁻¹ = w) :
    (letI := cosetNormalizerAction ((fun v : G => u * v) '' (U : Set G));
      MulAction.IsMultiplyPretransitive (Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)))
        ((fun v : G => u * v) '' (U : Set G)) 2) ∧
      ∀ x₁ ∈ (fun v : G => u * v) '' (U : Set G), ∀ x₂ ∈ (fun v : G => u * v) '' (U : Set G),
      ∀ y₁ ∈ (fun v : G => u * v) '' (U : Set G), ∀ y₂ ∈ (fun v : G => u * v) '' (U : Set G),
        x₁ ≠ x₂ → y₁ ≠ y₂ → ∃ n ∈ Subgroup.normalizer ((fun v : G => u * v) '' (U : Set G)),
          n * x₁ * n⁻¹ = y₁ ∧ n * x₂ * n⁻¹ = y₂ := by
  set Δ : Set G := (fun v : G => u * v) '' (U : Set G) with hΔ
  set Tg : Subgroup G := (T : Subgroup (Subgroup.centralizer ({u} : Set G))).map
    (Subgroup.centralizer ({u} : Set G)).subtype with hTg
  have hu1 := mul_self_eq_one_of_orderOf_eq_two hu
  have hcentral := commute_of_mem_centralizer huC
  have huΔ : u ∈ Δ := ⟨1, U.one_mem, mul_one u⟩
  obtain ⟨S, z, hzS, hzcenter, hzU⟩ := hfusion
  obtain ⟨v₀, hv₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hv₀1 : (v₀ : G) ≠ 1 := fun h => hv₀ (Subtype.ext h)
  have hET : Subgroup.closure ({u} : Set G) ⊔ U ≤ Tg := by
    rw [← hΩ, Subgroup.closure_le]
    exact fun x hx => hx.1
  have hUT : U ≤ Tg := le_sup_right.trans hET
  have hpartition : ∀ x : G, x ∈ Tg → IsInvolution x → x ∈ U ∨ x ∈ Δ := by
    intro x hx hinv
    have hxo : orderOf x = 2 := orderOf_eq_prime hinv.sq_eq_one hinv.ne_one
    have hxE : x ∈ Subgroup.closure ({u} : Set G) ⊔ U := by
      rw [← hΩ]
      exact Subgroup.subset_closure ⟨hx, hxo⟩
    exact (mem_closure_singleton_sup_iff hu1 hcentral).mp hxE
  have hz : IsInvolution z := by
    obtain ⟨c, hc⟩ := isConj_iff.mp (hzU v₀ (v₀.property) hv₀1)
    have hv : IsInvolution (v₀ : G) :=
      ⟨hv₀1, elemPow_eq_one_of_isElementaryAbelian (p := 2) (v₀ : G) v₀.property⟩
    have : z = rightConjugateElem (v₀ : G) c := by
      rw [rightConjugateElem, ← hc]
      group
    rw [this]
    exact isInvolution_rightConjugateElem hv
  have hclasses : ∀ w : G, w ∈ involutionPointClass z → w ∉ involutionPointClass u := by
    intro w hwz hwu
    rw [mem_involutionPointClass_iff] at hwz hwu
    have huv : IsConj u (v₀ : G) := (hwu.trans hwz.symm).trans (hzU v₀ v₀.property hv₀1)
    have hvΔ : (v₀ : G) ∈ Δ := by
      rw [← hclass]
      exact ⟨huv, hUT v₀.property⟩
    obtain ⟨v', hv'U, hv'⟩ := hvΔ
    apply huU
    have : u = v₀ * v'⁻¹ := by rw [← hv']; group
    rw [this]
    exact U.mul_mem v₀.property (U.inv_mem hv'U)
  have hDelta : involutionPointClass u ∩ (Tg : Set G) = Δ := by
    rw [← hclass]
    ext x
    simp only [Set.mem_inter_iff, mem_involutionPointClass_iff]
    rfl
  have hmove := coset_normalizer_moves_of_central_sylow_fusion U u z hz T S hzS hzcenter hclasses
    hpartition hDelta
  have hstab : ∀ s : G, s ∈ Δ → s ≠ u → ∀ t : G, t ∈ Δ → t ≠ u →
      ∃ a : (Subgroup.normalizer Δ ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G),
        rightConjugateElem s (a : G) = t := by
    rintro _ ⟨v, hv, rfl⟩ hvu _ ⟨w, hw, rfl⟩ hwu
    have hv1 : v ≠ 1 := by
      rintro rfl
      exact hvu (mul_one u)
    have hw1 : w ≠ 1 := by
      rintro rfl
      exact hwu (mul_one u)
    obtain ⟨g, hg, hgvw⟩ := htrans v hv w hw hv1 hw1
    have hginv : g⁻¹ ∈ Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.normalizer (U : Set G) :=
      Subgroup.inv_mem _ hg
    refine ⟨⟨g⁻¹, centralizer_inf_normalizer_le_normalizer_coset U u hginv, hginv.1⟩, ?_⟩
    have hgu : g * u = u * g := Subgroup.mem_centralizer_singleton_iff.mp hg.1
    change (g⁻¹)⁻¹ * (u * v) * g⁻¹ = u * w
    rw [inv_inv, ← hgvw, ← mul_assoc g u, hgu]
    group
  have h2 := cosetNormalizerAction_isTwoPretransitive Δ u huΔ
    (full_conjugation_transitivity_of_move_and_stabilizer Δ u huΔ hmove hstab) hstab
  refine ⟨h2, fun x₁ hx₁ x₂ hx₂ y₁ hy₁ y₂ hy₂ hx hy => ?_⟩
  let := cosetNormalizerAction Δ
  obtain ⟨n, hn₁, hn₂⟩ := MulAction.is_two_pretransitive_iff.mp h2
    (show (⟨x₁, hx₁⟩ : Δ) ≠ ⟨x₂, hx₂⟩ from fun h => hx (congrArg Subtype.val h))
    (show (⟨y₁, hy₁⟩ : Δ) ≠ ⟨y₂, hy₂⟩ from fun h => hy (congrArg Subtype.val h))
  exact ⟨n, n.2, congrArg Subtype.val hn₁, congrArg Subtype.val hn₂⟩

end CFSG.ProperTwoGeneratedCore.CosetNormalizer
