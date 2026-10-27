module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.SignStabilizerQuotients
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.CatalogueBFixedCentralQuotient
open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem rootSpan_rootCharKernel_le_toralCentralizer
    (a : Fin τ.rank → Kˣ) :
    rootSpan τ K (rootCharKernel a) ≤ toralCentralizer τ K a :=
  le_trans (le_sup_right : rootSpan τ K (rootCharKernel a) ≤
    torusGroup τ K ⊔ rootSpan τ K (rootCharKernel a)) (toralRootGroup_le a)

theorem canonicalRep_mem_normalizer_rootSpan_rootCharKernel
    {a : Fin τ.rank → Kˣ}
    {w : WeylGroup τ} (hw : w ∈ rootCharStabilizer a) :
    canonicalRep (coxeterSystem τ) K w ∈
      Subgroup.normalizer (rootSpan τ K (rootCharKernel a) : Set (ModGL τ K)) := by
  have hS := (canonical_weyl_root_transport τ K).1 w (rootCharKernel a) fun α hα => hα.1
  rw [image_rootCharKernel hw] at hS
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe hS
  rw [Subgroup.coe_map] at h
  exact h

theorem toralCentralizer_le_normalizer_rootSpan
    (a : Fin τ.rank → Kˣ) :
    toralCentralizer τ K a ≤
      Subgroup.normalizer (rootSpan τ K (rootCharKernel a) : Set (ModGL τ K)) := by
  rw [(Chevalley_toral_centralizer_Bruhat_factors τ K a).2.2.2]
  refine sup_le (sup_le (torusGroup_le_normalizer_rootSpan fun _ hα => hα.1)
    Subgroup.le_normalizer) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨w, hw, rfl⟩
  exact canonicalRep_mem_normalizer_rootSpan_rootCharKernel hw

instance rootSpan_rootCharKernel_normal
    (a : Fin τ.rank → Kˣ) :
    ((rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer
    (rootSpan_rootCharKernel_le_toralCentralizer a)).2 (toralCentralizer_le_normalizer_rootSpan a)

open _root_.Classical in
@[expose] def signTupleBits (a : Fin τ.rank → Kˣ) : Fin τ.rank → Bool :=
  fun i => decide (a i = -1)

variable (K) in
abbrev intUnitsMap : ℤˣ →* Kˣ :=
  Units.map (Int.castRingHom K).toMonoidHom

theorem intUnitsMap_injective (hK : ringChar K ≠ 2) : Function.Injective (intUnitsMap K) := by
  refine (injective_iff_map_eq_one _).2 fun u hu => ?_
  rcases Int.units_eq_one_or u with rfl | rfl
  · rfl
  · exfalso
    refine Ring.neg_one_ne_one_of_char_ne_two hK ?_
    simpa using congrArg (fun x : Kˣ => (x : K)) hu

open _root_.Classical in
theorem rootChar_eq_intUnitsMap (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (v : Fin τ.rank → ℤ) :
    rootChar a v = intUnitsMap K (maskChar (signTupleBits a) (Multiplicative.ofAdd v)) := by
  let ψ : Multiplicative (Fin τ.rank → ℤ) →* Kˣ :=
    { toFun := fun v => rootChar a (Multiplicative.toAdd v)
      map_one' := rootChar_zero a
      map_mul' := fun u v => rootChar_add a _ _ }
  have h1 : (1 : Kˣ) ≠ -1 := fun h =>
    Ring.neg_one_ne_one_of_char_ne_two hK (congrArg Units.val h).symm
  have h : ψ = (intUnitsMap K).comp (maskChar (signTupleBits a)) := by
    refine lattice_hom_ext fun j => ?_
    have hj : rootChar a (Pi.single j 1) = a j := by
      simpa using rootChar_nsmul_single a j 1
    have hp : maskPairing (signTupleBits a) (Pi.single j 1) =
        if signTupleBits a j then 1 else 0 := by
      simpa using maskPairing_zsmul_single (signTupleBits a) 1 j
    change rootChar a (Pi.single j 1) =
      intUnitsMap K ((-1) ^ maskPairing (signTupleBits a) (Pi.single j 1))
    rw [hj, hp]
    rcases ha j with e | e
    · rw [e, signTupleBits, e, decide_eq_false h1]
      simp
    · rw [e, signTupleBits, e, decide_eq_true rfl]
      ext
      simp
  exact DFunLike.congr_fun h (Multiplicative.ofAdd v)

theorem rootCharKernel_eq_kernelRoots
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    rootCharKernel a = kernelRoots (maskChar (signTupleBits a)) := by
  ext α
  refine and_congr_right fun _ => ?_
  rw [rootChar_eq_intUnitsMap hK ha, map_eq_one_iff _ (intUnitsMap_injective hK)]

theorem mem_rootCharStabilizer_iff
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) {w : WeylGroup τ} :
    w ∈ rootCharStabilizer a ↔ w ∈ charStabilizer (maskChar (signTupleBits a)) := by
  rw [mem_charStabilizer]
  refine forall_congr' fun v => ?_
  rw [rootChar_eq_intUnitsMap hK ha, rootChar_eq_intUnitsMap hK ha]
  exact (intUnitsMap_injective hK).eq_iff

theorem kernelReflectionGroup_eq_kernelWeylGroup
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    kernelReflectionGroup a = kernelWeylGroup (maskChar (signTupleBits a)) := by
  rw [kernelReflectionGroup, kernelWeylGroup, rootCharKernel_eq_kernelRoots hK ha]

theorem orderOf_dvd_two_of_charQuotient
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (q : CharQuotient χ) : orderOf q ∣ 2 := by
  obtain ⟨-, -, h1, h2, h3⟩ := sign_character_Weyl_stabilizer_quotients τ χ
  by_cases hE7 : τ = .E7
  · exact (orderOf_dvd_natCard q).trans (h2 hE7)
  by_cases hD4 : τ = .D4
  · have := (h3 hD4).2
    exact (Monoid.order_dvd_exponent q).trans (CFSG.IsElementaryAbelian.exponent_dvd_p 2 _)
  have heq := h1 (by cases τ <;> simp_all)
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  have hq : (QuotientGroup.mk ⟨w, hw⟩ : CharQuotient χ) = 1 := by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, ← heq]
    exact hw
  rw [hq, orderOf_one]
  exact one_dvd 2

theorem weylQuotient_mul_comm
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1)
    (q q' : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) :
    q * q' = q' * q := by
  obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨⟨w', hw'⟩, rfl⟩ := QuotientGroup.mk_surjective q'
  have hc := Commute.of_orderOf_dvd_two (orderOf_dvd_two_of_charQuotient _)
    (QuotientGroup.mk ⟨w, (mem_rootCharStabilizer_iff hK ha).1 hw⟩ :
      CharQuotient (maskChar (signTupleBits a)))
    (QuotientGroup.mk ⟨w', (mem_rootCharStabilizer_iff hK ha).1 hw'⟩)
  rw [Commute, SemiconjBy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hc
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    kernelReflectionGroup_eq_kernelWeylGroup hK ha]
  exact hc

theorem toralQuotient_mul_comm
    (hK : ringChar K ≠ 2) {a : Fin τ.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1)
    (x y : toralCentralizer τ K a ⧸ (toralRootGroup τ K a).subgroupOf (toralCentralizer τ K a)) :
    x * y = y * x := by
  obtain ⟨-, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  obtain ⟨q, rfl⟩ := hφ x
  obtain ⟨q', rfl⟩ := hφ y
  rw [← map_mul, ← map_mul, weylQuotient_mul_comm hK ha]

theorem derivedSeries_two_toralCentralizer_quotient
    (hK : ringChar K ≠ 2)
    {a : Fin τ.rank → Kˣ} (ha : ∀ i, a i = 1 ∨ a i = -1) :
    derivedSeries (toralCentralizer τ K a ⧸
      (rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)) 2 = ⊥ := by
  set X := toralCentralizer τ K a
  set N := (rootSpan τ K (rootCharKernel a)).subgroupOf X
  set π := QuotientGroup.mk' N
  have h1 : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ (toralRootGroup τ K a).subgroupOf X := by
    refine Subgroup.commutator_le.2 fun g _ h _ => ?_
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' _ ⁅g, h⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact toralQuotient_mul_comm hK ha _ _
  have h2 : (toralRootGroup τ K a).subgroupOf X = (torusGroup τ K).subgroupOf X ⊔ N :=
    Subgroup.subgroupOf_sup (torusGroup_le_toralCentralizer a)
      (rootSpan_rootCharKernel_le_toralCentralizer a)
  have hN : N.map π = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have h3 : ⁅(torusGroup τ K).subgroupOf X, (torusGroup τ K).subgroupOf X⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subtype.ext ((triangular_borel_structure.{0, 0} τ K).1 _
      (Subgroup.mem_subgroupOf.1 hy) _ (Subgroup.mem_subgroupOf.1 hx))
  have hD1 : derivedSeries (X ⧸ N) 1 ≤ ((torusGroup τ K).subgroupOf X).map π := by
    rw [derivedSeries_succ, derivedSeries_zero,
      ← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N),
      ← Subgroup.map_commutator]
    refine (Subgroup.map_mono h1).trans ?_
    rw [h2, Subgroup.map_sup, hN, sup_bot_eq]
  rw [derivedSeries_succ, eq_bot_iff]
  refine (Subgroup.commutator_mono hD1 hD1).trans ?_
  rw [← Subgroup.map_commutator, h3, Subgroup.map_bot]

theorem odd_toral_involution_centralizer_p_component_root_reduction
    (τ : Tag) (K : Type)
    [Field K] [Finite K] (hK : ringChar K ≠ 2) (a : Fin τ.rank → Kˣ)
    (ha : ∀ i, a i = 1 ∨ a i = -1) :
    rootSpan τ K (rootCharKernel a) ≤ toralCentralizer τ K a ∧
    ((rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)).Normal ∧
    Group.IsSolvable (toralCentralizer τ K a ⧸
      (rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)) ∧
    derivedSeries (toralCentralizer τ K a ⧸
      (rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)) 2 = ⊥ ∧
    ∀ p : ℕ, p.Prime → ∀ L : Subgroup (toralCentralizer τ K a),
      (CFSG.IsPComponent p L ↔
        L ≤ (rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a) ∧
          CFSG.IsPComponent p
            (L.subgroupOf ((rootSpan τ K (rootCharKernel a)).subgroupOf
              (toralCentralizer τ K a)))) := by
  have hD := derivedSeries_two_toralCentralizer_quotient hK ha
  have hsolv : Group.IsSolvable (toralCentralizer τ K a ⧸
      (rootSpan τ K (rootCharKernel a)).subgroupOf (toralCentralizer τ K a)) := ⟨⟨2, hD⟩⟩
  have : Finite (ModGL τ K) := finite_modGL
  refine ⟨rootSpan_rootCharKernel_le_toralCentralizer a, inferInstance, hsolv, hD,
    fun p hp L => ?_⟩
  exact p_components_solvable_quotient_invariance p hp _ L

end CFSG.LieType.Chevalley
