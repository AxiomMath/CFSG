module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Plane
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BMPairs
public import Certificates.Certificate13690

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
open CFSG.Sporadic.Fi24 (R J JR jR tR cls lvl gs letters)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem fi24Three_facts :
    FixFacts [18] 221549 ∧ FixFacts [16, 19] 221549 ∧ FixFacts [14, 16, 16, 14, 16, 16] 14069 ∧
      Nat.card (MulAction.orbit (lvl 3) (⟨14069, by norm_num⟩ : Fin 306936)) = 1152 ∧
      FixFacts [16] 221549 ∧ FreeFacts [2] ⟨12, by norm_num⟩ :=
  Certificates.certificate13690

section Bounds

theorem chainBase_three : chainBase[3]! = 221549 := by decide

theorem bound_base3 (H : Subgroup CFSG.Sporadic.Fi24.J)
    (hH : ∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧
      idx 306936 g 221549 = 221549) : Nat.card H ∣ 3 ^ 12 := by
  have hT := CFSG.Sporadic.Fi24.chain_facts'.1 3
    (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num)
  rw [CFSG.Sporadic.Fi24.tree_size_of (l := 3) rfl] at hT
  have e : (⟨chainBase[3]!, CFSG.Sporadic.Fi24.chainBase_get_lt
      (by rw [CFSG.Sporadic.Fi24.chainBase_size]; norm_num)⟩ : Fin 306936) = ⟨221549, by norm_num⟩ :=
    Fin.ext chainBase_three
  rw [e] at hT
  exact card_dvd_of_fix_lvl3_card (by norm_num) (by rw [hT]; norm_num) H hH

theorem bound_14069
    (h : Nat.card (MulAction.orbit (lvl 3) (⟨14069, by norm_num⟩ : Fin 306936)) = 1152)
    (H : Subgroup CFSG.Sporadic.Fi24.J)
    (hH : ∀ g ∈ H, (∀ t < 3, idx 306936 g chainBase[t]! = chainBase[t]!) ∧
      idx 306936 g 14069 = 14069) : Nat.card H ∣ 3 ^ 12 :=
  card_dvd_of_fix_lvl3_card (by norm_num) (by rw [h]; norm_num) H hH

end Bounds

section Reps

theorem rep_gLAPPrimeCoreOf_eq_bot (i : Fin 5) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({fi24Rep3 i} : Set CFSG.Sporadic.Fi24.J)) = ⊥ := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := fi24Three_facts
  fin_cases i
  · exact gLAPPrimeCoreOf_eq_bot_of_fixFacts h0 bound_base3
  · exact gLAPPrimeCoreOf_eq_bot_of_fixFacts h1 bound_base3
  · exact gLAPPrimeCoreOf_eq_bot_of_fixFacts h2 (bound_14069 h3)
  · exact gLAPPrimeCoreOf_eq_bot_of_fixFacts h4 bound_base3
  · exact gLAPPrimeCoreOf_eq_bot_of_freeFacts h5

end Reps

section OPrime

theorem oPrimeCoreTrivialAt_J_of_classes (hcl : Fi24ThreeClasses) : OPrimeCoreTrivialAt 3 CFSG.Sporadic.Fi24.J := by
  intro s hs
  obtain ⟨i, hi⟩ := hcl s hs
  obtain ⟨c, hc⟩ := isConj_iff.1 hi
  refine (gLAPPrimeCoreOf_centralizer_conj c s).1 ?_
  rw [hc]
  exact rep_gLAPPrimeCoreOf_eq_bot i

theorem sporadicOPrimeHolds_Fi24_three_of_classes (hcl : Fi24ThreeClasses) :
    SporadicOPrimeHolds .Fi24Prime 3 :=
  sporadicOPrimeHolds_of_carrier
    (@OPrimeCoreTrivialAt.of_mulEquiv 3 (NativeSporadic.Carrier .Fi24Prime) _ CFSG.Sporadic.Fi24.J (Subgroup.toGroup CFSG.Sporadic.Fi24.J)
      CFSG.Sporadic.Fi24.fi24EquivJ (oPrimeCoreTrivialAt_J_of_classes hcl))

end OPrime

section Outer

theorem outer_involution_cases {r : R} (hr2 : r * r = 1) (hrJ : r ∉ JR) :
    (∃ k : Fin 306936, r = cls k) ∨ ∃ K : Set (Fin 306936), TripleOf r K := by
  have hr1 : r ≠ 1 := fun h => hrJ (h ▸ JR.one_mem)
  obtain ⟨s, hs, hsr⟩ := fi24_involution_class hr2 hr1
  obtain ⟨c, hc⟩ := (isConj_iff (α := R)).1 hsr
  have hsJ : s ∉ JR := fun h => hrJ (by
    rw [← hc]
    exact CFSG.Sporadic.Fi24.normal_JR.conj_mem s h c)
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · exact absurd (CFSG.Sporadic.Fi24.MR_le_JR (fi23ToR_mem _)) hsJ
  · left
    obtain ⟨k, hk⟩ := CFSG.Sporadic.Fi24.exists_cls
      (show r ∈ CFSG.Sporadic.Fi24.D24 from isConj_iff.2 ⟨c, hc⟩)
    exact ⟨k, hk.symm⟩
  · left
    obtain ⟨k, hk⟩ := CFSG.Sporadic.Fi24.exists_cls fi24D_mul_tR_mem
    refine ⟨c • k, ?_⟩
    rw [CFSG.Sporadic.Fi24.cls_smul_R, hk, hc]
  · right
    obtain ⟨k₁, k₂, k₃, -, -, hfix, hcomm, hchar⟩ := fi24U2T_triple
    subst hc
    exact ⟨_, (TripleOf.mk ⟨k₁, k₂, k₃, rfl⟩ hfix hcomm hchar).conj c⟩
  · right
    obtain ⟨k₁, k₂, k₃, -, -, hfix, hcomm, hchar⟩ := fi24U3T_triple
    subst hc
    exact ⟨_, (TripleOf.mk ⟨k₁, k₂, k₃, rfl⟩ hfix hcomm hchar).conj c⟩

theorem rep_exists_noncomm (i : Fin 5) {r : R} (hr2 : r * r = 1) (hrJ : r ∉ JR) :
    ∃ t : CFSG.Sporadic.Fi24.J, t * fi24Rep3 i = fi24Rep3 i * t ∧ jR t * r ≠ r * jR t := by
  obtain ⟨h0, h1, h2, -, h4, h5⟩ := fi24Three_facts
  have key : ∀ {s : CFSG.Sporadic.Fi24.J}, (∀ k, ∃ t : CFSG.Sporadic.Fi24.J, t * s = s * t ∧ jR t * cls k ≠ cls k * jR t) →
      (∀ {r : R} {K : Set (Fin 306936)}, TripleOf r K →
        ∃ t : CFSG.Sporadic.Fi24.J, t * s = s * t ∧ jR t * r ≠ r * jR t) →
      ∃ t : CFSG.Sporadic.Fi24.J, t * s = s * t ∧ jR t * r ≠ r * jR t := by
    intro s hD hT
    rcases outer_involution_cases hr2 hrJ with ⟨k, rfl⟩ | ⟨K, hK⟩
    · exact hD k
    · exact hT hK
  fin_cases i
  · exact key (exists_noncomm_cls_of_fixFacts h0) (exists_noncomm_triple_of_fixFacts h0)
  · exact key (exists_noncomm_cls_of_fixFacts h1) (exists_noncomm_triple_of_fixFacts h1)
  · exact key (exists_noncomm_cls_of_fixFacts h2) (exists_noncomm_triple_of_fixFacts h2)
  · exact key (exists_noncomm_cls_of_fixFacts h4) (exists_noncomm_triple_of_fixFacts h4)
  · exact key (exists_noncomm_cls_of_freeFacts h5) (exists_noncomm_triple_of_freeFacts h5)

theorem exists_noncomm_of_classes (hcl : Fi24ThreeClasses) {s : CFSG.Sporadic.Fi24.J} (hs : orderOf s = 3) {r : R}
    (hr2 : r * r = 1) (hrJ : r ∉ JR) : ∃ t : CFSG.Sporadic.Fi24.J, t * s = s * t ∧ jR t * r ≠ r * jR t := by
  obtain ⟨i, hi⟩ := hcl s hs
  obtain ⟨c, hc⟩ := isConj_iff.1 hi
  have hc' : c * s * c⁻¹ = fi24Rep3 i := hc
  set r' := jR c * r * (jR c)⁻¹ with hr'
  have hr2' : r' * r' = 1 := by
    calc r' * r' = jR c * (r * r) * (jR c)⁻¹ := by rw [hr']; group
      _ = 1 := by rw [hr2, mul_one, mul_inv_cancel]
  have hrJ' : r' ∉ JR := fun h => hrJ (by
    have := CFSG.Sporadic.Fi24.normal_JR.conj_mem r' h (jR c)⁻¹
    rwa [hr', show (jR c)⁻¹ * (jR c * r * (jR c)⁻¹) * (jR c)⁻¹⁻¹ = r by group] at this)
  obtain ⟨t', ht's, ht'r⟩ := rep_exists_noncomm i hr2' hrJ'
  refine ⟨c⁻¹ * t' * c, ?_, ?_⟩
  · rw [← hc'] at ht's
    calc c⁻¹ * t' * c * s = c⁻¹ * (t' * (c * s * c⁻¹)) * c := by group
      _ = c⁻¹ * ((c * s * c⁻¹) * t') * c := by rw [ht's]
      _ = s * (c⁻¹ * t' * c) := by group
  · intro h
    apply ht'r
    rw [map_mul, map_mul, map_inv] at h
    calc jR t' * r' = jR c * ((jR c)⁻¹ * jR t' * jR c * r) * (jR c)⁻¹ := by rw [hr']; group
      _ = jR c * (r * ((jR c)⁻¹ * jR t' * jR c)) * (jR c)⁻¹ := by rw [h]
      _ = r' * jR t' := by rw [hr']; group

theorem sporadicOuterHolds_Fi24_three_of_classes (hcl : Fi24ThreeClasses) :
    SporadicOuterHolds .Fi24Prime 3 := by
  intro S _ _ _ ⟨e⟩ σ hσ2 hσi s hs
  set θ : S ≃* CFSG.Sporadic.Fi24.J := e.trans CFSG.Sporadic.Fi24.fi24EquivJ with hθ
  obtain ⟨r, hr⟩ := CFSG.Sporadic.FischerOddCore.conjJ_surjective ((θ.symm.trans σ).trans θ)
  have hrx : ∀ x : S, θ (σ x) = CFSG.Sporadic.Fi24.conjJ r (θ x) := fun x => by
    rw [hr]
    show θ (σ x) = θ (σ (θ.symm (θ x)))
    rw [MulEquiv.symm_apply_apply]
  have hσσ : σ * σ = 1 := by rw [← sq]; exact hσ2
  have hr2 : r * r = 1 := by
    apply CFSG.Sporadic.Fi24.conjJ_injective
    rw [map_mul, map_one, hr]
    refine MulEquiv.ext fun x => ?_
    show θ (σ (θ.symm (θ (σ (θ.symm x))))) = x
    rw [MulEquiv.symm_apply_apply, ← MulAut.mul_apply, hσσ, MulAut.one_apply,
      MulEquiv.apply_symm_apply]
  have hrJ : r ∉ JR := by
    intro hJ
    obtain ⟨j, rfl⟩ : r ∈ jR.range := by rw [CFSG.Sporadic.Fi24.range_jR]; exact hJ
    apply hσi
    refine ⟨θ.symm j, MulEquiv.ext fun x => θ.injective ?_⟩
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hrx,
      CFSG.Sporadic.Fi24.conjJ_jR, MulAut.conj_apply]
  have hs' : orderOf (θ s) = 3 := by
    rw [MulEquiv.orderOf_eq]
    exact hs
  obtain ⟨t, ht, htr⟩ := exists_noncomm_of_classes hcl hs' hr2 hrJ
  refine ⟨θ.symm t, ?_, ?_⟩
  · apply θ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact ht.symm
  · intro hσt
    apply htr
    have h1 := hrx (θ.symm t)
    rw [hσt, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg jR h1
    rw [CFSG.Sporadic.Fi24.jR_conjJ] at h2
    calc jR t * r = r * jR t * r⁻¹ * r := by rw [← h2]
      _ = r * jR t := by group

end Outer

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
