module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcTwistedE6
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open scoped commutatorElement
open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (subfieldRootGroupImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (twistedE6_zpowers_of_fixes)
open CFSG.HardMathSupport.Lang.Coordinator (mem_inner_of_mem_inn_sup_diag
  twisted_E6_field_descent_data_of_prime_order)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)
open CFSG.EvenSmallLie.CatalogOrders


theorem exists_simple_normal_fieldActor {d : ℕ} (hd : 1 ≤ d) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ (2 * d * 3)) (T κ σ ε : K ≃+* K) (hT : ∀ c, T c = c ^ 3 ^ d)
    (hκ : ∀ c, κ c = c ^ 3 ^ (2 * d)) (hσ : ∀ c, σ c = c ^ 3 ^ (d * 3))
    (hε : ∀ c, ε c = c ^ 3 ^ (d * (3 + 1))) :
    ∃ M : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      M ≤ fixSubgroup (fieldActor (t := TwistTag.E6) σ ε) ∧
      ∃ _ : (M.subgroupOf (fixSubgroup (fieldActor (t := TwistTag.E6) σ ε))).Normal,
      Group.IsSolvable (↥(fixSubgroup (fieldActor (t := TwistTag.E6) σ ε)) ⧸
        M.subgroupOf (fixSubgroup (fieldActor (t := TwistTag.E6) σ ε))) ∧
      IsSimpleGroup ↥M ∧ (∃ x y : ↥M, x * y ≠ y * x) ∧ 3 ∣ Nat.card ↥M ∧
      (3 ^ d) ^ 36 ∣ Nat.card ↥M := by
  classical
  have hℓ : Nat.Prime 3 := Nat.prime_three
  have hm3 : 3 ≤ 3 := le_rfl
  have hodd : Odd 3 := by decide
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (fixSubfield κ) := Subtype.finite
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ 3 ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hK0, hJC, hδord, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd hm3 hodd K hK
      κ hκ σ hσ (fixSubfieldRestrict T κ) hσ₀ ε hε
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ)
    with hJdef
  have hder' : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J.subgroupOf C := hder
  have hJΓ : J.subgroupOf C ≤ fixSubgroup δ := by
    rw [← hder']
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ha hb)
        ((fixSubgroup δ).inv_mem ha)) ((fixSubgroup δ).inv_mem hb)
  have hJnorm : ((J.subgroupOf C).subgroupOf (fixSubgroup δ)).Normal := by
    rw [← hder']
    have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup δ) (fixSubgroup δ)
    rwa [sup_idem] at h
  have hsol : Group.IsSolvable
      (↥(fixSubgroup δ) ⧸ (J.subgroupOf C).subgroupOf (fixSubgroup δ)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [ExcTwistedE6.inv_mul_mul_eq_commutatorElement, Subgroup.mem_subgroupOf, ← hder',
      ExcTwistedE6.coe_commutatorElement_subgroup]
    exact Subgroup.commutator_mem_commutator (y⁻¹).2 (x⁻¹).2
  have eJC : J.subgroupOf C ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have hJs : IsSimpleGroup (J.subgroupOf C) := eJC.isSimpleGroup
  have hJn : ∃ x y : J.subgroupOf C, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hσ₀' : ∀ c : fixSubfield κ, fixSubfieldRestrict T κ c = c ^ (3 ^ d) := fun c =>
    Subtype.ext (by rw [hσ₀]; rfl)
  have hK0' : Nat.card (fixSubfield κ) = (3 ^ d) ^ TwistTag.E6.order := by
    rw [hK0, ← pow_mul, mul_comm]
    rfl
  have hmodel : ChevalleyExceptionalModel
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom)
      .twistedE6 3 d :=
    ⟨⟨hℓ, hd, rfl⟩, excTwistedModel_graphFixedRootGroup TwistTag.E6 hℓ hd (fixSubfield κ) hK0'
      (fixSubfieldRestrict T κ) hσ₀'⟩
  obtain ⟨hchevG, hdvdG, hL27G⟩ := excModel_facts (t := .twistedE6)
    (by simp [chevalleyExceptionalTags]) (by omega) hmodel
  let eM : ↥(J.subgroupOf C) ≃*
      graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom :=
    eJC.trans ((Subgroup.equivMapOfInjective _ _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)).symm)
  refine ⟨J.subgroupOf C, hJΓ, hJnorm, hsol, hJs, hJn, ?_, ?_⟩
  · rw [Nat.card_congr eM.toEquiv]
    exact hdvdG
  · rw [Nat.card_congr eM.toEquiv, card_eq_lieOrd_of_exceptional hmodel]
    exact pow_lieExp_dvd (t := .twistedE6) (n := 0) (by simp [lieMin]) (3 ^ d)

theorem pow_dvd_card_pSimple_fieldActor {d : ℕ} (hd : 1 ≤ d) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 3 ^ (2 * d * 3)) (T κ σ ε : K ≃+* K) (hT : ∀ c, T c = c ^ 3 ^ d)
    (hκ : ∀ c, κ c = c ^ 3 ^ (2 * d)) (hσ : ∀ c, σ c = c ^ 3 ^ (d * 3))
    (hε : ∀ c, ε c = c ^ 3 ^ (d * (3 + 1)))
    {S : Type} [Group S] [Finite S] (ψ : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    {β : MulAut S} (h : MulAut.congr ψ β = fieldActor (t := TwistTag.E6) σ ε) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) : (3 ^ d) ^ 36 ∣ Nat.card (PSimple 3 I) := by
  obtain ⟨M, hMC, hMn, hMsol, hMs, hMnc, hMdvd, hMpow⟩ :=
    exists_simple_normal_fieldActor hd K hK T κ σ ε hT hκ hσ hε
  haveI := hMn
  obtain ⟨e⟩ := exists_equiv_of_conj ψ h hMC hMsol hMs hMnc hMdvd hI
  rw [Nat.card_congr e.toEquiv]
  exact hMpow

theorem false_of_root {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
    {S : Type} [Group S] [Finite S] (θ : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    {β : MulAut S} (hβ : orderOf β = 3) (hout : β ∉ (MulAut.conj : S →* MulAut S).range)
    {I : Subgroup S} (hI : GLAPComponent 3 (fixSubgroup β) I) (hU : Nat.card (PSimple 3 I) = 25920) :
    False := by
  classical
  have hℓ : Nat.Prime 3 := Nat.prime_three
  have hℓ2 : (3 : ℕ) ≠ 2 := by norm_num
  set α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := MulAut.congr θ β with hαdef
  have hα : orderOf α = 3 := by rw [hαdef, MulEquiv.orderOf_eq]; exact hβ
  have hout' : α ∉ CFSG.HardMathSupport.Solomon.LocalBalance.innerAut
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := fun hin =>
    hout ((congr_mem_range_conj_iff θ β).1 hin)
  have hαp : α ^ 3 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hK2f : Nat.card K = 3 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hpg : ¬ 3 ∣ Nat.gcd 3 (3 ^ f + 1) := fun h => by
    have h1 : 3 ∣ 3 ^ f + 1 := h.trans (Nat.gcd_dvd_right 3 _)
    have h2 : 3 ∣ 3 ^ f := dvd_pow_self _ (by omega)
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  have hη1 : Θ α ≠ 1 := by
    intro h1
    have hmem : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout' (mem_inner_of_mem_inn_sup_diag hℓ hK hσ hpg hcube hαp hmem)
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order hℓ hf K hK2f σ hσ Θ hΘ hℓ hℓ2 α hαp hη1
  have hdp : d * 3 = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ 3 ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = 3 ^ (2 * d * 3) := by rw [hK2f, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ 3 ^ (d * 3) := fun c => by rw [hσ, hdp]
  have hrsβ : (β ^ r) ^ s = β := by
    apply (MulAut.congr θ).injective
    rw [map_pow, map_pow, ← hαdef]
    exact hrs
  have hI' : GLAPComponent 3 (fixSubgroup (β ^ r)) I := by
    rw [ExcTwistedE6.fixSubgroup_pow_eq hrsβ]
    exact hI
  let Ψ : S ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    θ.trans (ψ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≃* _)
  have hΨ : MulAut.congr Ψ (β ^ r) = fieldActor (t := TwistTag.E6) σ ε := by
    have h1 : MulAut.congr Ψ (β ^ r) = ψ * α ^ r * ψ⁻¹ := by
      rw [hαdef, ← map_pow]
      ext x
      rfl
    rw [h1, hψ]
  have hpow := pow_dvd_card_pSimple_fieldActor hd1 K hKdp T κ σ ε hT hκ hσdp hε Ψ hΨ hI'
  rw [hU] at hpow
  have h36 : 3 ^ 36 ∣ 25920 := (pow_dvd_pow_of_dvd (dvd_pow_self 3 (by omega)) 36).trans hpow
  norm_num at h36

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.H1429Sub
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem i1429SubTwE6_holds : I1429SubLieAt SubIsTwE6 := by
  intro S _ _ hS hnc d hchar ⟨q, hd⟩ ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  cases hd
  have hq3 : q.p = 3 := by simpa using hchar
  exfalso
  have hchev : ChevalleyExceptionalModel S .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
      CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv (by omega) (by decide) e⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  rw [hq3] at hcard hσ
  exact false_of_root q.exponent_pos K hcard σ hσ e' hord hout hI (I1431Z.card_eq_of_u4two hU)

end CFSG.LocalAnalysis.GLTheoremA

end
