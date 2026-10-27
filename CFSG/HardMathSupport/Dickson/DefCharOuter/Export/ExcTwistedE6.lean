module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExceptionalBase
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcInterface
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcFacts
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyTwistedE6

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.ComponentBalance CFSG.LocalAnalysis.GLTheoremA
  CFSG.Yardstones.Md0ec50421ce4
open scoped commutatorElement

namespace ExcTwistedE6

section Generic

variable {S : Type} [Group S]

theorem mul_conj_mul_inv_eq (φ : MulAut S) (z : S) :
    φ * MulAut.conj z * φ⁻¹ = MulAut.conj (φ z) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem congr_mem_innerAut_iff {G H : Type} [Group G] [Group H] (θ : G ≃* H) (α : MulAut G) :
    MulAut.congr θ α ∈ innerAut H ↔ α ∈ innerAut G := by
  have key : ∀ x : G, MulAut.congr θ (MulAut.conj x) = MulAut.conj (θ x) := fun x => by
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨θ.symm y, ?_⟩
    apply (MulAut.congr θ).injective
    rw [key, MulEquiv.apply_symm_apply, hy]
  · rintro ⟨x, rfl⟩
    exact ⟨θ x, (key x).symm⟩

theorem fixSubgroup_le_pow (α : MulAut S) (n : ℕ) : fixSubgroup α ≤ fixSubgroup (α ^ n) := by
  intro x hx
  rw [mem_fixSubgroup] at hx ⊢
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx]; exact ih

theorem fixSubgroup_pow_eq {α : MulAut S} {r s : ℕ} (h : (α ^ r) ^ s = α) :
    fixSubgroup (α ^ r) = fixSubgroup α :=
  le_antisymm (by
    have := fixSubgroup_le_pow (α ^ r) s
    rwa [h] at this) (fixSubgroup_le_pow α r)

theorem inv_mul_mul_eq_commutatorElement {G : Type*} [Group G] (x y : G) :
    (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
  simp [commutatorElement_def, mul_assoc]

theorem coe_commutatorElement_subgroup {G : Type*} [Group G] (H : Subgroup G) (a b : H) :
    ((⁅a, b⁆ : H) : G) = ⁅(a : G), (b : G)⁆ := by
  simp [commutatorElement_def]

theorem not_mem_innerAut_of_conj {α δ ψ : MulAut S} {r s : ℕ} (hrs : (α ^ r) ^ s = α)
    (hψ : ψ * α ^ r * ψ⁻¹ = δ) (hout : α ∉ innerAut S) : δ ∉ innerAut S := by
  intro hδ
  apply hout
  have h1 : α ^ r ∈ innerAut S := by
    obtain ⟨x, hx⟩ := hδ
    refine ⟨ψ⁻¹ x, ?_⟩
    have h2 : α ^ r = ψ⁻¹ * δ * ψ := by rw [← hψ]; group
    rw [h2, ← hx]
    have := mul_conj_mul_inv_eq ψ⁻¹ x
    rw [inv_inv] at this
    exact this.symm
  rw [← hrs]
  exact (innerAut S).pow_mem h1 s

end Generic

end ExcTwistedE6

section Main

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.RankThree.Chevalley (subfieldRootGroupImage
  twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (twistedE6_zpowers_of_fixes)
open CFSG.HardMathSupport.Lang.Coordinator (mem_inner_of_mem_inn_sup_diag
  twisted_E6_field_descent_data_of_prime_order)
open CFSG.HardMathSupport.Dickson.I271 (isChevSimple_of_mulEquiv isLTwoTwentySeven_of_mulEquiv)
open CFSG.LocalAnalysis.ComponentInitial (finite_field_automorphism_fixed_field_cardinality)

namespace ExcTwistedE6

theorem outerCentData_fieldActor {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) (hm3 : 3 ≤ ℓ)
    (hodd : Odd ℓ) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * d * ℓ))
    (T κ σ ε : K ≃+* K) (hT : ∀ c, T c = c ^ ℓ ^ d) (hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d))
    (hσ : ∀ c, σ c = c ^ ℓ ^ (d * ℓ)) (hε : ∀ c, ε c = c ^ ℓ ^ (d * (ℓ + 1)))
    (hout : fieldActor (t := TwistTag.E6) σ ε ∉
      innerAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    OuterCentData ℓ (fieldActor (t := TwistTag.E6) σ ε) := by
  classical
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have : Finite (fixSubfield κ) := Subtype.finite
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hK0, hJC, hδord, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd hm3 hodd K hK
      κ hκ σ hσ (fixSubfieldRestrict T κ) hσ₀ ε hε
  have hfixpow := twistedE6_zpowers_of_fixes hℓ hd hm3 hodd K hK κ hκ σ hσ
    (fixSubfieldRestrict T κ) hσ₀ ε hε
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
    rw [inv_mul_mul_eq_commutatorElement, Subgroup.mem_subgroupOf, ← hder',
      coe_commutatorElement_subgroup]
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
  have hσ₀' : ∀ c : fixSubfield κ, fixSubfieldRestrict T κ c = c ^ (ℓ ^ d) := fun c =>
    Subtype.ext (by rw [hσ₀]; rfl)
  have hK0' : Nat.card (fixSubfield κ) = (ℓ ^ d) ^ TwistTag.E6.order := by
    rw [hK0, ← pow_mul, mul_comm]
    rfl
  have hmodel : ChevalleyExceptionalModel
      (graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom)
      .twistedE6 ℓ d :=
    ⟨⟨hℓ, hd, rfl⟩, excTwistedModel_graphFixedRootGroup TwistTag.E6 hℓ hd (fixSubfield κ) hK0'
      (fixSubfieldRestrict T κ) hσ₀'⟩
  obtain ⟨hchevG, hdvdG, hL27G⟩ := excModel_facts (t := .twistedE6)
    (by simp [chevalleyExceptionalTags]) (by omega) hmodel
  let eM : ↥(J.subgroupOf C) ≃*
      graphFixedRootGroup TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ).toRingHom :=
    eJC.trans ((Subgroup.equivMapOfInjective _ _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) (fixSubfield κ).subtype)).symm)
  refine OuterCentData.ofStabilizer hℓ hδord hout
    (exceptional_fixed_center_trivial TwistTag.E6 K σ) hJΓ hJnorm hJs hJn hsol
    (fun w _ hw => hfixpow w fun x hx => hw x (Subgroup.mem_subgroupOf.2 hx))
    (isChevSimple_of_mulEquiv eM.symm hchevG) ?_ ?_
  · rw [Nat.card_congr eM.toEquiv]
    exact hdvdG
  · intro h3 hL
    exact hL27G h3 (isLTwoTwentySeven_of_mulEquiv eM hL)

theorem outerCentData_root {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hα : orderOf α = ℓ) (hout : α ∉ innerAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    OuterCentData ℓ α := by
  classical
  have hαp : α ^ ℓ = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  have hK2f : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  have hpg : ¬ ℓ ∣ Nat.gcd 3 (ℓ ^ f + 1) := fun h => by
    have h1 : ℓ ∣ ℓ ^ f + 1 := h.trans (Nat.gcd_dvd_right 3 _)
    have h2 : ℓ ∣ ℓ ^ f := dvd_pow_self _ (by omega)
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  have hη1 : Θ α ≠ 1 := by
    intro h1
    have hmem : α ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout (mem_inner_of_mem_inn_sup_diag hℓ hK hσ hpg hcube hαp hmem)
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    twisted_E6_field_descent_data_of_prime_order hℓ hf K hK2f σ hσ Θ hΘ hℓ hℓ2 α hαp hη1
  have hdp : d * ℓ = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ := finite_field_automorphism_fixed_field_cardinality hℓ
    (by omega : 1 ≤ 2 * f) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * ℓ) := by rw [hK2f, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * ℓ) := fun c => by rw [hσ, hdp]
  have hm3 : 3 ≤ ℓ := by have := hℓ.two_le; omega
  have hδ := outerCentData_fieldActor hℓ hd1 hm3 (hℓ.odd_of_ne_two hℓ2) K hKdp T κ σ ε hT hκ
    hσdp hε (not_mem_innerAut_of_conj hrs hψ hout)
  exact OuterCentData.of_pow r (OuterCentData.of_conj_aut hℓ ψ (hψ ▸ hδ)) (fixSubgroup_pow_eq hrs)

end ExcTwistedE6

theorem outerCentExcTags_twistedE6 : OuterCentExcTags IsExcTwistedE6 := by
  intro S _ _ hS hnc idx hidx he p hp hp2 hpc β hβ hout
  obtain ⟨d, hv⟩ := idx
  obtain ⟨e⟩ := he
  have hex : ∃ q, d = .twistedE6 q := by
    cases d <;> first | exact ⟨_, rfl⟩ | exact False.elim hidx
  obtain ⟨q, rfl⟩ := hex
  have hpq : p = q.p := hpc.trans (TauCeti.LieTypeIndex.characteristic_twistedE6 q)
  subst hpq
  have hchev : ChevalleyExceptionalModel S .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
      CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hp2 (by decide) e⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  refine OuterCentData.of_congr hp e' ?_
  exact ExcTwistedE6.outerCentData_root hp hp2 q.exponent_pos K hcard σ hσ (MulAut.congr e' β)
    (by rw [MulEquiv.orderOf_eq]; exact hβ)
    fun h => hout ((ExcTwistedE6.congr_mem_innerAut_iff e' β).1 h)

end Main

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
