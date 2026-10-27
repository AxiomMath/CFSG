module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderTwistedE6Diag
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6OddField
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter

open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

private theorem congr_mem_inner_iff' {G H : Type*} [Group G] [Group H] (θ : G ≃* H)
    (α : MulAut G) :
    MulAut.congr θ α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner H ↔
      α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner G := by
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

private theorem pow_apply_eq_of_apply_eq {G : Type*} [Group G] {α : MulAut G} {x : G}
    (h : α x = x) (n : ℕ) : (α ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]

private theorem perfectInLayer_of_fixSubgroup_eq {G : Type*} [Group G] {α γ : MulAut G}
    (h : fixSubgroup α = fixSubgroup γ) (hα : PerfectInLayer α) : PerfectInLayer γ := by
  intro P hP hPP
  rw [← h] at hP ⊢
  exact hα P hP hPP

private theorem inv_mul_mul_eq_commutatorElement {G : Type*} [Group G] (x y : G) :
    (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
  simp [commutatorElement_def, mul_assoc]

private theorem coe_commutatorElement_subgroup {G : Type*} [Group G] (H : Subgroup G) (a b : H) :
    ((⁅a, b⁆ : H) : G) = ⁅(a : G), (b : G)⁆ := by
  simp [commutatorElement_def]

section Main

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem perfectInLayer_twistedE6_outer (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedE6 q, hv⟩)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpc : p = q.p)
    {β : MulAut S} (hβ : β ^ p = 1) (hout : ∀ a : S, MulAut.conj a ≠ β) :
    PerfectInLayer β := by
  subst hpc
  have hchev : ChevalleyExceptionalModel S .twistedE6 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, CFSG.TauCetiBridge.twistedModel_of_bridge
      CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hp2 (by decide) e⟩
  obtain ⟨K, _, _, σ, hcard, hσ, ⟨e'⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hchev
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hK2f : Nat.card K = q.p ^ (2 * q.exponent) := by rw [hcard, ← pow_mul, mul_comm]
  have hβp : (MulAut.congr e' β) ^ q.p = 1 := by rw [← map_pow, hβ, map_one]
  have hout' : MulAut.congr e' β ∉ twistedE6Inn K σ := fun hin => by
    obtain ⟨a, ha⟩ := (congr_mem_inner_iff' e' β).1 hin
    exact hout a ha
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -, hcube, -⟩, -, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hp hf K hcard σ hσ
  have hpg : ¬ q.p ∣ Nat.gcd 3 (q.p ^ q.exponent + 1) := fun h => by
    have h1 : q.p ∣ q.p ^ q.exponent + 1 := h.trans (Nat.gcd_dvd_right 3 _)
    have h2 : q.p ∣ q.p ^ q.exponent := dvd_pow_self _ q.exponent_pos.ne'
    exact hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_add_right h2).1 h1))
  have hη1 : Θ (MulAut.congr e' β) ≠ 1 := by
    intro h1
    have hmem : MulAut.congr e' β ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ := by
      rw [← hker, MonoidHom.mem_ker]
      exact h1
    exact hout' (CFSG.HardMathSupport.Lang.Coordinator.mem_inner_of_mem_inn_sup_diag hp hcard hσ hpg hcube hβp hmem)
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hp hf K hK2f σ hσ Θ hΘ hp hp2
      (MulAut.congr e' β) hβp hη1
  have hdp : d * q.p = q.exponent := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hp
    (by omega : 1 ≤ 2 * q.exponent) hK2f
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ q.p ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = q.p ^ (2 * d * q.p) := by rw [hK2f, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ q.p ^ (d * q.p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ q.p ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ q.p := by have := hp.two_le; omega
  have hpodd : Odd q.p := hp.odd_of_ne_two hp2
  obtain ⟨-, -, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hp hd1 hm3 hpodd K
      hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set δ := fieldActor (t := TwistTag.E6) σ ε with hδ
  set J := CFSG.RankThree.Chevalley.subfieldRootGroupImage TwistTag.E6 (fixSubfield κ)
    (fixSubfieldRestrict T κ)
    with hJdef
  have hder' : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J.subgroupOf (twistedE6RootGroup K σ) := hder
  have hJΓ : J.subgroupOf (twistedE6RootGroup K σ) ≤ fixSubgroup δ := by
    rw [← hder']
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ha hb)
        ((fixSubgroup δ).inv_mem ha)) ((fixSubgroup δ).inv_mem hb)
  haveI hJnorm : ((J.subgroupOf (twistedE6RootGroup K σ)).subgroupOf (fixSubgroup δ)).Normal := by
    rw [← hder']
    have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup δ) (fixSubgroup δ)
    rwa [sup_idem] at h
  have eJC : J.subgroupOf (twistedE6RootGroup K σ) ≃* J := Subgroup.subgroupOfEquivOfLe hJC
  have hJs : IsSimpleGroup (J.subgroupOf (twistedE6RootGroup K σ)) := eJC.isSimpleGroup
  have hJn : ∃ x y : J.subgroupOf (twistedE6RootGroup K σ), x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    apply hncJ
    intro a b
    have h := hcon (eJC.symm a) (eJC.symm b)
    apply eJC.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hq : CFSG.IsQuasisimple (J.subgroupOf (twistedE6RootGroup K σ)) :=
    LieSemisimple.isQuasisimple_of_isSimpleGroup hJs hJn
  have hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸
      (J.subgroupOf (twistedE6RootGroup K σ)).subgroupOf (fixSubgroup δ)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    rw [inv_mul_mul_eq_commutatorElement, Subgroup.mem_subgroupOf, ← hder',
      coe_commutatorElement_subgroup]
    exact Subgroup.commutator_mem_commutator (y⁻¹).2 (x⁻¹).2
  have hδPIL : PerfectInLayer δ := LieSemisimple.perfectInLayer_of_normal_quasisimple hJΓ hq hsol
  have hrβ : PerfectInLayer ((MulAut.congr e' β) ^ r) := by
    have h := LieSemisimple.perfectInLayer_conj ψ⁻¹ δ hδPIL
    rwa [← hψ, show ψ⁻¹ * (ψ * (MulAut.congr e' β) ^ r * ψ⁻¹) * ψ⁻¹⁻¹ =
      (MulAut.congr e' β) ^ r by group] at h
  have hfix : fixSubgroup ((MulAut.congr e' β) ^ r) = fixSubgroup (MulAut.congr e' β) := by
    ext x
    rw [mem_fixSubgroup, mem_fixSubgroup]
    constructor
    · intro hx
      rw [← hrs]
      exact pow_apply_eq_of_apply_eq hx s
    · intro hx
      exact pow_apply_eq_of_apply_eq hx r
  exact LieSemisimple.perfectInLayer_of_congr e' β
    (perfectInLayer_of_fixSubgroup_eq hfix hrβ)

end Main

end CFSG.HardMathSupport.Dickson.DefCharOuter
