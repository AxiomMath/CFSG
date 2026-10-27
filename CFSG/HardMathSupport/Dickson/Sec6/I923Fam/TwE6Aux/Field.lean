module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeTwField
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.LieArith
public import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Transport

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem mulAut_zpow_apply_of_fixed {P : Type} [Group P] {β : MulAut P} {x : P} (h : β x = x)
    (k : ℤ) : (β ^ k) x = x := by
  have hn : ∀ n : ℕ, (β ^ n) x = x := mulAut_pow_apply_of_fixed h
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · rw [zpow_natCast]
    exact hn n
  · rw [zpow_neg, zpow_natCast]
    exact (MulEquiv.symm_apply_eq _).2 (hn n).symm

theorem fixSubgroup_le_of_mem_zpowers {P : Type} [Group P] {β β' : MulAut P}
    (h : β' ∈ Subgroup.zpowers β) : fixSubgroup β ≤ fixSubgroup β' := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
  intro x hx
  exact mulAut_zpow_apply_of_fixed hx k

theorem fixSubgroup_eq_of_zpowers_eq {P : Type} [Group P] {β β' : MulAut P}
    (h : Subgroup.zpowers β = Subgroup.zpowers β') : fixSubgroup β = fixSubgroup β' :=
  le_antisymm (fixSubgroup_le_of_mem_zpowers (h ▸ Subgroup.mem_zpowers β'))
    (fixSubgroup_le_of_mem_zpowers (h ▸ Subgroup.mem_zpowers β))

theorem chevalleyExceptionalModel_twistedE6_of_equiv
    {S : Type} [Group S] {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d)
    {k : Type} [Field k] [Finite k] (hk : Nat.card k = (ℓ ^ d) ^ 2) (σ₀ : k ≃+* k)
    (hσ₀ : ∀ c, σ₀ c = c ^ (ℓ ^ d)) (e : S ≃* twistedE6RootGroup k σ₀) :
    ChevalleyExceptionalModel S .twistedE6 ℓ d := by
  have hperf := (finite_fixed_root_group_perfect TwistTag.E6 hℓ hd k hk σ₀.toRingHom hσ₀).2.2.1
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 k σ₀.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ₀.surjective
  obtain ⟨E⟩ := nonempty_derivedCentralQuotient_equiv hperf hZ
  exact ⟨⟨hℓ, hd, rfl⟩, k, inferInstance, inferInstance, hk, σ₀.toRingHom, hσ₀,
    ⟨e.trans E.symm⟩⟩

section


theorem noL2Layer_fieldActor_twE6 (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput)
    {ℓ d : ℕ} (hℓ : ℓ.Prime) (hd : 1 ≤ d) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ (2 * d * 3)) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ (d * 3)))
    {η : K ≃+* K} (hη : orderOf η = 3) :
    NoL2Layer (fieldActor (t := TwistTag.E6) σ η) := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have h2d3 : 1 ≤ 2 * d * 3 := by omega
  obtain ⟨fr, hfr, hord, hgen, hcardAut, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ h2d3 hK
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hcardAut]; omega)
  have : IsCyclic (K ≃+* K) := isCyclic_iff_exists_zpowers_eq_top.2 ⟨fr, hgen⟩
  obtain ⟨T, hTdef⟩ : ∃ T, fr ^ d = T := ⟨_, rfl⟩
  have hT : ∀ c, T c = c ^ ℓ ^ d := fun c => by
    rw [← hTdef]
    exact ringAut_pow_apply_of_frobenius hfr d c
  have hT6 : T ^ (2 * 3) = 1 := by
    rw [← hTdef, ← pow_mul, show d * (2 * 3) = orderOf fr by rw [hord]; ring,
      pow_orderOf_eq_one]
  obtain ⟨ε, hεdef⟩ : ∃ ε, T ^ (3 + 1) = ε := ⟨_, rfl⟩
  have hε : ∀ c, ε c = c ^ ℓ ^ (d * (3 + 1)) := fun c => by
    rw [← hεdef, ← hTdef, ← pow_mul]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hε3 : ε ^ 3 = 1 := by
    rw [← hεdef, ← pow_mul, show (3 + 1) * 3 = 2 * 3 * 2 by norm_num, pow_mul, hT6, one_pow]
  obtain ⟨κ, hκdef⟩ : ∃ κ, T ^ 2 = κ := ⟨_, rfl⟩
  have hκ : ∀ c, κ c = c ^ ℓ ^ (2 * d) := fun c => by
    rw [← hκdef, ← hTdef, ← pow_mul, mul_comm]
    exact ringAut_pow_apply_of_frobenius hfr _ c
  have hσ₀ : ∀ c, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d := fun c => by
    rw [coe_fixSubfieldRestrict, hT]
  obtain ⟨-, hkcard, hJC, hδord, hderived, hsimple, hnc, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer hℓ hd le_rfl
      (by decide) K hK κ hκ σ hσ (fixSubfieldRestrict T κ) hσ₀ ε hε
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hεne : ε ≠ 1 := fun h => by
    rw [h, fieldActor_one, orderOf_one] at hδord
    exact absurd hδord (by norm_num)
  have hεo : orderOf ε = 3 := orderOf_eq_prime hε3 hεne
  have hz : Subgroup.zpowers ε = Subgroup.zpowers η := by
    refine le_antisymm (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hη hε3
    · exact mem_zpowers_of_pow_eq_one_of_isCyclic' (by norm_num) hεo
        (by rw [← hη]; exact pow_orderOf_eq_one _)
  have hzA : Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ ε) =
      Subgroup.zpowers (fieldActor (t := TwistTag.E6) σ η) := by
    have h1 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) ε
    have h2 := MonoidHom.map_zpowers (fieldActorHom (t := TwistTag.E6) σ) η
    rw [hz] at h1
    exact h1.symm.trans h2
  have hfix := fixSubgroup_eq_of_zpowers_eq hzA.symm
  set k := fixSubfield κ with hkdef
  set σ₀ := fixSubfieldRestrict T κ with hσ₀def
  set J := subfieldRootGroupImage TwistTag.E6 k σ₀ with hJ
  set C := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC
  have hΓ : fixSubgroup (fieldActor (t := TwistTag.E6) σ ε) =
      MonoidHom.eqLocus (fieldActor σ ε).toMonoidHom (MonoidHom.id C) := rfl
  have hSD : J.subgroupOf C = ⁅fixSubgroup (fieldActor (t := TwistTag.E6) σ η),
      fixSubgroup (fieldActor (t := TwistTag.E6) σ η)⁆ := by
    rw [hfix, hΓ]
    exact hderived.symm
  have e1 : ↥(J.subgroupOf C) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJC
  haveI : IsSimpleGroup ↥J := hsimple
  have hs : IsSimpleGroup ↥(J.subgroupOf C) := e1.isSimpleGroup
  have hnab : ∃ a b : ↥(J.subgroupOf C), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hnc
    intro a b
    have h := hcon (e1.symm a) (e1.symm b)
    apply e1.symm.injective
    rw [map_mul, map_mul]
    exact h
  have hcardk : Nat.card k = (ℓ ^ d) ^ 2 := by rw [hkcard, ← pow_mul, mul_comm]
  have hσ₀' : ∀ c, σ₀ c = c ^ (ℓ ^ d) := fun c => Subtype.ext (by
    rw [hσ₀ c, SubmonoidClass.coe_pow])
  haveI : Finite k := Subtype.finite
  have eJ : ↥J ≃* twistedE6RootGroup k σ₀ :=
    (Subgroup.equivMapOfInjective (twistedE6RootGroup k σ₀) _
      (baseChangeGL_injective (τ := TwistTag.E6.tag) k.subtype)).symm
  have hM : ChevalleyExceptionalModel ↥(J.subgroupOf C) .twistedE6 ℓ d :=
    chevalleyExceptionalModel_twistedE6_of_equiv hℓ hd hcardk σ₀ hσ₀' (e1.trans eJ)
  have hX : LieModel ↥(J.subgroupOf C) .twistedE6 0 ℓ d :=
    Or.inr (Or.inl ⟨rfl, by decide, hM⟩)
  have hZ : Subgroup.center ↥(J.subgroupOf C) = ⊥ := center_eq_bot_of_simple hnab
  exact noL2_of_simple_commutator_fixed (fieldActor (t := TwistTag.E6) σ η) (J.subgroupOf C) hSD
    hs hnab fun r hr => not_typeL2_of_lieModel hO hX.admissible hX (by decide) (by decide) hZ hr

theorem noL2Layer_of_not_mem_twistedE6Inndiag
    (hO : ComponentClassification.CatLeaf.LieOrderFormulasInput) {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {x : MulAut (twistedE6RootGroup K σ)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ twistedE6Inn K σ ⊔ twistedE6Diag K σ) : NoL2Layer x := by
  have hK' : Nat.card K = ℓ ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  obtain ⟨hηo, ⟨d, hd⟩, ψ, hψ⟩ := exists_conj_fieldActor_of_not_mem_twistedE6Inndiag hℓ hf K hK'
    σ hσ Θ hΘ Nat.prime_three (by norm_num) hx3 hxo
  have hd0 : 1 ≤ d := by omega
  subst hd
  have hKdp : Nat.card K = ℓ ^ (2 * d * 3) := by rw [hK']; ring_nf
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * 3) := fun c => by rw [hσ]; ring_nf
  have h1 := noL2Layer_conj ψ⁻¹ (noL2Layer_fieldActor_twE6 hO hℓ hd0 hKdp σ hσdp hηo)
  have h2 : ψ⁻¹ * fieldActor (t := TwistTag.E6) σ (Θ x) * ψ⁻¹⁻¹ = x := by
    rw [← hψ]
    group
  rwa [h2] at h1

theorem exists_twistedE6RootGroup_equiv {P : Type} [Group P] {p f : ℕ} (hp : p.Prime)
    (hf : 1 ≤ f) (h : TwistedChevalleyModel P TwistTag.E6 (p ^ f)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K), Nat.card K = (p ^ f) ^ 2 ∧
      (∀ c, σ c = c ^ (p ^ f)) ∧ Nonempty (twistedE6RootGroup K σ ≃* P) := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hp hf h
  let σ' : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσeq : σ'.toRingHom = σ := RingHom.ext fun c => rfl
  refine ⟨K, inferInstance, inferInstance, σ', hK, fun c => hσ c, ?_⟩
  show Nonempty (graphFixedRootGroup TwistTag.E6 K σ'.toRingHom ≃* P)
  rw [hσeq]
  exact ⟨e⟩

end

section Perfect


theorem commutator_twistedE6RootGroup {P : Type} [Group P] {p f : ℕ}
    (hE : ChevalleyExceptionalModel P .twistedE6 p f) {K : Type} [Field K] [Finite K]
    (σ : K ≃+* K) (e : twistedE6RootGroup K σ ≃* P) :
    commutator (twistedE6RootGroup K σ) = ⊤ := by
  obtain ⟨hnt, hsimple⟩ := CFSG.LieType.Simplicity.fam_2e6_simplicity P p f hE
  haveI : IsSimpleGroup ↥(twistedE6RootGroup K σ) := e.isSimpleGroup
  haveI : Nontrivial ↥(twistedE6RootGroup K σ) := e.toEquiv.nontrivial
  have hZ : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    center_graphFixedRootGroup_eq_bot σ.surjective
  exact (isQuasisimple_of_simple (exists_noncomm_of_center_bot hZ)).1

end Perfect

end CFSG.HardMathSupport.Dickson.Sec6.I923
