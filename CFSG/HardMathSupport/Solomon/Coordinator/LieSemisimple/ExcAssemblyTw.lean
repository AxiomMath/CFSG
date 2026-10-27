module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TwE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcInnerLang.TriD4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTamePrime
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.DualOuterFull

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.Chevalley
  (twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer subfieldRootGroupImage)
open scoped commutatorElement

private theorem perfectInLayer_of_fixSubgroup_eq {G : Type*} [Group G] {α γ : MulAut G}
    (h : fixSubgroup α = fixSubgroup γ) (hα : PerfectInLayer α) : PerfectInLayer γ := by
  intro P hP hPP
  rw [← h] at hP ⊢
  exact hα P hP hPP

private theorem pow_apply_eq_of_fix {G : Type*} [Group G] {α : MulAut G} {x : G}
    (h : α x = x) (n : ℕ) : (α ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, h]

private theorem fixSubgroup_pow_eq_of_pow_pow {G : Type*} [Group G] {α : MulAut G} {r s : ℕ}
    (h : (α ^ r) ^ s = α) : fixSubgroup (α ^ r) = fixSubgroup α := by
  ext x
  rw [mem_fixSubgroup, mem_fixSubgroup]
  exact ⟨fun hx => by rw [← h]; exact pow_apply_eq_of_fix hx s, fun hx => pow_apply_eq_of_fix hx r⟩

private theorem perfectInLayer_of_derived_eq_simple {S : Type*} [Group S] {δ : MulAut S}
    {J : Subgroup S} (hder : ⁅fixSubgroup δ, fixSubgroup δ⁆ = J) (hs : IsSimpleGroup J)
    (hnc : ∃ a b : J, a * b ≠ b * a) : PerfectInLayer δ := by
  have hJΓ : J ≤ fixSubgroup δ := by
    rw [← hder]
    exact Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact (fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ((fixSubgroup δ).mul_mem ha hb)
        ((fixSubgroup δ).inv_mem ha)) ((fixSubgroup δ).inv_mem hb)
  haveI hJnorm : (J.subgroupOf (fixSubgroup δ)).Normal := by
    rw [← hder]
    have h := Subgroup.normal_subgroupOf_commutator_sup (fixSubgroup δ) (fixSubgroup δ)
    rwa [sup_idem] at h
  have hsol : Group.IsSolvable (↥(fixSubgroup δ) ⧸ J.subgroupOf (fixSubgroup δ)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
      ← hder]
    have e : (((x * y)⁻¹ * (y * x) : ↥(fixSubgroup δ)) : S) =
        ⁅((y⁻¹ : ↥(fixSubgroup δ)) : S), ((x⁻¹ : ↥(fixSubgroup δ)) : S)⁆ := by
      simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact Subgroup.commutator_mem_commutator (y⁻¹).2 (x⁻¹).2
  exact perfectInLayer_of_normal_quasisimple hJΓ (isQuasisimple_of_isSimpleGroup hs hnc) hsol

section Certs


private theorem perfectInLayer_twE6_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = ℓ ^ (2 * f)) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Θ : MulAut (twistedE6RootGroup K σ) →* RingAut K)
    (hΘ : ∀ α g u δ, α = MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u *
      fieldActor σ δ → Θ α = δ)
    (β : MulAut (twistedE6RootGroup K σ)) (hβ : β ^ p = 1) (hη1 : Θ β ≠ 1) :
    PerfectInLayer β := by
  obtain ⟨d, hd, hd1, r, s, T, ε, hT, hε, hrs, ψ, hψ, -⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.twisted_E6_field_descent_data_of_prime_order hℓ hf K hK
      σ hσ Θ hΘ hp hp2 β hβ hη1
  have hdp : d * p = f := by rw [hd, mul_comm]
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 2 * f) hK
  obtain ⟨κ, hκ⟩ : ∃ κ : K ≃+* K, ∀ c, κ c = c ^ ℓ ^ (2 * d) :=
    ⟨fr ^ (2 * d), fun c => ringAut_pow_apply_of_frobenius hfr (2 * d) c⟩
  have hKdp : Nat.card K = ℓ ^ (2 * d * p) := by rw [hK, mul_assoc, hdp]
  have hσdp : ∀ c, σ c = c ^ ℓ ^ (d * p) := fun c => by rw [hσ, hdp]
  have hσ₀ : ∀ c : fixSubfield κ, (fixSubfieldRestrict T κ c : K) = (c : K) ^ ℓ ^ d :=
    fun c => by rw [coe_fixSubfieldRestrict, hT]
  have hm3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, -, hJC, -, hder, hsimpleJ, hncJ, -⟩ :=
    twisted_E6_canonical_odd_field_derived_subgroup_and_pointwise_centralizer
      hℓ hd1 hm3 (hp.odd_of_ne_two hp2) K hKdp κ hκ σ hσdp (fixSubfieldRestrict T κ) hσ₀ ε hε
  set δ := fieldActor (t := TwistTag.E6) σ ε
  set J := subfieldRootGroupImage TwistTag.E6 (fixSubfield κ) (fixSubfieldRestrict T κ)
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
  have hδPIL : PerfectInLayer δ := perfectInLayer_of_derived_eq_simple hder hJs hJn
  have hrβ : PerfectInLayer (β ^ r) := by
    have h := perfectInLayer_conj ψ⁻¹ δ hδPIL
    rwa [← hψ, show ψ⁻¹ * (ψ * β ^ r * ψ⁻¹) * ψ⁻¹⁻¹ = β ^ r by group] at h
  exact perfectInLayer_of_fixSubgroup_eq (fixSubgroup_pow_eq_of_pow_pow hrs) hrβ

private theorem perfectInLayer_triD4_field {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (Θ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) →* (K ≃+* K))
    (hΘ : ∀ α g δ, α = MulAut.conj g * fieldActor σ δ → Θ α = δ)
    {β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)} (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) (hβout : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    PerfectInLayer β := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hβord : orderOf β = p := orderOf_eq_prime hβ hβ1
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hηord, hpf, ⟨h₀, hh₀⟩, -⟩ :=
    CFSG.RankThree.Chevalley.triality_noninner_large_prime_field_descent_and_local_core_trivial
      hℓ hf K hK σ hσ Θ hΘ hp (by omega) ⊤ le_top ⟨β, Subgroup.mem_top _⟩ hβout
      (by rw [Subgroup.orderOf_mk]; exact hβord)
  have hh₀' : MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹ =
      fieldActor (t := TwistTag.D4) σ (Θ β) := hh₀
  obtain ⟨f', hff'⟩ := hpf
  have hd : 1 ≤ f' := by
    rcases Nat.eq_zero_or_pos f' with h | h
    · rw [h, mul_zero] at hff'
      omega
    · exact h
  obtain ⟨φ, hφ, hφord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality hℓ
      (by omega : 1 ≤ 3 * f) hK3
  obtain ⟨δc, hδcdef⟩ : ∃ δc, φ ^ (3 * f') = δc := ⟨_, rfl⟩
  have hδc : ∀ c, δc c = c ^ ℓ ^ (3 * f') := fun c => by
    rw [← hδcdef]
    exact ringAut_pow_apply_of_frobenius hφ _ c
  have hδcord : orderOf δc = p := by
    rw [← hδcdef, orderOf_pow_of_dvd (by omega)
      (by rw [hφord, hff']; exact ⟨p, by ring⟩), hφord, hff',
      show 3 * (p * f') = 3 * f' * p by ring, Nat.mul_div_cancel_left p (by omega)]
  have hzp : Subgroup.zpowers (Θ β) = Subgroup.zpowers δc :=
    CFSG.RankThree.PartOne.CTP.zpowers_ringEquiv_eq_of_orderOf hℓ (by omega : 1 ≤ 3 * f) hK3
      hηord hδcord
  have hfix_eq : fixSubgroup (fieldActor (t := TwistTag.D4) σ (Θ β)) =
      fixSubgroup (fieldActor (t := TwistTag.D4) σ δc) := by
    have h := CFSG.RankThree.PartOne.CTP.fixedSubgroup_eq_of_zpowers_eq
      (fieldActorHom (t := TwistTag.D4) σ) hzp
    ext x
    exact SetLike.ext_iff.1 h x
  have hm3 : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
  have hK' : Nat.card K = ℓ ^ (3 * f' * p) := by
    rw [hK3, hff']; congr 1; ring
  have hσ' : ∀ c, σ c = c ^ ℓ ^ (f' * p) := fun c => by
    rw [hσ c, hff', mul_comm p f']
  obtain ⟨-, -, -, -, -, -, hfixJ, hsimpJ, hncJ, -⟩ :=
    CFSG.RankThree.Chevalley.triality_canonical_field_full_centralizer_and_pointwise_kernel hℓ hd
      hp.two_le hm3 K hK' σ hσ' δc hδc
  haveI := hsimpJ
  have e3 : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) ≃* ↥(trialityFieldImage σ δc) :=
    (Subgroup.equivMapOfInjective _ (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
      (MulEquiv.subgroupCongr hfixJ)
  have hsimE : IsSimpleGroup ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)) :=
    e3.isSimpleGroup
  have hncE : ∃ a b : ↥(fixSubgroup (fieldActor (t := TwistTag.D4) σ δc)), a * b ≠ b * a := by
    simp only [not_forall, ne_eq] at hncJ
    obtain ⟨a, b, hab⟩ := hncJ
    refine ⟨e3.symm a, e3.symm b, fun h => hab ?_⟩
    have h' := congrArg e3 h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h'
    exact h'
  have hPfix : PerfectInLayer (fieldActor (t := TwistTag.D4) σ δc) :=
    perfectInLayer_of_isSimpleGroup _ hsimE hncE
  have hPΘ : PerfectInLayer (fieldActor (t := TwistTag.D4) σ (Θ β)) :=
    perfectInLayer_of_fixSubgroup_eq hfix_eq.symm hPfix
  have h := perfectInLayer_conj (MulAut.conj h₀)⁻¹ _ hPΘ
  rw [← hh₀'] at h
  rwa [show (MulAut.conj h₀)⁻¹ * (MulAut.conj h₀ * β * (MulAut.conj h₀)⁻¹) *
      (MulAut.conj h₀)⁻¹⁻¹ = β by group] at h

theorem exists_setup_prime {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) : ∃ p₀ : ℕ, p₀.Prime ∧ p₀ ≠ ℓ ∧ (5 ≤ p₀ ∨ 4 ≤ ℓ ^ f) := by
  have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  by_cases h32 : p = 3 ∧ ℓ ^ f = 2
  · refine ⟨5, Nat.prime_five, fun h5 => ?_, Or.inl le_rfl⟩
    have hℓ2 : ℓ = 2 := by
      have hdvd : ℓ ∣ 2 := h32.2 ▸ dvd_pow_self ℓ (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hdvd
    omega
  · refine ⟨p, hp, hpℓ, ?_⟩
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    by_cases h3 : p = 3
    · subst h3
      right
      by_contra h
      have : ℓ ^ f = 2 ∨ ℓ ^ f = 3 := by omega
      rcases this with h' | h'
      · exact h32 ⟨rfl, h'⟩
      · apply hpℓ
        have hdvd : 3 ∣ ℓ ^ f := by rw [h']
        exact (Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
          (Nat.prime_three.dvd_of_dvd_pow hdvd)
    · left
      have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
      omega

theorem natCast_ne_zero_algebraicClosure_of_ne {ℓ f m p : ℕ} (hℓ : ℓ.Prime) (hp : p.Prime)
    {K : Type} [Field K] (hK : Nat.card K = (ℓ ^ f) ^ m) (hpℓ : p ≠ ℓ) :
    ((p : ℕ) : AlgebraicClosure K) ≠ 0 := by
  classical
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hr, hn⟩ := FiniteField.card K (ringChar K)
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP (AlgebraicClosure K) (ringChar K) :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective _
  have hrℓ : ringChar K = ℓ := by
    have h1 : ringChar K ∣ (ℓ ^ f) ^ m := by
      rw [← hK, Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self _ n.pos.ne'
    rw [← pow_mul] at h1
    exact (Nat.prime_dvd_prime_iff_eq hr hℓ).1 (hr.dvd_of_dvd_pow h1)
  rw [Ne, CharP.cast_eq_zero_iff (AlgebraicClosure K) (ringChar K), hrℓ]
  exact fun h => hpℓ ((Nat.prime_dvd_prime_iff_eq hℓ hp).1 h).symm

section TwE6


theorem perfectInLayer_exc_twE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hmon : MonomialToralAt Tag.E6 p)
    (β : MulAut ↥(twistedE6RootGroup K σ)) (hβ : β ^ p = 1)
    (hβ1 : β ≠ 1) :
    PerfectInLayer β := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -, hker, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form hℓ hf K hK σ hσ
  by_cases hΘβ : Θ β = 1
  ·
    have hmem : β ∈ (twistedE6InndiagConj K σ).range := by
      rw [range_twistedE6InndiagConj, ← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨h, rfl⟩ := hmem
    have hp1 : h ^ p = 1 :=
      twistedE6InndiagConj_injective hℓ hf hK σ hσ (by rw [map_pow, hβ, map_one])
    have hh1 : h ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
    obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
    obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inndiag_twE6_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀ hmon
        (twistedE6InndiagConj K σ h) (h : ModGL TwistTag.E6.tag K) h.2
        (twistedE6InndiagConj_apply h) (by rw [← Subgroup.coe_pow, hp1]; rfl)
        (fun h' => hh1 (Subtype.ext h'))
    exact perfectInLayer_of_langSetup_of_prime S hp ι hinj hrange _ hconj hT hap h1
      (langSetup_hTame_of_prime S hp (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ)
        (fun h => absurd h (by decide)) hT hap h1)
  ·
    exact perfectInLayer_twE6_field hℓ hf (by rw [hK, ← pow_mul, mul_comm]) σ hσ hp hp2 Θ hΘ β hβ
      hΘβ

end TwE6

section TriD4


theorem perfectInLayer_exc_triD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (hmon : MonomialToralAt Tag.D4 p)
    (β : MulAut ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hβ : β ^ p = 1) (hβ1 : β ≠ 1) : PerfectInLayer β := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  obtain ⟨hZ, -, Θ, hΘ, hker⟩ :=
    CFSG.RankThree.Chevalley.triality_normal_form_data hℓ hf K hK σ hσ
  by_cases hΘβ : Θ β = 1
  ·
    have hmem : β ∈ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := by
      rw [← hker, MonoidHom.mem_ker]
      exact hΘβ
    obtain ⟨x, rfl⟩ := hmem
    have hxp : x ^ p = 1 :=
      mulAut_conj_injective_of_center_eq_bot hZ (by rw [map_pow, hβ, map_one])
    have hx1 : x ≠ 1 := fun h' => hβ1 (by rw [h', map_one])
    obtain ⟨p₀, hp₀, hp₀ℓ, hq₀⟩ := exists_setup_prime hℓ hf hp hp2 hpℓ
    obtain ⟨S, a, ι, -, -, hT, hap, h1, hinj, hrange, hconj⟩ :=
      exists_langSetup_of_inner_triD4_of_prime hℓ hf hK σ hσ hp hpℓ hp₀ hp₀ℓ hq₀ hmon x hxp hx1
    exact perfectInLayer_of_langSetup_of_prime S hp ι hinj hrange _ hconj hT hap h1
      (langSetup_hTame_of_prime S hp (natCast_ne_zero_algebraicClosure_of_ne hℓ hp hK hpℓ)
        (fun h => absurd h (by decide)) hT hap h1)
  ·
    have hβout : β ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
        MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range := fun hmem =>
      hΘβ (by rw [← MonoidHom.mem_ker, hker]; exact hmem)
    by_cases hp3 : p = 3
    · subst hp3
      haveI : Fact ℓ.Prime := ⟨hℓ⟩
      exact D4Dual.perfectInLayer_triality_outer_three (Ne.symm hpℓ) hf hK σ hσ β hβ hβout
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        have h4 : p ≠ 4 := fun h => by rw [h] at hp; exact absurd hp (by norm_num)
        omega
      exact perfectInLayer_triD4_field hℓ hf hK σ hσ hp hp5 Θ hΘ hβ hβ1 hβout

end TriD4

end Certs

end CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
