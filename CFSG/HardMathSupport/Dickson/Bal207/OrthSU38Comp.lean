module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthFixedType
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Glue

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthFix

open Polynomial Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.GroupTheory.WeirSylow

theorem factorization_two_of_eq {N a u : ℕ} (hN : N = 2 ^ a * u) (hu : Odd u) :
    N.factorization 2 = a := by
  subst hN
  have hu0 : u ≠ 0 := fun h => by
    rw [h] at hu
    exact (by decide : ¬ Odd 0) hu
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hu0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hu.not_two_dvd_nat, add_zero]

theorem factorization_two_of_int_eq {N a : ℕ} {U : ℤ} (hN : (N : ℤ) = 2 ^ a * U) (hU : Odd U)
    (hN0 : 0 < N) : N.factorization 2 = a := by
  have hU0 : 0 ≤ U := by
    by_contra hlt
    push Not at hlt
    have h1 : (2 : ℤ) ^ a * U < 0 := mul_neg_of_pos_of_neg (by positivity) hlt
    have h2 : (0 : ℤ) < N := by exact_mod_cast hN0
    linarith
  obtain ⟨u, rfl⟩ := Int.eq_ofNat_of_zero_le hU0
  exact factorization_two_of_eq (by exact_mod_cast hN) (by simpa using hU)

theorem factorization_two_su38 : (5515776 : ℕ).factorization 2 = 9 :=
  factorization_two_of_eq (u := 10773) (by norm_num) (by decide)

theorem odd_prod_pow_sub_one {c : ℤ} (hc : Even c) (m : ℕ) :
    Odd (∏ i ∈ Finset.Icc 1 m, (c ^ i - 1)) :=
  Finset.prod_induction _ Odd (fun _ _ ha hb => ha.mul hb) odd_one fun i hi =>
    (hc.pow_of_ne_zero (by have := (Finset.mem_Icc.1 hi).1; omega)).sub_odd odd_one

theorem eq_three_of_mul_choose_two {f m : ℕ} (hf : f = 1 ∨ f = 3) (hm : 2 ≤ m)
    (h : f * (m * (m - 1) / 2) = 9) : f = 3 ∧ m = 3 := by
  have hm5 : m ≤ 5 := by
    by_contra hc
    have h6 : 6 * 5 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    rcases hf with rfl | rfl <;> omega
  interval_cases m <;> rcases hf with rfl | rfl <;> exact ⟨by omega, by omega⟩

private theorem odd_card_center_of_sq {H : Type*} [Group H] [Finite H]
    (h : ∀ z ∈ Subgroup.center H, z ^ 2 = 1 → z = 1) : Odd (Nat.card (Subgroup.center H)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center H) := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center H)) 2 h2
  have hz2 : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have h1 : z = 1 := Subtype.ext (h z z.2 (by simpa using congrArg Subtype.val hz2))
  rw [h1, orderOf_one] at hz
  omega

theorem factorization_two_card_of_odd_center {H : Type*} [Group H] [Finite H]
    (hZ : Odd (Nat.card (Subgroup.center H))) :
    (Nat.card H).factorization 2 = (Nat.card (H ⧸ Subgroup.center H)).factorization 2 := by
  have : Finite (H ⧸ Subgroup.center H) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (Subgroup.center H))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center H),
    Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hZ.not_two_dvd_nat, add_zero]

section Orders

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W]

theorem factorization_two_card_orthogonalGroup {R : QuadraticForm K W}
    (hR : (polarBilin R).Nondegenerate) {m f : ℕ} (hdim : finrank K W = 2 * (m + 1))
    (hK : Nat.card K = 2 ^ f) :
    (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R)).factorization 2 =
      1 + f * (m * (m + 1)) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hε : ∃ ε : ℤ, (ε = 1 ∧ IsPlusType R) ∨ (ε = -1 ∧ ¬ IsPlusType R) := by
    by_cases h : IsPlusType R
    · exact ⟨1, Or.inl ⟨rfl, h⟩⟩
    · exact ⟨-1, Or.inr ⟨rfl, h⟩⟩
  obtain ⟨ε, hε⟩ := hε
  have hcard := natCard_orthogonalGroup_of_type hR hdim hε
  have hq : Even (Nat.card K : ℤ) := by
    rw [hK]
    push_cast
    exact (even_two).pow_of_ne_zero (by
      rintro rfl
      have : 1 < Nat.card K := Finite.one_lt_card
      rw [hK, pow_zero] at this
      exact lt_irrefl _ this)
  have hodd1 : Odd ((Nat.card K : ℤ) ^ (m + 1) - ε) := by
    rcases hε with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact (hq.pow_of_ne_zero (Nat.succ_ne_zero m)).sub_odd odd_one
    · rw [sub_neg_eq_add]
      exact (hq.pow_of_ne_zero (Nat.succ_ne_zero m)).add_odd odd_one
  have hodd2 := odd_prod_pow_sub_one (hq.pow_of_ne_zero two_ne_zero) m
  refine factorization_two_of_int_eq (U := ((Nat.card K : ℤ) ^ (m + 1) - ε) *
      ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1)) ?_ (hodd1.mul hodd2)
    Nat.card_pos
  rw [hcard, hK]
  push_cast
  ring

theorem card_orthogonalGroup_eq_two_mul {R : QuadraticForm K W}
    (hR : (polarBilin R).Nondegenerate)
    (hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) = Nat.card (orthDerived R) * 2 := by
  have : Nontrivial W := by
    obtain ⟨U, hU3, -⟩ := hT
    exact Module.nontrivial_of_finrank_pos (R := K)
      (lt_of_lt_of_le (by norm_num : 0 < 3) (hU3 ▸ Submodule.finrank_le U))
  have hΩ : CFSG.RankThree.OrthogonalInvolutions.omegaGroup R hR = orthDerived R :=
    le_antisymm (CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT)
      (CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup hR)
  have hidx := CFSG.RankThree.OrthogonalInvolutions.relIndex_omegaGroup R hR
  rw [hΩ, Subgroup.relIndex] at hidx
  have hle : orthDerived R ≤ TauCeti.QuadraticMap.orthogonalGroup R :=
    Subgroup.commutator_le_self _
  rw [← Subgroup.card_mul_index ((orthDerived R).subgroupOf
    (TauCeti.QuadraticMap.orthogonalGroup R)), hidx,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]

theorem factorization_two_card_orthDerived {R : QuadraticForm K W}
    (hR : (polarBilin R).Nondegenerate)
    (hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0) {m f : ℕ}
    (hdim : finrank K W = 2 * (m + 1)) (hK : Nat.card K = 2 ^ f) :
    (Nat.card (orthDerived R)).factorization 2 = f * (m * (m + 1)) := by
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) := Finite.of_injective (fun e : W ≃ₗ[K] W => (e : W → W))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have h1 := factorization_two_card_orthogonalGroup hR hdim hK
  rw [card_orthogonalGroup_eq_two_mul hR hT, Nat.factorization_mul Nat.card_pos.ne' two_ne_zero,
    Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_two] at h1
  omega

end Orders

section Components

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_exp (hK : Nat.card K = 2 ∨ Nat.card K = 8) :
    ∃ f : ℕ, (f = 1 ∨ f = 3) ∧ Nat.card K = 2 ^ f := by
  rcases hK with h | h
  · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
  · exact ⟨3, Or.inr rfl, by rw [h]; norm_num⟩

theorem exists_fixedFactors' {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
      (∀ i, CFSG.IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal) ∧
      (FixedLayerListed Q x → ⨆ i, F i = supportedFixedDerived Q x) ∧
      (¬ FixedLayerListed Q x → n = 0) ∧
      (∀ i, finrank K (fixedSpace x) ≤ 4 ∨ F i = supportedFixedDerived Q x) := by
  by_cases hlist : FixedLayerListed Q x
  · have hQW := hx.polarBilin_fixed_nondegenerate
    by_cases hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
        ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0
    · refine ⟨1, fun _ => supportedFixedDerived Q x, fun _ =>
        ⟨hx.isQuasisimple_supportedFixedDerived hT, le_rfl, ?_⟩, fun _ => iSup_const,
        fun h => absurd hlist h, fun _ => Or.inr rfl⟩
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    · obtain ⟨-, h2⟩ := orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype) hQW
        hlist.1
      obtain ⟨n, F, -, -, hsup, hF, -, -⟩ := hx.exists_supported_factors (h2 hlist.2)
      refine ⟨n, F, hF, fun _ => hsup, fun h => absurd hlist h, fun i => ?_⟩
      by_cases h4 : finrank K (fixedSpace x) ≤ 4
      · exact Or.inl h4
      right
      obtain ⟨s, hs⟩ := hx.even_finrank_fixed
      have h6 : finrank K (fixedSpace x) = 6 := by
        by_contra h6
        obtain ⟨m, hm⟩ : ∃ m, s = m ∧ 4 ≤ m := ⟨s, rfl, by omega⟩
        exact hT (exists_threeSingular_of_dim _ hQW hm.2 (by omega))
      have hts : ∀ U : Submodule K (fixedSpace x), finrank K U = 3 →
          ∃ u ∈ U, (Q.comp (fixedSpace x).subtype) u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hT ⟨U, hU, hcon⟩
      obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, -, -, -, -, -, -⟩ :=
        even_minus_six_actual_derived_extraction _ hQW h6 hts
      have hsimpΩ : IsSimpleGroup ↥(orthDerived (Q.comp (fixedSpace x).subtype)) := by
        have he : orthDerived (Q.comp (fixedSpace x).subtype) = ρ.range := hcomm
        rw [he]
        exact hsimple
      obtain ⟨hFq, hFle, hFn⟩ := hF i
      let e := supportedFixedDerivedEquiv hx
      let A : Subgroup ↥(supportedFixedDerived Q x) := (F i).subgroupOf (supportedFixedDerived Q x)
      have hAn : (A.map e.toMonoidHom).Normal := hFn.map e.toMonoidHom e.surjective
      haveI := hAn
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (A.map e.toMonoidHom) with hb | ht
      · exfalso
        have hAb : A = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hb
        have hFb : F i = ⊥ := by
          rw [eq_bot_iff]
          intro g hg
          have h1 : (⟨g, hFle hg⟩ : ↥(supportedFixedDerived Q x)) ∈ A := hg
          rw [hAb, Subgroup.mem_bot] at h1
          rw [Subgroup.mem_bot]
          exact congrArg Subtype.val h1
        have := CFSG.LocalCores.isQuasisimple_nontrivial hFq
        rw [hFb] at this
        exact (Subgroup.nontrivial_iff_ne_bot _).mp this rfl
      · have hAt : A = ⊤ := by
          rw [← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at ht
          exact Subgroup.map_injective e.injective ht
        refine le_antisymm hFle fun g hg => ?_
        have h1 : (⟨g, hg⟩ : ↥(supportedFixedDerived Q x)) ∈ A := hAt ▸ Subgroup.mem_top _
        exact h1
  · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun h => absurd h hlist, fun _ => rfl,
      fun i => i.elim0⟩

theorem eq_one_of_commute_specialBlock {p : ℕ} {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) {g : V ≃ₗ[K] V} (hg : g ∈ specialBlock Q x h)
    (hc : ∀ g' ∈ specialBlock Q x h, g * g' = g' * g) (hg2 : g ^ 2 = 1) : g = 1 := by
  obtain ⟨c, hcw⟩ := orth2_exists_smul_of_commute_specialBlock hx hp2 hh hne1 hself hm
    (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer h hg)).2 hc
  have h2 : (2 : AdjoinRoot h) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot h)) 2, CharTwo.two_eq_zero, map_zero]
  have hcc : ∀ w : primaryComponent x.toLinearMap h, (c * c) • w = w := fun w => by
    apply Subtype.ext
    have h1 : g (g (w : V)) = (w : V) := by
      have h0 : (g ^ 2) (w : V) = (w : V) := by
        rw [hg2]
        rfl
      rwa [pow_two, LinearEquiv.mul_apply] at h0
    rw [hcw w, hcw (c • w), smul_smul] at h1
    exact h1
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp
    (primaryComponent_ne_bot hx.squarefree_minpoly hh)
  have hc2 : c * c = 1 := by
    by_contra hne
    have hu : c * c - 1 ≠ 0 := sub_ne_zero.mpr hne
    apply hw0
    have h3 : (c * c - 1) • (⟨w, hw⟩ : primaryComponent x.toLinearMap h) = 0 := by
      rw [sub_smul, hcc, one_smul, sub_self]
    have h4 := congrArg (fun v => (c * c - 1)⁻¹ • v) h3
    simp only [smul_smul, inv_mul_cancel₀ hu, one_smul, smul_zero] at h4
    exact congrArg Subtype.val h4
  have hc1 : c = 1 := by
    have h5 : (c - 1) * (c - 1) = 0 := by
      have h6 : (c - 1) * (c - 1) = c * c + 1 - 2 * c := by ring
      rw [h6, hc2, one_add_one_eq_two, h2, zero_mul, sub_zero]
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h5)
  have hs : g ∈ supportedBlock Q x h := specialBlock_le_supportedBlock h hg
  have hb : blockGL Q x h ⟨g, hs⟩ = 1 := by
    refine Units.ext (LinearMap.ext fun w => Subtype.ext ?_)
    rw [coe_blockGL]
    show g (w : V) = (w : V)
    rw [hcw w, hc1, one_smul]
  exact congrArg Subtype.val (hx.eq_one_of_blockGL_eq_one hh hb)

theorem odd_card_center_specialBlock_phi {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) :
    Odd (Nat.card (Subgroup.center ↥(specialBlock Q x (X ^ 2 + X + 1)))) := by
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hmem⟩
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  refine odd_card_center_of_sq fun z hz hz2 => Subtype.ext ?_
  refine eq_one_of_commute_specialBlock hx ⟨1, rfl⟩ hmem phi_ne (reciprocal_cyc3 K).symm hm z.2
    (fun g' hg' => ?_) (by simpa using congrArg Subtype.val hz2)
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g', hg'⟩)).symm

theorem factorization_two_card_specialBlock {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q 3 x)
    (hmem : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors x.toLinearMap) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) :
    (Nat.card (specialBlock Q x (X ^ 2 + X + 1))).factorization 2 =
      f * (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) *
        (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) - 1) / 2) := by
  have hirr := irreducible_of_mem_primaryFactors hmem
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨hirr⟩
  obtain ⟨d, ℓ, f', hU, B, -, hq, hBsymm, hBl, hrange⟩ :=
    orth2_exists_unitary_model hx ⟨1, rfl⟩ hmem phi_ne (reciprocal_cyc3 K).symm
  have e₁ : ↥(specialBlock Q x (X ^ 2 + X + 1)) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hmem)).trans
      (MulEquiv.subgroupCongr hrange)
  obtain ⟨-, -, -, -, -, -, h2⟩ := CFSG.LinearGroups.unitary_full_group_order hU hBsymm hBl
    (n := primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1)) rfl
    (hx.primaryMultiplicity_pos hmem)
  have hℓ : ℓ = 2 := by
    have hf' : f' ≠ 0 := by
      rintro rfl
      have := hU.one_le
      rw [zero_mul] at this
      omega
    have h1 : ℓ ∣ 2 ^ f := by
      rw [← hK, hq]
      exact dvd_pow_self ℓ hf'
    exact (Nat.prime_dvd_prime_iff_eq hU.prime Nat.prime_two).mp (hU.prime.dvd_of_dvd_pow h1)
  subst hℓ
  have : Module.Finite K (AdjoinRoot (X ^ 2 + X + 1 : K[X])) :=
    (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have hcardE : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : K[X])) = Nat.card K ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), (AdjoinRoot.powerBasis hirr.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim, monic_phi.2]
  have hqf : f' * d = f := by
    have h1 := hU.card
    rw [hcardE, hK, ← pow_mul] at h1
    have := Nat.pow_right_injective le_rfl h1
    omega
  have h3 : 2 ^ (Nat.card ↥(sesqSpecialUnitaryGroup B)).factorization 2 =
      2 ^ (f * (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) *
        (primaryMultiplicity x.toLinearMap (X ^ 2 + X + 1) - 1) / 2)) := by
    rw [h2, ← hqf, ← pow_mul]
  rw [Nat.card_congr e₁.toEquiv]
  exact Nat.pow_right_injective le_rfl h3

theorem card_fixedFactor_ne [Nontrivial V] (hQ : (polarBilin Q).Nondegenerate) {f : ℕ}
    (hKf : Nat.card K = 2 ^ f) (hf : f = 1 ∨ f = 3) {p : ℕ} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q p x) {F : Subgroup (V ≃ₗ[K] V)}
    (hFle : F ≤ supportedFixedDerived Q x)
    (hF : finrank K (fixedSpace x) ≤ 4 ∨ F = supportedFixedDerived Q x) :
    Nat.card (↥((F.subgroupOf (orthDerived Q)).map (piOrth Q)) ⧸
      Subgroup.center ↥((F.subgroupOf (orthDerived Q)).map (piOrth Q))) ≠ 5515776 := by
  intro hc
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (fixedSpace x ≃ₗ[K] fixedSpace x) :=
    Finite.of_injective (fun e : fixedSpace x ≃ₗ[K] fixedSpace x => (e : fixedSpace x → _))
      fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  set L := (F.subgroupOf (orthDerived Q)).map (piOrth Q) with hL
  set R := Q.comp (fixedSpace x).subtype with hRdef
  have hR : (polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  have hFΩ : F ≤ orthDerived Q := hFle.trans hx.supportedFixedDerived_le_orthDerived
  let eL : ↥L ≃* ↥F :=
    (Subgroup.equivMapOfInjective _ (piOrth Q) (piOrth_injective hQ)).symm.trans
      (Subgroup.subgroupOfEquivOfLe hFΩ)
  have hLc : Nat.card ↥L = 5515776 * Nat.card (Subgroup.center ↥L) := by
    rw [← hc]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hFW : Nat.card ↥(supportedFixedDerived Q x) = Nat.card ↥(orthDerived R) :=
    Nat.card_congr (supportedFixedDerivedEquiv hx).toEquiv
  have hle : orthDerived R ≤ TauCeti.QuadraticMap.orthogonalGroup R :=
    Subgroup.commutator_le_self _
  obtain ⟨s, hs⟩ := hx.even_finrank_fixed
  by_cases h4 : finrank K (fixedSpace x) ≤ 4
  · have h9 : 2 ^ 9 ∣ Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) := by
      have h1 : 2 ^ 9 ∣ Nat.card ↥L := by
        rw [hLc]
        exact Dvd.dvd.mul_right (by norm_num) _
      rw [Nat.card_congr eL.toEquiv] at h1
      have h2 := Subgroup.card_dvd_of_le hFle
      rw [hFW] at h2
      exact h1.trans (h2.trans (Subgroup.card_dvd_of_le hle))
    have h9' := (Nat.prime_two.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h9
    rcases (show s = 0 ∨ s = 1 ∨ s = 2 by omega) with hs0 | hs1 | hs2
    · have : Subsingleton (fixedSpace x) := (Module.finrank_zero_iff (R := K)).mp (by omega)
      have h1 : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup R) = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (LinearEquiv.ext fun w =>
          Subsingleton.elim _ _)⟩, ⟨1⟩⟩
      rw [h1] at h9
      norm_num at h9
    · rw [factorization_two_card_orthogonalGroup hR (m := 0) (by omega) hKf] at h9'
      omega
    · rw [factorization_two_card_orthogonalGroup hR (m := 1) (by omega) hKf] at h9'
      rcases hf with rfl | rfl <;> omega
  · have hFe : F = supportedFixedDerived Q x := hF.resolve_left h4
    have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
    let eLW : ↥L ≃* ↥(orthDerived R) :=
      eL.trans ((MulEquiv.subgroupCongr hFe).trans (supportedFixedDerivedEquiv hx))
    have hLF : Nat.card ↥L = Nat.card ↥(orthDerived R) := Nat.card_congr eLW.toEquiv
    have hZ : Nat.card (Subgroup.center ↥L) = Nat.card (Subgroup.center ↥(orthDerived R)) :=
      Nat.card_congr (Subgroup.centerCongr eLW).toEquiv
    by_cases hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧ ∀ u ∈ U, R u = 0
    · rw [hZ, center_orthDerived_eq_bot hR hT, Subgroup.card_bot, mul_one, hLF] at hLc
      obtain ⟨m, hm⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
      have h1 := factorization_two_card_orthDerived hR hT (m := m) (by omega) hKf
      rw [hLc, factorization_two_su38] at h1
      have he : Even (f * (m * (m + 1))) := (Nat.even_mul_succ_self m).mul_left f
      rw [← h1] at he
      exact (by decide : ¬ Even 9) he
    · have h6 : finrank K (fixedSpace x) = 6 := by
        by_contra h6
        exact hT (exists_threeSingular_of_dim R hR (m := s) (by omega) (by omega))
      have hts : ∀ U : Submodule K (fixedSpace x), finrank K U = 3 → ∃ u ∈ U, R u ≠ 0 := by
        intro U hU
        by_contra hcon
        push Not at hcon
        exact hT ⟨U, hU, hcon⟩
      obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hsimple, -, hnab, hcardρ, -, -, -⟩ :=
        even_minus_six_actual_derived_extraction R hR h6 hts
      have he : orthDerived R = ρ.range := hcomm
      haveI := hsimple
      have hZ1 : Nat.card (Subgroup.center ↥ρ.range) = 1 := by
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥ρ.range) with hb | ht
        · rw [hb]
          exact Subgroup.card_bot
        · refine absurd (fun a b => ?_) hnab
          have hb : b ∈ Subgroup.center ↥ρ.range := by
            rw [ht]
            exact Subgroup.mem_top b
          exact Subgroup.mem_center_iff.mp hb a
      rw [hZ, he, hZ1, mul_one, hLF, he, hcardρ, hKf] at hLc
      rcases hf with rfl | rfl <;> norm_num at hLc

theorem eq_componentImage_of_card (hK : Nat.card K = 2 ∨ Nat.card K = 8)
    (hQ : (polarBilin Q).Nondegenerate) (x : orthDerived Q) (hx3 : orderOf x = 3)
    {L : Subgroup (ProjOrthDerived Q)}
    (hL : CFSG.Open.IsComponentOf L
      (Subgroup.centralizer ({piOrth Q x} : Set (ProjOrthDerived Q))))
    (hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 5515776) :
    Nat.card K = 8 ∧ (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (x : V ≃ₗ[K] V).toLinearMap ∧
      primaryMultiplicity (x : V ≃ₗ[K] V).toLinearMap (X ^ 2 + X + 1) = 3 ∧
      L = componentImage Q (x : V ≃ₗ[K] V) (X ^ 2 + X + 1) := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hpl : (3 : ℕ) ≠ ringChar K := by
    rw [ringChar.eq K 2]
    norm_num
  have hx := oddOrderIsometry_of_orthDerived Nat.prime_three hpl hQ x hx3
  have : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    haveI := hV
    have h1 : x = 1 := Subtype.ext (LinearEquiv.ext fun v => Subsingleton.elim _ _)
    rw [h1, orderOf_one] at hx3
    omega
  obtain ⟨f, hf, hKf⟩ := exists_exp hK
  have hpq : 3 ∣ Nat.card K + 1 := by
    rcases hK with h | h <;> rw [h] <;> norm_num
  rw [← centralizerImage_eq hQ x] at hL
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  set xe : V ≃ₗ[K] V := (x : V ≃ₗ[K] V) with hxe
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) with hρ
  set N : Subgroup (ProjOrthDerived Q) := centralizerImage Q xe with hN
  obtain ⟨n, F, hFq, hFsup, hFn0, hFix⟩ := exists_fixedFactors' hx
  have hFΩ : ∀ i, F i ≤ orthDerived Q := fun i =>
    (hFq i).2.1.trans hx.supportedFixedDerived_le_orthDerived
  set C : Fin n → Subgroup (ProjOrthDerived Q) := fun i => ((F i).subgroupOf (orthDerived Q)).map ρ
    with hC
  have hCsup : (⨆ i, C i) = fixedLayerImage Q xe := by
    by_cases hlist : FixedLayerListed Q xe
    · rw [fixedLayerImage_of_listed hlist]
      unfold fixedComponentImage
      rw [← hFsup hlist, subgroupOf_iSup_of_le F _ hFΩ, Subgroup.map_iSup]
    · have hn := hFn0 hlist
      subst hn
      simp [fixedLayerImage, hlist]
  have hCle : ∀ i, C i ≤ fixedComponentImage Q xe := fun i =>
    Subgroup.map_mono fun g hg => Subgroup.mem_subgroupOf.mpr
      ((hFq i).2.1 (Subgroup.mem_subgroupOf.mp hg))
  have hCcomp : ∀ i, CFSG.Open.IsComponentOf (C i) N := by
    intro i
    have hconj := map_conj_mem ρ (F := (F i).subgroupOf (orthDerived Q))
      (F' := (supportedFixedDerived Q xe).subgroupOf (orthDerived Q)) (fun h k hh hk => by
        have := (Subgroup.normal_subgroupOf_iff (hFq i).2.1).mp (hFq i).2.2 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this)
    refine isComponentOf_of_normal_normal (hCle i) fixedComponentImage_le_centralizerImage ?_
      hx.normal_fixedComponentImage (isQuasisimple_map_projective (hFΩ i) (hFq i).1)
    rw [Subgroup.normal_subgroupOf_iff (hCle i)]
    intro h k hh hk
    exact hconj _ _ hh hk
  let ι₁ := {r : ↥Rep // r.1 ≠ X - 1 ∧ CFSG.IsQuasisimple ↥(specialBlock Q xe r.1)}
  have hspecΩ : ∀ r : ι₁, specialBlock Q xe r.1.1 ≤ orthDerived Q := fun r =>
    specialBlock_le_orthDerived_of_perfect r.2.2.1
      ((specialBlock_le_isometryCentralizer r.1.1).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))
  let S : ι₁ → Subgroup (ProjOrthDerived Q) := fun r => componentImage Q xe r.1.1
  have hScomp : ∀ r, CFSG.Open.IsComponentOf (S r) N := fun r =>
    isComponentOf_of_normal_normal componentImage_le_centralizerImage le_rfl normal_componentImage
      (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top)
      (isQuasisimple_map_projective (hspecΩ r) r.2.2)
  set EN : Subgroup (ProjOrthDerived Q) := (⨆ r, S r) ⊔ fixedLayerImage Q xe with hEN
  have hSN : ∀ r, S r ≤ N := fun r => componentImage_le_centralizerImage
  have hENN : EN ≤ N := sup_le (iSup_le hSN) fixedLayerImage_le_centralizerImage
  have hENnormal : (EN.subgroupOf N).Normal :=
    normal_subgroupOf_sup (iSup_le hSN) fixedLayerImage_le_centralizerImage
      (normal_subgroupOf_iSup S hSN fun r => normal_componentImage) hx.normal_fixedLayerImage
  have hENn : ∀ c ∈ N, ∀ e ∈ EN, c * e * c⁻¹ ∈ EN := fun c hc e he =>
    (Subgroup.normal_subgroupOf_iff hENN).mp hENnormal e c he hc
  have hperf : ∀ P : Subgroup (ProjOrthDerived Q), P ≤ N → commutator ↥P = ⊤ → P ≤ EN := by
    intro P hPN hP
    obtain ⟨S₀, hS₀N, hS₀sol, hcomm⟩ := exists_solvable_comm_le hQ Nat.prime_three
      (by norm_num) x hx hRep EN
      (fun h hh hne hq => le_sup_of_le_left (le_iSup S (⟨⟨h, hh⟩, hne, hq⟩ : ι₁)))
      (fun hlist => by
        rw [← fixedLayerImage_of_listed hlist]
        exact le_sup_right)
    haveI := hS₀sol
    exact perfect_le_of_le_sup_solvable hENN hS₀N hENn hcomm hPN (Subgroup.isPerfect_iff.1 ⟨hP⟩)
  let Fm : ι₁ ⊕ Fin n → Subgroup (ProjOrthDerived Q) := Sum.elim S C
  have hFm : ∀ i, CFSG.Open.IsComponentOf (Fm i) N := by
    rintro (r | i)
    · exact hScomp r
    · exact hCcomp i
  have hiSup : (⨆ i, Fm i) = EN := by
    rw [iSup_sum]
    simp only [Fm, Sum.elim_inl, Sum.elim_inr]
    rw [hCsup]
  obtain ⟨i, rfl⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.component_mem_named_factors
    Fm hFm (fun P hPN hP => hiSup ▸ hperf P hPN hP) hL
  rcases i with ⟨⟨h, hh⟩, hne, hq⟩ | i
  · have hh' : h ∈ primaryFactors xe.toLinearMap := hRep.1 hh
    obtain rfl : h = X ^ 2 + X + 1 := eq_phi hx hpq hh' hne
    haveI : Fact (Irreducible (X ^ 2 + X + 1 : K[X])) := ⟨irreducible_of_mem_primaryFactors hh'⟩
    have hm2 : 2 ≤ primaryMultiplicity xe.toLinearMap (X ^ 2 + X + 1) := by
      have h1 := hx.primaryMultiplicity_pos hh'
      by_contra hlt
      have hbot := hx.specialBlock_eq_bot_of_finrank_eq_one hh' (by omega)
      have hnt := CFSG.LocalCores.isQuasisimple_nontrivial hq
      rw [hbot] at hnt
      exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt rfl
    have hsΩ := hspecΩ ⟨⟨X ^ 2 + X + 1, hh⟩, hne, hq⟩
    let eL : ↥(componentImage Q xe (X ^ 2 + X + 1)) ≃* ↥(specialBlock Q xe (X ^ 2 + X + 1)) :=
      (Subgroup.equivMapOfInjective _ (piOrth Q) (piOrth_injective hQ)).symm.trans
        (Subgroup.subgroupOfEquivOfLe hsΩ)
    have hZ : Odd (Nat.card (Subgroup.center ↥(componentImage Q xe (X ^ 2 + X + 1)))) := by
      rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv]
      exact odd_card_center_specialBlock_phi hx hh' hm2
    have hcard' : Nat.card (↥(componentImage Q xe (X ^ 2 + X + 1)) ⧸
        Subgroup.center ↥(componentImage Q xe (X ^ 2 + X + 1))) = 5515776 := hcard
    have h9 := factorization_two_card_of_odd_center hZ
    rw [hcard', factorization_two_su38, Nat.card_congr eL.toEquiv,
      factorization_two_card_specialBlock hx hh' hKf] at h9
    obtain ⟨hf3, hm3⟩ := eq_three_of_mul_choose_two hf hm2 h9
    subst hf3
    exact ⟨by rw [hKf]; norm_num, hh', hm3, rfl⟩
  · exact absurd hcard (card_fixedFactor_ne hQ hKf hf hx (hFq i).2.1 (hFix i))

end Components

end CFSG.HardMathSupport.Dickson.Bal207.OrthFix

end
