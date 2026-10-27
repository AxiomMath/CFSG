module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2Descent
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenAutomorphisms

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GroupTheory
  CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section


theorem G2_form_of_normal_form {p : ℕ} (hp : p.Prime) (K : Type) [Field K]
    (hNF : ∀ α : MulAut (adjointGroup Tag.G2 K), ∃! gσ : adjointGroup Tag.G2 K × (K ≃+* K),
      ∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) = (gσ.1 : ModGL Tag.G2 K) *
        Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL Tag.G2 K) * (gσ.1 : ModGL Tag.G2 K)⁻¹)
    (Θ : MulAut (adjointGroup Tag.G2 K) →* (K ≃+* K))
    (hΘ : ∀ (α : MulAut (adjointGroup Tag.G2 K)) (g : adjointGroup Tag.G2 K) (σ : K ≃+* K),
        (∀ h : adjointGroup Tag.G2 K, (α h : ModGL Tag.G2 K) = (g : ModGL Tag.G2 K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 K) * (g : ModGL Tag.G2 K)⁻¹) →
        Θ α = σ)
    (hΘker : Θ.ker = (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range)
    (α : MulAut (adjointGroup Tag.G2 K)) (hαp : orderOf α = p) (hαinn : α ∉ inner (adjointGroup Tag.G2 K)) :
    ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α
  have hασ : α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    refine MulEquiv.ext fun u => Subtype.ext ?_
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
    exact hxσ u
  have hΘα : Θ α = σ := hΘ α x σ hxσ
  have hαpow : α ^ p = 1 := by rw [← hαp]; exact pow_orderOf_eq_one α
  have h1 : σ ^ p = 1 := by rw [← hΘα, ← map_pow, hαpow, map_one]
  have h2 : σ ≠ 1 := fun h1 => hαinn (by
    change α ∈ (MulAut.conj : adjointGroup Tag.G2 K →* MulAut (adjointGroup Tag.G2 K)).range
    rw [← hΘker, MonoidHom.mem_ker, hΘα, h1])
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨x, σ, orderOf_eq_prime h1 h2, hασ⟩

theorem G2_form_odd {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime)
    (α : MulAut (adjointGroup Tag.G2 K)) (hαp : orderOf α = p)
    (hαinn : α ∉ inner (adjointGroup Tag.G2 K)) :
    ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
  obtain ⟨hNF, Θ, hΘ, -, hΘker, -⟩ :=
    odd_F4_and_nonexceptional_G2_automorphism_normal_form hℓ hℓ2 hf K hK .G2 (Or.inr ⟨rfl, hℓ3⟩)
  exact G2_form_of_normal_form hp K hNF Θ hΘ hΘker α hαp hαinn

theorem G2_form_even {f p : ℕ} (hf : 2 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (hp : p.Prime) (α : MulAut (adjointGroup Tag.G2 K)) (hαp : orderOf α = p)
    (hαinn : α ∉ inner (adjointGroup Tag.G2 K)) :
    ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
  obtain ⟨hNF, Θ, hΘ, -, hΘker, -⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf K hK
  exact G2_form_of_normal_form hp K hNF Θ hΘ hΘker α hαp hαinn

theorem G2_form_three {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K 3] (hK : Nat.card K = 3 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K)) (hαp : orderOf α = p)
    (hαinn : α ∉ inner (adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K)) :
    ∃ (x : adjointGroup CFSG.LieType.Ree.ReeTag.G2.tag K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.G2.tag σ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K CFSG.LieType.Ree.ReeTag.G2.prime := inferInstanceAs (CharP K 3)
  have : NeZero (2 * f) := ⟨by omega⟩
  have hα'pow : α ^ p = 1 := by rw [← hαp]; exact pow_orderOf_eq_one α
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨x, k⟩, hxk, -⟩ := hNF α
  dsimp only at hxk
  set a : ℕ := (k : ℕ) with ha_def
  have ha : a < 2 * f := k.isLt
  have hΘα : Θ α = Multiplicative.ofAdd (a : ZMod (2 * f)) := hΘ α x a hxk
  have ha0 : a ≠ 0 := by
    intro h0
    apply hαinn
    rw [hxk, h0, pow_zero, mul_one]
    exact ⟨_, rfl⟩
  have hdvd : 2 * f ∣ p * a := by
    have h1 : Θ (α ^ p) = 1 := by rw [hα'pow, map_one]
    rwa [map_pow, hΘα, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at h1
  have hp2f : p ∣ 2 * f := by
    by_contra hnd
    have hcop : Nat.Coprime (2 * f) p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd).symm
    exact ha0 (Nat.eq_zero_of_dvd_of_lt (hcop.dvd_of_dvd_mul_left hdvd) ha)
  have hpf : p ∣ f :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hp2f
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; omega)
  have hdp : d * p = f := by rw [hd, mul_comm]
  have h2d : 2 * d ∣ a := by
    have h1 : p * (2 * d) ∣ p * a := by
      rw [show p * (2 * d) = 2 * f by rw [hd]; ring]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hp.pos h1
  obtain ⟨j, hj⟩ := h2d
  have hjp : j < p := by
    by_contra hjp
    have h1 : 2 * d * p ≤ 2 * d * j := Nat.mul_le_mul_left _ (not_lt.1 hjp)
    have h2 : 2 * d * p = 2 * f := by rw [hd]; ring
    omega
  have hj0 : 0 < j := Nat.pos_of_ne_zero fun h => ha0 (by rw [hj, h, mul_zero])
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_three hf hK
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ 3 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro p rfl), hord,
      ← hdp, Nat.mul_div_cancel_left p hd0]
  have hFrT : CFSG.LieType.Ree.ReeTag.G2.finiteFrobeniusAut K ^ d =
      entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.G2.tag T := by
    rw [← exactNormalAut_one_eq_finiteFrobeniusAut_pow CFSG.LieType.Ree.ReeTag.G2 (σ := T) (j := d)
      hT, FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
  have hφT : CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K ^ (2 * d) =
      entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.G2.tag T := by
    rw [finiteExceptionalAut_pow_two_mul, hFrT]
  have hTj : entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.G2.tag (T ^ j) =
      CFSG.LieType.Ree.ReeTag.G2.finiteExceptionalAut K ^ a := by
    rw [entrywiseAdjointAut_pow, ← hφT, ← pow_mul, hj]
  have hTjp : orderOf (T ^ j) = p := by
    refine orderOf_eq_prime ?_ (pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hTord]; exact hjp))
    rw [← pow_mul, mul_comm, pow_mul, ← hTord, pow_orderOf_eq_one, one_pow]
  exact ⟨x, T ^ j, hTjp, by rw [hxk, hTj]⟩

theorem outerFixedOrder_adjointG2 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (h3 : 3 ≤ ℓ ^ f)
    (K : Type) [Field K] (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup Tag.G2 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .G2 0 (ℓ ^ f₀) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.G2 K)).one_mem)
  have hform : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
      orderOf σ = p ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hf2 : 2 ≤ f := by
        by_contra h
        have : f = 1 := by omega
        subst this
        omega
      exact G2_form_even hf2 K hK hp α hαord hα
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      have : CharP K 3 := finite_field_prime_power_characteristic hℓ hf hK
      exact G2_form_three hf K hK hp hp2 α hαord hα
    · exact G2_form_odd hℓ hℓ2 hℓ3 hf K hK hp α hαord hα
  obtain ⟨x, σ, hσp, hασ⟩ := hform
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK hp α hαord x σ hσp
    hασ
  exact outerFixedOrder_G2_of_conj hℓ hf K hK hp α σ hσp δ hδ

theorem outerFixedOrderBoundAt_G2 :
    CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAt .G2 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  have hℓ : ℓ.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have h3 : 3 ≤ ℓ ^ f := hadm.2.2.2
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.G2 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.G2 F) := fun hin =>
      hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
    rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ α]
    exact outerFixedOrder_adjointG2 hℓ hf h3 F hFcard hp hp2 _ hβp hβout
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end

end CFSG.HardMathSupport.Lang.E6Descent
