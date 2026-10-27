module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedE6Adjoint
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderPSU
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.CatLeaf (lieOrderNumerator lieOrderDivisor)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem ordF4_eq_lieOrderNumerator (q : ℕ) :
    CFSG.Open.ordF4 q = lieOrderNumerator .F4 0 q := rfl

section


theorem card_entrywiseFixedGroup_F4_dvd {M : Type} [Field M] [Finite M] (σ : M ≃+* M)
    {q₀ : ℕ} (hq₀ : Nat.card (fixSubfield σ) = q₀) :
    Nat.card (entrywiseFixedGroup Tag.F4 σ) ∣ lieOrderNumerator .F4 0 q₀ := by
  set Γ := entrywiseFixedGroup Tag.F4 σ with hΓ
  set J := fixedFieldImage Tag.F4 σ with hJ
  set Jg := J.subgroupOf Γ with hJg
  have h1 : Nat.card Jg * Jg.index = Nat.card Γ := Subgroup.card_mul_index Jg
  have h2 : Nat.card Jg = Nat.card J :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe fixedFieldImage_le).toEquiv
  have h3 : Nat.card J = Nat.card (adjointGroup Tag.F4 (fixSubfield σ)) :=
    (Nat.card_congr (fixedFieldImageEquiv (τ := Tag.F4) σ).toEquiv).symm
  have h4 : Nat.card (adjointGroup Tag.F4 (fixSubfield σ)) = CFSG.Open.ordF4 q₀ := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, hq₀]
  obtain ⟨hd1, -⟩ := fixedFieldImage_index_dvd_card (τ := Tag.F4) σ
  have hdet : Tag.F4.cartan.det.natAbs = 1 := by
    rw [det_cartan_F4]
    rfl
  rw [hdet] at hd1
  have hidx : Jg.index = 1 := Nat.dvd_one.1 hd1
  rw [← h1, h2, h3, h4, hidx, mul_one, ordF4_eq_lieOrderNumerator]

theorem even_F4_odd_prime_field_descent
    {f p : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup ReeTag.F4.tag K)) (hα'p : orderOf α = p)
    (hα : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range) :
    ∃ (σ : K ≃+* K) (ψ : MulAut (adjointGroup ReeTag.F4.tag K)),
      orderOf σ = p ∧ ψ * α * ψ⁻¹ = entrywiseAdjointAut ReeTag.F4.tag σ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : NeZero (2 * f) := ⟨by omega⟩
  have hα'pow : α ^ p = 1 := by
    rw [← hα'p]
    exact pow_orderOf_eq_one α
  obtain ⟨-, hNF, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨x, a'⟩, hxa', -⟩ := hNF α
  have ha : (a' : ℕ) < 2 * f := a'.isLt
  have hxa : α = MulAut.conj x * ReeTag.F4.finiteExceptionalAut K ^ (a' : ℕ) := hxa'
  generalize (a' : ℕ) = a at ha hxa
  have hΘα : Θ α = Multiplicative.ofAdd (a : ZMod (2 * f)) := hΘ α x a hxa
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hα
    rw [hxa, pow_zero, mul_one]
    exact ⟨x, rfl⟩
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
  have ha2 : a / 2 = d * j := by
    rw [hj, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  obtain ⟨fr, hfr, hord, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  set T := fr ^ d with hTdef
  have hT : ∀ c, T c = c ^ 2 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hTord : orderOf T = p := by
    rw [hTdef, orderOf_pow_of_dvd (by omega) (by rw [hord, ← hdp]; exact Dvd.intro p rfl), hord,
      ← hdp, Nat.mul_div_cancel_left p hd0]
  obtain ⟨r, hr⟩ := exists_mul_mod_eq_one hp hj0 hjp
  obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF (α ^ r)
  dsimp only at hyk
  have hk2d : (k : ℕ) = 2 * d := by
    have h1 : Θ (α ^ r) = Multiplicative.ofAdd (((k : ℕ) : ZMod (2 * f))) := hΘ _ y k hyk
    rw [map_pow, hΘα, ← ofAdd_nsmul, nsmul_eq_mul, ← Nat.cast_mul] at h1
    have h2 := (ZMod.natCast_eq_natCast_iff' _ _ _).1 (Multiplicative.ofAdd.injective h1)
    have ht : r * a = 2 * d + 2 * f * (r * j / p) := by
      have h3 := Nat.div_add_mod (r * j) p
      rw [hr] at h3
      rw [hj, hd]
      calc r * (2 * d * j) = 2 * d * (r * j) := by ring
        _ = 2 * d * (p * (r * j / p) + 1) := by rw [h3]
        _ = 2 * d + 2 * (p * d) * (r * j / p) := by ring
    have h2d2f : 2 * d < 2 * f := by
      have : d < f := by rw [← hdp]; exact lt_mul_right hd0 hp.one_lt
      omega
    rw [ht, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2d2f, Nat.mod_eq_of_lt k.isLt] at h2
    exact h2.symm
  have hβ : α ^ r = MulAut.conj y * entrywiseAdjointAut ReeTag.F4.tag T := by
    rw [hyk, hk2d, finiteExceptionalAut_pow_two_mul,
      ← entrywiseAdjointAut_eq_finiteFrobeniusAut_pow hT]
  have hβp : (MulAut.conj y * entrywiseAdjointAut ReeTag.F4.tag T) ^ p = 1 := by
    rw [← hβ, ← pow_mul, mul_comm, pow_mul, hα'pow, one_pow]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : MulAut (adjointGroup ReeTag.F4.tag K),
      ψ * (MulAut.conj y * entrywiseAdjointAut ReeTag.F4.tag T) * ψ⁻¹ =
        entrywiseAdjointAut ReeTag.F4.tag T := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_conj_eq_entrywiseAdjointAut ReeTag.F4.tag K hK hd0 hp.one_lt.le hdp T hT
      (AlgebraicClosure K) y hβp
  have hψα : ψ * α * ψ⁻¹ = entrywiseAdjointAut ReeTag.F4.tag (T ^ j) := by
    have hαβ : α = (α ^ r) ^ j := by rw [← pow_mul, pow_eq_self_of_mod_eq_one hα'p hr]
    rw [hαβ, ← conj_pow, hβ, hψ, ← entrywiseAdjointAut_pow]
  have hTjp : orderOf (T ^ j) = p := by
    refine orderOf_eq_prime ?_ (pow_ne_one_of_lt_orderOf hj0.ne' (by rw [hTord]; exact hjp))
    rw [← pow_mul, mul_comm, pow_mul, ← hTord, pow_orderOf_eq_one, one_pow]
  exact ⟨T ^ j, ψ, hTjp, hψα⟩

theorem outerFixedOrder_adjointF4
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup Tag.F4 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.F4 K)) :
    ∃ f₀ : ℕ, f = p * f₀ ∧ Nat.card (fixedSubgroup α) ∣ lieOrderNumerator .F4 0 (ℓ ^ f₀) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have : CharP K ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup Tag.F4 K)).one_mem)
  have hαin : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range :=
    hα
  obtain ⟨σ, ψ, hσp, hψ⟩ : ∃ (σ : K ≃+* K) (ψ : MulAut (adjointGroup Tag.F4 K)),
      orderOf σ = p ∧ ψ * α * ψ⁻¹ = entrywiseAdjointAut Tag.F4 σ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact even_F4_odd_prime_field_descent hf K hK hp hp2 α hαord hαin
    · obtain ⟨-, σ, δ, hσp, -, hδ, -⟩ :=
        odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hp α hαord hαin
      exact ⟨σ, δ, hσp, hδ⟩
  obtain ⟨hpf, hcard⟩ := card_fixSubfield hℓ hf hK σ
  rw [hσp] at hpf hcard
  obtain ⟨d, hd⟩ := hpf
  have hd0 : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; have := hp.pos; omega)
  refine ⟨d, by rw [hd, mul_comm], ?_⟩
  rw [← card_fixedSubgroup_conj ψ α, hψ, card_fixedSubgroup_entrywiseAdjointAut]
  refine card_entrywiseFixedGroup_F4_dvd σ (q₀ := ℓ ^ d) ?_
  rw [hcard, hd, Nat.mul_div_cancel_left d hp.pos]

theorem outerFixedOrderBoundAt_F4 :
    CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderBoundAt .F4 := by
  intro K _ _ n ℓ f hadm hmodel _ p hp hp2 _ _ α hαp hαin
  left
  have : Fact ℓ.Prime := ⟨hadm.1⟩
  have hf : 1 ≤ f := hadm.2.1
  rcases hmodel with ⟨ht, -⟩ | ⟨hn, -, hE⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · subst hn
    obtain ⟨-, F, hF, hFin, hFcard, ⟨e⟩⟩ := hE
    let θ : K ≃* adjointGroup Tag.F4 F := e.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
    have hβout : MulAut.congr θ α ∉ inner (adjointGroup Tag.F4 F) := fun hin =>
      hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
    rw [← CFSG.HardMathSupport.Lang.Coordinator.card_fixedSubgroup_congr θ α]
    exact outerFixedOrder_adjointF4 hf F hFcard hp hp2 _ hβp hβout
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end

end CFSG.HardMathSupport.Lang.E6Descent
