module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUniPairs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResUniWeir
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResPairDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleTowerUnitaryFinal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.LieType.SeitzGeneration (RankLE2 HasThreeIndep)
open CFSG.Open (IsElemAbelian StatedProj StatedSU)

section Transfer

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem primeFormP_mulEquiv_statedProj (hU : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    (hq : ¬ (n = 3 ∧ ℓ ^ f = 2)) :
    Nonempty (primeFormP hU (idCn n K) ≃* StatedProj (StatedSU n (ℓ ^ f) K)) := by
  obtain ⟨⟨eT⟩, -⟩ := unitary_prime_form_full_semilinear_realization hU
    (isPrimeFormGram_one (n := n)) hn hq
  exact ⟨eT.trans (unitaryPSUEquiv hU (by omega))⟩

theorem dvd_card_gramSU_of_pow_neg_eq_one (hU : UnitaryFieldData ℓ f K) {p e : ℕ} (he : 2 ≤ e)
    (h : (-((ℓ ^ f : ℕ) : ZMod p)) ^ e = 1) :
    p ∣ Nat.card (gramSU hU (1 : Matrix (Fin e) (Fin e) K)) := by
  refine dvd_card_gramSU_one hU he (Or.inl ?_)
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_pow, Int.cast_natCast, Int.cast_neg, Int.cast_one]
  generalize ((ℓ ^ f : ℕ) : ZMod p) = q' at h ⊢
  rcases Nat.even_or_odd e with hev | hod
  · rw [hev.neg_one_pow]
    rw [hev.neg_pow] at h
    rw [h, sub_self]
  · rw [hod.neg_one_pow]
    rw [hod.neg_pow] at h
    have h' : q' ^ e = -1 := by
      have := congrArg Neg.neg h
      simpa using this
    rw [h', sub_neg_eq_add, neg_add_cancel]

end Transfer

theorem unitary_outer_fixesPair {ℓ f n : ℕ} {K : Type} [Field K] (hU : UnitaryFieldData ℓ f K)
    (hn : 3 ≤ n) (hq : ¬ (n = 3 ∧ ℓ ^ f = 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) (hnp : ¬ (n = 3 ∧ p = 3))
    (hle : RankLE2 p (primeFormP hU (idCn n K)))
    (hge : ∃ E : Subgroup (primeFormP hU (idCn n K)), IsElemAbelian p E ∧ Nat.card E = p ^ 2)
    {α : MulAut (primeFormP hU (idCn n K))} (hα : α ∉ inner (primeFormP hU (idCn n K)))
    (hαp : α ^ p = 1) : FixesIndepPair p α := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := hU.finite
  have hC1 : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one' (n := n)
  have hα1 : α ≠ 1 := fun h => hα (h ▸ (inner (primeFormP hU (idCn n K))).one_mem)
  have hao : orderOf α = p := orderOf_eq_prime hαp hα1
  have hThree : p ∣ ℓ ^ f + 1 → 5 ≤ n → False := by
    intro hpq h5
    obtain ⟨eS⟩ := primeFormP_mulEquiv_statedProj hU hn hq
    exact hasThreeIndep_false_of_rankLE2 hp
      (HasThreeIndep.of_mulEquiv eS.symm
        (CFSG.LieType.SeitzGeneration.hasThreeIndep_psu hU h5 hp hpq)) hle
  have hpn : n < 5 → ¬ p ∣ n := by
    intro h5 hd
    have : n = 3 ∨ n = 4 := by omega
    rcases this with rfl | rfl
    · exact hnp ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd⟩
    · have h4 : p ∣ 2 ^ 2 := by simpa using hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  by_cases hD : α ∈ primeFormD hU (idCn n K)
  ·
    exfalso
    have hpq := dvd_of_mem_primeFormD_not_inner hU hp hD hα hαp
    have hdn : p ∣ n := by
      by_contra hpn'
      exact hα (mem_inner_of_mem_primeFormD_of_not_dvd hU hn hp hpn' hD hαp)
    by_cases h5 : 5 ≤ n
    · exact hThree hpq h5
    · exact hpn (by omega) hdn
  ·
    have hker := ker_primeFormFieldFactor hU hC1 hn hq
    set σ : K ≃+* K := primeFormFieldFactor hU hC1 hn hq α with hσdef
    have hσ1 : σ ≠ 1 := fun h => hD (by
      rw [← hker]
      exact h)
    have hσp : σ ^ p = 1 := by rw [hσdef, ← map_pow, hαp, map_one]
    have hσo : orderOf σ = p := orderOf_eq_prime hσp hσ1
    obtain ⟨-, -, -, -, -, M, hM⟩ :=
      CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' hU hn hq hp hp2
        α hao σ rfl hσo
    have hpair : FixesIndepPair p (primeFormFieldHom hU hC1 σ) := by
      by_cases hpq : p ∣ ℓ ^ f + 1
      · by_cases h5 : 5 ≤ n
        · exact (hThree hpq h5).elim
        · obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ :=
            exists_two_indep_fixed_diag_unitary hU hp hn (hpn (by omega)) hpq hσp
          exact ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩
      · obtain ⟨E, hE, hEc⟩ := hge
        have h2e := two_mul_orderOf_le_of_elemAbelian_unitary hU hn hq hp hp2 hpℓ hpq hE hEc
        have hq0 : ((ℓ ^ f : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hd
          exact hpℓ ((Nat.prime_dvd_prime_iff_eq hp hU.prime).1 (hp.dvd_of_dvd_pow hd))
        have hpos : 0 < orderOf (-((ℓ ^ f : ℕ) : ZMod p)) :=
          orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2
            ⟨p - 1, by have := hp.two_le; omega,
              ZMod.pow_card_sub_one_eq_one (neg_ne_zero.2 hq0)⟩)
        have hne1 : orderOf (-((ℓ ^ f : ℕ) : ZMod p)) ≠ 1 := by
          intro h1
          have h2 : -((ℓ ^ f : ℕ) : ZMod p) = 1 := orderOf_eq_one_iff.1 h1
          apply hpq
          rw [← ZMod.natCast_eq_zero_iff]
          push_cast at h2 ⊢
          linear_combination -h2
        have he2 : 2 ≤ orderOf (-((ℓ ^ f : ℕ) : ZMod p)) := by omega
        have hdvd := dvd_card_gramSU_of_pow_neg_eq_one hU he2
          (pow_orderOf_eq_one (-((ℓ ^ f : ℕ) : ZMod p)))
        obtain ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩ :=
          exists_two_indep_fixed_unitary hU hp hpq hdvd h2e (by omega) σ hσp
        exact ⟨x₁, x₂, hc, h1, h2, hi, hf1, hf2⟩
    have hah : α = primeFormConjHom hU (idCn n K) M * primeFormFieldHom hU hC1 σ *
        (primeFormConjHom hU (idCn n K) M)⁻¹ := by
      calc α = primeFormConjHom hU (idCn n K) M *
            ((primeFormConjHom hU (idCn n K) M)⁻¹ * α * primeFormConjHom hU (idCn n K) M) *
            (primeFormConjHom hU (idCn n K) M)⁻¹ := by group
        _ = _ := by rw [hM]
    rw [hah]
    exact hpair.map _

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
