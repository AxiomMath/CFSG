module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6Noninner

public noncomputable section

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.RankThree.Chevalley
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.LocalRank SteinbergBT
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.GroupTheory
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

section


theorem prime_dvd_of_diag_noninner (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ) (α : MulAut (adjointGroup τ K))
    (hαdiag : α = MulAut.conj g * rootDiagAut τ K a) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup τ K)) :
    p ∣ τ.cartan.det.natAbs ∧ p ∣ Nat.card K - 1 := by
  obtain ⟨Φ, -, hΦker, hΦcard⟩ := exists_outer_hom_E (K := K) (τ := τ) hτ
  have hmker : QuotientGroup.mk' (inner (adjointGroup τ K)) α ∈ Φ.ker := by
    rw [hΦker]
    refine ⟨a, ?_⟩
    have hc : QuotientGroup.mk' (inner (adjointGroup τ K)) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
    rw [hαdiag, map_mul, hc, one_mul]
    rfl
  have hkerq : Nat.card Φ.ker ∣ (Nat.card K - 1) ^ τ.rank := by
    rw [hΦker]
    refine (Subgroup.card_range_dvd _).trans ?_
    rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units]
  have hmp : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K)) α) ∣ p :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hαp, map_one])
  have hm3 : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K)) α) ∣ Nat.card Φ.ker :=
    Subgroup.orderOf_dvd_natCard Φ.ker hmker
  have hm1 : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K)) α) ≠ 1 := fun h1 =>
    hα ((QuotientGroup.eq_one_iff (N := inner (adjointGroup τ K)) α).1 (orderOf_eq_one_iff.1 h1))
  have hmp' : orderOf (QuotientGroup.mk' (inner (adjointGroup τ K)) α) = p :=
    ((Nat.dvd_prime hp).1 hmp).resolve_left hm1
  rw [hmp'] at hm3
  exact ⟨hm3.trans hΦcard, hp.dvd_of_dvd_pow (hm3.trans hkerq)⟩

theorem exists_conj_entrywise_of_not_innerDiag (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a) :
    ∃ (d : ℕ) (T : K ≃+* K) (r j : ℕ) (ψ : MulAut (adjointGroup τ K)), f = p * d ∧
      orderOf T = p ∧ Nat.card (fixSubfield T) = ℓ ^ d ∧ (∀ c, T c = c ^ ℓ ^ d) ∧
        orderOf (T ^ j) = p ∧ (α ^ r) ^ j = α ∧ ψ * α ^ r * ψ⁻¹ = entrywiseAdjointAut τ T := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  obtain ⟨d, T, r, j, ψ, hd, hTord, hcard, hT, hTjord, hαβ, hψ, -, -⟩ :=
    exists_conj_entrywise_of_not_innerDiag_of_quotient τ hτ hf K hK hp hp2 Θ hΘ α hαp hnd
  exact ⟨d, T, r, j, ψ, hd, hTord, hcard, hT, hTjord, hαβ, hψ⟩

theorem exists_conj_entrywise_of_outer_E
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f p : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ¬ p ∣ τ.cartan.det.natAbs)
    (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup τ K)) :
    ∃ (d : ℕ) (T : K ≃+* K) (r j : ℕ) (ψ : MulAut (adjointGroup τ K)), f = p * d ∧
      orderOf T = p ∧ Nat.card (fixSubfield T) = ℓ ^ d ∧ (α ^ r) ^ j = α ∧
        ψ * α ^ r * ψ⁻¹ = entrywiseAdjointAut τ T := by
  have : Finite K :=
    Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos (Fact.out : ℓ.Prime).pos f).ne')
  obtain ⟨d, T, r, j, ψ, hd, hTo, hc, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_not_innerDiag τ hτ hf K hK hp hp2 α hαp fun g a h =>
      hdet (prime_dvd_of_diag_noninner τ hτ K hp g a α h hαp hα).1
  exact ⟨d, T, r, j, ψ, hd, hTo, hc, hαβ, hψ⟩

end

end CFSG.HardMathSupport.Lang.E6Descent
