module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Ree

theorem mem_diagonalFieldActors_of_entrywise (τ : Tag) (K : Type) [Field K]
    (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K)
    (h : ∀ x : adjointGroup τ K, (α x : ModGL τ K) =
      (g : ModGL τ K) * Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) *
        (g : ModGL τ K)⁻¹) : α ∈ diagonalFieldActors τ K := by
  rw [(Chevalley_diagonal_field_actor_data.1 τ K).1 α]
  refine ⟨g, g.2, 1, σ, fun x => ?_⟩
  rw [h x, rootDiagUnit_one]
  simp

theorem g2_three_odd_mem {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.G2.prime] (hK : Nat.card K = 3 ^ f)
    (α : MulAut (adjointGroup ReeTag.G2.tag K)) (hα : Odd (orderOf α)) :
    α ∈ diagonalFieldActors ReeTag.G2.tag K := by
  classical
  obtain ⟨-, hex, ⟨Θ, hΘ1, -, -⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hk, -⟩ := hex α
  have hΘα : Θ α = Multiplicative.ofAdd (((k : ℕ)) : ZMod (2 * f)) := hΘ1 α g k hk
  have hpow : Θ α ^ orderOf α = 1 := by
    rw [← map_pow Θ α (orderOf α), pow_orderOf_eq_one, map_one]
  rw [hΘα, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at hpow
  have hdvd : 2 * f ∣ orderOf α * (k : ℕ) := by
    have : (((orderOf α * (k : ℕ) : ℕ)) : ZMod (2 * f)) = 0 := by
      push_cast
      exact hpow
    exact (ZMod.natCast_eq_zero_iff _ _).1 this
  have h2 : 2 ∣ orderOf α * (k : ℕ) := (Dvd.intro f rfl).trans hdvd
  have hk2 : 2 ∣ (k : ℕ) := by
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact absurd h (by simpa [even_iff_two_dvd] using Nat.not_even_iff_odd.2 hα)
    · exact h
  obtain ⟨j, hj⟩ := hk2
  obtain ⟨fr, hfr, -, -⟩ := finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hK
  have hφ : ReeTag.G2.finiteExceptionalAut K ^ (k : ℕ) =
      exactNormalAut ReeTag.G2.tag K 1 (fr ^ j) 0 := by
    rw [hj, finiteExceptionalAut_pow_two_mul,
      exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2
        (σ := fr ^ j) (ringAut_pow_apply_of_frobenius hfr j)]
  refine mem_diagonalFieldActors_of_entrywise ReeTag.G2.tag K α g (fr ^ j) fun x => ?_
  have hx : (α x : ModGL ReeTag.G2.tag K) = (g : ModGL ReeTag.G2.tag K) *
      ((ReeTag.G2.finiteExceptionalAut K ^ (k : ℕ)) x : ModGL ReeTag.G2.tag K) *
      (g : ModGL ReeTag.G2.tag K)⁻¹ := by
    rw [hk]
    simp [MulAut.conj_apply]
  rw [hx, hφ, coe_exactNormalAut_zero, rootDiagUnit_one]
  simp

theorem g2_aut_facts {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = p ^ f) :
    (∀ α : MulAut (adjointGroup .G2 K), Odd (orderOf α) → α ∈ diagonalFieldActors .G2 K) ∧
    ∃ (H : Type) (_ : Group H) (_ : IsCyclic H) (Θ : MulAut (adjointGroup .G2 K) →* H),
      Θ.ker = (MulAut.conj : adjointGroup .G2 K →* MulAut (adjointGroup .G2 K)).range := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP K ReeTag.G2.prime :=
      finite_field_prime_power_characteristic hp hf hK
    obtain ⟨-, -, ⟨Θ, -, -, hΘk⟩, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
    exact ⟨fun α hα => g2_three_odd_mem hf K hK α hα,
      Multiplicative (ZMod (2 * f)), inferInstance, inferInstance, Θ, hΘk⟩
  · obtain ⟨hex, Θ, -, -, hΘk, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf K hK .G2 (Or.inr ⟨rfl, hp3⟩)
    refine ⟨fun α _ => ?_, K ≃+* K, inferInstance,
      (card_ringAut_and_isCyclic hp K hK).2, Θ, hΘk⟩
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hex α
    exact mem_diagonalFieldActors_of_entrywise .G2 K α g σ hgσ

end CFSG.GH74.GLS.Stage2.Bender.Thm1
