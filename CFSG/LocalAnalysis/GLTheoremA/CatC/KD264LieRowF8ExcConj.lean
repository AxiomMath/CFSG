module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowF8ExcRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1LinCoreTransfer
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.E6Aux.Diag

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Timmesfeld.CrossChar
  (e6Inndiag exists_conj_entrywise_of_not_mem_e6Inndiag)
open CFSG.RankThree.Chevalley.SteinbergBT
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie.X1LinCore.Transfer (isElemAbelian_map_gen)


theorem exists_conj_entrywise (τ : Tag) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ 3)
    {x : MulAut (adjointGroup τ K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ innAutDerived (adjointGroup τ K)) :
    ∃ (σ : K ≃+* K) (ψ : MulAut (adjointGroup τ K)), ψ * x * ψ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hf : 1 ≤ 3 := by norm_num
  haveI hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      hf hK
  have hxinner : x ∉ (MulAut.conj : ↥(adjointGroup τ K) →*
      MulAut ↥(adjointGroup τ K)).range := fun hx => hxo (inner_le_innAutDerived _ hx)
  have hxord : orderOf x = 3 :=
    orderOf_eq_prime hx3 fun h => hxinner (by rw [h]; exact one_mem _)
  have hαp : orderOf (⟨x, Subgroup.mem_top x⟩ :
      (⊤ : Subgroup (MulAut ↥(adjointGroup τ K)))) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hxord
  rcases hτ with rfl | rfl | hτ'
  ·
    haveI : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := by
      rw [show CFSG.LieType.Ree.ReeTag.F4.prime = 2 from rfl]
      exact hchar
    have hNF := (even_F4_exact_automorphism_normal_form hf K hK).2.1
    obtain ⟨⟨y, k⟩, hyk, -⟩ := hNF x
    obtain ⟨-, -, ⟨σ, hσ⟩, hmain, -⟩ :=
      even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hK Nat.prime_three
        (by norm_num) ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp y k k.isLt hyk
    obtain ⟨-, ψ, hψ⟩ := hmain σ hσ
    exact ⟨σ, ψ, hψ⟩
  ·
    have hxI : x ∉ e6Inndiag K := fun hmem =>
      hxo (commutator_le_innAutDerived _
        (CFSG.HardMathSupport.Dickson.Sec6.I923.e6Inndiag_le_commutator (K := K) hmem))
    obtain ⟨σ, -, -, ψ, hψ⟩ := exists_conj_entrywise_of_not_mem_e6Inndiag Nat.prime_two hf K hK
      Nat.prime_three (by norm_num) hx3 hxI
    exact ⟨σ, ψ, hψ⟩
  ·
    have hτ'' : τ = .E7 ∨ τ = .E8 := hτ'
    have hNF := conj_normalForm_of_pointwise
      (even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ'').1
    obtain ⟨⟨y, σ⟩, hyσ, -⟩ := hNF x
    obtain ⟨-, -, ⟨ψ, hψ⟩, -⟩ :=
      even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ'' hf K hK
        Nat.prime_three ⊤ le_top ⟨x, Subgroup.mem_top x⟩ hxinner hαp y σ hyσ
    exact ⟨σ, ψ, hψ⟩

theorem exists_fixed_rank_four_of_outer (τ : Tag)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 3) {x : MulAut (adjointGroup τ K)} (hx3 : x ^ 3 = 1)
    (hxo : x ∉ innAutDerived (adjointGroup τ K)) :
    ∃ E : Subgroup (adjointGroup τ K), E ≤ fixSubgroup x ∧ IsElemAbelian 3 E ∧
      3 ^ 4 ≤ Nat.card E := by
  classical
  haveI hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  obtain ⟨σ, ψ, hψ⟩ := exists_conj_entrywise τ hτ hK hx3 hxo
  obtain ⟨E₀, hE₀, hel, hcard⟩ := exists_fixed_rank_four τ hτ σ
  refine ⟨E₀.map (ψ⁻¹ : MulAut (adjointGroup τ K)).toMonoidHom, ?_, isElemAbelian_map_gen _ hel, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : entrywiseAdjointAut τ σ y = y := mem_fixSubgroup.1 (hE₀ hy)
    rw [mem_fixSubgroup]
    have h1 : (ψ * x * ψ⁻¹) y = y := by rw [hψ]; exact hy'
    have h2 : ψ (x (ψ⁻¹ y)) = y := by simpa [MulAut.mul_apply] using h1
    show x (ψ⁻¹ y) = ψ⁻¹ y
    apply ψ.injective
    rw [h2, MulAut.apply_inv_self]
  · rw [Subgroup.card_map_of_injective (ψ⁻¹ : MulAut (adjointGroup τ K)).injective, hcard]

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.F8Exc

end
