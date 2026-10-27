module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisHomC
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.SigmaDich

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.GroupTheory.WeirSylow
open CFSG.RankThree.PartOne.OutStructure (Inn)
open CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis (isElemAbelian_map_iff_of_injective)

theorem heisD_exists_elemAbelian_sigmaModel {p e a N : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hm : p ≤ N / e) :
    ∃ E : Subgroup (sigmaModel p e a N), CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ p := by
  have hL : 1 < (Nat.digits p (N / e)).length := by
    rw [Nat.lt_digits_length_iff hp.one_lt]
    simpa using hm
  have hne : N / e ≠ 0 := by
    have := hp.pos
    omega
  let i₁ : Fin (Nat.digits p (N / e)).length := ⟨(Nat.digits p (N / e)).length - 1, by omega⟩
  have hi₁ : 1 ≤ (i₁ : ℕ) := by
    show 1 ≤ (Nat.digits p (N / e)).length - 1
    omega
  have hpos : 0 < (Nat.digits p (N / e))[i₁] := by
    have hlast := Nat.getLast_digit_ne_zero p hne
    have heq : (Nat.digits p (N / e))[i₁] =
        (Nat.digits p (N / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
      rw [List.getLast_eq_getElem]
      rfl
    rw [heq]
    exact Nat.pos_of_ne_zero hlast
  let j₁ : Fin (Nat.digits p (N / e))[i₁] := ⟨0, hpos⟩
  obtain ⟨E, hE, hEcard⟩ :=
    WeakClosureHeis.SigmaDich.exists_elemAbelian_wreathTower hp ha i₁ hi₁
  have hinj := WeakClosureHeis.SigmaDich.sigmaEmbed_injective p e a N i₁ j₁
  refine ⟨E.map (WeakClosureHeis.SigmaDich.sigmaEmbed p e a N i₁ j₁),
    (isElemAbelian_map_iff_of_injective _ hinj E).2 hE, ?_⟩
  rw [Subgroup.card_map_of_injective hinj, hEcard]

theorem heisD_noHeisAut_of_sigmaModel_sylow {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hZ : Function.Injective (MulAut.conj : X →* MulAut X)) (hCyc : OutPCyc p X)
    (hrk : ∀ A : Subgroup X, IsMulCommutative A → (∀ x ∈ A, x ^ p = 1) → Nat.card A ≤ p ^ 3)
    {q N : ℕ} (ha : 1 ≤ padicValNat p (q ^ orderOf (q : ZMod p) - 1))
    (hSyl : ∀ S : Sylow p X, Nonempty (↥(S : Subgroup X) ≃* sigmaModel p (orderOf (q : ZMod p))
      (padicValNat p (q ^ orderOf (q : ZMod p) - 1)) N))
    (hout : (∃ α : MulAut X, α ∉ Inn X ∧ α ^ p = 1) → ∃ c : ℕ, q = c ^ p ∧ ¬ p ∣ c ∧ 2 ≤ c) :
    NoHeisAut p X := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hm : N / orderOf (q : ZMod p) < p
  · have hS := sylow_equiv_homC_of_sigmaModel hp hm hSyl
    refine noHeisAut_of_homC_sylow hp hp5 hZ hCyc hrk fun S =>
      ⟨_, _, hS S, Or.inr fun h => ?_⟩
    obtain ⟨c, rfl, hc, hc2⟩ := hout h
    exact heis_two_le_padicValNat hp hc hc2
  · exfalso
    push Not at hm
    obtain ⟨E, hE, hEcard⟩ := heisD_exists_elemAbelian_sigmaModel hp ha hm
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p X))
    obtain ⟨φ⟩ := hSyl S
    let Ψ : sigmaModel p (orderOf (q : ZMod p)) (padicValNat p (q ^ orderOf (q : ZMod p) - 1))
        N →* X :=
      (S : Subgroup X).subtype.comp φ.symm.toMonoidHom
    have hΨ : Function.Injective Ψ := Subtype.coe_injective.comp φ.symm.injective
    have hE' := (isElemAbelian_map_iff_of_injective Ψ hΨ E).2 hE
    have h1 := hrk (E.map Ψ) hE'.1 hE'.2
    rw [Subgroup.card_map_of_injective hΨ, hEcard] at h1
    have h2 : p ^ 3 < p ^ p := Nat.pow_lt_pow_right hp.one_lt (by omega)
    omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
