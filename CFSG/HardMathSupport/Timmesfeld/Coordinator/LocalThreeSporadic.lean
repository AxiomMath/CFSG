module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance

@[expose] def IsLocallyOneBalancedAbs (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ x : MulAut K, orderOf x = p → ∀ H : Subgroup (MulAut K), innerAut K ≤ H →
    x ∈ Subgroup.normalizer (H : Set (MulAut K)) →
      GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({x} : Set (MulAut K))) = ⊥

@[expose] def NoElemAbelianCubeAut (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D ≠ p ^ 3

variable {p : ℕ} {K : Type*} [Group K]

theorem IsLocallyOneBalancedAbs.isLocallyBalancedAbs (hp : p.Prime) {k : ℕ} (hk : 1 ≤ k)
    (h : IsLocallyOneBalancedAbs p K) : IsLocallyBalancedAbs p k K := by
  intro D hD hcard H hH hDH
  have : Fact p.Prime := ⟨hp⟩
  have hlt : 1 < Nat.card D := by
    rw [hcard]
    exact Nat.one_lt_pow (by omega) hp.one_lt
  have : Finite D := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial D := Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  have hd1 : (d : MulAut K) ≠ 1 := fun h1 => hd (Subtype.ext h1)
  have hdp : (d : MulAut K) ^ p = 1 := hD.2 d d.2
  have hord : orderOf (d : MulAut K) = p := orderOf_eq_prime hdp hd1
  rw [eq_bot_iff]
  calc localDeltaIn p H D
      ≤ GLAPPrimeCoreOf p (H ⊓ Subgroup.centralizer ({(d : MulAut K)} : Set (MulAut K))) :=
        iInf₂_le_of_le (d : MulAut K) d.2 (iInf_le_of_le hd1 le_rfl)
    _ = ⊥ := h d hord H hH (hDH d.2)

theorem isLocallyBalancedAbs_three_of_noElemAbelianCubeAut (h : NoElemAbelianCubeAut p K) :
    IsLocallyBalancedAbs p 3 K :=
  fun D hD hcard _ _ _ => absurd hcard (h D hD)

@[expose] def SporadicLocalThreeData : Prop :=
  ∀ (name : TauCeti.SporadicName) (p : ℕ), p.Prime → p ≠ 2 →
    NoElemAbelianCubeAut p (TauCeti.CFSGIndex.sporadic name).Group ∨
      IsLocallyOneBalancedAbs p (TauCeti.CFSGIndex.sporadic name).Group

theorem localThreeBalanceSporadic_of_data (h : SporadicLocalThreeData) :
    LocalThreeBalanceSporadic := by
  intro S _ _ _ _ name ⟨e⟩ p hp hp2
  refine IsLocallyBalancedAbs.of_mulEquiv e ?_
  rcases h name p hp hp2 with h3 | h1
  · exact isLocallyBalancedAbs_three_of_noElemAbelianCubeAut h3
  · exact h1.isLocallyBalancedAbs hp (by norm_num)

end CFSG.HardMathSupport.Timmesfeld.Coordinator
