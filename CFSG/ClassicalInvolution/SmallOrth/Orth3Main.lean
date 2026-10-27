module

public import CFSG.ClassicalInvolution.SmallOrth.Orth3GaussMain

public section

namespace CFSG.ClassicalGroups.Orthogonal.Small

open QuadraticMap CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V}

theorem oddCoreIn_centralizer_eq_bot_of_mk (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ Module.finrank F V)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) (g : ↥(elementaryGroup Q))
    (h1 : (QuotientGroup.mk g : ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q)) ≠ 1)
    (h2 : (QuotientGroup.mk g : ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q)) *
      QuotientGroup.mk g = 1) :
    oddCoreIn (Subgroup.centralizer ({(QuotientGroup.mk g : ↥(elementaryGroup Q) ⧸
      Subgroup.center ↥(elementaryGroup Q))} : Set (↥(elementaryGroup Q) ⧸
        Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
  have hdim3 : 3 ≤ Module.finrank F V := by omega
  have hZc : ∀ {z : ↥(elementaryGroup Q)},
      z ∈ Subgroup.center ↥(elementaryGroup Q) ↔ (z : V ≃ₗ[F] V) ∈ scalars F V :=
    fun {_} => mem_center_iff_mem_scalars hF hQ hdim3
  have hgs : (g : V ≃ₗ[F] V) ∉ scalars F V := fun h =>
    h1 ((QuotientGroup.eq_one_iff g).mpr (hZc.mpr h))
  have hgg : g * g ∈ Subgroup.center ↥(elementaryGroup Q) :=
    (QuotientGroup.eq_one_iff (g * g)).mp (by rw [QuotientGroup.mk_mul]; exact h2)
  have hggs : ((g * g : ↥(elementaryGroup Q)) : V ≃ₗ[F] V) ∈ scalars F V := hZc.mp hgg
  obtain ⟨c, hc⟩ := mem_scalars.mp hggs
  obtain ⟨P, a, -, ha⟩ := exists_hypPair_and_aniso hF hQ hdim3
  have hc2 : c ^ 2 = 1 := by
    have h3 := map_of_mem (elementaryGroup_le_orthogonalGroup Q (g * g).2) a
    rw [hc a, map_smul_eq_sq] at h3
    have h4 : (c ^ 2 - 1) * Q a = 0 := by rw [sub_mul, h3, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h4).resolve_right ha)
  have hc2' : c * c = 1 := by rw [← pow_two]; exact hc2
  rcases mul_self_eq_one_iff.mp hc2' with hc1 | hc1
  · refine oddCoreIn_centralizer_eq_bot_of_involution hF hQ hdim3 g ?_ hgs
    refine LinearEquiv.ext fun v => ?_
    have h5 := hc v
    rw [hc1, one_smul] at h5
    exact h5
  · refine oddCoreIn_centralizer_eq_bot_of_neg_one hF hQ hdim hOE g fun x => ?_
    have h5 := hc x
    rw [hc1, neg_one_smul] at h5
    exact h5

theorem oddCoreIn_centralizer_eq_bot_of_orderOf_eq_two (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ Module.finrank F V)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q)
    (s : ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q)) (hs : orderOf s = 2) :
    oddCoreIn (Subgroup.centralizer ({s} : Set (↥(elementaryGroup Q) ⧸
      Subgroup.center ↥(elementaryGroup Q)))) = ⊥ := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective s
  have hs' := orderOf_eq_prime_iff.mp hs
  exact oddCoreIn_centralizer_eq_bot_of_mk hF hQ hdim hOE g hs'.2 (by rw [← pow_two]; exact hs'.1)

noncomputable def projElementaryEquivCenter (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 3 ≤ Module.finrank F V) :
    ProjElementary Q ≃* ↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q) :=
  QuotientGroup.quotientMulEquivOfEq (by
    ext z
    rw [Subgroup.mem_subgroupOf]
    exact (mem_center_iff_mem_scalars hF hQ hdim).symm)

theorem involutionOddCore_eq_bot_of_mulEquiv (hF : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 6 ≤ Module.finrank F V)
    (hOE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      elementaryGroup Q) {X : Type} [Group X]
    (e : X ≃* (↥(elementaryGroup Q) ⧸ Subgroup.center ↥(elementaryGroup Q))) (x : X)
    (hx : orderOf x = 2) : CFSG.Assembly.Dichotomy.involutionOddCore x = ⊥ := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  exact oddCoreIn_centralizer_eq_bot_of_mulEquiv e x
    (oddCoreIn_centralizer_eq_bot_of_orderOf_eq_two hF hQ hdim hOE (e x)
      (by rw [MulEquiv.orderOf_eq]; exact hx))

end CFSG.ClassicalGroups.Orthogonal.Small
