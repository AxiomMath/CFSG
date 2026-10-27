module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusModel

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

universe uV uM

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type uV} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

structure IsMinus (Q : QuadraticForm K V) (m : ℕ) : Prop where
  nondeg : (polarBilin Q).Nondegenerate
  finrank_eq : finrank K V = 2 * m
  noTS : ∀ U : Submodule K V, finrank K U = m → ∃ u ∈ U, Q u ≠ 0

theorem HypPair.linearIndependent_pair (P : HypPair Q) : LinearIndependent K ![P.e, P.f] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 := congrArg (polar Q P.e) hst
  have h2 := congrArg (polar Q P.f) hst
  simp only [polar_add_right, polar_smul_right_eq, P.polar_ee, P.polar_ef, P.polar_fe,
    P.polar_ff, polar_zero_right] at h1 h2
  exact ⟨by linear_combination h2, by linear_combination h1⟩

theorem HypPair.finrank_span (P : HypPair Q) : finrank K (Submodule.span K {P.e, P.f}) = 2 := by
  rw [← Matrix.range_cons_cons_empty P.e P.f ![], finrank_span_eq_card P.linearIndependent_pair,
    Fintype.card_fin]

theorem IsMinus.perp [FiniteDimensional K V] {m : ℕ} (h : IsMinus Q (m + 1)) (P : HypPair Q) :
    IsMinus (Q.restrict P.perp) m := by
  have hdim : finrank K P.perp = 2 * m := by
    have := Submodule.finrank_add_eq_of_isCompl P.isCompl_perp
    rw [P.finrank_span, h.finrank_eq] at this
    omega
  refine ⟨nondegenerate_polarBilin_restrict (HypPair.polarNondegOn_perp h.nondeg P), hdim, ?_⟩
  intro U hU
  by_contra hcon
  push Not at hcon
  have hdisj : Disjoint (U.map P.perp.subtype) (Submodule.span K {P.e}) := by
    rw [Submodule.disjoint_def]
    intro x hx hxe
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxe
    have hyc : (y : V) = c • P.e := hc.symm
    have hmemP : (y : V) ∈ Submodule.span K {P.e, P.f} := by
      rw [hyc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    exact (Submodule.disjoint_def.mp P.isCompl_perp.1) (y : V) hmemP y.2
  have hmapfin : finrank K (U.map P.perp.subtype) = m := by
    rw [← hU]
    exact LinearEquiv.finrank_eq
      (Submodule.equivMapOfInjective P.perp.subtype P.perp.injective_subtype U).symm
  have hfin : finrank K (U.map P.perp.subtype ⊔ Submodule.span K {P.e} : Submodule K V) =
      m + 1 := by
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (U.map P.perp.subtype)
      (Submodule.span K {P.e})
    rw [hdisj.eq_bot, finrank_bot, finrank_span_singleton P.e_ne_zero, hmapfin] at h1
    omega
  obtain ⟨u, hu, hQu⟩ := h.noTS _ hfin
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp ha
  apply hQu
  have hy0 : Q (P.perp.subtype y) = 0 := hcon y hy
  have hpe : polar Q (P.perp.subtype y) P.e = 0 := by
    rw [polar_comm]; exact (HypPair.mem_perp.mp y.2).1
  rw [QuadraticMap.map_add Q, hy0, map_smul_eq_sq, P.Q_e, polar_smul_right_eq, hpe]
  ring

open CFSG.RankThree.PartOne.KCOrthogonal in
theorem exists_minus_data [FiniteDimensional K V] {m : ℕ} (hm : 2 ≤ m) (h : IsMinus Q m) :
    ∃ x x' w : V, Q x = 0 ∧ Q x' = 0 ∧ polar Q x x' = 1 ∧ polar Q x w = 0 ∧
      polar Q x' w = 0 ∧ Q w ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  obtain ⟨E, _, _, D, ψ, hψ⟩ := exists_evenMinus_model Q h.nondeg (n := k + 2) (by omega)
    h.finrank_eq h.noTS
  have hψ' : ∀ w, evenNormTailForm D.N (k + 1) (ψ w) = Q w := hψ
  set e₀ : ((Fin (k + 1) → K) × (Fin (k + 1) → K)) × E := ((Pi.single 0 1, 0), 0) with he₀
  set f₀ : ((Fin (k + 1) → K) × (Fin (k + 1) → K)) × E := ((0, Pi.single 0 1), 0) with hf₀
  set z₀ : ((Fin (k + 1) → K) × (Fin (k + 1) → K)) × E := ((0, 0), 1) with hz₀
  have hN1 : D.N 1 = 1 := by
    apply (algebraMap K E).injective
    rw [D.algebraMap_N, map_one, one_mul, map_one]
  have hQ : ∀ v, Q (ψ.symm v) = evenNormTailForm D.N (k + 1) v := fun v => by
    rw [← hψ', LinearEquiv.apply_symm_apply]
  have hQe : evenNormTailForm D.N (k + 1) e₀ = 0 := by
    simp [he₀, evenNormTailForm_apply]
  have hQf : evenNormTailForm D.N (k + 1) f₀ = 0 := by
    simp [hf₀, evenNormTailForm_apply]
  have hQz : evenNormTailForm D.N (k + 1) z₀ = 1 := by
    simp [hz₀, evenNormTailForm_apply, hN1]
  have hQef : evenNormTailForm D.N (k + 1) (e₀ + f₀) = 1 := by
    simp [he₀, hf₀, evenNormTailForm_apply, Pi.single_apply]
  have hQez : evenNormTailForm D.N (k + 1) (e₀ + z₀) = 1 := by
    simp [he₀, hz₀, evenNormTailForm_apply, hN1]
  have hQfz : evenNormTailForm D.N (k + 1) (f₀ + z₀) = 1 := by
    simp [hf₀, hz₀, evenNormTailForm_apply, hN1]
  have hpol : ∀ a b : ((Fin (k + 1) → K) × (Fin (k + 1) → K)) × E,
      polar Q (ψ.symm a) (ψ.symm b) =
        evenNormTailForm D.N (k + 1) (a + b) - evenNormTailForm D.N (k + 1) a -
          evenNormTailForm D.N (k + 1) b := fun a b => by
    rw [polar, ← map_add, hQ, hQ, hQ]
  refine ⟨ψ.symm e₀, ψ.symm f₀, ψ.symm z₀, by rw [hQ, hQe], by rw [hQ, hQf], ?_, ?_, ?_, ?_⟩
  · rw [hpol, hQef, hQe, hQf]; ring
  · rw [hpol, hQez, hQe, hQz]; ring
  · rw [hpol, hQfz, hQf, hQz]; ring
  · rw [hQ, hQz]; exact one_ne_zero

end CFSG.ClassicalGroups.Orthogonal
