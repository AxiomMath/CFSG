module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenCompl
public import CFSG.ClassicalGroups.Orthogonal.Restrict

public section

universe w

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] def restrictIso (g : V ≃ₗ[K] V) (hg3 : g ^ 3 = 1) (U : Submodule K V)
    (hU : ∀ u ∈ U, g u ∈ U) : U ≃ₗ[K] U where
  toFun u := ⟨g u, hU u u.2⟩
  map_add' a b := Subtype.ext (map_add g (a : V) (b : V))
  map_smul' c a := Subtype.ext (map_smul g c (a : V))
  invFun u := ⟨g (g u), hU _ (hU u u.2)⟩
  left_inv u := Subtype.ext (apply_apply_apply_of_pow_three hg3 u)
  right_inv u := Subtype.ext (apply_apply_apply_of_pow_three hg3 u)

theorem restrictIso_mem_orthogonalGroup {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg3 : g ^ 3 = 1) (U : Submodule K V)
    (hU : ∀ u ∈ U, g u ∈ U) :
    restrictIso g hg3 U hU ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.restrict U) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro u
  exact map_of_mem hg u

theorem restrictIso_pow_three (g : V ≃ₗ[K] V) (hg3 : g ^ 3 = 1) (U : Submodule K V)
    (hU : ∀ u ∈ U, g u ∈ U) : restrictIso g hg3 U hU ^ 3 = 1 := by
  refine LinearEquiv.ext fun u => Subtype.ext ?_
  rw [pow_three]
  exact apply_apply_apply_of_pow_three hg3 u

theorem GoodPair.of_restrict {Q : QuadraticForm K V} {g : V ≃ₗ[K] V} (hg3 : g ^ 3 = 1)
    {U : Submodule K V} (hU : ∀ u ∈ U, g u ∈ U) {x y : U}
    (h : GoodPair (Q.restrict U) (restrictIso g hg3 U hU) x y) :
    GoodPair Q g (x : V) (y : V) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, ?_, h3, ?_⟩
  · rw [← polar_restrict]
    exact h2
  · rcases h4 with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨congrArg Subtype.val a, congrArg Subtype.val b⟩
    · exact Or.inr ⟨congrArg Subtype.val a, congrArg Subtype.val b⟩

theorem exists_frame [Finite K] (hK : Odd (Nat.card K)) (h3 : (3 : K) ≠ 0) :
    ∀ n : ℕ, ∀ (V : Type w) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate → 2 * n + 1 ≤ Module.finrank K V →
      ∀ g : V ≃ₗ[K] V, g ∈ TauCeti.QuadraticMap.orthogonalGroup Q → g ^ 3 = 1 →
      ∃ x y : Fin n → V, (∀ i, GoodPair Q g (x i) (y i)) ∧
        ∀ i j, i ≠ j → polar Q (x i) (x j) = 0 ∧ polar Q (x i) (y j) = 0 ∧
          polar Q (y i) (x j) = 0 ∧ polar Q (y i) (y j) = 0 := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ Q hQ hdim g hg hg3
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
    intro V _ _ _ Q hQ hdim g hg hg3
    obtain ⟨x₀, y₀, hxy⟩ := exists_goodPair hK h3 hQ (by omega) hg hg3
    obtain ⟨U, hUnd, hUperp, hUg, hUdim⟩ := exists_complement_of_goodPair h3 hQ hg hg3 hxy
    have hQU : (polarBilin (Q.restrict U)).Nondegenerate := nondegenerate_polarBilin_restrict hUnd
    obtain ⟨x', y', hgood, horth⟩ := ih U (Q.restrict U) hQU (by omega)
      (restrictIso g hg3 U hUg) (restrictIso_mem_orthogonalGroup hg hg3 U hUg)
      (restrictIso_pow_three g hg3 U hUg)
    refine ⟨Fin.cons x₀ (fun i => (x' i : V)), Fin.cons y₀ (fun i => (y' i : V)), ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hxy
      · simpa using GoodPair.of_restrict hg3 hUg (hgood j)
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j' =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact ⟨(hUperp _ (x' j').2).1, (hUperp _ (y' j').2).1, (hUperp _ (x' j').2).2,
            (hUperp _ (y' j').2).2⟩
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [polar_comm]; exact (hUperp _ (x' i').2).1
          · rw [polar_comm]; exact (hUperp _ (x' i').2).2
          · rw [polar_comm]; exact (hUperp _ (y' i').2).1
          · rw [polar_comm]; exact (hUperp _ (y' i').2).2
        | succ j' =>
          simp only [Fin.cons_succ]
          have hne : i' ≠ j' := fun h => hij (by rw [h])
          obtain ⟨o1, o2, o3, o4⟩ := horth i' j' hne
          exact ⟨by rwa [polar_restrict] at o1, by rwa [polar_restrict] at o2,
            by rwa [polar_restrict] at o3, by rwa [polar_restrict] at o4⟩

end OmSeven

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
