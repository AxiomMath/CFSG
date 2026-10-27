module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusType
public import CFSG.ClassicalGroups.Orthogonal.OmegaPlusSix

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

universe uV uM

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type uV} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

structure IsPlus (Q : QuadraticForm K V) (m : ℕ) : Prop where
  nondeg : (polarBilin Q).Nondegenerate
  finrank_eq : finrank K V = 2 * m
  pairs : ∃ P : Fin m → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j)

theorem IsPlus.perp [FiniteDimensional K V] {m : ℕ} (hm : 1 ≤ m) (h : IsPlus Q (m + 1))
    (Ph : HypPair Q) : IsPlus (Q.restrict Ph.perp) m := by
  have hdim : finrank K Ph.perp = 2 * m := by
    have := Submodule.finrank_add_eq_of_isCompl Ph.isCompl_perp
    rw [Ph.finrank_span, h.finrank_eq] at this
    omega
  refine ⟨nondegenerate_polarBilin_restrict (HypPair.polarNondegOn_perp h.nondeg Ph), hdim, ?_⟩
  obtain ⟨P, hP⟩ := h.pairs
  have h01 : (P ⟨0, by omega⟩).Orth (P ⟨1, by omega⟩) := hP _ _ (by simp [Fin.ext_iff])
  obtain ⟨g, hg1, hg2⟩ := exists_gom_pair h.nondeg h01 (P ⟨0, by omega⟩).Q_e
    (P ⟨0, by omega⟩).Q_f Ph.Q_e Ph.Q_f (P ⟨0, by omega⟩).polar_ef Ph.polar_ef
  have hmem : ∀ i : Fin m, ((P ⟨i.1 + 1, by omega⟩).mapGom g).e ∈ Ph.perp ∧
      ((P ⟨i.1 + 1, by omega⟩).mapGom g).f ∈ Ph.perp := by
    intro i
    have hne : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨i.1 + 1, by omega⟩ := by simp [Fin.ext_iff]
    have hO := hP _ _ hne
    refine ⟨HypPair.mem_perp.mpr ⟨?_, ?_⟩, HypPair.mem_perp.mpr ⟨?_, ?_⟩⟩
    · rw [← hg1, HypPair.mapGom, Gom.polar_app]; exact hO.ee
    · rw [← hg2, HypPair.mapGom, Gom.polar_app]; exact hO.fe
    · rw [← hg1, HypPair.mapGom, Gom.polar_app]; exact hO.ef
    · rw [← hg2, HypPair.mapGom, Gom.polar_app]; exact hO.ff
  refine ⟨fun i => HypPair.restrict ((P ⟨i.1 + 1, by omega⟩).mapGom g)
    (hmem i).1 (hmem i).2, fun i j hij => ?_⟩
  have hne : (⟨i.1 + 1, by omega⟩ : Fin (m + 1)) ≠ ⟨j.1 + 1, by omega⟩ := by
    intro h'; exact hij (Fin.ext (by simpa [Fin.ext_iff] using h'))
  exact HypPair.Orth.restrict ((hP _ _ hne).mapGom g) (hmem i).1 (hmem i).2 (hmem j).1 (hmem j).2

theorem exists_plus_data {m : ℕ} (hm : 2 ≤ m) (h : IsPlus Q m) :
    ∃ x x' w : V, Q x = 0 ∧ Q x' = 0 ∧ polar Q x x' = 1 ∧ polar Q x w = 0 ∧
      polar Q x' w = 0 ∧ Q w ≠ 0 := by
  obtain ⟨P, hP⟩ := h.pairs
  have h01 : (P ⟨0, by omega⟩).Orth (P ⟨1, by omega⟩) := hP _ _ (by simp [Fin.ext_iff])
  set P₀ := P ⟨0, by omega⟩
  set P₁ := P ⟨1, by omega⟩
  refine ⟨P₀.e, P₀.f, P₁.e + P₁.f, P₀.Q_e, P₀.Q_f, P₀.polar_ef, ?_, ?_, ?_⟩
  · rw [polar_add_right, h01.ee, h01.ef, add_zero]
  · rw [polar_add_right, h01.fe, h01.ff, add_zero]
  · rw [QuadraticMap.map_add Q, P₁.Q_e, P₁.Q_f, P₁.polar_ef]; simp

theorem omegaPlus_card_eq_pow_aux :
    ∀ m : ℕ, 2 ≤ m → ∀ {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
      (Q : QuadraticForm K V), IsPlus Q (m + 1) →
      ∀ {M : Type uM} [AddCommGroup M] [Finite M], (∀ x : M, x + x = 0) →
      ∀ [DistribMulAction (Gom Q) M] (Ph : HypPair Q),
      IsCompl (fixedSub M (Lom Q Ph.e : Set (Gom Q))) (fixedSub M (Lom Q Ph.f : Set (Gom Q))) →
      ∃ n : ℕ, Nat.card M = Nat.card K ^ (2 ^ m * n) := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro V _ _ _ Q h M _ _ h2 _ Ph hdec
    obtain ⟨n, hn⟩ := omegaPlus6_card_eq_pow Q h.nondeg (by simpa using h.finrank_eq)
      (by simpa using h.pairs) h2 Ph hdec
    exact ⟨n, by simpa using hn⟩
  | succ m hm ih =>
    intro V _ _ _ Q h M _ _ h2 _ Ph hdec
    have hperp : IsPlus (Q.restrict Ph.perp) (m + 1) := h.perp (by omega) Ph
    obtain ⟨x₁, x₁', w, hx₁, hx₁', hxx, hw₁, hw₂, hQw⟩ := exists_plus_data (by omega) hperp
    have hxx' : polar Q (x₁ : V) (x₁' : V) = 1 := by
      rw [← polar_restrict]; exact hxx
    obtain ⟨n, hn⟩ := omega_step h.nondeg Ph x₁ x₁' w hx₁ hx₁' hxx'
      (by rw [← polar_restrict]; exact hw₁) (by rw [← polar_restrict]; exact hw₂) hQw
      (e := 2 ^ m)
      (fun M' _ _ h2' _ hdec' =>
        ih (Q.restrict Ph.perp) hperp h2' ⟨x₁, x₁', hx₁, hx₁', hxx⟩ hdec')
      h2 hdec
    exact ⟨n, by rw [hn]; congr 2; ring⟩

end CFSG.ClassicalGroups.Orthogonal
