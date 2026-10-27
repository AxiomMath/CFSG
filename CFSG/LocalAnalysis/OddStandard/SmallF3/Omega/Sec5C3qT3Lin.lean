module

public import CFSG.GH74.Filter.Small.Eigenbasis
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CrossSL2
import CFSG.RankThree.PartTwo.Sec13.F135LastFourCube
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Matrix.Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Module

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem sec5c3q_finite_end [FiniteDimensional (ZMod 3) V] :
    Finite (Module.End (ZMod 3) V) := by
  haveI : Finite V := Module.finite_of_finite (ZMod 3)
  exact Finite.of_injective (fun f : Module.End (ZMod 3) V => (f : V → V)) DFunLike.coe_injective

theorem sec5c3q_apply_apply {t : Module.End (ZMod 3) V} (ht : t * t = 1) (v : V) :
    t (t v) = v := by
  rw [← Module.End.mul_apply, ht, Module.End.one_apply]

theorem sec5c3q_neg_sub_self (v : V) : -v - v = v := by
  have h2 : (-1 - 1 : ZMod 3) = 1 := by decide
  calc -v - v = (-1 : ZMod 3) • v - (1 : ZMod 3) • v := by simp
    _ = ((-1 : ZMod 3) - 1) • v := by rw [sub_smul]
    _ = (1 : ZMod 3) • v := by rw [h2]
    _ = v := one_smul _ _

theorem sec5c3q_range_sub_one {t : Module.End (ZMod 3) V} (ht : t * t = 1) :
    LinearMap.range (t - 1) = LinearMap.ker (t + 1) := by
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨w, rfl⟩
    simp only [LinearMap.add_apply, LinearMap.sub_apply, Module.End.one_apply, map_sub,
      sec5c3q_apply_apply ht]
    abel
  · intro hv
    refine ⟨v, ?_⟩
    have hv' : t v + v = 0 := by simpa using hv
    have htv : t v = -v := eq_neg_of_add_eq_zero_left hv'
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [htv]
    exact sec5c3q_neg_sub_self v

private lemma sec5c3q_mu_eq {ι : Type*} {f : ι → Module.End (ZMod 3) V} {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {μ : ι → Fin n → ZMod 3}
    (hb : ∀ i j, f i (b j) = μ i j • b j) (hsq : ∀ i, f i * f i = 1) :
    ∀ i j, μ i j = 1 ∨ μ i j = -1 := by
  intro i j
  have h1 : (f i * f i) (b j) = b j := by rw [hsq i, Module.End.one_apply]
  rw [Module.End.mul_apply, hb, map_smul, hb, smul_smul] at h1
  have h3 : (μ i j * μ i j - 1) • b j = 0 := by rw [sub_smul, h1, one_smul, sub_self]
  have h4 : μ i j * μ i j = 1 :=
    sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right (b.ne_zero j))
  exact mul_self_eq_one_iff.1 h4

private lemma sec5c3q_card_neg {ι : Type*} {f : ι → Module.End (ZMod 3) V} {n : ℕ}
    {b : Module.Basis (Fin n) (ZMod 3) V} {μ : ι → Fin n → ZMod 3}
    (hb : ∀ i j, f i (b j) = μ i j • b j) (hμ : ∀ i j, μ i j = 1 ∨ μ i j = -1) (i : ι) :
    (Finset.univ.filter (fun j : Fin n => μ i j = -1)).card =
      finrank (ZMod 3) (LinearMap.range (f i - 1)) := by
  have hsub : ∀ j : Fin n, (f i - 1) (b j) = (μ i j - 1) • b j := by
    intro j
    calc (f i - 1) (b j) = f i (b j) - (1 : Module.End (ZMod 3) V) (b j) := by
          rw [LinearMap.sub_apply]
      _ = μ i j • b j - b j := by rw [Module.End.one_apply, hb]
      _ = μ i j • b j - (1 : ZMod 3) • b j := by rw [one_smul]
      _ = (μ i j - 1) • b j := by rw [sub_smul]
  have hdiag : LinearMap.toMatrix b b (f i - 1) = Matrix.diagonal (fun j => μ i j - 1) := by
    ext k j
    by_cases hkj : k = j
    · subst hkj
      simp [LinearMap.toMatrix_apply, hsub]
    · simp [LinearMap.toMatrix_apply, hsub, hkj]
  have hfilter : Finset.univ.filter (fun j : Fin n => μ i j - 1 ≠ 0) =
      Finset.univ.filter (fun j : Fin n => μ i j = -1) := by
    apply Finset.filter_congr
    intro j _
    rcases hμ i j with h | h <;> rw [h] <;> decide
  have hrank : (LinearMap.toMatrix b b (f i - 1)).rank =
      finrank (ZMod 3) (LinearMap.range (f i - 1)) := by
    rw [Matrix.rank_eq_finrank_range_toLin (LinearMap.toMatrix b b (f i - 1)) b b,
      Matrix.toLin_toMatrix]
  have hrank2 : (LinearMap.toMatrix b b (f i - 1)).rank =
      Fintype.card {j : Fin n // μ i j - 1 ≠ 0} := by
    rw [hdiag, Matrix.rank_diagonal]
  have hcard : (Finset.univ.filter (fun j : Fin n => μ i j = -1)).card =
      Fintype.card {j : Fin n // μ i j - 1 ≠ 0} := by
    rw [Fintype.card_subtype, ← hfilter]
  calc (Finset.univ.filter (fun j : Fin n => μ i j = -1)).card
      = Fintype.card {j : Fin n // μ i j - 1 ≠ 0} := hcard
    _ = (LinearMap.toMatrix b b (f i - 1)).rank := hrank2.symm
    _ = finrank (ZMod 3) (LinearMap.range (f i - 1)) := hrank

theorem sec5c3q_comm_subsets [FiniteDimensional (ZMod 3) V] {ι : Type*} [Finite ι]
    (f : ι → Module.End (ZMod 3) V) (hcomm : ∀ i j, Commute (f i) (f j))
    (hsq : ∀ i, f i * f i = 1) :
    ∃ A : ι → Finset (Fin (finrank (ZMod 3) V)),
      (∀ i k, A i = A k → f i = f k) ∧
        ∀ i, (A i).card = finrank (ZMod 3) (LinearMap.range (f i - 1)) := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  obtain ⟨b, μ, hb⟩ := CFSG.GH74.Filter.exists_basis_common_eigenvectors_of_sq_eq_one h2 f hcomm
    (fun i => by rw [sq]; exact hsq i)
  have hμ := sec5c3q_mu_eq hb hsq
  refine ⟨fun i => Finset.univ.filter (fun j => μ i j = -1), ?_,
    fun i => sec5c3q_card_neg hb hμ i⟩
  intro i k hik
  have hiff : ∀ j, μ i j = -1 ↔ μ k j = -1 := fun j => by
    have h := Finset.ext_iff.mp hik j
    simpa using h
  have hμeq : ∀ j, μ i j = μ k j := by
    intro j
    rcases hμ i j with h1 | h1 <;> rcases hμ k j with h3 | h3
    · rw [h1, h3]
    · exact absurd ((hiff j).mpr h3) (by rw [h1]; decide)
    · exact absurd ((hiff j).mp h1) (by rw [h3]; decide)
    · rw [h1, h3]
  exact b.ext fun j => by rw [hb, hb, hμeq j]

theorem sec5c3q_card_le_choose [FiniteDimensional (ZMod 3) V] {ι : Type*} [Finite ι]
    (f : ι → Module.End (ZMod 3) V) (hcomm : ∀ i j, Commute (f i) (f j))
    (hsq : ∀ i, f i * f i = 1) (hinj : Function.Injective f) (k : ℕ)
    (hk : ∀ i, finrank (ZMod 3) (LinearMap.range (f i - 1)) = k) :
    Nat.card ι ≤ Nat.choose (finrank (ZMod 3) V) k := by
  classical
  obtain ⟨A, hA, hAcard⟩ := sec5c3q_comm_subsets f hcomm hsq
  have hmem : ∀ i, A i ∈ Finset.powersetCard k
      (Finset.univ : Finset (Fin (finrank (ZMod 3) V))) := fun i => by
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, (hAcard i).trans (hk i)⟩
  have hAinj : Function.Injective (fun i => (⟨A i, hmem i⟩ : ↥(Finset.powersetCard k
      (Finset.univ : Finset (Fin (finrank (ZMod 3) V)))))) := by
    intro i i' h
    exact hinj (hA i i' (congrArg Subtype.val h))
  calc Nat.card ι ≤ Nat.card ↥(Finset.powersetCard k
        (Finset.univ : Finset (Fin (finrank (ZMod 3) V)))) :=
        Nat.card_le_card_of_injective _ hAinj
    _ = Nat.choose (finrank (ZMod 3) V) k := by
        rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_powersetCard,
          Finset.card_univ, Fintype.card_fin]

theorem sec5c3q_card_le_two_pow [FiniteDimensional (ZMod 3) V] {ι : Type*} [Finite ι]
    (f : ι → Module.End (ZMod 3) V) (hcomm : ∀ i j, Commute (f i) (f j))
    (hsq : ∀ i, f i * f i = 1) (hinj : Function.Injective f) :
    Nat.card ι ≤ 2 ^ finrank (ZMod 3) V := by
  classical
  obtain ⟨A, hA, -⟩ := sec5c3q_comm_subsets f hcomm hsq
  have hAinj : Function.Injective A := fun i i' h => hinj (hA i i' h)
  calc Nat.card ι ≤ Nat.card (Finset (Fin (finrank (ZMod 3) V))) :=
        Nat.card_le_card_of_injective _ hAinj
    _ = 2 ^ finrank (ZMod 3) V := by
        rw [Nat.card_eq_fintype_card, Fintype.card_finset, Fintype.card_fin]

theorem sec5c3q_no_anticomm {E : Type} [AddCommGroup E] [Module (ZMod 3) E]
    (hE : finrank (ZMod 3) E = 3) {u w : Module.End (ZMod 3) E} (hu : u * u = 1)
    (hw : w * w = 1) (h : u * w = -(w * u)) : False := by
  have hev := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.even_finrank_of_anticommute (p := 3)
    (by norm_num) w u ⟨⟨w, w, hw, hw⟩, rfl⟩ ⟨⟨u, u, hu, hu⟩, rfl⟩ h
  rw [hE] at hev
  exact absurd hev (by decide)

theorem sec5c3q_no_sqrt_neg_one {E : Type} [AddCommGroup E] [Module (ZMod 3) E]
    [FiniteDimensional (ZMod 3) E] (hE : finrank (ZMod 3) E = 3)
    {u : Module.End (ZMod 3) E} (hu : u * u = -1) : False := by
  have hev := CFSG.RankThree.PartTwo.Sec13.F135Last.l10b_even_of_sq_eq_neg_one u hu
  rw [hE] at hev
  exact absurd hev (by decide)

end CFSG.OddStandard.SmallF3.Omega
