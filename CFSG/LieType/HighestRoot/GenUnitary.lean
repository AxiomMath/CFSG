module

public import CFSG.LieType.HighestRoot.GenBasic
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Universal.Unitary.Extras.Basic
public import CFSG.LieType.Universal.Unitary.Extras.Unipotent
public import CFSG.LieType.Universal.Unitary.Extras.RankOneLast
import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.LieType.HighestRoot

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras

section General

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}

private theorem commute_of_sub_one_mul {A B : Matrix (Fin n) (Fin n) F}
    (h1 : (A - 1) * (B - 1) = 0) (h2 : (B - 1) * (A - 1) = 0) : A * B = B * A := by
  have e : A * B - B * A = (A - 1) * (B - 1) - (B - 1) * (A - 1) := by noncomm_ring
  rw [h1, h2, sub_zero] at e
  exact sub_eq_zero.1 e

private theorem weight_sub_notMem {e : Fin (n / 2) → ℤ} (he : e ≠ 0) {a c b : Fin n} {k l : ℕ}
    (hk : weight n a - weight n c = k • e) (hl : weight n c - weight n b = l • e)
    (hkl : 3 ≤ k + l) : False := by
  have hs : weight n a - weight n b = (k + l) • e := by
    rw [add_nsmul, ← hk, ← hl]
    abel
  exact he (eq_zero_of_weight_sub_eq_nsmul hs hkl)

private theorem exists_nsmul_of_mem_wt2 {e w : Fin (n / 2) → ℤ} (h : w ∈ wt2 e) :
    ∃ k : ℕ, 1 ≤ k ∧ w = k • e := by
  rcases h with rfl | rfl
  exacts [⟨1, le_rfl, (one_nsmul _).symm⟩, ⟨2, by norm_num, rfl⟩]

private theorem mul_eq_zero_of_hasWt {e : Fin (n / 2) → ℤ} (he : e ≠ 0)
    {N M : Matrix (Fin n) (Fin n) F} {k₀ l₀ : ℕ} (h3 : 3 ≤ k₀ + l₀)
    (hN : HasWt (wt2 (k₀ • e)) N) (hM : HasWt (wt2 (l₀ • e)) M) : N * M = 0 := by
  have hNM : HasWt (∅ : Set (Fin (n / 2) → ℤ)) (N * M) := hN.mul hM fun a c b h1 h2 => by
    exfalso
    obtain ⟨k, hk, h1⟩ := exists_nsmul_of_mem_wt2 h1
    obtain ⟨l, hl, h2⟩ := exists_nsmul_of_mem_wt2 h2
    rw [smul_smul] at h1 h2
    refine weight_sub_notMem he h1 h2 ?_
    nlinarith
  exact Matrix.ext fun a b => hNM.eq_zero_apply (Set.notMem_empty _)

theorem commute_of_mem_rootGroup_two_smul {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ ≠ 0)
    {x y : SU σ n} (hx : x ∈ rootGroup σ hσ n γ) (hy : y ∈ rootGroup σ hσ n (2 • γ)) :
    Commute x y := by
  have hN := hasWt_of_mem_rootGroup hσ hx
  have hM := hasWt_of_mem_rootGroup hσ hy
  rw [toStd_nsmul_two] at hM
  rw [← one_nsmul (toStd n γ)] at hN
  have h1 := mul_eq_zero_of_hasWt hγ (by norm_num) hN hM
  have h2 := mul_eq_zero_of_hasWt hγ (by norm_num) hM hN
  show x * y = y * x
  apply mat_injective
  rw [map_mul, map_mul]
  exact commute_of_sub_one_mul h1 h2

end General

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

private theorem of_mem_divisible {n : ℕ} {i : Fin (n / 2)} (hi : i ∈ divisible n) :
    ¬ Even n ∧ i.val + 1 = n / 2 := by
  unfold divisible at hi
  split_ifs at hi with he
  · exact absurd hi (Set.notMem_empty i)
  · exact ⟨he, hi⟩

theorem divisibleNormalizes_unitary (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ) :
    DivisibleNormalizes (Unitary.rootDatum hF n) := by
  intro i hi
  have hR : (Pi.single i 1 : Fin (n / 2) → ℤ) ∈ roots (isFiniteType_cartan n) (divisible n) :=
    Or.inl ⟨1, i, by simp⟩
  exact le_normalizer_of_forall_commute fun x hx y hy =>
    commute_of_mem_rootGroup_two_smul (BorelTits.unitaryInvolution_involutive hF)
      (toStd_ne_zero_of_mem_roots hR) hx hy

omit [Finite F] in
theorem levelWeyl_mem_of_mem_divisible {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) {n : ℕ}
    (ζ : traceZero σ) {i : Fin (n / 2)} (hi : i ∈ divisible n) :
    levelWeyl hσ ζ i ∈ rootGroup σ hσ n (2 • Pi.single i 1) ⊔
      rootGroup σ hσ n (-(2 • Pi.single i 1)) := by
  obtain ⟨he, hlast⟩ := of_mem_divisible hi
  have hk : ¬ i.val + 1 < n / 2 := by omega
  have h1 : 2 • weight n (lowIdx i) = toStd n (2 • Pi.single i 1) := by
    rw [toStd_nsmul_two, toStd_last_odd hk he]
  have h2 : 2 • weight n (Fin.rev (lowIdx i)) = toStd n (-(2 • Pi.single i 1)) := by
    rw [← smul_neg, toStd_nsmul_two, toStd_neg_last_odd hk he]
  rw [levelWeyl, dite_eq_right hk, longWeyl_def]
  refine mul_mem (mul_mem ?_ ?_) ?_
  · exact Subgroup.mem_sup_left (longRootHom_mem hσ _ h1 _)
  · exact Subgroup.mem_sup_right (longRootHom_mem hσ _ h2 _)
  · exact Subgroup.mem_sup_left (longRootHom_mem hσ _ h1 _)

theorem divisibleWeylMem_unitary (hF : Nat.card F = (p ^ f) ^ 2) (n : ℕ)
    (ζ : traceZero (BorelTits.unitaryInvolution F p f)) :
    DivisibleWeylMem (Unitary.rootDatum hF n)
      (levelWeyl (BorelTits.unitaryInvolution_involutive hF) ζ) := fun _ hi =>
  levelWeyl_mem_of_mem_divisible (BorelTits.unitaryInvolution_involutive hF) ζ hi

end CFSG.LieType.HighestRoot
