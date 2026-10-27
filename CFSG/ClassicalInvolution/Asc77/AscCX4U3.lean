module

public import CFSG.ClassicalInvolution.Asc77.AscCX4U2
public import CFSG.ClassicalInvolution.Asc77.AscCX4U1

public section

namespace CFSG.ClassicalInvolution.Asc77.CX.CX4.U4

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalGroups.Unitary CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] in
theorem jMat_mul_map (σ : K ≃+* K) (m n m' n' : K) :
    (!![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] : Matrix (Fin 4) (Fin 4) K) *
      σ.mapMatrix !![0, m', 0, 0; -m', 0, 0, 0; 0, 0, 0, n'; 0, 0, -n', 0] =
        !![-(m * σ m'), 0, 0, 0; 0, -(m * σ m'), 0, 0; 0, 0, -(n * σ n'), 0;
          0, 0, 0, -(n * σ n')] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply]

omit [Finite K] in
theorem map_jInv_mul (σ : K ≃+* K) (m n m' n' : K) :
    σ.mapMatrix (!![0, -m'⁻¹, 0, 0; m'⁻¹, 0, 0, 0; 0, 0, 0, -n'⁻¹; 0, 0, n'⁻¹, 0] :
      Matrix (Fin 4) (Fin 4) K) * !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] =
        !![(-(m * σ m'))⁻¹, 0, 0, 0; 0, (-(m * σ m'))⁻¹, 0, 0; 0, 0, (-(n * σ n'))⁻¹, 0;
          0, 0, 0, (-(n * σ n'))⁻¹] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, RingEquiv.mapMatrix_apply, mul_comm]

theorem twisted_comp (hK : Nat.card K = (p ^ f) ^ 2) (α α' : Su K p f 4 →* Su K p f 4)
    {m n m' n' : K}
    (hα : ∀ x, suMat (α x) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
      (unitaryInvolution K p f).mapMatrix (suMat x) *
        !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0])
    (hα' : ∀ x, suMat (α' x) = !![0, m', 0, 0; -m', 0, 0, 0; 0, 0, 0, n'; 0, 0, -n', 0] *
      (unitaryInvolution K p f).mapMatrix (suMat x) *
        !![0, -m'⁻¹, 0, 0; m'⁻¹, 0, 0, 0; 0, 0, 0, -n'⁻¹; 0, 0, n'⁻¹, 0]) :
    ∀ x, suMat (α (α' x)) =
      !![-(m * unitaryInvolution K p f m'), 0, 0, 0; 0, -(m * unitaryInvolution K p f m'), 0, 0;
        0, 0, -(n * unitaryInvolution K p f n'), 0; 0, 0, 0, -(n * unitaryInvolution K p f n')] *
      suMat x * !![(-(m * unitaryInvolution K p f m'))⁻¹, 0, 0, 0;
        0, (-(m * unitaryInvolution K p f m'))⁻¹, 0, 0;
        0, 0, (-(n * unitaryInvolution K p f n'))⁻¹, 0;
        0, 0, 0, (-(n * unitaryInvolution K p f n'))⁻¹] := by
  have hσσ := unitaryInvolution_involutive hK
  intro x
  have hmm : (unitaryInvolution K p f).mapMatrix
      ((unitaryInvolution K p f).mapMatrix (suMat x)) = suMat x := by
    ext i j
    exact hσσ (suMat x i j)
  rw [hα, hα', map_mul, map_mul, hmm, ← jMat_mul_map, ← map_jInv_mul]
  simp only [Matrix.mul_assoc]

theorem twisted_sq (hK : Nat.card K = (p ^ f) ^ 2) {X : Type} [Group X] (θ : Su K p f 4 →* X)
    (hθ : Function.Surjective θ) (s : MulAut X) (α : Su K p f 4 →* Su K p f 4)
    (hα : ∀ x, θ (α x) = s (θ x)) {m n : K} (hNm : unitaryInvolution K p f m * m = 1)
    (hNn : unitaryInvolution K p f n * n = 1)
    (hαM : ∀ x, suMat (α x) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
      (unitaryInvolution K p f).mapMatrix (suMat x) *
        !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0]) : s * s = 1 := by
  have hc := twisted_comp hK α α hαM hαM
  have hm' : -(m * unitaryInvolution K p f m) = -1 := by rw [mul_comm, hNm]
  have hn' : -(n * unitaryInvolution K p f n) = -1 := by rw [mul_comm, hNn]
  have h2 : ∀ x, α (α x) = x := by
    intro x
    apply suMat_injective
    rw [hc x, hm', hn']
    exact conj_scalar4 (neg_ne_zero.mpr one_ne_zero) (suMat x)
  ext y
  obtain ⟨x, rfl⟩ := hθ y
  show s (s (θ x)) = θ x
  rw [← hα, ← hα, h2]

theorem conj_z_sq {X : Type} [Group X] (θ : Su K p f 4 →* X) :
    MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) *
      MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) = 1 := by
  rw [← map_mul, ← map_mul, rootInvSU_mul_self_four, map_one, map_one]

theorem two_elem_cases (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {X : Type} [Group X] (θ : Su K p f 4 →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f 4)) (s : MulAut X)
    (hfix0 : ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A))
    (hfix2 : ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 2 (by norm_num) A)) {k : ℕ} (hk : s ^ (2 ^ k) = 1) :
    (s = 1 ∨ s = MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num)))) ∨
    ∃ α : Su K p f 4 →* Su K p f 4, (∀ x, θ (α x) = s (θ x)) ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
      unitaryInvolution K p f m * m = 1 ∧ unitaryInvolution K p f n * n = 1 ∧
      ∀ x, suMat (α x) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
        (unitaryInvolution K p f).mapMatrix (suMat x) *
          !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] := by
  obtain ⟨α, hα, ⟨a, b, ha, hb, hNa, hNb, hαM⟩ | ⟨m, n, hm, hn, hNm, hNn, hαM⟩⟩ :=
    fix_cases hK hp hq θ hθ hker s hfix0 hfix2
  · exact Or.inl (diag_two_elem hK hq1 θ hθ hker s α hα ha hb hNa hNb hαM hk)
  · exact Or.inr ⟨α, hα, m, n, hm, hn, hNm, hNn, hαM⟩

theorem norm_neg_mul (hK : Nat.card K = (p ^ f) ^ 2) {m m' : K}
    (hNm : unitaryInvolution K p f m * m = 1) (hNm' : unitaryInvolution K p f m' * m' = 1) :
    unitaryInvolution K p f (-(m * unitaryInvolution K p f m')) *
      (-(m * unitaryInvolution K p f m')) = 1 := by
  rw [map_neg, map_mul, unitaryInvolution_involutive hK]
  linear_combination (unitaryInvolution K p f m' * m') * hNm + hNm'

theorem fix_pgroup (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hq1 : p ^ f % 4 = 1) {X : Type} [Group X] (θ : Su K p f 4 →* X)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (Su K p f 4))
    (P : Subgroup (MulAut X)) (hP : IsPGroup 2 P)
    (hfix : ∀ s ∈ P, (∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ (blockEmb K p f 4 2 0 (by norm_num) A)) ∧
      ∀ A : Su K p f 2, s (θ (blockEmb K p f 4 2 2 (by norm_num) A)) =
        θ (blockEmb K p f 4 2 2 (by norm_num) A)) :
    (∀ s ∈ P, s * s = 1) ∧ Nat.card P ≤ 4 := by
  classical
  set c := MulAut.conj (θ (rootInvSU K p f (show 2 ≤ 4 by norm_num))) with hcdef
  have hpow : ∀ s ∈ P, ∃ k : ℕ, s ^ (2 ^ k) = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hP ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hcase : ∀ s ∈ P, (s = 1 ∨ s = c) ∨
      ∃ α : Su K p f 4 →* Su K p f 4, (∀ x, θ (α x) = s (θ x)) ∧ ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧
        unitaryInvolution K p f m * m = 1 ∧ unitaryInvolution K p f n * n = 1 ∧
        ∀ x, suMat (α x) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
          (unitaryInvolution K p f).mapMatrix (suMat x) *
            !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0] := by
    intro s hs
    obtain ⟨k, hk⟩ := hpow s hs
    exact two_elem_cases hK hp hq hq1 θ hθ hker s (hfix s hs).1 (hfix s hs).2 hk
  have hsq' : ∀ s ∈ P, s * s = 1 := by
    intro s hs
    rcases hcase s hs with (rfl | rfl) | ⟨α, hα, m, n, -, -, hNm, hNn, hαM⟩
    · exact mul_one 1
    · exact conj_z_sq θ
    · exact twisted_sq hK θ hθ s α hα hNm hNn hαM
  refine ⟨hsq', ?_⟩
  have hcard : ∀ S : Finset (MulAut X), S.card ≤ 4 → (P : Set (MulAut X)) ⊆ ↑S →
      Nat.card P ≤ 4 := by
    intro S hS hsub
    have h := Nat.card_mono (Set.toFinite _) hsub
    have e : Nat.card (↑S : Set (MulAut X)) = S.card := by
      rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
    calc Nat.card P = Nat.card (P : Set (MulAut X)) := rfl
      _ ≤ Nat.card (↑S : Set (MulAut X)) := h
      _ = S.card := e
      _ ≤ 4 := hS
  by_cases hγ : ∃ γ ∈ P, ∃ α : Su K p f 4 →* Su K p f 4, (∀ x, θ (α x) = γ (θ x)) ∧
      ∃ m n : K, m ≠ 0 ∧ n ≠ 0 ∧ unitaryInvolution K p f m * m = 1 ∧
        unitaryInvolution K p f n * n = 1 ∧
        ∀ x, suMat (α x) = !![0, m, 0, 0; -m, 0, 0, 0; 0, 0, 0, n; 0, 0, -n, 0] *
          (unitaryInvolution K p f).mapMatrix (suMat x) *
            !![0, -m⁻¹, 0, 0; m⁻¹, 0, 0, 0; 0, 0, 0, -n⁻¹; 0, 0, n⁻¹, 0]
  · obtain ⟨γ, hγP, α, hα, m, n, hm, hn, hNm, hNn, hαM⟩ := hγ
    have hγ2 : γ * γ = 1 := hsq' γ hγP
    refine hcard {1, c, γ, γ * c} Finset.card_le_four ?_
    intro s hs
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases hcase s hs with (h | h) | ⟨α', hα', m', n', hm', hn', hNm', hNn', hαM'⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · have hγs : γ * s ∈ P := mul_mem hγP hs
      obtain ⟨k, hk⟩ := hpow _ hγs
      have hlift : ∀ x, θ (α.comp α' x) = (γ * s) (θ x) := fun x => by
        rw [MonoidHom.comp_apply, hα, hα']
        rfl
      have hσm' : unitaryInvolution K p f m' ≠ 0 := (map_ne_zero _).mpr hm'
      have hσn' : unitaryInvolution K p f n' ≠ 0 := (map_ne_zero _).mpr hn'
      have hseq : s = γ * (γ * s) := by rw [← mul_assoc, hγ2, one_mul]
      rcases diag_two_elem hK hq1 θ hθ hker (γ * s) (α.comp α') hlift
          (neg_ne_zero.mpr (mul_ne_zero hm hσm')) (neg_ne_zero.mpr (mul_ne_zero hn hσn'))
          (norm_neg_mul hK hNm hNm') (norm_neg_mul hK hNn hNn')
          (twisted_comp hK α α' hαM hαM') hk with h | h
      · right; right; left
        rw [hseq, h, mul_one]
      · right; right; right
        rw [hseq, h]
  · refine hcard {1, c} (Finset.card_le_two.trans (by norm_num)) ?_
    intro s hs
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rcases hcase s hs with (h | h) | ⟨α', hα', m', n', hm', hn', hNm', hNn', hαM'⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd ⟨s, hs, α', hα', m', n', hm', hn', hNm', hNn', hαM'⟩ hγ

end CFSG.ClassicalInvolution.Asc77.CX.CX4.U4
