module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTRigid

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open scoped MatrixGroups

section Tor

variable {K : Type} [Field K] {N : ℕ}

noncomputable abbrev ctV (N : ℕ) : Fin (2 * N + 1) := q2Coord N 1 (Sum.inr 0)

@[expose] noncomputable def ctTorEntry (a : K) (i : Fin (2 * N + 1)) : K :=
  if i = ctV N then a else 1

theorem ctTorEntry_mul_inv (a : Kˣ) (i : Fin (2 * N + 1)) :
    ctTorEntry (a : K) i * ctTorEntry ((a⁻¹ : Kˣ) : K) i = 1 := by
  unfold ctTorEntry
  split_ifs
  · exact a.mul_inv
  · exact one_mul 1

theorem ctTorEntry_inv_mul (a : Kˣ) (i : Fin (2 * N + 1)) :
    ctTorEntry ((a⁻¹ : Kˣ) : K) i * ctTorEntry (a : K) i = 1 := by
  rw [mul_comm, ctTorEntry_mul_inv]

theorem ctTorEntry_of_ne {a : K} {i : Fin (2 * N + 1)} (h : i ≠ ctV N) : ctTorEntry a i = 1 :=
  ite_eq_right_iff.2 fun h' => absurd h' h

theorem ctTorEntry_ctV (a : K) : ctTorEntry a (ctV N) = a :=
  ite_eq_left_iff.2 fun h => absurd rfl h

@[expose] noncomputable def ctTorGL (a : Kˣ) : GL (Fin (2 * N + 1)) K where
  val := diagonal (ctTorEntry (a : K))
  inv := diagonal (ctTorEntry ((a⁻¹ : Kˣ) : K))
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact ctTorEntry_mul_inv a i
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact ctTorEntry_inv_mul a i

@[expose] noncomputable def ctTorAut (a : Kˣ) : MulAut (SpecialLinearGroup (Fin (2 * N + 1)) K) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation (2 * N + 1) K
    (ctTorGL a)

theorem coe_ctTorAut (a : Kˣ) (x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
    ((ctTorAut a x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
      diagonal (ctTorEntry (a : K)) * (x : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
        diagonal (ctTorEntry ((a⁻¹ : Kˣ) : K)) :=
  CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix _ K _ x

theorem ctTorAut_apply_apply (a : Kˣ) (x : SpecialLinearGroup (Fin (2 * N + 1)) K)
    (i j : Fin (2 * N + 1)) :
    ((ctTorAut a x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) i j =
      ctTorEntry (a : K) i * (x : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) i j *
        ctTorEntry ((a⁻¹ : Kˣ) : K) j := by
  rw [coe_ctTorAut, mul_diagonal, diagonal_mul]

theorem ctTorAut_one : ctTorAut (N := N) (K := K) 1 = 1 := by
  ext1 x
  apply Subtype.ext
  ext i j
  rw [ctTorAut_apply_apply, MulAut.one_apply, inv_one]
  unfold ctTorEntry
  split_ifs <;> simp

theorem ctTorAut_mem_blockSpecialLinear (a : Kˣ) {W : Finset (Fin (2 * N + 1))}
    {x : SpecialLinearGroup (Fin (2 * N + 1)) K} (hx : x ∈ blockSpecialLinear W) :
    ctTorAut a x ∈ blockSpecialLinear W := by
  rw [mem_blockSpecialLinear] at hx ⊢
  intro i j hij
  rw [ctTorAut_apply_apply, hx i j hij]
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, mul_one, ctTorEntry_mul_inv]
  · rw [Matrix.one_apply_ne h, mul_zero, zero_mul]

theorem ctTorAut_mem_q2Block (a : Kˣ) {R : Finset (Fin N)}
    {x : SpecialLinearGroup (Fin (2 * N + 1)) K} (hx : x ∈ q2Block 1 K R) :
    ctTorAut a x ∈ q2Block 1 K R :=
  ctTorAut_mem_blockSpecialLinear a hx

theorem q2Coord_inl_ne_ctV (u : Fin N ⊕ Fin N) : q2Coord N 1 (Sum.inl u) ≠ ctV N := fun h =>
  Sum.inl_ne_inr ((q2Coord N 1).injective h)

theorem ctTorAut_ctEmbed [CharP K 2] (a : Kˣ) (y : StatedSp N K) :
    ctTorAut a (ctEmbed 1 y) = ctEmbed 1 y := by
  apply Subtype.ext
  ext i j
  obtain ⟨w, rfl⟩ := (q2Coord N 1).surjective i
  obtain ⟨w', rfl⟩ := (q2Coord N 1).surjective j
  rw [ctTorAut_apply_apply, ctEmbed_apply_q2Coord]
  rcases w with u | e <;> rcases w' with v | e'
  · rw [ctTorEntry_of_ne (q2Coord_inl_ne_ctV u), ctTorEntry_of_ne (q2Coord_inl_ne_ctV v), one_mul,
      mul_one]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply, mul_zero, zero_mul]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, zero_mul]
  · obtain rfl : e = 0 := Subsingleton.elim _ _
    obtain rfl : e' = 0 := Subsingleton.elim _ _
    rw [fromBlocks_apply₂₂, Matrix.one_apply_eq, mul_one, ctTorEntry_mul_inv]

end Tor

section CommuteBlock

variable {K : Type} [Field K] {n : ℕ}

theorem commute_block_of_rowcol {W : Finset (Fin n)} {Q : Matrix (Fin n) (Fin n) K}
    {π : Fin n → Fin n} (hπ : ∀ a, π (π a) = a) (hπW : ∀ a, a ∉ W → π a ∉ W) {c : K}
    (hin : ∀ a ∈ W, (∀ i, Q i a = if i = a then c else 0) ∧ (∀ j, Q a j = if j = a then c else 0))
    (hout : ∀ a, a ∉ W →
      (∀ j, Q a j = if j = π a then 1 else 0) ∧ (∀ i, Q i a = if i = π a then 1 else 0))
    {y : SpecialLinearGroup (Fin n) K} (hy : y ∈ blockSpecialLinear W) :
    Q * (y : Matrix (Fin n) (Fin n) K) = (y : Matrix (Fin n) (Fin n) K) * Q := by
  ext i j
  by_cases hi : i ∈ W
  · rw [mul_apply_of_row ((hin i hi).2)]
    by_cases hj : j ∈ W
    · rw [mul_apply_of_col ((hin j hj).1), mul_comm]
    · rw [mul_apply_of_col_perm ((hout j hj).2),
        apply_eq_zero_of_mem_blockSpecialLinear hy (fun h' : i = j => hj (h' ▸ hi)) (Or.inr hj),
        apply_eq_zero_of_mem_blockSpecialLinear hy (fun h' : i = π j => hπW j hj (h' ▸ hi))
          (Or.inr (hπW j hj)), mul_zero]
  · rw [mul_apply_of_row_perm ((hout i hi).1)]
    by_cases hj : j ∈ W
    · rw [mul_apply_of_col ((hin j hj).1),
        apply_eq_zero_of_mem_blockSpecialLinear hy (fun h' : π i = j => hπW i hi (h' ▸ hj))
          (Or.inl (hπW i hi)),
        apply_eq_zero_of_mem_blockSpecialLinear hy (fun h' : i = j => hi (h' ▸ hj)) (Or.inl hi),
        zero_mul]
    · rw [mul_apply_of_col_perm ((hout j hj).2),
        (mem_blockSpecialLinear.mp hy) _ _ (Or.inl (hπW i hi)),
        (mem_blockSpecialLinear.mp hy) _ _ (Or.inl hi), Matrix.one_apply, Matrix.one_apply]
      congr 1
      exact propext ⟨fun h => by rw [← h, hπ], fun h => by rw [h, hπ]⟩

end CommuteBlock

section OddRigid

variable {K : Type} [Field K] {N : ℕ}

theorem eq_ctV_or_exists_plane_of_mem_compl {R : Finset (Fin N)} {a : Fin (2 * N + 1)}
    (ha : a ∈ (planeCoordsQ2 1 R)ᶜ) :
    a = ctV N ∨ ∃ p, p ∉ R ∧ (a = ctE N 1 p ∨ a = ctF N 1 p) := by
  obtain ⟨w, rfl⟩ := (q2Coord N 1).surjective a
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2] at ha
  rcases w with (u | u) | i
  · exact Or.inr ⟨u, ha, Or.inl rfl⟩
  · exact Or.inr ⟨u, ha, Or.inr rfl⟩
  · left
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl

theorem ctV_mem_compl (R : Finset (Fin N)) : ctV N ∈ (planeCoordsQ2 1 R)ᶜ := by
  rw [Finset.mem_compl, q2Coord_mem_planeCoordsQ2]
  exact not_inPlanes_inr R 0

theorem exists_ctTor_conj_of_rowcol {R : Finset (Fin N)} (T : GL (Fin (2 * N + 1)) K)
    {π : Fin (2 * N + 1) → Fin (2 * N + 1)} (hπ : ∀ a, π (π a) = a)
    (hπW : ∀ a, a ∉ (planeCoordsQ2 1 R)ᶜ → π a ∉ (planeCoordsQ2 1 R)ᶜ) {c : K} (hc : c ≠ 0)
    (hrc : ∀ p, p ∉ R → ∀ a, (a = ctE N 1 p ∨ a = ctF N 1 p) →
      (∀ i, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) i a = if i = a then c else 0) ∧
        (∀ j, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) a j = if j = a then c else 0))
    (hoff : ∀ a, a ∉ (planeCoordsQ2 1 R)ᶜ →
      (∀ j, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) a j = if j = π a then 1 else 0) ∧
        (∀ i, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) i a = if i = π a then 1 else 0)) :
    ∃ a : Kˣ, ∀ y : SpecialLinearGroup (Fin (2 * N + 1)) K, y ∈ q2Block 1 K R →
      (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
          (y : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
          ((T⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
        ((ctTorAut a y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
          Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) := by
  set W := (planeCoordsQ2 1 R)ᶜ with hW
  set A := (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) with hA
  have hvW : ctV N ∈ W := ctV_mem_compl R
  have hrowv : ∀ j, j ≠ ctV N → A (ctV N) j = 0 := by
    intro j hj
    by_cases hjW : j ∈ W
    · rcases eq_ctV_or_exists_plane_of_mem_compl hjW with h | ⟨p, hp, hpj⟩
      · exact absurd h hj
      · rw [(hrc p hp j hpj).1 (ctV N), ite_eq_right (Ne.symm hj)]
    · rw [(hoff j hjW).2 (ctV N), ite_eq_right (fun h : ctV N = π j => hπW j hjW (h ▸ hvW))]
  have hcolv : ∀ i, i ≠ ctV N → A i (ctV N) = 0 := by
    intro i hi
    by_cases hiW : i ∈ W
    · rcases eq_ctV_or_exists_plane_of_mem_compl hiW with h | ⟨p, hp, hpi⟩
      · exact absurd h hi
      · rw [(hrc p hp i hpi).2 (ctV N), ite_eq_right (Ne.symm hi)]
    · rw [(hoff i hiW).1 (ctV N), ite_eq_right (fun h : ctV N = π i => hπW i hiW (h ▸ hvW))]
  set μ := A (ctV N) (ctV N) with hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply Matrix.GeneralLinearGroup.det_ne_zero T
    refine Matrix.det_eq_zero_of_row_eq_zero (ctV N) fun j => ?_
    by_cases hj : j = ctV N
    · rw [hj]
      exact h0
    · exact hrowv j hj
  set a : Kˣ := Units.mk0 (μ / c) (div_ne_zero hμ0 hc) with ha
  refine ⟨a, fun y hy => ?_⟩
  set Q : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K :=
    diagonal (ctTorEntry ((a⁻¹ : Kˣ) : K)) * A with hQ
  have hQapp : ∀ i j, Q i j = ctTorEntry ((a⁻¹ : Kˣ) : K) i * A i j := fun i j => by
    rw [hQ, diagonal_mul]
  have hainv : ((a⁻¹ : Kˣ) : K) * μ = c := by
    rw [Units.val_inv_eq_inv_val, ha, Units.val_mk0, inv_div]
    field_simp
  have hin : ∀ b ∈ W, (∀ i, Q i b = if i = b then c else 0) ∧
      (∀ j, Q b j = if j = b then c else 0) := by
    intro b hb
    rcases eq_ctV_or_exists_plane_of_mem_compl hb with rfl | ⟨p, hp, hpb⟩
    · refine ⟨fun i => ?_, fun j => ?_⟩
      · rw [hQapp]
        by_cases hi : i = ctV N
        · rw [hi, ite_eq_left rfl, ctTorEntry_ctV, ← hμ, hainv]
        · rw [ite_eq_right hi, hcolv i hi, mul_zero]
      · rw [hQapp, ctTorEntry_ctV]
        by_cases hj : j = ctV N
        · rw [hj, ite_eq_left rfl, ← hμ, hainv]
        · rw [ite_eq_right hj, hrowv j hj, mul_zero]
    · have hbv : b ≠ ctV N := by
        rcases hpb with rfl | rfl
        · exact q2Coord_inl_ne_ctV _
        · exact q2Coord_inl_ne_ctV _
      refine ⟨fun i => ?_, fun j => ?_⟩
      · rw [hQapp, (hrc p hp b hpb).1 i]
        by_cases hi : i = b
        · rw [hi, ite_eq_left rfl, ctTorEntry_of_ne hbv, one_mul]
        · rw [ite_eq_right hi, mul_zero]
      · rw [hQapp, ctTorEntry_of_ne hbv, one_mul, (hrc p hp b hpb).2 j]
  have hout : ∀ b, b ∉ W → (∀ j, Q b j = if j = π b then 1 else 0) ∧
      (∀ i, Q i b = if i = π b then 1 else 0) := by
    intro b hb
    have hbv : b ≠ ctV N := fun h => hb (h ▸ hvW)
    have hπbv : π b ≠ ctV N := fun h => hπW b hb (h ▸ hvW)
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [hQapp, ctTorEntry_of_ne hbv, one_mul, (hoff b hb).1 j]
    · rw [hQapp, (hoff b hb).2 i]
      by_cases hi : i = π b
      · rw [hi, ite_eq_left rfl, ctTorEntry_of_ne hπbv, one_mul]
      · rw [ite_eq_right hi, mul_zero]
  have hcomm := commute_block_of_rowcol hπ hπW hin hout hy
  have hDQ : diagonal (ctTorEntry (a : K)) * Q = A := by
    rw [hQ, ← Matrix.mul_assoc, diagonal_mul_diagonal]
    have h1 : (fun i : Fin (2 * N + 1) => ctTorEntry (a : K) i * ctTorEntry ((a⁻¹ : Kˣ) : K) i) =
        fun _ => 1 := funext (ctTorEntry_mul_inv a)
    rw [h1, diagonal_one, Matrix.one_mul]
  have hQT : Q * ((T⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
      diagonal (ctTorEntry ((a⁻¹ : Kˣ) : K)) := by
    rw [hQ, Matrix.mul_assoc, hA, Units.mul_inv, Matrix.mul_one]
  rw [coe_ctTorAut]
  calc A * (y : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
        ((T⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)
      = diagonal (ctTorEntry (a : K)) * Q * (y : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
        ((T⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) := by
          rw [hDQ]
    _ = diagonal (ctTorEntry (a : K)) * (Q * (y : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)) *
        ((T⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) := by
          rw [Matrix.mul_assoc (diagonal _) Q]
    _ = diagonal (ctTorEntry (a : K)) * (y : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
        (Q * ((T⁻¹ : GL (Fin (2 * N + 1)) K) :
          Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)) := by
          rw [hcomm]
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [hQT]

variable [CharP K 2] [Finite K]

theorem exists_ctTor_of_fix_of_conj_form {R : Finset (Fin N)} {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (θ : MulAut (q2Block 1 K R)) (hθ : ∀ s ∈ ctSpBlock 1 K R, θ s = s)
    (A₀ : GL (Fin ((planeCoordsQ2 1 R)ᶜ.card)) K) (σ : K ≃+* K)
    (h : ∀ x : q2Block 1 K R,
      (((θ x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
        ((ctBlockGL (planeCoordsQ2 1 R)ᶜ A₀ : GL (Fin (2 * N + 1)) K) :
          Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
          (((x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
            Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)).map σ *
          (((ctBlockGL (planeCoordsQ2 1 R)ᶜ A₀)⁻¹ : GL (Fin (2 * N + 1)) K) :
            Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)) :
    ∃ a : Kˣ, ∀ x : q2Block 1 K R,
      ((θ x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) =
        ctTorAut a (x : SpecialLinearGroup (Fin (2 * N + 1)) K) := by
  set M : GL (Fin (2 * N + 1)) K := ctBlockGL (planeCoordsQ2 1 R)ᶜ A₀ with hM
  have hfix : ∀ y ∈ spBlock K Rᶜ, (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
      ((ctEmbed 1 y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K).map σ =
      ((ctEmbed 1 y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) * M := by
    intro y hy
    have h1 := h ⟨ctEmbed 1 y, ctEmbed_mem_q2Block_iff.2 hy⟩
    rw [hθ _ (mem_ctSpBlock.2 ⟨y, hy, rfl⟩)] at h1
    have h2 := congrArg (· * (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)) h1
    simp only [Matrix.mul_assoc] at h2
    rw [Units.inv_mul, Matrix.mul_one] at h2
    exact h2.symm
  obtain ⟨hσ, hne, hrc⟩ := eq_one_and_rowcol_of_fix_ctSp hp₀ hfix
  obtain ⟨a, ha⟩ := exists_ctTor_conj_of_rowcol (R := R) M (π := id) (fun _ => rfl)
    (fun _ hb => hb) hne hrc (fun b hb => ctBlockGL_apply_of_notMem A₀ hb)
  refine ⟨a, fun x => Subtype.ext ?_⟩
  have hx := h x
  rw [hσ] at hx
  have hmap : (((x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)).map ((1 : K ≃+* K) : K → K) =
      ((x : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) := by
    ext
    rfl
  rw [hmap] at hx
  rw [hx]
  exact ha _ x.2

theorem exists_ctTor_of_fix_of_dual_form {R : Finset (Fin N)} {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (θ : MulAut (q2Block 1 K R)) (hθ : ∀ s ∈ ctSpBlock 1 K R, θ s = s)
    (A₀ : GL (Fin ((planeCoordsQ2 1 R)ᶜ.card)) K) (σ : K ≃+* K)
    (h : ∀ x : q2Block 1 K R,
      (((θ x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
        ((ctBlockGL (planeCoordsQ2 1 R)ᶜ A₀ : GL (Fin (2 * N + 1)) K) :
          Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
          ((((x⁻¹ : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) :
            Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K))ᵀ.map σ *
          (((ctBlockGL (planeCoordsQ2 1 R)ᶜ A₀)⁻¹ : GL (Fin (2 * N + 1)) K) :
            Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)) :
    ∃ a : Kˣ, ∀ x : q2Block 1 K R,
      ((θ x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) =
        ctTorAut a (ctGraph 1 (x : SpecialLinearGroup (Fin (2 * N + 1)) K)) := by
  set M : GL (Fin (2 * N + 1)) K := ctBlockGL (planeCoordsQ2 1 R)ᶜ A₀ with hM
  set P : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K := q2GramMat 1 with hP
  set PG : GL (Fin (2 * N + 1)) K := SpecialLinearGroup.toGL (ctEmbed 1 (q2SpJ (N := N) (K := K)))
    with hPG
  have hPGm : (PG : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) = P := by
    change q2EmbedMat 1 (mat N K q2SpJ) = q2GramMat 1
    rw [mat_q2SpJ]
    rfl
  have hPGinv : ((PG⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
      P := by
    rw [hPG, ← map_inv, ctEmbed_q2SpJ_inv]
    exact hPGm
  have hP2 : P * P = 1 := q2GramMat_mul_self
  set T : GL (Fin (2 * N + 1)) K := M * PG with hT
  have hTm : (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
      (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) * P := by
    rw [hT, Units.val_mul, hPGm]
  have hTinv : ((T⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
      P * ((M⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) := by
    rw [hT, _root_.mul_inv_rev, Units.val_mul, hPGinv]
  have hfix : ∀ y ∈ spBlock K Rᶜ, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
      ((ctEmbed 1 y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K).map σ =
      ((ctEmbed 1 y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) * T := by
    intro y hy
    have h1 := h ⟨ctEmbed 1 y, ctEmbed_mem_q2Block_iff.2 hy⟩
    rw [hθ _ (mem_ctSpBlock.2 ⟨y, hy, rfl⟩)] at h1
    change ((ctEmbed 1 y : SpecialLinearGroup (Fin (2 * N + 1)) K) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) =
      (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) *
        ((((ctEmbed 1 y)⁻¹ : SpecialLinearGroup (Fin (2 * N + 1)) K) :
          Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K))ᵀ.map σ *
        ((M⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) at h1
    rw [inv_transpose_ctEmbed, Matrix.map_mul, Matrix.map_mul, map_q2GramMat] at h1
    rw [hTm]
    conv_rhs => rw [h1]
    rw [← hP]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul_cancel_left, hP2, Matrix.mul_one]
  obtain ⟨hσ, hne, hrc⟩ := eq_one_and_rowcol_of_fix_ctSp hp₀ hfix
  have hparW : ∀ a, a ∉ (planeCoordsQ2 1 R)ᶜ → q2Par N 1 a ∉ (planeCoordsQ2 1 R)ᶜ := by
    intro a ha
    rw [Finset.mem_compl, not_not] at ha ⊢
    exact q2Par_mem_planeCoordsQ2.2 ha
  have hoffT : ∀ a, a ∉ (planeCoordsQ2 1 R)ᶜ →
      (∀ j, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) a j =
        if j = q2Par N 1 a then 1 else 0) ∧
      (∀ i, (T : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) i a =
        if i = q2Par N 1 a then 1 else 0) := by
    intro a ha
    refine ⟨fun j => ?_, fun i => ?_⟩
    · rw [hTm, mul_apply_of_row_perm ((ctBlockGL_apply_of_notMem A₀ ha).1), hP,
        q2GramMat_apply]
    · have hcol : ∀ k, P k a = if k = q2Par N 1 a then 1 else 0 := by
        intro k
        rw [hP, q2GramMat_apply]
        congr 1
        exact propext ⟨fun h => by rw [h, q2Par_q2Par], fun h => by rw [h, q2Par_q2Par]⟩
      rw [hTm, mul_apply_of_col_perm hcol, (ctBlockGL_apply_of_notMem A₀ (hparW a ha)).2 i]
  obtain ⟨a, ha⟩ := exists_ctTor_conj_of_rowcol (R := R) T (π := q2Par N 1) q2Par_q2Par hparW
    hne hrc hoffT
  refine ⟨a, fun x => Subtype.ext ?_⟩
  have hx := h x
  rw [hσ] at hx
  set z : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K :=
    ((((x : SpecialLinearGroup (Fin (2 * N + 1)) K))⁻¹ : SpecialLinearGroup (Fin (2 * N + 1)) K) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)ᵀ with hz
  have hmap : ((((x⁻¹ : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) :
      Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K))ᵀ.map ((1 : K ≃+* K) : K → K) = z := by
    ext
    rfl
  rw [hmap] at hx
  have hy : ctGraph 1 (x : SpecialLinearGroup (Fin (2 * N + 1)) K) ∈ q2Block 1 K R :=
    ctGraph_mem_q2Block x.2
  rw [hx, ← ha _ hy, coe_ctGraph, ← hz, ← hP, hTm, hTinv]
  calc (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) * z *
        ((M⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K)
      = (M : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) * (P * P) * z * (P * P) *
        ((M⁻¹ : GL (Fin (2 * N + 1)) K) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) K) := by
          rw [hP2, Matrix.mul_one, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_ctTor_of_fix {R : Finset (Fin N)} (h3 : 3 ≤ ((planeCoordsQ2 1 R)ᶜ).card)
    {p₀ : Fin N} (hp₀ : p₀ ∉ R) (θ : MulAut (q2Block 1 K R))
    (hθ : ∀ s ∈ ctSpBlock 1 K R, θ s = s) :
    ∃ a : Kˣ, (∀ x : q2Block 1 K R,
        ((θ x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) =
          ctTorAut a (x : SpecialLinearGroup (Fin (2 * N + 1)) K)) ∨
      ∀ x : q2Block 1 K R, ((θ x : q2Block 1 K R) : SpecialLinearGroup (Fin (2 * N + 1)) K) =
        ctTorAut a (ctGraph 1 (x : SpecialLinearGroup (Fin (2 * N + 1)) K)) := by
  obtain ⟨A₀, σ, h | h⟩ := exists_matrix_form_of_mulAut_block (K := K) (planeCoordsQ2 1 R)ᶜ h3 θ
  · obtain ⟨a, ha⟩ := exists_ctTor_of_fix_of_conj_form hp₀ θ hθ A₀ σ h
    exact ⟨a, Or.inl ha⟩
  · obtain ⟨a, ha⟩ := exists_ctTor_of_fix_of_dual_form hp₀ θ hθ A₀ σ h
    exact ⟨a, Or.inr ha⟩

theorem exists_ctTor_of_range_eq {G : Type*} [Group G] {R : Finset (Fin N)}
    (h3 : 3 ≤ ((planeCoordsQ2 1 R)ᶜ).card) {p₀ : Fin N} (hp₀ : p₀ ∉ R)
    (φP φQ : q2Block 1 K R →* G) (hP : Function.Injective φP) (hQ : Function.Injective φQ)
    (hr : φP.range = φQ.range) (hS : ∀ s ∈ ctSpBlock 1 K R, φP s = φQ s) :
    ∃ a : Kˣ, (∀ x : q2Block 1 K R,
        φP x = φQ ⟨ctTorAut a (x : SpecialLinearGroup (Fin (2 * N + 1)) K),
          ctTorAut_mem_q2Block a x.2⟩) ∨
      ∀ x : q2Block 1 K R,
        φP x = φQ ⟨ctTorAut a (ctGraph 1 (x : SpecialLinearGroup (Fin (2 * N + 1)) K)),
          ctTorAut_mem_q2Block a (ctGraph_mem_q2Block x.2)⟩ := by
  set θ : MulAut (q2Block 1 K R) := ((MonoidHom.ofInjective hP).trans
    (MulEquiv.subgroupCongr hr)).trans (MonoidHom.ofInjective hQ).symm with hθdef
  have hθ : ∀ y, φQ (θ y) = φP y := by
    intro y
    have h := (MonoidHom.ofInjective hQ).apply_symm_apply
      (MulEquiv.subgroupCongr hr (MonoidHom.ofInjective hP y))
    have h2 := congrArg Subtype.val h
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨a, h1 | h1⟩ := exists_ctTor_of_fix h3 hp₀ θ
    (fun s hs => hQ ((hθ s).trans (hS s hs)))
  · refine ⟨a, Or.inl fun x => ?_⟩
    rw [← hθ x]
    exact congrArg φQ (Subtype.ext (h1 x))
  · refine ⟨a, Or.inr fun x => ?_⟩
    rw [← hθ x]
    exact congrArg φQ (Subtype.ext (h1 x))

end OddRigid

end CFSG.SeitzReduction.SymplecticPilot
