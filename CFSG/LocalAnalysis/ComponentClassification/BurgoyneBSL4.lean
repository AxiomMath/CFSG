module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSlices
public import CFSG.LocalAnalysis.ComponentClassification.BurgoynePSLSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.PSL
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem one_sub_compInd (J : Finset (Fin n)) :
    (1 : Matrix (Fin n) (Fin n) K) - compInd K J = diagonal fun i => if i ∈ J then 1 else 0 := by
  rw [compInd, ← diagonal_one, diagonal_sub]
  congr 1
  funext i
  by_cases hi : i ∈ J <;> simp [hi]

theorem one_sub_compInd_mul_one_sub_compInd {I I' : Finset (Fin n)} (hII : Disjoint I I') :
    (1 - compInd K I) * (1 - compInd K I') = 0 := by
  rw [one_sub_compInd, one_sub_compInd, diagonal_mul_diagonal, ← diagonal_zero]
  congr 1
  funext i
  by_cases hi : i ∈ I
  · simp [hi, Finset.disjoint_left.1 hII hi]
  · simp [hi]

theorem coordBlock_commute_of_disjoint {I I' : Finset (Fin n)} (hII : Disjoint I I')
    {g h : SL(n, K)} (hg : g ∈ coordBlock K I) (hh : h ∈ coordBlock K I') : g * h = h * g := by
  have hsplit : ∀ {J : Finset (Fin n)} {x : SL(n, K)}, x ∈ coordBlock K J →
      (x : Matrix (Fin n) (Fin n) K) - 1 = ((x : Matrix (Fin n) (Fin n) K) - 1) *
        (1 - compInd K J) ∧
      (x : Matrix (Fin n) (Fin n) K) - 1 = (1 - compInd K J) *
        ((x : Matrix (Fin n) (Fin n) K) - 1) := by
    intro J x hx
    obtain ⟨h1, h2⟩ := hx
    constructor
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h2]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h1]
      abel
  have hz := one_sub_compInd_mul_one_sub_compInd (K := K) hII
  have hz' : (1 - compInd K I') * (1 - compInd K I) = 0 := by
    have : (1 - compInd K I') * (1 - compInd K I) = (1 - compInd K I) * (1 - compInd K I') := by
      rw [one_sub_compInd, one_sub_compInd, diagonal_mul_diagonal, diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    rw [this, hz]
  set G := (g : Matrix (Fin n) (Fin n) K) with hG
  set H := (h : Matrix (Fin n) (Fin n) K) with hH
  have e1 : (G - 1) * (H - 1) = 0 := by
    rw [(hsplit hg).1, (hsplit hh).2, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - compInd K I),
      hz, Matrix.zero_mul, Matrix.mul_zero]
  have e2 : (H - 1) * (G - 1) = 0 := by
    rw [(hsplit hh).1, (hsplit hg).2, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - compInd K I'),
      hz', Matrix.zero_mul, Matrix.mul_zero]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← hG, ← hH]
  have hGH : G * H = (G - 1) * (H - 1) + G + H - 1 := by noncomm_ring
  have hHG : H * G = (H - 1) * (G - 1) + G + H - 1 := by noncomm_ring
  rw [hGH, hHG, e1, e2]

variable {a b c d : Fin 4}

theorem signMat_mul_signMat_eq_neg_one
    (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4))) :
    signMat K {a, b} * signMat K {c, d} = -1 := by
  have hf : (fun x : Fin 4 => (if x ∈ ({a, b} : Finset (Fin 4)) then (-1 : K) else 1) *
      (if x ∈ ({c, d} : Finset (Fin 4)) then (-1 : K) else 1)) = fun _ => -1 := by
    funext x
    by_cases hx : x ∈ ({a, b} : Finset (Fin 4))
    · have hx' : x ∉ ({c, d} : Finset (Fin 4)) := (hpair x).1 hx
      simp only [hx, hx', ↓reduceIte]
      ring
    · have hx' : x ∈ ({c, d} : Finset (Fin 4)) := by
        by_contra h
        exact hx ((hpair x).2 h)
      simp only [hx, hx', ↓reduceIte]
      ring
  rw [signMat, signMat, diagonal_mul_diagonal, hf]
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem disjoint_of_pair
    (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4))) :
    Disjoint ({a, b} : Finset (Fin 4)) {c, d} := by
  rw [Finset.disjoint_left]
  intro x hx
  exact (hpair x).1 hx

theorem pairInvolution_eq (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4))) :
    pairInvolution K hcd = pairInvolution K hab := by
  have h : proj 4 K (signSL K {c, d} (even_card_pair hcd)) =
      proj 4 K (signSL K {a, b} (even_card_pair hab)) := by
    rw [proj_eq_proj_iff, mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
    have hinv : (signSL K {c, d} (even_card_pair hcd))⁻¹ = signSL K {c, d} (even_card_pair hcd) :=
      inv_eq_of_mul_eq_one_right (signSL_mul_self _ _)
    rw [← Matrix.SpecialLinearGroup.coe_inv, hinv, coe_signSL, coe_signSL,
      ← (show signMat K {a, b} * signMat K {c, d} = signMat K {c, d} * signMat K {a, b} by
        rw [signMat, signMat, diagonal_mul_diagonal, diagonal_mul_diagonal]
        congr 1
        funext x
        ring), signMat_mul_signMat_eq_neg_one hpair]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  change conjProj 4 K _ = conjProj 4 K _
  simp only [conjProj, MonoidHom.comp_apply, h]

theorem pairSlice_commute
    (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4)))
    {x y : MulAut (projectiveSL 4 K)} (hx : x ∈ pairSlice K a b) (hy : y ∈ pairSlice K c d) :
    x * y = y * x := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨h, hh, rfl⟩ := hy
  rw [← map_mul, ← map_mul, coordBlock_commute_of_disjoint (disjoint_of_pair hpair) hg hh]

theorem pairSlice_inter
    (hinj : Function.Injective (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)))
    (hab : a ≠ b) (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔
      x ∉ ({c, d} : Finset (Fin 4)))
    (hu2 : pairInvolution K hab * pairInvolution K hab = 1) {x : MulAut (projectiveSL 4 K)}
    (hx₁ : x ∈ pairSlice K a b) (hx₂ : x ∈ pairSlice K c d) :
    x = 1 ∨ x = pairInvolution K hab := by
  have hZ := center_pairSlice (K := K) (by omega) hinj hab
  have hxZ : x ∈ (center (pairSlice K a b)).map (pairSlice K a b).subtype := by
    refine ⟨⟨x, hx₁⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    rintro ⟨y, hy⟩
    exact Subtype.ext (pairSlice_commute hpair hy hx₂)
  rw [hZ] at hxZ
  exact eq_one_or_eq_of_mem_zpowers (by rw [pow_two]; exact hu2) hxZ

abbrev PairBlockScalar {m : ℕ} (a b : Fin m) (M : Matrix (Fin m) (Fin m) K) : Prop :=
  M a a = M b b ∧ M a b = 0 ∧ M b a = 0

variable [Finite K]

theorem pair_actsProperly
    (hinj : Function.Injective (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)))
    {B : Subgroup (MulAut (projectiveSL 4 K))} {A : GL (Fin 4) K}
    (hAt : orderOf (conjAut 4 K A) = 2) (hab : a ≠ b)
    (hAblk : compInd K {a, b} * (A : Matrix (Fin 4) (Fin 4) K) = A * compInd K {a, b})
    (hAnc : ¬ PairBlockScalar a b (A : Matrix (Fin 4) (Fin 4) K))
    (hcore : ∀ y ∈ oddCoreIn B (conjAut 4 K A), ∃ D : GL (Fin 4) K, y = conjAut 4 K D ∧
      compInd K {a, b} * (D : Matrix (Fin 4) (Fin 4) K) = D * compInd K {a, b} ∧
      (PairBlockScalar a b (D : Matrix (Fin 4) (Fin 4) K) → conjAut 4 K D = 1))
    {Y : Subgroup (MulAut (projectiveSL 4 K))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (conjAut 4 K A)) :
    ActsProperly (conjAut 4 K A) Y (pairSlice K a b) ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  set p := ringChar K with hp
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  refine actsProperly_of_core hAt hY hYO (conjAut_mem_normalizer_pairSlice hAblk) ?_ ?_ ?_
  · by_contra h
    push Not at h
    exact hAnc (pairBlock_of_commute (p := p) hinj hab h)
  · intro y hy
    obtain ⟨D, rfl, hDb, -⟩ := hcore y hy
    exact conjAut_mem_normalizer_pairSlice hDb
  · intro y hy hc
    obtain ⟨D, rfl, -, hDs⟩ := hcore y hy
    exact hDs (pairBlock_of_commute (p := p) hinj hab hc)

end CFSG.ComponentClassification.Burgoyne.B
