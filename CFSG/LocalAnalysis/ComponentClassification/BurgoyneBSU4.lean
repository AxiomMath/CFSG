module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneBSL4
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneUSlice

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.B

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.Burgoyne.Proj CFSG.ComponentClassification.Burgoyne.U
open CFSG.ComponentClassification.Burgoyne.PSL (compInd signMat commute_signMat_iff
  exists_not_mem_pair)
open scoped MatrixGroups

variable {n : ℕ} {K : Type} [Field K]

theorem mat_commute_of_disjoint {I I' : Finset (Fin n)} (hII : Disjoint I I')
    {G H : Matrix (Fin n) (Fin n) K} (hG1 : compInd K I * G = compInd K I)
    (hG2 : G * compInd K I = compInd K I) (hH1 : compInd K I' * H = compInd K I')
    (hH2 : H * compInd K I' = compInd K I') : G * H = H * G := by
  have hsplit : ∀ {J : Finset (Fin n)} {M : Matrix (Fin n) (Fin n) K},
      compInd K J * M = compInd K J → M * compInd K J = compInd K J →
      M - 1 = (M - 1) * (1 - compInd K J) ∧ M - 1 = (1 - compInd K J) * (M - 1) := by
    intro J M h1 h2
    constructor
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h2]
      abel
    · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, h1]
      abel
  have hz := one_sub_compInd_mul_one_sub_compInd (K := K) hII
  have hz' : (1 - compInd K I') * (1 - compInd K I) = 0 := by
    rw [← one_sub_compInd_mul_one_sub_compInd (K := K) hII, one_sub_compInd I,
      one_sub_compInd I', diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  have e1 : (G - 1) * (H - 1) = 0 := by
    rw [(hsplit hG1 hG2).1, (hsplit hH1 hH2).2, Matrix.mul_assoc,
      ← Matrix.mul_assoc (1 - compInd K I), hz, Matrix.zero_mul, Matrix.mul_zero]
  have e2 : (H - 1) * (G - 1) = 0 := by
    rw [(hsplit hH1 hH2).1, (hsplit hG1 hG2).2, Matrix.mul_assoc,
      ← Matrix.mul_assoc (1 - compInd K I'), hz', Matrix.zero_mul, Matrix.mul_zero]
  have hGH : G * H = (G - 1) * (H - 1) + G + H - 1 := by noncomm_ring
  have hHG : H * G = (H - 1) * (G - 1) + G + H - 1 := by noncomm_ring
  rw [hGH, hHG, e1, e2]

variable {p f : ℕ} (h : UnitaryFieldData p f K)

include h in
theorem utwo_ne_zero (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  intro e
  have e' : ((2 : ℕ) : K) = 0 := by exact_mod_cast e
  rw [CharP.cast_eq_zero_iff K p] at e'
  have := Nat.le_of_dvd (by norm_num) e'
  have := h.prime.two_le
  exact hp2 (by omega)

theorem ringChar_fixedSubfield_ne_two [Finite K] [Fact p.Prime] [CharP K p] (h2 : (2 : K) ≠ 0) :
    ringChar (CFSG.LieType.Steinberg.fixedSubfield K p f) ≠ 2 := by
  set F := CFSG.LieType.Steinberg.fixedSubfield K p f
  have h2F : (2 : F) ≠ 0 := fun e => h2 (by
    have h1 : ((1 + 1 : F) : K) = 1 + 1 := by rw [Subfield.coe_add, Subfield.coe_one]
    rw [← one_add_one_eq_two] at e ⊢
    rw [← h1, e, Subfield.coe_zero])
  exact fun e => h2F (by
    have := ringChar.spec F 2
    exact_mod_cast (this.2 (by rw [e])))

theorem uBlock_commute_of_disjoint {I I' : Finset (Fin n)} (hII : Disjoint I I')
    {g g' : StatedSU n (p ^ f) K} (hg : g ∈ uBlock p f K I) (hg' : g' ∈ uBlock p f K I') :
    g * g' = g' * g := by
  obtain ⟨hg1, hg2⟩ := hg
  obtain ⟨hg1', hg2'⟩ := hg'
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  exact mat_commute_of_disjoint hII hg1 hg2 hg1' hg2'

theorem uslice_commute {I I' : Finset (Fin n)} (hII : Disjoint I I')
    {x y : MulAut (StatedProj (StatedSU n (p ^ f) K))} (hx : x ∈ slice (uBlock p f K I))
    (hy : y ∈ slice (uBlock p f K I')) : x * y = y * x := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨g', hg', rfl⟩ := hy
  rw [← map_mul, ← map_mul, uBlock_commute_of_disjoint hII hg hg']

theorem uPairSign_mul_self {a b : Fin n} (hab : a ≠ b) : uPairSign h hab * uPairSign h hab = 1 :=
  Subtype.ext (Units.ext (by
    rw [Subgroup.coe_mul, Units.val_mul, coe_uPairSign, PSL.signMat_mul_self]
    rfl))

theorem conjProjH_uPairSign_eq {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4))) :
    conjProjH (StatedSU 4 (p ^ f) K) (uPairSign h hcd) =
      conjProjH (StatedSU 4 (p ^ f) K) (uPairSign h hab) := by
  have hinv : (uPairSign h hcd)⁻¹ = uPairSign h hcd :=
    inv_eq_of_mul_eq_one_right (uPairSign_mul_self h hcd)
  have hpr : projH (StatedSU 4 (p ^ f) K) (uPairSign h hcd) =
      projH (StatedSU 4 (p ^ f) K) (uPairSign h hab) := by
    rw [projH_eq_projH_iff, hinv, mem_subgroupOf]
    refine ⟨-1, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar, Subgroup.coe_mul, Units.val_mul, coe_uPairSign,
      coe_uPairSign, ← (show signMat K {a, b} * signMat K {c, d} =
        signMat K {c, d} * signMat K {a, b} by
          rw [signMat, signMat, diagonal_mul_diagonal, diagonal_mul_diagonal]
          congr 1
          funext x
          ring), signMat_mul_signMat_eq_neg_one hpair]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  simp only [conjProjH, MonoidHom.comp_apply, hpr]

theorem uBlock_conj_of_commute (h2 : (2 : K) ≠ 0) {a b : Fin n} (hab : a ≠ b) :
    ∀ g' : StatedSU n (p ^ f) K, g' * uPairSign h hab = uPairSign h hab * g' →
      ∀ g ∈ uBlock p f K {a, b}, g' * g * g'⁻¹ ∈ uBlock p f K {a, b} := by
  intro g' hg' g hg
  have e1 := congrArg (fun x : StatedSU n (p ^ f) K =>
    ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hg'
  simp only [Subgroup.coe_mul, Units.val_mul] at e1
  have hc := (commute_signMat_iff h2 {a, b} _).1 e1.symm
  refine conj_mem_uBlock (D := ((g' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (Di := (((g'⁻¹ : StatedSU n (p ^ f) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    ?_ ?_ hc hg ?_
  · rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
  · rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]

theorem uslice_inter
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU 4 (p ^ f) K) →*
      MulAut (StatedProj (StatedSU 4 (p ^ f) K)))) (h2 : (2 : K) ≠ 0) {a b c d : Fin 4}
    (hab : a ≠ b)
    (hpair : ∀ x : Fin 4, x ∈ ({a, b} : Finset (Fin 4)) ↔ x ∉ ({c, d} : Finset (Fin 4)))
    {F : Type} [Field F] (e : uBlock p f K {a, b} ≃* SL(2, F))
    {x : MulAut (StatedProj (StatedSU 4 (p ^ f) K))} (hx₁ : x ∈ slice (uBlock p f K {a, b}))
    (hx₂ : x ∈ slice (uBlock p f K {c, d})) :
    x = 1 ∨ x = conjProjH (StatedSU 4 (p ^ f) K) (uPairSign h hab) := by
  obtain ⟨k, hk⟩ := exists_not_mem_pair (by norm_num : 3 ≤ 4) a b
  have hZ := center_slice hinj (fun g hg hz => eq_one_of_mem_uBlock_scalars hk hg hz)
    (uPairSign_mem h hab) e (uPairSign_eq_neg_one h h2 hab e)
  have hxZ : x ∈ (center (slice (uBlock p f K {a, b}))).map
      (slice (uBlock p f K {a, b})).subtype := by
    refine ⟨⟨x, hx₁⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff]
    rintro ⟨y, hy⟩
    exact Subtype.ext (uslice_commute (disjoint_of_pair hpair) hy hx₂)
  rw [hZ] at hxZ
  have hu2 : conjProjH (StatedSU 4 (p ^ f) K) (uPairSign h hab) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, uPairSign_mul_self, map_one]
  exact eq_one_or_eq_of_mem_zpowers hu2 hxZ

theorem uslice_isPComponent (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 3 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))}
    (hB : (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))).range ≤ B) {a b : Fin n} (hab : a ≠ b) :
    IsPComponent 2 ((slice (uBlock p f K {a, b})).subgroupOf
      (B ⊓ centralizer ({conjProjH (StatedSU n (p ^ f) K) (uPairSign h hab)} :
        Set (MulAut (StatedProj (StatedSU n (p ^ f) K)))))) := by
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.charP
  have h2 := utwo_ne_zero h hp2
  have hFc : Nat.card (CFSG.LieType.Steinberg.fixedSubfield K p f) = p ^ f :=
    CFSG.LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  obtain ⟨e⟩ := nonempty_uBlock_pair_equiv h hab
  obtain ⟨k, hk⟩ := exists_not_mem_pair hn a b
  exact slice_isPComponent hinj hB (fun g hg hz => eq_one_of_mem_uBlock_scalars hk hg hz)
    (ringChar_fixedSubfield_ne_two h2) (by rw [hFc]; omega) (uPairSign_mem h hab) e
    (uPairSign_eq_neg_one h h2 hab e) (fun g hg => commute_uPairSign h h2 hab hg)
    (uBlock_conj_of_commute h h2 hab)

theorem uPairBlock_of_commute (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 1 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K)))) {a b : Fin n} (hab : a ≠ b) {D : uU h n}
    (hD : ∀ x ∈ slice (uBlock p f K {a, b}), uConjAut h hn D * x = x * uConjAut h hn D) :
    PairBlockScalar a b ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  obtain ⟨ζ, hζ0, hζ, hζ2⟩ := exists_norm_one_sq_ne_one h
  have e1 := commute_of_centralize h hp2 h5 hn hinj hab hD
    (uDiag2_mem_uBlock h hab (by simp) (by simp) hζ0 hζ)
  rw [coe_uDiag2] at e1
  have hoff := entries_of_commute_diag hζ0 hζ2 e1 b (Ne.symm hab)
  have e2 := commute_of_centralize h hp2 h5 hn hinj hab hD
    (uRot_mem_uBlock h hab (by simp) (by simp))
  rw [coe_uRot] at e2
  exact ⟨diag_eq_of_commute_rot hab e2 hoff.1, hoff.1, hoff.2⟩

theorem uPair_actsProperly (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ f) (hn : 1 ≤ n)
    (hinj : Function.Injective (MulAut.conj : StatedProj (StatedSU n (p ^ f) K) →*
      MulAut (StatedProj (StatedSU n (p ^ f) K))))
    {B : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} {A : uU h n}
    (hAt : orderOf (uConjAut h hn A) = 2) {a b : Fin n} (hab : a ≠ b)
    (hAblk : compInd K {a, b} * ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b})
    (hAnc : ¬ PairBlockScalar a b ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (hcore : ∀ y ∈ oddCoreIn B (uConjAut h hn A), ∃ D : uU h n, y = uConjAut h hn D ∧
      compInd K {a, b} * ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * compInd K {a, b} ∧
      (PairBlockScalar a b ((D : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
        uConjAut h hn D = 1))
    {Y : Subgroup (MulAut (StatedProj (StatedSU n (p ^ f) K)))} (hY : Y ≠ ⊥)
    (hYO : Y ≤ oddCoreIn B (uConjAut h hn A)) :
    ActsProperly (uConjAut h hn A) Y (slice (uBlock p f K {a, b})) ⊥ := by
  have := h.finite
  refine actsProperly_of_core hAt hY hYO (uConjAut_mem_normalizer_slice h hn hAblk) ?_ ?_ ?_
  · by_contra hc
    push Not at hc
    exact hAnc (uPairBlock_of_commute h hp2 h5 hn hinj hab hc)
  · intro y hy
    obtain ⟨D, rfl, hDb, -⟩ := hcore y hy
    exact uConjAut_mem_normalizer_slice h hn hDb
  · intro y hy hc
    obtain ⟨D, rfl, -, hDs⟩ := hcore y hy
    exact hDs (uPairBlock_of_commute h hp2 h5 hn hinj hab hc)

end CFSG.ComponentClassification.Burgoyne.B
