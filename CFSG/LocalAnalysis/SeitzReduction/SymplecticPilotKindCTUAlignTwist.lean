module

public import CFSG.LieType.Steinberg.CentralExt.UnitaryRankOneLast
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryModel

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Tor

variable {N ε : ℕ} {F : Type} [Field F]

@[expose] noncomputable def ctuaTorEntry (ν : F) (a : Fin (2 * N + ε)) : F :=
  Sum.elim (fun _ => 1) (fun _ => ν) ((ctuCoord N ε).symm a)

theorem ctuaTorEntry_inl (ν : F) (u : Fin N ⊕ Fin N) :
    ctuaTorEntry (N := N) (ε := ε) ν (ctuCoord N ε (Sum.inl u)) = 1 := by
  simp [ctuaTorEntry]

theorem ctuaTorEntry_inr (ν : F) (i : Fin ε) :
    ctuaTorEntry (N := N) (ε := ε) ν (ctuCoord N ε (Sum.inr i)) = ν := by
  simp [ctuaTorEntry]

theorem ctuaTorEntry_rev (hε : ε ≤ 1) (ν : F) (a : Fin (2 * N + ε)) :
    ctuaTorEntry ν (Fin.rev a) = ctuaTorEntry (N := N) (ε := ε) ν a := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rw [ctuCoord_rev hε]
  rcases w with u | i
  · rw [ctuPar_inl, ctuaTorEntry_inl, ctuaTorEntry_inl]
  · rw [ctuPar_inr]

theorem ctuaTorEntry_mul_inv (ν : Fˣ) (a : Fin (2 * N + ε)) :
    ctuaTorEntry (ν : F) a * ctuaTorEntry ((ν⁻¹ : Fˣ) : F) a = 1 := by
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rcases w with u | i
  · rw [ctuaTorEntry_inl, ctuaTorEntry_inl, one_mul]
  · rw [ctuaTorEntry_inr, ctuaTorEntry_inr, Units.mul_inv]

theorem ctuaTorEntry_ne_zero (ν : Fˣ) (a : Fin (2 * N + ε)) : ctuaTorEntry (ν : F) a ≠ 0 :=
  left_ne_zero_of_mul_eq_one (ctuaTorEntry_mul_inv ν a)

@[expose] noncomputable def ctuaTorGL (ν : Fˣ) : GL (Fin (2 * N + ε)) F :=
  ⟨diagonal (ctuaTorEntry (ν : F)), diagonal (ctuaTorEntry ((ν⁻¹ : Fˣ) : F)),
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext a
      exact ctuaTorEntry_mul_inv ν a,
    by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext a
      rw [mul_comm]
      exact ctuaTorEntry_mul_inv ν a⟩

theorem coe_ctuaTorGL (ν : Fˣ) :
    ((ctuaTorGL (N := N) (ε := ε) ν : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = diagonal (ctuaTorEntry (ν : F)) := rfl

theorem coe_ctuaTorGL_inv (ν : Fˣ) :
    (((ctuaTorGL (N := N) (ε := ε) ν)⁻¹ : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
        diagonal (ctuaTorEntry ((ν⁻¹ : Fˣ) : F)) := rfl

theorem ctuaTorGL_one : ctuaTorGL (N := N) (ε := ε) (1 : Fˣ) = 1 := by
  apply Units.ext
  rw [coe_ctuaTorGL]
  change diagonal (ctuaTorEntry ((1 : Fˣ) : F)) = 1
  rw [← diagonal_one]
  congr 1
  funext a
  obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
  rcases w with u | i
  · rw [ctuaTorEntry_inl]
  · rw [ctuaTorEntry_inr, Units.val_one]

theorem ctuaTorGL_eq_one_of_zero (ν : Fˣ) : ctuaTorGL (N := N) (ε := 0) ν = 1 := by
  apply Units.ext
  rw [coe_ctuaTorGL, Units.val_one, ← diagonal_one]
  congr 1
  funext a
  obtain ⟨w, rfl⟩ := (ctuCoord N 0).surjective a
  rcases w with u | i
  · rw [ctuaTorEntry_inl]
  · exact i.elim0

theorem ctuaTorGL_isometry (hε : ε ≤ 1) (σ : F ≃+* F) {ν : Fˣ} (hν : σ ν * ν = 1) :
    conjTr σ ((ctuaTorGL (N := N) (ε := ε) ν : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * antidiag (2 * N + ε) *
        ((ctuaTorGL ν : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) =
          antidiag (2 * N + ε) := by
  ext a b
  rw [CFSG.LieType.Steinberg.conjTr_mul_antidiag_mul_apply, coe_ctuaTorGL,
    Finset.sum_eq_single a]
  · rw [diagonal_apply_eq, diagonal_apply, antidiag, of_apply]
    by_cases hb : b = Fin.rev a
    · subst hb
      rw [ite_eq_left rfl, ite_eq_left rfl, ctuaTorEntry_rev hε]
      obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective a
      rcases w with u | i
      · rw [ctuaTorEntry_inl, map_one, one_mul]
      · rw [ctuaTorEntry_inr, hν]
    · rw [ite_eq_right (fun h => hb h.symm), ite_eq_right hb, mul_zero]
  · intro t _ hta
    rw [diagonal_apply_ne _ hta, map_zero, zero_mul]
  · simp

end Tor

section Auts

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem ctua_conj_mem_SU {A : GL (Fin n) F}
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F) =
      antidiag n) {x : GL (Fin n) F} (hx : x ∈ SU σ n) : A * x * A⁻¹ ∈ SU σ n := by
  rw [mem_SU] at hx ⊢
  have hAA : (A : Matrix (Fin n) (Fin n) F) * ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, det_mul, det_mul, hx.1, mul_one, ← det_mul, hAA, det_one]
  · have hAi : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
        ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n := by
      calc _ = conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
              (A : Matrix (Fin n) (Fin n) F)) *
              ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [hA]
        _ = conjTr σ ((A : Matrix (Fin n) (Fin n) F) *
              ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * antidiag n *
            ((A : Matrix (Fin n) (Fin n) F) *
              ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [conjTr_mul]
          simp only [Matrix.mul_assoc]
        _ = antidiag n := by rw [hAA, conjTr_one, Matrix.one_mul, Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, conjTr_mul, conjTr_mul]
    calc conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (x : Matrix (Fin n) (Fin n) F) * conjTr σ (A : Matrix (Fin n) (Fin n) F)) *
          antidiag n * ((A : Matrix (Fin n) (Fin n) F) * (x : Matrix (Fin n) (Fin n) F) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
        conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (x : Matrix (Fin n) (Fin n) F) *
            (conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n *
              (A : Matrix (Fin n) (Fin n) F)) *
              (x : Matrix (Fin n) (Fin n) F)) *
            ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          simp only [Matrix.mul_assoc]
      _ = antidiag n := by rw [hA, hx.2, hAi]

theorem ctua_glAut_mem_SU {x : GL (Fin n) F} (hx : x ∈ SU σ n) :
    glAut σ x ∈ SU σ n := by
  rw [mem_SU] at hx ⊢
  rw [coe_glAut]
  refine ⟨?_, ?_⟩
  · rw [show (x : Matrix (Fin n) (Fin n) F).map σ = (σ : F →+* F).mapMatrix x from rfl,
      ← RingHom.map_det, hx.1, map_one]
  · have hJ : (antidiag n : Matrix (Fin n) (Fin n) F).map σ = antidiag n := by
      ext i j
      simp only [map_apply, antidiag, of_apply]
      split_ifs <;> simp
    have h1 : conjTr σ ((x : Matrix (Fin n) (Fin n) F).map σ) =
        (conjTr σ (x : Matrix (Fin n) (Fin n) F)).map σ := by
      ext i j
      simp only [conjTr, transpose_apply, map_apply]
    rw [h1, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hx.2]

variable (σ) in
@[expose] noncomputable def ctuaBarAut (hσ : ∀ c, σ (σ c) = c) (n : ℕ) : MulAut (SU σ n) where
  toFun x := ⟨glAut σ x, ctua_glAut_mem_SU x.2⟩
  invFun x := ⟨glAut σ x, ctua_glAut_mem_SU x.2⟩
  left_inv x := Subtype.ext (Units.ext (by
    rw [coe_glAut, coe_glAut, Matrix.map_map]
    ext i j
    simp only [map_apply, Function.comp_apply, hσ]))
  right_inv x := Subtype.ext (Units.ext (by
    rw [coe_glAut, coe_glAut, Matrix.map_map]
    ext i j
    simp only [map_apply, Function.comp_apply, hσ]))
  map_mul' x y := Subtype.ext (map_mul (glAut σ) (x : GL (Fin n) F) y)

theorem coe_ctuaBarAut (hσ : ∀ c, σ (σ c) = c) (x : SU σ n) :
    ((ctuaBarAut σ hσ n x : SU σ n) : GL (Fin n) F) = glAut σ (x : GL (Fin n) F) := rfl

variable (σ) in
@[expose] noncomputable def ctuaConjAut (A : GL (Fin n) F)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F) =
      antidiag n)
    (hA' : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n) : MulAut (SU σ n) where
  toFun x := ⟨A * x * A⁻¹, ctua_conj_mem_SU hA x.2⟩
  invFun x := ⟨A⁻¹ * x * A⁻¹⁻¹, ctua_conj_mem_SU hA' x.2⟩
  left_inv x := Subtype.ext (by
    change A⁻¹ * (A * (x : GL (Fin n) F) * A⁻¹) * A⁻¹⁻¹ = x
    group)
  right_inv x := Subtype.ext (by
    change A * (A⁻¹ * (x : GL (Fin n) F) * A⁻¹⁻¹) * A⁻¹ = x
    group)
  map_mul' x y := Subtype.ext (by
    change A * ((x : GL (Fin n) F) * y) * A⁻¹ = (A * x * A⁻¹) * (A * y * A⁻¹)
    group)

theorem coe_ctuaConjAut (A : GL (Fin n) F)
    (hA : conjTr σ (A : Matrix (Fin n) (Fin n) F) * antidiag n * (A : Matrix (Fin n) (Fin n) F) =
      antidiag n)
    (hA' : conjTr σ ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * antidiag n *
      ((A⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = antidiag n) (x : SU σ n) :
    ((ctuaConjAut σ A hA hA' x : SU σ n) : GL (Fin n) F) = A * x * A⁻¹ := rfl

end Auts

section Twist

variable {N ε : ℕ} {F : Type} [Field F]

theorem ctuaTorGL_inv (ν : Fˣ) :
    (ctuaTorGL (N := N) (ε := ε) ν)⁻¹ = ctuaTorGL (F := F) ν⁻¹ := Units.ext rfl

theorem ctuaTorGL_inv_isometry (hε : ε ≤ 1) (σ : F ≃+* F) {ν : Fˣ} (hν : σ ν * ν = 1) :
    conjTr σ (((ctuaTorGL (N := N) (ε := ε) ν)⁻¹ : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) * antidiag (2 * N + ε) *
        (((ctuaTorGL ν)⁻¹ : GL (Fin (2 * N + ε)) F) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) = antidiag (2 * N + ε) := by
  rw [ctuaTorGL_inv]
  refine ctuaTorGL_isometry hε σ ?_
  rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hν, inv_one]

@[expose] noncomputable def ctuaTwist (hε : ε ≤ 1) (σ : F ≃+* F) (hσ : ∀ c, σ (σ c) = c)
    (ν : Fˣ) (hν : σ ν * ν = 1) (b : Bool) : MulAut (SU σ (2 * N + ε)) :=
  ctuaConjAut σ (ctuaTorGL ν) (ctuaTorGL_isometry hε σ hν) (ctuaTorGL_inv_isometry hε σ hν) *
    (bif b then ctuaBarAut σ hσ (2 * N + ε) else 1)

variable {hε : ε ≤ 1} {σ : F ≃+* F} {hσ : ∀ c, σ (σ c) = c}

theorem ctuaTwist_apply_apply {ν : Fˣ} (hν : σ ν * ν = 1) (b : Bool) (x : SU σ (2 * N + ε))
    (i j : Fin (2 * N + ε)) :
    (((ctuaTwist hε σ hσ ν hν b x : SU σ (2 * N + ε)) : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i j =
        ctuaTorEntry (ν : F) i * (bif b then σ (((x : GL (Fin (2 * N + ε)) F) :
          Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i j) else
            ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) i j) *
          ctuaTorEntry ((ν⁻¹ : Fˣ) : F) j := by
  rw [ctuaTwist, MulAut.mul_apply, coe_ctuaConjAut, Units.val_mul, Units.val_mul,
    coe_ctuaTorGL, coe_ctuaTorGL_inv, mul_diagonal, diagonal_mul]
  cases b
  · rfl
  · change ctuaTorEntry (ν : F) i * ((x : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F).map σ i j * _ = _
    rfl

theorem ctuaTorEntry_mul_mul_eq_one_iff {R : Finset (Fin N)} (ν : Fˣ) {a b : Fin (2 * N + ε)}
    (hab : a ∈ ctuPlanes ε R ∨ b ∈ ctuPlanes ε R) (m : F) :
    ctuaTorEntry (ν : F) a * m * ctuaTorEntry ((ν⁻¹ : Fˣ) : F) b =
        (1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b ↔
      m = (1 : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b := by
  have hpl : ∀ c : Fin (2 * N + ε), c ∈ ctuPlanes ε R → ∀ μ : F, ctuaTorEntry μ c = 1 := by
    intro c hc μ
    obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective c
    rcases w with u | i
    · exact ctuaTorEntry_inl μ u
    · exact absurd (ctuCoord_mem_ctuPlanes.1 hc) (not_inPlanes_inr R i)
  by_cases h : a = b
  · subst h
    have h1 : ctuaTorEntry (ν : F) a = 1 ∧ ctuaTorEntry ((ν⁻¹ : Fˣ) : F) a = 1 := by
      rcases hab with h | h <;> exact ⟨hpl a h _, hpl a h _⟩
    rw [h1.1, h1.2, one_mul, mul_one]
  · rw [one_apply_ne h, mul_eq_zero, mul_eq_zero]
    constructor
    · rintro ((h1 | h1) | h1)
      · exact absurd h1 (ctuaTorEntry_ne_zero ν a)
      · exact h1
      · exact absurd h1 (ctuaTorEntry_ne_zero ν⁻¹ b)
    · intro h1
      exact Or.inl (Or.inr h1)

theorem ctuaTwist_mem_ctuBlock_iff {ν : Fˣ} (hν : σ ν * ν = 1) (b : Bool) (R : Finset (Fin N))
    (x : SU σ (2 * N + ε)) :
    ctuaTwist hε σ hσ ν hν b x ∈ ctuBlock σ ε R ↔ x ∈ ctuBlock σ ε R := by
  rw [mem_ctuBlock, mem_ctuBlock]
  refine forall₂_congr fun a c => imp_congr_right fun hac => ?_
  rw [ctuaTwist_apply_apply, ctuaTorEntry_mul_mul_eq_one_iff ν hac]
  cases b
  · rfl
  · change σ _ = _ ↔ _
    by_cases h : a = c
    · subst h
      rw [one_apply_eq]
      exact ⟨fun h1 => σ.injective (h1.trans (map_one σ).symm), fun h1 => by rw [h1, map_one]⟩
    · rw [one_apply_ne h]
      exact ⟨fun h1 => σ.injective (h1.trans (map_zero σ).symm), fun h1 => by rw [h1, map_zero]⟩

end Twist

section Admissible

variable {N ε : ℕ} {K F : Type} [Field K] [Field F] [CharP K 2] {hε : ε ≤ 1} {σ : F ≃+* F}
  {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}

variable (hε σ ι hι) in
structure CtuaAdmissible (T : MulAut (SU σ (2 * N + ε))) : Prop where
  mem_iff : ∀ (R : Finset (Fin N)) (x : SU σ (2 * N + ε)),
    T x ∈ ctuBlock σ ε R ↔ x ∈ ctuBlock σ ε R
  fix : ∀ y : StatedSp N K, T (ctuEmbed ε hε σ ι hι y) = ctuEmbed ε hε σ ι hι y

theorem CtuaAdmissible.inv {T : MulAut (SU σ (2 * N + ε))} (hT : CtuaAdmissible hε σ ι hι T) :
    CtuaAdmissible hε σ ι hι T⁻¹ where
  mem_iff R x := by
    rw [← hT.mem_iff R (T⁻¹ x), ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  fix y := by
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq, hT.fix y]

theorem ctuaTwist_admissible {hσ : ∀ c, σ (σ c) = c} {ν : Fˣ} (hν : σ ν * ν = 1) (b : Bool) :
    CtuaAdmissible hε σ ι hι (ctuaTwist (N := N) hε σ hσ ν hν b) where
  mem_iff := ctuaTwist_mem_ctuBlock_iff hν b
  fix y := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    rw [ctuaTwist_apply_apply]
    obtain ⟨w, rfl⟩ := (ctuCoord N ε).surjective i
    obtain ⟨w', rfl⟩ := (ctuCoord N ε).surjective j
    rw [ctuEmbed_apply_ctuCoord]
    have hσE : σ (fromBlocks ((CFSG.LieType.Universal.Symplectic.SpExtras.mat N K y).map ι) 0 0 1
        w w') = fromBlocks ((CFSG.LieType.Universal.Symplectic.SpExtras.mat N K y).map ι) 0 0 1
          w w' := by
      rcases w with u | i <;> rcases w' with v | j
      · rw [fromBlocks_apply₁₁, map_apply, hι]
      · rw [fromBlocks_apply₁₂, Matrix.zero_apply, map_zero]
      · rw [fromBlocks_apply₂₁, Matrix.zero_apply, map_zero]
      · rw [fromBlocks_apply₂₂]
        by_cases h : i = j
        · rw [h, one_apply_eq, map_one]
        · rw [one_apply_ne h, map_zero]
    have hb : (bif b then σ (fromBlocks ((CFSG.LieType.Universal.Symplectic.SpExtras.mat N K
        y).map ι) 0 0 1 w w') else fromBlocks ((CFSG.LieType.Universal.Symplectic.SpExtras.mat N
          K y).map ι) 0 0 1 w w') = fromBlocks ((CFSG.LieType.Universal.Symplectic.SpExtras.mat N
            K y).map ι) 0 0 1 w w' := by
      cases b
      · rfl
      · exact hσE
    rw [hb]
    rcases w with u | i <;> rcases w' with v | j
    · rw [ctuaTorEntry_inl, ctuaTorEntry_inl, one_mul, mul_one]
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply, mul_zero, zero_mul]
    · rw [fromBlocks_apply₂₁, Matrix.zero_apply, mul_zero, zero_mul]
    · rw [ctuaTorEntry_inr, ctuaTorEntry_inr, fromBlocks_apply₂₂]
      by_cases h : i = j
      · rw [h, one_apply_eq, mul_one, Units.mul_inv]
      · rw [one_apply_ne h, mul_zero, zero_mul]

end Admissible

section Detect

variable {N ε : ℕ} {F : Type} [Field F] {σ : F ≃+* F}

theorem ctuCoord_inl_ne_rev (hε : ε ≤ 1) (u : Fin N ⊕ Fin N) :
    ctuCoord N ε (Sum.inl u) ≠ Fin.rev (ctuCoord N ε (Sum.inl u)) := by
  rw [ctuCoord_rev hε, ctuPar_inl, Ne, (ctuCoord N ε).injective.eq_iff]
  rcases u with p | p <;> simp [par]

theorem ctuCoord_inr_rev (hε : ε ≤ 1) (i : Fin ε) :
    Fin.rev (ctuCoord N ε (Sum.inr i)) = ctuCoord N ε (Sum.inr i) := by
  rw [ctuCoord_rev hε, ctuPar_inr]

theorem ctua_apply_of_plane {R : Finset (Fin N)} {a b : Fin (2 * N + ε)}
    (hab : a ∈ ctuPlanes ε R ∨ b ∈ ctuPlanes ε R) {i j : Fin (2 * N + ε)}
    (hi : i ∉ ctuPlanes ε R) (hj : j ∉ ctuPlanes ε R) (c : F) :
    (single i j c : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) a b = 0 := by
  refine single_apply_of_ne _ _ _ _ _ fun h => ?_
  rcases hab with h1 | h1
  · exact hi (h.1 ▸ h1)
  · exact hj (h.2 ▸ h1)

theorem exists_ctua_short (hε : ε ≤ 1) (hσ : ∀ c, σ (σ c) = c) {p p' : Fin N} (hpp : p ≠ p')
    (c : F) :
    ∃ x : SU σ (2 * N + ε), (∀ R : Finset (Fin N), p ∉ R → p' ∉ R → x ∈ ctuBlock σ ε R) ∧
      ((x : GL (Fin (2 * N + ε)) F) : Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F)
        (ctuCoord N ε (Sum.inl (Sum.inl p))) (ctuCoord N ε (Sum.inl (Sum.inl p'))) = c := by
  set i := ctuCoord N ε (Sum.inl (Sum.inl p)) with hi
  set j := ctuCoord N ε (Sum.inl (Sum.inl p')) with hj
  have hij : i ≠ j := by
    rw [hi, hj, Ne, (ctuCoord N ε).injective.eq_iff]
    simpa using hpp
  refine ⟨rootHom σ hσ hij (ctuCoord_inl_ne_rev hε _) (ctuCoord_inl_ne_rev hε _)
    (Multiplicative.ofAdd c), fun R hpR hp'R => ?_, ?_⟩
  · rw [mem_ctuBlock, coe_rootHom]
    intro a b hab
    have hpl : ∀ u : Fin N ⊕ Fin N, planeOf u ∉ R →
        ctuCoord N ε (Sum.inl u) ∉ ctuPlanes ε R := by
      intro u hu h
      exact hu (ctuCoord_mem_ctuPlanes.1 h)
    have hri : Fin.rev i ∉ ctuPlanes ε R := by
      rw [hi, ctuCoord_rev hε, ctuPar_inl]
      exact hpl _ (by simpa using hpR)
    have hrj : Fin.rev j ∉ ctuPlanes ε R := by
      rw [hj, ctuCoord_rev hε, ctuPar_inl]
      exact hpl _ (by simpa using hp'R)
    rw [rootMatrix, Matrix.sub_apply, Matrix.add_apply,
      ctua_apply_of_plane hab (hpl _ (by simpa using hpR)) (hpl _ (by simpa using hp'R)),
      ctua_apply_of_plane hab hrj hri, add_zero, sub_zero]
  · rw [coe_rootHom, rootMatrix, Matrix.sub_apply, Matrix.add_apply, one_apply_ne hij,
      single_apply_same, single_apply_of_row_ne, zero_add, sub_zero]
    · rfl
    · rw [hj, ctuCoord_rev hε, ctuPar_inl, hi, Ne, (ctuCoord N ε).injective.eq_iff]
      simp [par]

theorem exists_ctua_heis (hσ : ∀ c, σ (σ c) = c) (p : Fin N) {a b : F}
    (hab : b + σ b + σ a * a = 0) :
    ∃ x : SU σ (2 * N + 1), (∀ R : Finset (Fin N), p ∉ R → x ∈ ctuBlock σ 1 R) ∧
      ((x : GL (Fin (2 * N + 1)) F) : Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) F)
        (ctuCoord N 1 (Sum.inl (Sum.inl p))) (ctuCoord N 1 (Sum.inr 0)) = a := by
  set i := ctuCoord N 1 (Sum.inl (Sum.inl p)) with hi
  set k := ctuCoord N 1 (Sum.inr 0) with hk
  have hir : i ≠ Fin.rev i := ctuCoord_inl_ne_rev le_rfl _
  have hik : i ≠ k := by
    rw [hi, hk, Ne, (ctuCoord N 1).injective.eq_iff]
    simp
  have hkr : Fin.rev k = k := ctuCoord_inr_rev le_rfl 0
  have h1 : heisenbergMatrix σ i k a b * heisenbergMatrix σ i k (-a) (-b - a * σ a) = 1 := by
    rw [heisenbergMatrix_mul σ hir hik hkr, map_neg, add_neg_cancel,
      show b + (-b - a * σ a) - a * -σ a = 0 by ring, heisenbergMatrix_zero]
  have h2 : heisenbergMatrix σ i k (-a) (-b - a * σ a) * heisenbergMatrix σ i k a b = 1 := by
    rw [heisenbergMatrix_mul σ hir hik hkr, neg_add_cancel,
      show -b - a * σ a + b - -a * σ a = 0 by ring, heisenbergMatrix_zero]
  refine ⟨⟨⟨heisenbergMatrix σ i k a b, heisenbergMatrix σ i k (-a) (-b - a * σ a), h1, h2⟩,
    det_heisenbergMatrix σ hir hik hkr a b, heisenbergMatrix_isometry σ hσ hir hik hkr hab⟩,
    fun R hpR => ?_, ?_⟩
  · rw [mem_ctuBlock]
    intro c d hcd
    have hiR : i ∉ ctuPlanes 1 R := fun h => hpR (by simpa using ctuCoord_mem_ctuPlanes.1 h)
    have hirR : Fin.rev i ∉ ctuPlanes 1 R := by
      rw [hi, ctuCoord_rev le_rfl, ctuPar_inl]
      exact fun h => hpR (by simpa using ctuCoord_mem_ctuPlanes.1 h)
    have hkR : k ∉ ctuPlanes 1 R := fun h => not_inPlanes_inr R 0 (ctuCoord_mem_ctuPlanes.1 h)
    change heisenbergMatrix σ i k a b c d = _
    rw [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply,
      ctua_apply_of_plane hcd hiR hkR, ctua_apply_of_plane hcd hkR hirR,
      ctua_apply_of_plane hcd hiR hirR, add_zero, sub_zero, add_zero]
  · change heisenbergMatrix σ i k a b i k = a
    rw [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, one_apply_ne hik,
      single_apply_same, single_apply_of_row_ne (Ne.symm hik),
      single_apply_of_col_ne _ _ (fun h => hik (by rw [← Fin.rev_rev i, h, hkr])), zero_add,
      sub_zero, add_zero]

theorem ctuaTwist_false_eq_one {hε : ε ≤ 1} {hσ : ∀ c, σ (σ c) = c} {ν : Fˣ}
    (hν : σ ν * ν = 1) (hd : ctuaTorGL (N := N) (ε := ε) (F := F) ν = 1) :
    ctuaTwist (N := N) hε σ hσ ν hν false = 1 := by
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [ctuaTwist, MulAut.mul_apply, Bool.cond_false, MulAut.one_apply, coe_ctuaConjAut, hd,
    one_mul, inv_one, mul_one]

theorem ctuaTwist_eq_one_of_fix {hε : ε ≤ 1} {hσ : ∀ c, σ (σ c) = c} {ν : Fˣ}
    (hν : σ ν * ν = 1) (b : Bool) (hbar : ∃ c : F, σ c ≠ c) (htr : ∃ c : F, c + σ c + 1 = 0)
    {R : Finset (Fin N)} (hR : 2 ≤ Rᶜ.card)
    (h : ∀ x ∈ ctuBlock σ ε R, ctuaTwist hε σ hσ ν hν b x = x) :
    ctuaTwist (N := N) hε σ hσ ν hν b = 1 := by
  obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.1 (by omega : 1 < Rᶜ.card)
  have hpR : p ∉ R := Finset.mem_compl.1 hp
  have hp'R : p' ∉ R := Finset.mem_compl.1 hp'
  cases b
  · rcases (show ε = 0 ∨ ε = 1 by omega) with rfl | rfl
    · exact ctuaTwist_false_eq_one hν (ctuaTorGL_eq_one_of_zero ν)
    · obtain ⟨c, hc⟩ := htr
      obtain ⟨x, hxR, hx⟩ := exists_ctua_heis hσ p (a := 1) (b := c)
        (by rw [map_one, one_mul]; exact hc)
      have h1 := congrArg (fun z : SU σ (2 * N + 1) => ((z : GL (Fin (2 * N + 1)) F) :
        Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) F) (ctuCoord N 1 (Sum.inl (Sum.inl p)))
          (ctuCoord N 1 (Sum.inr 0))) (h x (hxR R hpR))
      rw [ctuaTwist_apply_apply, Bool.cond_false, hx, ctuaTorEntry_inl, ctuaTorEntry_inr, one_mul,
        one_mul] at h1
      have hν1 : ν = 1 := inv_eq_one.1 (Units.ext h1)
      subst hν1
      exact ctuaTwist_false_eq_one hν ctuaTorGL_one
  · exfalso
    obtain ⟨c, hc⟩ := hbar
    obtain ⟨x, hxR, hx⟩ := exists_ctua_short hε hσ hpp c
    have h1 := congrArg (fun z : SU σ (2 * N + ε) => ((z : GL (Fin (2 * N + ε)) F) :
      Matrix (Fin (2 * N + ε)) (Fin (2 * N + ε)) F) (ctuCoord N ε (Sum.inl (Sum.inl p)))
        (ctuCoord N ε (Sum.inl (Sum.inl p')))) (h x (hxR R hpR hp'R))
    rw [ctuaTwist_apply_apply, Bool.cond_true, hx, ctuaTorEntry_inl, ctuaTorEntry_inl, one_mul,
      mul_one] at h1
    exact hc h1

end Detect

end CFSG.SeitzReduction.SymplecticPilot
