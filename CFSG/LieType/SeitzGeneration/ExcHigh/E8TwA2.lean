module

public import CFSG.LieType.SeitzGeneration.ExcHigh.E8TwWeyl

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration.ExcHigh.E8Layer CFSG.Open Matrix
open scoped MatrixGroups

section Algebra

variable {L : Type} [Field L]

theorem su3_twist_conj_diag {n : Type} [Fintype n] [DecidableEq n] (Fr : L →+* L) (d : n → L)
    (hd : ∀ i, d i ≠ 0) (Z : Matrix n n L) (hZ : (Z.map Fr)ᵀ * Z = 1) :
    diagonal (fun i => d i * Fr (d i)) *
      ((((diagonal d) * Z * diagonal (fun i => (d i)⁻¹)).map Fr)⁻¹)ᵀ *
      diagonal (fun i => (d i * Fr (d i))⁻¹) =
    diagonal d * Z * diagonal (fun i => (d i)⁻¹) := by
  have hFd : ∀ i, Fr (d i) ≠ 0 := fun i => (map_ne_zero Fr).2 (hd i)
  have hZ' : Z * (Z.map Fr)ᵀ = 1 := mul_eq_one_comm.1 hZ
  have hZ2 : Z.map Fr * Zᵀ = 1 := by
    have := congrArg Matrix.transpose hZ'
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  have hmap : ((diagonal d * Z * diagonal (fun i => (d i)⁻¹)).map Fr) =
      diagonal (fun i => Fr (d i)) * Z.map Fr * diagonal (fun i => (Fr (d i))⁻¹) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero Fr),
      Matrix.diagonal_map (map_zero Fr)]
    simp [map_inv₀]
  have hDD : diagonal (fun i => (Fr (d i))⁻¹) * diagonal (fun i => Fr (d i)) =
      (1 : Matrix n n L) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hFd i)
  have hDD' : diagonal (fun i => Fr (d i)) * diagonal (fun i => (Fr (d i))⁻¹) =
      (1 : Matrix n n L) := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hFd i)
  have hinv : ((diagonal d * Z * diagonal (fun i => (d i)⁻¹)).map Fr)⁻¹ =
      diagonal (fun i => Fr (d i)) * Zᵀ * diagonal (fun i => (Fr (d i))⁻¹) := by
    refine Matrix.inv_eq_right_inv ?_
    rw [hmap]
    calc diagonal (fun i => Fr (d i)) * Z.map Fr * diagonal (fun i => (Fr (d i))⁻¹) *
          (diagonal (fun i => Fr (d i)) * Zᵀ * diagonal (fun i => (Fr (d i))⁻¹))
        = diagonal (fun i => Fr (d i)) * Z.map Fr *
            (diagonal (fun i => (Fr (d i))⁻¹) * diagonal (fun i => Fr (d i))) * Zᵀ *
              diagonal (fun i => (Fr (d i))⁻¹) := by simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hDD, Matrix.mul_one, Matrix.mul_assoc _ (Z.map Fr), hZ2, Matrix.mul_one, hDD']
  rw [hinv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose,
    Matrix.diagonal_transpose, Matrix.transpose_transpose]
  have h1 : diagonal (fun i => d i * Fr (d i)) * diagonal (fun i => (Fr (d i))⁻¹) =
      diagonal d := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_inv_cancel_right₀ (hFd i) (d i)
  have h2 : diagonal (fun i => Fr (d i)) * diagonal (fun i => (d i * Fr (d i))⁻¹) =
      diagonal (fun i => (d i)⁻¹) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    have := hd i
    have := hFd i
    field_simp
  calc diagonal (fun i => d i * Fr (d i)) *
        (diagonal (fun i => (Fr (d i))⁻¹) * (Z * diagonal (fun i => Fr (d i)))) *
          diagonal (fun i => (d i * Fr (d i))⁻¹)
      = (diagonal (fun i => d i * Fr (d i)) * diagonal (fun i => (Fr (d i))⁻¹)) * Z *
          (diagonal (fun i => Fr (d i)) * diagonal (fun i => (d i * Fr (d i))⁻¹)) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

theorem su3_exists_conj_fixed [IsAlgClosed L] (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {n : Type} [Fintype n] [DecidableEq n] (A : GL n L)
    (hAd : ∀ r j : n, r ≠ j → (A : Matrix n n L) r j = 0) :
    ∃ D : GL n L, ∀ Z : Matrix n n L, (Z.map Fr)ᵀ * Z = 1 →
      (A : Matrix n n L) *
          ((((D : Matrix n n L) * Z * (↑D⁻¹ : Matrix n n L)).map Fr)⁻¹)ᵀ *
            (↑A⁻¹ : Matrix n n L) =
        (D : Matrix n n L) * Z * (↑D⁻¹ : Matrix n n L) := by
  classical
  set a : n → L := fun i => (A : Matrix n n L) i i with ha
  have hAm : (A : Matrix n n L) = diagonal a := by
    ext r j
    by_cases h : r = j
    · subst h
      simp [ha]
    · rw [hAd r j h, diagonal_apply_ne _ h]
  have ha0 : ∀ i, a i ≠ 0 := by
    intro i h
    have hdet := Matrix.GeneralLinearGroup.det_ne_zero A
    rw [hAm, det_diagonal] at hdet
    exact hdet (Finset.prod_eq_zero (Finset.mem_univ i) h)
  choose d hd using fun i => IsAlgClosed.exists_pow_nat_eq (a i) (Nat.succ_pos q)
  have hd0 : ∀ i, d i ≠ 0 := fun i h => ha0 i (by rw [← hd i, h, zero_pow (Nat.succ_ne_zero q)])
  have hda : ∀ i, d i * Fr (d i) = a i := fun i => by rw [hFr, ← pow_succ', hd]
  have hAi : (↑A⁻¹ : Matrix n n L) = diagonal fun i => (a i)⁻¹ := by
    rw [Matrix.coe_units_inv, hAm]
    refine Matrix.inv_eq_right_inv ?_
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (ha0 i)
  refine ⟨⟨diagonal d, diagonal fun i => (d i)⁻¹, ?_, ?_⟩, fun Z hZ => ?_⟩
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hd0 i)
  · rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hd0 i)
  · have e := su3_twist_conj_diag Fr d hd0 Z hZ
    simp only [hda] at e
    rw [hAm, hAi]
    exact e

theorem su3_eq_zero_of_conj_single {n : ℕ} (hn : 2 ≤ n) (A : GL (Fin n) L)
    (h : ∀ i j : Fin n, i ≠ j → ∃ c : L,
      (A : Matrix (Fin n) (Fin n) L) * (1 - single j i 1) * (↑A⁻¹ : Matrix (Fin n) (Fin n) L) =
        1 + single j i c) :
    ∀ r j : Fin n, r ≠ j → (A : Matrix (Fin n) (Fin n) L) r j = 0 := by
  intro r j hrj
  obtain ⟨i, hij⟩ : ∃ i : Fin n, i ≠ j := by
    by_cases h0 : j = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h0]; simp⟩
    · exact ⟨⟨0, by omega⟩, fun e => h0 e.symm⟩
  obtain ⟨c, hc⟩ := h i j hij
  have e1 : (A : Matrix (Fin n) (Fin n) L) * (1 - single j i 1) =
      (1 + single j i c) * (A : Matrix (Fin n) (Fin n) L) := by
    rw [← hc, Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.mul_one]
  have e2 := congrFun (congrFun e1 r) i
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.add_apply, Matrix.mul_single_apply_same, Matrix.single_mul_apply_of_ne _ _ _ _ _ hrj,
    mul_one] at e2
  linear_combination -e2

theorem su3_map_unitary {K : Type} [Field K] (ι : K →+* L) (Fr : L →+* L) {q : ℕ}
    (hFr : ∀ c, Fr c = c ^ q) {n : Type} [Fintype n] [DecidableEq n] {Y : Matrix n n K}
    (hY : (Y.map (· ^ q))ᵀ * Y = 1) : ((Y.map ι).map Fr)ᵀ * Y.map ι = 1 := by
  have h1 : (Y.map ι).map Fr = (Y.map (· ^ q)).map ι := by
    ext i j
    simp [hFr]
  rw [h1, ← Matrix.transpose_map, ← Matrix.map_mul, hY, Matrix.map_one ι (map_zero ι) (map_one ι)]

end Algebra

section Unitary

variable {K L : Type} [Field K] [Field L]

theorem statedSU_hom_ext {n q : ℕ} {M : Type*} [Group M] {f g : ↥(StatedSU n q K) →* M}
    (h : ∀ (Y : GL (Fin n) K) (hY : Y ∈ StatedSU n q K), (Y : Matrix (Fin n) (Fin n) K).det = 1 →
      ((Y : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (Y : Matrix (Fin n) (Fin n) K) = 1 →
        f ⟨Y, hY⟩ = g ⟨Y, hY⟩) :
    f = g := by
  refine MonoidHom.eq_of_eqOn_dense
    (Subgroup.closure_closure_coe_preimage
      (k := {A : GL (Fin n) K | (A : Matrix (Fin n) (Fin n) K).det = 1 ∧
        ((A : Matrix (Fin n) (Fin n) K).map (· ^ q))ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1}))
    ?_
  rintro ⟨Y, hY⟩ ⟨h1, h2⟩
  exact h Y hY h1 h2

theorem exists_su_hom (ι : K →+* L) (q : ℕ) (D : GL (Fin 3) L) :
    ∃ σ : ↥(StatedSU 3 q K) →* SL(3, L), Function.Injective σ ∧
      ∀ Y : ↥(StatedSU 3 q K), ((σ Y : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        (D : Matrix (Fin 3) (Fin 3) L) * (Y.1 : Matrix (Fin 3) (Fin 3) K).map ι *
          (↑D⁻¹ : Matrix (Fin 3) (Fin 3) L) := by
  let c : ↥(StatedSU 3 q K) →* GL (Fin 3) L :=
    (MulAut.conj D).toMonoidHom.comp
      ((Matrix.GeneralLinearGroup.map ι).comp (StatedSU 3 q K).subtype)
  have hc : ∀ Y, c Y ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) L →* Lˣ).ker := by
    intro Y
    rw [MonoidHom.mem_ker]
    have h1 : Matrix.GeneralLinearGroup.det (Y.1 : GL (Fin 3) K) = 1 :=
      Units.ext (CFSG.Open.StatedAPI.det_of_mem_statedSU Y.2)
    simp only [c, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, Matrix.GeneralLinearGroup.map_det, Subgroup.coe_subtype, h1, map_one, mul_one,
      mul_inv_cancel]
  have hcinj : Function.Injective c :=
    (MulAut.conj D).injective.comp
      ((Units.map_injective (Matrix.map_injective ι.injective)).comp Subtype.val_injective)
  refine ⟨(Matrix.SpecialLinearGroup.toGLKerEquiv).symm.toMonoidHom.comp (c.codRestrict _ hc),
    fun Y Y' h => hcinj ?_, fun Y => rfl⟩
  have h' : c.codRestrict _ hc Y = c.codRestrict _ hc Y' :=
    (MulEquiv.injective (Matrix.SpecialLinearGroup.toGLKerEquiv (n := Fin 3) (R := L)).symm) h
  exact congrArg Subtype.val h'

end Unitary


theorem rhoSigmaE8_range_le_adjointGroup (L : Type) [Field L] (v : WeylGroup Tag.E8) :
    (rhoSigmaE8 L v).range ≤ adjointGroup Tag.E8 L := by
  rw [rhoSigmaE8_range]
  exact rootSpan_le_adjointGroup L _

theorem exists_a2Twist {L : Type} [Field L] (Fr : L →+* L) (hFr : Function.Bijective Fr)
    (n : ModGL Tag.E8 L)
    (hn : ∀ i j : Fin 3, i ≠ j → ∃ c : Lˣ, ∀ t : L,
      n * pinnedX Tag.E8 L (sigmaRootE8 a2W i j) t * n⁻¹ =
        pinnedX Tag.E8 L (sigmaRootE8 a2W j i) ((c : L) * t)) :
    ∃ (Φ' : SL(3, L) ≃* SL(3, L)) (A : GL (Fin 3) L),
      (∀ X, n * Units.map (entrywiseHom Fr) (rhoSigmaE8 L a2W X) * n⁻¹ =
        rhoSigmaE8 L a2W (Φ' X)) ∧
      (∀ X : SL(3, L), ((Φ' X : SL(3, L)) : Matrix (Fin 3) (Fin 3) L) =
        (A : Matrix (Fin 3) (Fin 3) L) * (((X : Matrix (Fin 3) (Fin 3) L).map Fr)⁻¹)ᵀ *
          (↑A⁻¹ : Matrix (Fin 3) (Fin 3) L)) ∧
      ∀ r j : Fin 3, r ≠ j → (A : Matrix (Fin 3) (Fin 3) L) r j = 0 := by
  classical
  choose ε hε using fun (i j : Fin 3) (hij : i ≠ j) =>
    rhoSigmaE8_transvection (L := L) a2W i j hij
  let ε' : Fin 3 → Fin 3 → Lˣ := fun i j => if h : i = j then 1 else ε i j h
  have hgen : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      rhoSigmaE8 L a2W (Matrix.SpecialLinearGroup.transvection hij t) =
        pinnedX Tag.E8 L (sigmaRootE8 a2W i j) ((ε' i j : L) * t) := fun i j hij t => by
    simp only [ε', dif_neg hij]
    exact hε i j hij t
  obtain ⟨Φ', hΦ', b, hshape⟩ := exists_aut_of_rootData_n (τ := Tag.E8) (ν := 3)
    (rhoSigmaE8 L a2W) (rhoSigmaE8_injective a2W) (sigmaRootE8 a2W) ε' hgen Fr hFr n
    (fun i j => (j, i)) (fun i j hij => hij.symm) (fun i j hij => ⟨j, i, hij.symm, rfl⟩) hn
  obtain ⟨A, hA⟩ := CFSG.RankThree.Classical2.exists_conj_map_inv_transpose_of_root_permuting
    (n := 3) (by norm_num) Fr (Equiv.refl _) Φ'.toMonoidHom b (fun i j hij t => by
      simpa using hshape i j hij t)
  refine ⟨Φ', A, hΦ', fun X => hA X, ?_⟩
  refine su3_eq_zero_of_conj_single (by norm_num) A fun i j hij => ⟨(b i j : L), ?_⟩
  have h1 := hA (Matrix.SpecialLinearGroup.transvection hij 1)
  have h2 := hshape i j hij 1
  simp only [MulEquiv.coe_toMonoidHom] at h1
  have hm : ((Matrix.SpecialLinearGroup.transvection hij (1 : L) : SL(3, L)) :
      Matrix (Fin 3) (Fin 3) L).map Fr = 1 + single i j 1 := by
    rw [CFSG.LinearGroups.coe_transvection, Matrix.map_add _ (map_add Fr),
      Matrix.map_one _ (map_zero Fr) (map_one Fr), Matrix.map_single, map_one]
  rw [h1, hm, CFSG.RankThree.Classical2.inv_one_add_single hij, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_single, map_one, mul_one] at h2
  exact h2

theorem exists_su3_twisted {K L : Type} [Field K] [Field L] [IsAlgClosed L]
    (ι : K →+* L) (q : ℕ) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) (hbij : Function.Bijective Fr)
    (n : ModGL Tag.E8 L)
    (hn : ∀ i j : Fin 3, i ≠ j → ∃ c : Lˣ, ∀ t : L,
      n * pinnedX Tag.E8 L (sigmaRootE8 a2W i j) t * n⁻¹ =
        pinnedX Tag.E8 L (sigmaRootE8 a2W j i) ((c : L) * t)) :
    ∃ β : ↥(StatedSU 3 q K) →* ModGL Tag.E8 L, Function.Injective β ∧
      (∀ Y, β Y ∈ (rhoSigmaE8 L a2W).range) ∧
      (∀ Y, β Y ∈ adjointGroup Tag.E8 L) ∧
      ∀ Y, n * Units.map (entrywiseHom Fr) (β Y) * n⁻¹ = β Y := by
  obtain ⟨Φ', A, hΦ', hA, hAd⟩ := exists_a2Twist Fr hbij n hn
  obtain ⟨D, hD⟩ := su3_exists_conj_fixed Fr hFr A hAd
  obtain ⟨σ, hσinj, hσ⟩ := exists_su_hom ι q D
  have hfix : Φ'.toMonoidHom.comp σ = σ := by
    refine statedSU_hom_ext fun Y hY _ h2 => ?_
    refine Subtype.ext ?_
    have h := hA (σ ⟨Y, hY⟩)
    rw [hσ] at h
    exact h.trans ((hD _ (su3_map_unitary ι Fr hFr h2)).trans (hσ ⟨Y, hY⟩).symm)
  refine ⟨(rhoSigmaE8 L a2W).comp σ, (rhoSigmaE8_injective a2W).comp hσinj,
    fun Y => ⟨σ Y, rfl⟩,
    fun Y => rhoSigmaE8_range_le_adjointGroup L a2W ⟨σ Y, rfl⟩, fun Y => ?_⟩
  change n * Units.map (entrywiseHom Fr) (rhoSigmaE8 L a2W (σ Y)) * n⁻¹ =
    rhoSigmaE8 L a2W (σ Y)
  rw [hΦ']
  exact congrArg (rhoSigmaE8 L a2W) (DFunLike.congr_fun hfix Y)

end CFSG.LieType.SeitzGeneration.ExcHigh.E8Tw
