module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E8FiveTwoAct
public import CFSG.RankThree.PartOne.KE.E7FourStabFive

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five

namespace Two

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Classical2 CFSG.RankThree.PartOne.KE
  CFSG.RankThree.Lattice CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
  CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Griess
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.SeitzExcOpenRest4Twist
  CFSG.HardMathSupport.Timmesfeld.Steinberg
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Data

theorem single_mem_cosetRoots : ∀ k : Fin Tag.E8.rank, k ≠ 4 →
    (Pi.single k (1 : ℤ) : Fin Tag.E8.rank → ℤ) ∈ e8ListA ++ e8ListB := by
  decide +kernel

@[expose] def r0Vec : Fin Tag.E8.rank → ℤ := ![-2, -3, -4, -6, -5, -4, -3, -2]

theorem r0Vec_mem : r0Vec ∈ e8ListA ++ e8ListB :=
  List.mem_append_right _ List.mem_cons_self

theorem r0Vec_four : r0Vec 4 = -5 := by decide +kernel

end Data

section Torus

variable {L : Type} [Field L]

theorem exists_pow_of_rootChar_eq_one {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {c : Fin Tag.E8.rank → Lˣ} (h : ∀ r ∈ e8ListA ++ e8ListB, rootChar c r = 1) :
    ∃ j : ℕ, c = fun k => griessU hζ ^ (j * czVec k) := by
  have h1 : ∀ k : Fin Tag.E8.rank, k ≠ 4 → c k = 1 := fun k hk => by
    have := h _ (single_mem_cosetRoots k hk)
    have e := rootChar_nsmul_single c k 1
    rw [one_smul, pow_one] at e
    rw [← e]
    exact this
  have h4 : c 4 ^ 5 = 1 := by
    have := h _ r0Vec_mem
    unfold rootChar at this
    rw [Finset.prod_eq_single (4 : Fin Tag.E8.rank)] at this
    · have e : c 4 ^ r0Vec 4 = (c 4 ^ 5)⁻¹ := by
        rw [r0Vec_four, _root_.zpow_neg, show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast]
      rw [e] at this
      exact inv_eq_one.1 this
    · intro k _ hk
      rw [h1 k hk, _root_.one_zpow]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  have hc4 : ((c 4 : Lˣ) : L) ^ 5 = 1 := by
    have := congrArg (fun u : Lˣ => (u : L)) h4
    simpa using this
  obtain ⟨j, hj5, hj⟩ := hζ.eq_pow_of_pow_eq_one hc4
  refine ⟨j, funext fun k => ?_⟩
  by_cases hk : k = 4
  · subst hk
    apply Units.ext
    simp [czVec, griessU, hj]
  · rw [h1 k hk]
    have : czVec k = 0 := czVec_eq_zero hk
    simp [this]

theorem rootChar_sigma_eq_one_of_trivial (v : WeylGroup Tag.E8) (b : Fin Tag.E8.rank → Lˣ)
    (h : ∀ A, rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L v A * (rootDiagUnit Tag.E8 b)⁻¹ =
      rhoSigmaE8A4 L v A) {i j : Fin 5} (hij : i ≠ j) : rootChar b (sigmaRootE8A4 v i j) = 1 := by
  set d : Fin 5 → Lˣ := fun k => rootChar b (wbE8A4 v k) with hd
  have h1 : conjDiagn d (Matrix.SpecialLinearGroup.transvection hij (1 : L)) =
      Matrix.SpecialLinearGroup.transvection hij (1 : L) := by
    apply rhoSigmaE8A4_injective (L := L) v
    rw [← rhoSigmaE8A4_torus (L := L) v b, h]
  rw [conjDiagn_transvection] at h1
  have h2 := tv_inj hij h1
  rw [sigmaRootE8A4, rootChar_sub]
  have h3 : ((d i : Lˣ) : L) * 1 * (((d j)⁻¹ : Lˣ) : L) = 1 := h2
  rw [mul_one] at h3
  apply Units.ext
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one]
  have hdj : ((d j : Lˣ) : L) ≠ 0 := (d j).ne_zero
  rw [Units.val_inv_eq_inv_val] at h3
  simpa [hd] using h3

theorem eq_pow_z_of_trivial_action {ζ : L} (hζ : IsPrimitiveRoot ζ 5) {b : Fin Tag.E8.rank → Lˣ}
    (hA : ∀ A, rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L e8VA A * (rootDiagUnit Tag.E8 b)⁻¹ =
      rhoSigmaE8A4 L e8VA A)
    (hB : ∀ A, rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L e8VB A * (rootDiagUnit Tag.E8 b)⁻¹ =
      rhoSigmaE8A4 L e8VB A) : ∃ j : ℕ, rootDiagUnit Tag.E8 b = griessZ hζ ^ j := by
  have hroots : ∀ r ∈ e8ListA ++ e8ListB, rootChar b r = 1 := by
    intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · obtain ⟨i, j, hij, rfl⟩ := e8A_cover r hr
      have := rootChar_sigma_eq_one_of_trivial e8VA b hA hij
      rwa [sigmaRootE8A4_eq_smul, e8VA_smul] at this
    · obtain ⟨i, j, hij, rfl⟩ := e8B_cover r hr
      have := rootChar_sigma_eq_one_of_trivial e8VB b hB hij
      rwa [sigmaRootE8A4_eq_smul, e8VB_smul] at this
  obtain ⟨j, hj⟩ := exists_pow_of_rootChar_eq_one hζ hroots
  refine ⟨j, ?_⟩
  rw [hj, griessZ, SeitzExcOpenRest4Griess.rootDiagUnit_pow]
  congr 1
  funext k
  simp [pow_mul']

theorem exists_sl_of_gl [IsAlgClosed L] (M : GL (Fin 5) L) :
    ∃ (Y : SL(5, L)) (μ : L), μ ≠ 0 ∧
      (M : Matrix (Fin 5) (Fin 5) L) = μ • (Y : Matrix (Fin 5) (Fin 5) L) := by
  obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (Matrix.det (M : Matrix (Fin 5) (Fin 5) L))
    (by norm_num : 0 < 5)
  have hdet : Matrix.det (M : Matrix (Fin 5) (Fin 5) L) ≠ 0 := by
    have := M.isUnit.map Matrix.detMonoidHom
    exact this.ne_zero
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hμ]; norm_num)
  refine ⟨⟨μ⁻¹ • (M : Matrix (Fin 5) (Fin 5) L), ?_⟩, μ, hμ0, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin, ← hμ, ← mul_pow, inv_mul_cancel₀ hμ0, one_pow]
  · simp [smul_smul, hμ0]

theorem conjSLn_eq_of_smul {M : GL (Fin 5) L} {Y : SL(5, L)} {μ : L} (hμ : μ ≠ 0)
    (h : (M : Matrix (Fin 5) (Fin 5) L) = μ • (Y : Matrix (Fin 5) (Fin 5) L)) (X : SL(5, L)) :
    conjSLn M X = Y * X * Y⁻¹ := by
  let u : GL (Fin 5) L := Units.map (Matrix.scalar (Fin 5) : L →+* Matrix (Fin 5) (Fin 5) L)
    (Units.mk0 μ hμ)
  have hM : M = u * Matrix.SpecialLinearGroup.toGL Y := by
    apply Units.ext
    rw [h, Units.val_mul]
    simp [u, Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul]
  rw [hM, conjSLn_mul', conjSLn_toGL']
  have hu : conjSLn u (Y * X * Y⁻¹) = Y * X * Y⁻¹ := by
    apply Subtype.ext
    rw [coe_conjSLn]
    have hc : (u : Matrix (Fin 5) (Fin 5) L) * (↑(Y * X * Y⁻¹) : Matrix (Fin 5) (Fin 5) L) =
        (↑(Y * X * Y⁻¹) : Matrix (Fin 5) (Fin 5) L) * (u : Matrix (Fin 5) (Fin 5) L) := by
      simp only [u, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe, Matrix.scalar_apply]
      rw [← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one]
    rw [hc, Matrix.mul_assoc, show (u : Matrix (Fin 5) (Fin 5) L) * ↑u⁻¹ = 1 from
      congrArg Units.val (mul_inv_cancel u), Matrix.mul_one]
  exact hu

theorem scalar_of_central {Y : SL(5, L)} (h : ∀ X : SL(5, L), Y * X = X * Y) :
    ∃ c : L, (Y : Matrix (Fin 5) (Fin 5) L) = c • 1 := by
  have h1 : (Y : Matrix (Fin 5) (Fin 5) L) ∈ Set.range (Matrix.scalar (Fin 5)) := by
    refine Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => ?_
    have := congrArg Subtype.val (h (Matrix.SpecialLinearGroup.transvection t.hij t.c))
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
    exact this.symm
  obtain ⟨c, hc⟩ := h1
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

theorem scalar_of_rho_mul_eq_one {Y U : SL(5, L)}
    (h : rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U = 1) :
    (∃ c : L, (Y : Matrix (Fin 5) (Fin 5) L) = c • 1) ∧
      ∃ c : L, (U : Matrix (Fin 5) (Fin 5) L) = c • 1 := by
  have hA : rhoSigmaE8A4 L e8VA Y = (rhoSigmaE8A4 L e8VB U)⁻¹ := eq_inv_of_mul_eq_one_left h
  have hB : rhoSigmaE8A4 L e8VB U = (rhoSigmaE8A4 L e8VA Y)⁻¹ := eq_inv_of_mul_eq_one_right h
  refine ⟨scalar_of_central fun X => ?_, scalar_of_central fun X => ?_⟩
  · apply rhoSigmaE8A4_injective (L := L) e8VA
    rw [map_mul, map_mul, hA]
    exact ((rhoA_commute_rhoB X U).inv_right).symm.eq
  · apply rhoSigmaE8A4_injective (L := L) e8VB
    rw [map_mul, map_mul, hB]
    exact (rhoA_commute_rhoB Y X).inv_left.eq

@[expose] def zetaSL {ζ : L} (hζ : IsPrimitiveRoot ζ 5) : SL(5, L) :=
  ⟨ζ • (1 : Matrix (Fin 5) (Fin 5) L), by
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
    exact hζ.pow_eq_one⟩

theorem z_mem_range_rhoA {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    griessZ hζ ∈ (rhoSigmaE8A4 L e8VA).range := by
  have hT : rhoSigmaE8A4 L e8VA (zetaSL hζ) ∈ torusGroup Tag.E8 L :=
    rhoSigmaE8A4_diagonal e8VA (zetaSL hζ) fun i j hij => by
      simp [zetaSL, Matrix.smul_apply, Matrix.one_apply_ne hij]
  obtain ⟨b, hb⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup hT
  have hcentral : ∀ X : SL(5, L), zetaSL hζ * X = X * zetaSL hζ := fun X => by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    change (ζ • (1 : Matrix (Fin 5) (Fin 5) L)) * (X : Matrix (Fin 5) (Fin 5) L) =
      (X : Matrix (Fin 5) (Fin 5) L) * (ζ • (1 : Matrix (Fin 5) (Fin 5) L))
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨j, hj⟩ := eq_pow_z_of_trivial_action hζ (b := b)
    (fun A => by
      have h6 : zetaSL hζ * A * (zetaSL hζ)⁻¹ = A := by rw [hcentral A]; group
      rw [hb, ← map_inv, ← map_mul, ← map_mul, h6])
    (fun A => by
      rw [hb]
      calc rhoSigmaE8A4 L e8VA (zetaSL hζ) * rhoSigmaE8A4 L e8VB A *
            (rhoSigmaE8A4 L e8VA (zetaSL hζ))⁻¹
          = rhoSigmaE8A4 L e8VB A * rhoSigmaE8A4 L e8VA (zetaSL hζ) *
            (rhoSigmaE8A4 L e8VA (zetaSL hζ))⁻¹ := by
            rw [(rhoA_commute_rhoB (zetaSL hζ) A).eq]
        _ = rhoSigmaE8A4 L e8VB A := by group)
  have hne : rhoSigmaE8A4 L e8VA (zetaSL hζ) ≠ 1 := by
    intro h1
    have h2 : zetaSL hζ = 1 := rhoSigmaE8A4_injective (L := L) e8VA (by rw [h1, map_one])
    have h3 : ζ • (1 : Matrix (Fin 5) (Fin 5) L) = 1 := congrArg Subtype.val h2
    have h4 := congrFun (congrFun h3 0) 0
    simp at h4
    exact hζ.ne_one (by norm_num) h4
  have h5 : ¬ 5 ∣ j := by
    rintro ⟨m, rfl⟩
    apply hne
    rw [← hb, hj, pow_mul, griessZ_pow_five hζ, one_pow]
  obtain ⟨j', -, hj'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 h5).symm (by norm_num : 1 < 5)
  refine ⟨zetaSL hζ ^ j', ?_⟩
  rw [map_pow, ← hb, hj, ← pow_mul, pow_eq_pow_mod _ (griessZ_pow_five hζ), hj', pow_one]

@[expose] def mulSub (L : Type) [Field L] : Subgroup (ModGL Tag.E8 L) where
  carrier := {g | ∃ Y U : SL(5, L), g = rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U}
  one_mem' := ⟨1, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨Y, U, rfl⟩ ⟨Y', U', rfl⟩
    refine ⟨Y * Y', U * U', ?_⟩
    have h := (rhoA_commute_rhoB Y' U).eq
    calc rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U *
          (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U')
        = rhoSigmaE8A4 L e8VA Y * (rhoSigmaE8A4 L e8VA Y' * rhoSigmaE8A4 L e8VB U) *
          rhoSigmaE8A4 L e8VB U' := by rw [h]; group
      _ = rhoSigmaE8A4 L e8VA (Y * Y') * rhoSigmaE8A4 L e8VB (U * U') := by
        rw [map_mul, map_mul]; group
  inv_mem' := by
    rintro _ ⟨Y, U, rfl⟩
    refine ⟨Y⁻¹, U⁻¹, ?_⟩
    have h := (rhoA_commute_rhoB Y⁻¹ U⁻¹).eq
    rw [map_inv, map_inv] at h
    rw [map_inv, map_inv, _root_.mul_inv_rev]
    exact h.symm

theorem mem_mulSub {g : ModGL Tag.E8 L} :
    g ∈ mulSub L ↔ ∃ Y U : SL(5, L), g = rhoSigmaE8A4 L e8VA Y * rhoSigmaE8A4 L e8VB U :=
  Iff.rfl

theorem rhoA_le_mulSub : (rhoSigmaE8A4 L e8VA).range ≤ mulSub L := by
  rintro _ ⟨Y, rfl⟩
  exact ⟨Y, 1, by simp⟩

theorem rhoB_le_mulSub : (rhoSigmaE8A4 L e8VB).range ≤ mulSub L := by
  rintro _ ⟨U, rfl⟩
  exact ⟨1, U, by simp⟩

theorem ActsBy.apply_of_smul {ρ : SL(5, L) →* ModGL Tag.E8 L} {ε : ModGL Tag.E8 L}
    {M : GL (Fin 5) L} {Y : SL(5, L)} {μ : L} (hμ : μ ≠ 0) (h : ActsBy ρ ε M)
    (hM : (M : Matrix (Fin 5) (Fin 5) L) = μ • (Y : Matrix (Fin 5) (Fin 5) L)) (X : SL(5, L)) :
    ε * ρ X * ε⁻¹ = ρ (Y * X * Y⁻¹) := by
  rw [h X, conjSLn_eq_of_smul hμ hM X]

theorem torus_le_mulSub [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5) :
    torusGroup Tag.E8 L ≤ mulSub L := by
  intro t ht
  obtain ⟨b, rfl⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup ht
  obtain ⟨YA, μA, hμA, hYA⟩ :=
    exists_sl_of_gl (diagGLn (fun i => rootChar b (wbE8A4 e8VA i)) : GL (Fin 5) L)
  obtain ⟨YB, μB, hμB, hYB⟩ :=
    exists_sl_of_gl (diagGLn (fun i => rootChar b (wbE8A4 e8VB i)) : GL (Fin 5) L)
  have hdiagA : ∀ i j : Fin 5, i ≠ j → (YA : Matrix (Fin 5) (Fin 5) L) i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hYA i) j
    simp [diagGLn, Matrix.diagonal_apply_ne _ hij, hμA] at this
    exact this
  have hdiagB : ∀ i j : Fin 5, i ≠ j → (YB : Matrix (Fin 5) (Fin 5) L) i j = 0 := by
    intro i j hij
    have := congrFun (congrFun hYB i) j
    simp [diagGLn, Matrix.diagonal_apply_ne _ hij, hμB] at this
    exact this
  have hAT := rhoSigmaE8A4_diagonal (L := L) e8VA YA hdiagA
  have hBT := rhoSigmaE8A4_diagonal (L := L) e8VB YB hdiagB
  have hhT : rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB ∈ torusGroup Tag.E8 L :=
    mul_mem hAT hBT
  have hqT : rootDiagUnit Tag.E8 b *
      (rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB)⁻¹ ∈ torusGroup Tag.E8 L :=
    mul_mem (SeitzExcOpenRest4Griess.rootDiagUnit_mem_torus_E8 b) (inv_mem hhT)
  obtain ⟨b', hb'⟩ :=
    CFSG.LieType.SeitzGeneration.ExcHighThree.exists_rootDiagUnit_of_mem_torusGroup hqT
  have hactA := (actsBy_rootDiagUnit (L := L) e8VA b).apply_of_smul hμA hYA
  have hactB := (actsBy_rootDiagUnit (L := L) e8VB b).apply_of_smul hμB hYB
  have hcAB : ∀ W, rhoSigmaE8A4 L e8VB YB * rhoSigmaE8A4 L e8VA W =
      rhoSigmaE8A4 L e8VA W * rhoSigmaE8A4 L e8VB YB := fun W =>
    (rhoA_commute_rhoB W YB).eq.symm
  have hcBA : ∀ W, rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB W =
      rhoSigmaE8A4 L e8VB W * rhoSigmaE8A4 L e8VA YA := fun W =>
    (rhoA_commute_rhoB YA W).eq
  obtain ⟨j, hj⟩ := eq_pow_z_of_trivial_action hζ (b := b')
    (fun X => by
      rw [hb']
      have h1 : (rhoSigmaE8A4 L e8VB YB)⁻¹ * rhoSigmaE8A4 L e8VA (YA⁻¹ * X * YA) *
          rhoSigmaE8A4 L e8VB YB = rhoSigmaE8A4 L e8VA (YA⁻¹ * X * YA) := by
        rw [mul_assoc, ← hcAB, inv_mul_cancel_left]
      calc rootDiagUnit Tag.E8 b *
            (rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB)⁻¹ * rhoSigmaE8A4 L e8VA X *
            (rootDiagUnit Tag.E8 b *
              (rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB)⁻¹)⁻¹
          = rootDiagUnit Tag.E8 b * ((rhoSigmaE8A4 L e8VB YB)⁻¹ *
              ((rhoSigmaE8A4 L e8VA YA)⁻¹ * rhoSigmaE8A4 L e8VA X * rhoSigmaE8A4 L e8VA YA) *
                rhoSigmaE8A4 L e8VB YB) * (rootDiagUnit Tag.E8 b)⁻¹ := by group
        _ = rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L e8VA (YA⁻¹ * X * YA) *
              (rootDiagUnit Tag.E8 b)⁻¹ := by
            rw [← h1]
            simp only [map_mul, map_inv, mul_assoc]
        _ = rhoSigmaE8A4 L e8VA (YA * (YA⁻¹ * X * YA) * YA⁻¹) := hactA _
        _ = rhoSigmaE8A4 L e8VA X := by rw [show YA * (YA⁻¹ * X * YA) * YA⁻¹ = X by group])
    (fun X => by
      rw [hb']
      have h1 : (rhoSigmaE8A4 L e8VA YA)⁻¹ * rhoSigmaE8A4 L e8VB X *
          rhoSigmaE8A4 L e8VA YA = rhoSigmaE8A4 L e8VB X := by
        rw [mul_assoc, ← hcBA, inv_mul_cancel_left]
      calc rootDiagUnit Tag.E8 b *
            (rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB)⁻¹ * rhoSigmaE8A4 L e8VB X *
            (rootDiagUnit Tag.E8 b *
              (rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB)⁻¹)⁻¹
          = rootDiagUnit Tag.E8 b * ((rhoSigmaE8A4 L e8VB YB)⁻¹ *
              ((rhoSigmaE8A4 L e8VA YA)⁻¹ * rhoSigmaE8A4 L e8VB X * rhoSigmaE8A4 L e8VA YA) *
                rhoSigmaE8A4 L e8VB YB) * (rootDiagUnit Tag.E8 b)⁻¹ := by group
        _ = rootDiagUnit Tag.E8 b * rhoSigmaE8A4 L e8VB (YB⁻¹ * X * YB) *
              (rootDiagUnit Tag.E8 b)⁻¹ := by
            rw [h1]
            simp only [map_mul, map_inv, mul_assoc]
        _ = rhoSigmaE8A4 L e8VB (YB * (YB⁻¹ * X * YB) * YB⁻¹) := hactB _
        _ = rhoSigmaE8A4 L e8VB X := by rw [show YB * (YB⁻¹ * X * YB) * YB⁻¹ = X by group])
  have hz : griessZ hζ ^ j ∈ mulSub L := pow_mem (rhoA_le_mulSub (z_mem_range_rhoA hζ)) j
  have hfin : rootDiagUnit Tag.E8 b =
      griessZ hζ ^ j * (rhoSigmaE8A4 L e8VA YA * rhoSigmaE8A4 L e8VB YB) := by
    rw [← hj, hb']
    group
  rw [hfin]
  exact mul_mem hz (mul_mem (rhoA_le_mulSub ⟨YA, rfl⟩) (rhoB_le_mulSub ⟨YB, rfl⟩))

section Cent


theorem centralizer_le_mulSub [IsAlgClosed L] {ζ : L} (hζ : IsPrimitiveRoot ζ 5)
    {g : ModGL Tag.E8 L} (hg : g ∈ adjointGroup Tag.E8 L)
    (hcomm : g * griessZ hζ = griessZ hζ * g) : g ∈ mulSub L := by
  set a : Fin Tag.E8.rank → Lˣ := fun k => griessU hζ ^ czVec k with ha
  have h5 : ∀ i, a i ^ 5 = 1 := fun i => congrFun (pow_five_vec hζ czVec) i
  have hgc : g ∈ toralCentralizer Tag.E8 L a := by
    rw [mem_toralCentralizer]
    refine ⟨hg, ?_⟩
    show griessZ hζ * g * (griessZ hζ)⁻¹ = g
    rw [← hcomm]
    group
  rw [toralCentralizer_eq_toralRootGroup_E8_five L a h5] at hgc
  have hker : rootCharKernel a ⊆ {r | r ∈ e8ListA} ∪ {r | r ∈ e8ListB} := by
    rintro α ⟨hα, hχ⟩
    have hsum : ∑ k, (czVec k : ℤ) * α k = α 4 := by
      rw [Finset.sum_eq_single (4 : Fin Tag.E8.rank)]
      · simp [czVec]
      · intro k _ hk
        simp [czVec_eq_zero hk]
      · simp
    have hdvd : (5 : ℤ) ∣ α 4 := by
      have h1 : griessU hζ ^ (α 4) = 1 := by
        rw [← hsum, ← rootChar_powVec]
        exact hχ
      have h2 := (orderOf_dvd_iff_zpow_eq_one (G := Lˣ) (x := griessU hζ) (i := α 4)).2 h1
      rwa [← (griessU_prim hζ).eq_orderOf] at h2
    rw [← e8_coset_eq]
    exact ⟨hα, hdvd⟩
  have hle : toralRootGroup Tag.E8 L a ≤ torusGroup Tag.E8 L ⊔
      ((rhoSigmaE8A4 L e8VA).range ⊔ (rhoSigmaE8A4 L e8VB).range) := by
    refine sup_le_sup_left ?_ _
    rw [(rhoSigmaE8A4_range e8VA).trans (congrArg _ QuasiE8Ten.sigmaSet_A),
      (rhoSigmaE8A4_range e8VB).trans (congrArg _ QuasiE8Ten.sigmaSet_B),
      ← CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.rootSpan_union_eq]
    exact rootSpan_mono hker
  exact (sup_le (torus_le_mulSub hζ) (sup_le rhoA_le_mulSub rhoB_le_mulSub)) (hle hgc)

end Cent

end Torus

end Two

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8Five
