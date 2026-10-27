module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAL5Def
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement MatrixGroups

theorem ka_conj_inj_pl5 {F : Type} [Field F] [Finite F] (_hodd : ringChar F ≠ 2) :
    Function.Injective
      (MulAut.conj : projectiveSL 5 F →* MulAut (projectiveSL 5 F)) :=
  CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)

theorem ka_conjAut_inner_of_det_pow5 {F : Type} [Field F] [Finite F] (M : GL (Fin 5) F)
    (μ : Fˣ) (h : (M : Matrix (Fin 5) (Fin 5) F).det = (μ : F) ^ 5) :
    conjAut 5 F M ∈ innSub (projectiveSL 5 F) := by
  have hdet : GeneralLinearGroup.det M = μ ^ 5 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_pow_eq_pow_val]
  have hscal : GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 5) μ⁻¹) = (μ⁻¹) ^ 5 := by
    ext
    simp [GeneralLinearGroup.scalar]
  set B : GL (Fin 5) F := GeneralLinearGroup.scalar (Fin 5) μ⁻¹ * M with hB
  have hdetB : GeneralLinearGroup.det B = 1 := by
    rw [hB, map_mul, hscal, hdet, ← mul_pow, inv_mul_cancel, one_pow]
  have hBmem : (B : Matrix (Fin 5) (Fin 5) F).det = 1 := by
    have := congrArg (fun x : Fˣ => (x : F)) hdetB
    simpa using this
  let g : SpecialLinearGroup (Fin 5) F := ⟨(B : Matrix (Fin 5) (Fin 5) F), hBmem⟩
  refine ⟨proj 5 F g, ?_⟩
  rw [← conjAut_toGL]
  have hg : SpecialLinearGroup.toGL g = B := by
    ext1
    rfl
  rw [hg, hB, map_mul, conjAut_scalar, one_mul]

theorem ka_outc5_conjAut_inner_of_det {F : Type} [Field F] [Finite F] (M : GL (Fin 5) F)
    (μ : Fˣ) (h : Matrix.GeneralLinearGroup.det M = μ ^ 5) :
    conjAut 5 F M ∈ innSub (projectiveSL 5 F) :=
  ka_conjAut_inner_of_det_pow5 M μ (by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_pow_eq_pow_val])

theorem ka_pl5_pow_three {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 3) (x : F) :
    x ^ 3 = x := by
  have := Fintype.ofFinite F
  have h := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hcard] at h

theorem ka_pl5_ringEquiv_eq_one {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 3)
    (σ : F ≃+* F) : σ = 1 := by
  have hfix : ∀ x : F, σ x = x := by
    intro x
    have h : x * ((x - 1) * (x + 1)) = 0 := by linear_combination ka_pl5_pow_three hcard x
    rcases mul_eq_zero.1 h with h0 | h1
    · rw [h0, map_zero]
    · rcases mul_eq_zero.1 h1 with h2 | h3
      · rw [sub_eq_zero.1 h2, map_one]
      · rw [eq_neg_of_add_eq_zero_left h3, map_neg, map_one]
  exact RingEquiv.ext hfix

theorem ka_pl5_unit_pow_five {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 3) (u : Fˣ) :
    u ^ 5 = u := by
  have h3 : u ^ 3 = u :=
    Units.ext (by rw [Units.val_pow_eq_pow_val]; exact ka_pl5_pow_three hcard u)
  calc u ^ 5 = u ^ 3 * u ^ 2 := by rw [← pow_add]
    _ = u * u ^ 2 := by rw [h3]
    _ = u ^ 3 := by rw [← pow_succ']
    _ = u := h3

theorem ka_pl5_three_odd_inner {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 3)
    (e : MulAut (projectiveSL 5 F)) (hodd : Odd (orderOf e)) :
    e ∈ innSub (projectiveSL 5 F) := by
  have hinn : ∀ A : GL (Fin 5) F, conjAut 5 F A ∈ innSub (projectiveSL 5 F) := fun A =>
    ka_outc5_conjAut_inner_of_det A (GeneralLinearGroup.det A)
      (ka_pl5_unit_pow_five hcard _).symm
  obtain ⟨A, σ, ε, hε, he⟩ := (automorphism_generation (K := F) (n := 5) (by norm_num)).2 e
  have hσ : σ = 1 := ka_pl5_ringEquiv_eq_one hcard σ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one, hσ, map_one, mul_one] at he
    rw [he]
    exact hinn A
  · rw [pow_one] at he
    have hsq : e * e = conjAut 5 F (A * GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose A)) * fieldAut 5 F (σ * σ) := by
      rw [← sq e, he]
      exact sq_conjAut_fieldAut_dualAut A σ
    rw [hσ, mul_one, map_one, mul_one] at hsq
    refine ka_odd_mem_of_sq_mem ?_ hodd
    rw [hsq]
    exact hinn _

theorem ka_outCyc_pl5_three {F : Type} [Field F] [Finite F] (hcard : Nat.card F = 3) :
    KAOutCyc (projectiveSL 5 F) := by
  intro p hp hp2 P hPp hPinn
  have hbot : P = ⊥ := by
    rw [eq_bot_iff]
    intro e he
    exact (Subgroup.mem_bot).2
      (hPinn e he (ka_pl5_three_odd_inner hcard e (ka_odd_of_mem_pGroup hp hp2 hPp he)))
  rw [hbot]
  infer_instance

theorem ka_outc5_units_map {F : Type} [Field F] (σ : F ≃+* F) {e : Fˣ} (he : e * e = 1) :
    Units.map ((σ : F →+* F) : F →* F) e = e := by
  have h1 : (e : F) * (e : F) = 1 := by
    rw [← Units.val_mul, he, Units.val_one]
  apply Units.ext
  rcases mul_self_eq_one_iff.1 h1 with h | h <;> simp [h]

theorem ka_outc5_det_inverseTranspose {F : Type} [Field F] (A : GL (Fin 5) F) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.inverseTranspose A) =
      (Matrix.GeneralLinearGroup.det A)⁻¹ := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.coe_inverseTranspose,
    Matrix.det_transpose, ← Matrix.GeneralLinearGroup.val_det_apply, map_inv]

theorem ka_outCentral_pl5 {F : Type} [Field F] [Finite F] (_hodd : ringChar F ≠ 2)
    (B : GL (Fin 5) F) (_hB : B * B = 1) :
    ∀ x : MulAut (projectiveSL 5 F), ⁅x, conjAut 5 F B⁆ ∈ innSub (projectiveSL 5 F) := by
  intro x
  obtain ⟨X, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 5) (by norm_num)).2 x
  have hdB : Matrix.GeneralLinearGroup.det B * Matrix.GeneralLinearGroup.det B = 1 := by
    rw [← map_mul, _hB, map_one]
  have hσ : Units.map ((σ : F →+* F) : F →* F) (Matrix.GeneralLinearGroup.det B) =
      Matrix.GeneralLinearGroup.det B := ka_outc5_units_map σ hdB
  obtain ⟨-, -, h3, hdd, h5, -⟩ := standard_automorphism_transport (n := 5) (K := F)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
  · rw [pow_zero, mul_one]
    have e : ⁅conjAut 5 F X * fieldAut 5 F σ, conjAut 5 F B⁆ =
        conjAut 5 F (X * GeneralLinearGroup.map (σ : F →+* F) B * X⁻¹ * B⁻¹) := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← h3 σ B]
      group
    rw [e]
    refine ka_outc5_conjAut_inner_of_det _ 1 ?_
    simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.map_det]
    rw [mul_inv_cancel_comm, hσ, mul_inv_cancel, one_pow]
  · rw [pow_one]
    have hδ : (dualAut 5 F)⁻¹ = dualAut 5 F := inv_eq_of_mul_eq_one_right hdd
    have hδc : dualAut 5 F * conjAut 5 F B * (dualAut 5 F)⁻¹ =
        conjAut 5 F (Matrix.GeneralLinearGroup.inverseTranspose B) := by
      rw [hδ]
      exact h5 B
    have e : ⁅conjAut 5 F X * fieldAut 5 F σ * dualAut 5 F, conjAut 5 F B⁆ =
        conjAut 5 F (X * GeneralLinearGroup.map (σ : F →+* F)
          (Matrix.GeneralLinearGroup.inverseTranspose B) * X⁻¹ * B⁻¹) := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv,
        ← h3 σ (Matrix.GeneralLinearGroup.inverseTranspose B), ← hδc]
      group
    rw [e]
    refine ka_outc5_conjAut_inner_of_det _ 1 ?_
    simp only [map_mul, map_inv, Matrix.GeneralLinearGroup.map_det,
      ka_outc5_det_inverseTranspose]
    rw [mul_inv_cancel_comm, hσ, ← mul_inv, hdB, inv_one, one_pow]

theorem ka_pl5_sq_fixed {G : Type*} [Group G] (θ : MulAut G) {Z : Subgroup G}
    (hZ : Z ≤ center G) (hθ2 : ∀ x, θ (θ x) = x) (hZθ : ∀ z ∈ Z, θ z = z) {g : G}
    (hg : g⁻¹ * θ g ∈ Z) : θ (g * g) = g * g := by
  obtain ⟨t, htdef⟩ : ∃ t : G, t = g⁻¹ * θ g := ⟨_, rfl⟩
  have ht : t ∈ Z := htdef ▸ hg
  have hθg : θ g = g * t := by rw [htdef]; group
  have hθt : θ t = t := hZθ t ht
  have htc : ∀ x : G, x * t = t * x := fun x => Subgroup.mem_center_iff.mp (hZ ht) x
  have h1 : g = g * t * t := by
    calc g = θ (θ g) := (hθ2 g).symm
      _ = θ (g * t) := congrArg θ hθg
      _ = θ g * θ t := map_mul θ g t
      _ = g * t * t := by rw [hθg, hθt]
  have htt : t * t = 1 := by
    refine mul_left_cancel (a := g) ?_
    rw [mul_one, ← mul_assoc]
    exact h1.symm
  rw [map_mul, hθg]
  calc g * t * (g * t) = g * (t * g) * t := by group
    _ = g * (g * t) * t := by rw [← htc g]
    _ = g * g * (t * t) := by group
    _ = g * g := by rw [htt, mul_one]

theorem ka_pl5_slConj_scalar {F : Type} [Field F] (B : GL (Fin 5) F) {t : SL(5, F)}
    (ht : t ∈ scalars 5 F) : CatalogueBHigherLinearAction.slConjugation 5 F B t = t := by
  obtain ⟨u, -, hu⟩ := mem_scalars.mp ht
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CatalogueBHigherLinearAction.toGL_slConjugation]
  have h1 : Matrix.SpecialLinearGroup.toGL t = GeneralLinearGroup.scalar (Fin 5) u :=
    Units.ext hu
  rw [h1, ← GeneralLinearGroup.scalar_commute, mul_assoc, mul_inv_cancel, mul_one]

theorem ka_odd_mem_map_cent_pl5 {F : Type} [Field F] [Finite F] (B : GL (Fin 5) F)
    (hB : B * B = 1) {y : projectiveSL 5 F} (hy : conjAut 5 F B y = y)
    (ho : Odd (orderOf y)) : y ∈ (kaSlCent5 B).map (proj 5 F) := by
  obtain ⟨g, rfl⟩ := proj_surjective 5 F y
  have hθ2 : ∀ x : SL(5, F),
      CatalogueBHigherLinearAction.slConjugation 5 F B
        (CatalogueBHigherLinearAction.slConjugation 5 F B x) = x := by
    intro x
    have h1 : CatalogueBHigherLinearAction.slConjugation 5 F B *
        CatalogueBHigherLinearAction.slConjugation 5 F B = 1 := by
      rw [← map_mul (CatalogueBHigherLinearAction.slConjugation 5 F) B B, hB, map_one]
    exact congrArg (fun e : MulAut SL(5, F) => e x) h1
  have hy' : proj 5 F (CatalogueBHigherLinearAction.slConjugation 5 F B g) = proj 5 F g := by
    rw [← conjAut_proj]
    exact hy
  have hg : g⁻¹ * CatalogueBHigherLinearAction.slConjugation 5 F B g ∈ scalars 5 F :=
    proj_eq_proj_iff.mp hy'.symm
  have hfix := ka_pl5_sq_fixed (CatalogueBHigherLinearAction.slConjugation 5 F B)
    (scalars_le_center 5 F) hθ2 (fun _ hz => ka_pl5_slConj_scalar B hz) hg
  have hmem : g * g ∈ kaSlCent5 B := by
    show Matrix.SpecialLinearGroup.toGL (g * g) ∈ Subgroup.centralizer ({B} : Set (GL (Fin 5) F))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 := CatalogueBHigherLinearAction.toGL_slConjugation 5 F B (g * g)
    rw [hfix] at h1
    calc B * Matrix.SpecialLinearGroup.toGL (g * g)
        = B * Matrix.SpecialLinearGroup.toGL (g * g) * B⁻¹ * B := by group
      _ = Matrix.SpecialLinearGroup.toGL (g * g) * B := by rw [← h1]
  have hsq : proj 5 F g * proj 5 F g ∈ (kaSlCent5 B).map (proj 5 F) := by
    rw [← map_mul]
    exact ⟨g * g, hmem, rfl⟩
  exact ka_odd_mem_of_sq_mem hsq ho

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
