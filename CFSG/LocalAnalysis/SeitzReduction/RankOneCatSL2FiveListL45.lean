module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListAssembly
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

namespace FiveList

open CatalogueBOrthogonalFourSplit

theorem card_equalDeterminants_mul (K : Type) [Field K] [Finite K] :
    Nat.card (equalDeterminants K) * Nat.card Kˣ =
      Nat.card (GL (Fin 2) K) * Nat.card (GL (Fin 2) K) := by
  classical
  let p : equalDeterminants K →* GL (Fin 2) K :=
    (MonoidHom.fst _ _).comp (equalDeterminants K).subtype
  have hp : Function.Surjective p := fun A => ⟨⟨(A, A), rfl⟩, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_of_surjective hp
  let d : GL (Fin 2) K →* Kˣ := Matrix.GeneralLinearGroup.det
  have hd : Function.Surjective d := Matrix.GeneralLinearGroup.det_surjective
  have h2 := Subgroup.card_ker_mul_card_of_surjective hd
  have h3 : Nat.card p.ker = Nat.card d.ker := Nat.card_congr
    { toFun := fun z => ⟨z.1.1.2, by
        have hz1 : z.1.1.1 = 1 := z.2
        have hz2 : Matrix.GeneralLinearGroup.det z.1.1.1 =
            Matrix.GeneralLinearGroup.det z.1.1.2 := z.1.2
        rw [hz1, map_one] at hz2
        exact hz2.symm⟩
      invFun := fun B => ⟨⟨(1, B.1), by
          change Matrix.GeneralLinearGroup.det (1 : GL (Fin 2) K) =
            Matrix.GeneralLinearGroup.det B.1
          rw [map_one]
          exact B.2.symm⟩, rfl⟩
      left_inv := fun z => by
        have hz1 : z.1.1.1 = 1 := z.2
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext hz1.symm rfl
      right_inv := fun B => rfl }
  rw [← h1, ← h2, h3]
  ring

@[expose] def scalarPairHom (K : Type) [Field K] : Kˣ →* equalDeterminants K where
  toFun := scalarPair
  map_one' := Subtype.ext (Prod.ext (map_one _) (map_one _))
  map_mul' _ _ := Subtype.ext (Prod.ext (map_mul _ _ _) (map_mul _ _ _))

theorem card_ker_rho (K : Type) [Field K] [Finite K] :
    Nat.card (rho (K := K)).ker = Nat.card Kˣ := by
  have hinj : Function.Injective (scalarPairHom K) := fun c d h => by
    have h1 := congrArg (fun z : equalDeterminants K =>
      ((z.val.1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [scalarPairHom, MonoidHom.coe_mk, OneHom.coe_mk, scalarPair,
      Matrix.GeneralLinearGroup.coe_scalar] at h1
    exact Units.ext (by simpa using h1)
  have hrange : (scalarPairHom K).range = (rho (K := K)).ker := by
    ext z
    rw [MonoidHom.mem_range, MonoidHom.mem_ker, rho_eq_one_iff]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, rfl⟩
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

@[expose] def invTranspose {K : Type} [Field K] (A : GL (Fin 2) K) : GL (Fin 2) K :=
  ⟨((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ, (A : Matrix (Fin 2) (Fin 2) K)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem det_invTranspose_mul {K : Type} [Field K] (A : GL (Fin 2) K) :
    (invTranspose A : Matrix (Fin 2) (Fin 2) K).det * (A : Matrix (Fin 2) (Fin 2) K).det = 1 := by
  change (((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ).det * _ = 1
  rw [Matrix.det_transpose, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one]

theorem tau_conj_mem_range_rho {K : Type} [Field K] {g : DeterminantIsometries K}
    (hg : g ∈ (rho (K := K)).range) : tau * g * tau⁻¹ ∈ (rho (K := K)).range := by
  obtain ⟨⟨⟨A, B⟩, hAB⟩, rfl⟩ := hg
  have hdet : (A : Matrix (Fin 2) (Fin 2) K).det = (B : Matrix (Fin 2) (Fin 2) K).det :=
    (mem_equalDeterminants A B).mp hAB
  have hmem : (invTranspose B, invTranspose A) ∈ equalDeterminants K := by
    rw [mem_equalDeterminants]
    have h1 := det_invTranspose_mul A
    have h2 := det_invTranspose_mul B
    have hB0 : (B : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := (Matrix.isUnits_det_units B).ne_zero
    rw [hdet] at h1
    exact mul_right_cancel₀ hB0 (h2.trans h1.symm)
  refine ⟨⟨(invTranspose B, invTranspose A), hmem⟩, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  rw [tau_inv]
  change ((invTranspose B : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * X *
      ((invTranspose A)⁻¹ : GL (Fin 2) K).val =
    (A.val * X.transpose * (B⁻¹ : GL (Fin 2) K).val).transpose
  have hinv : ((invTranspose A)⁻¹ : GL (Fin 2) K).val = (A : Matrix (Fin 2) (Fin 2) K)ᵀ := rfl
  rw [hinv, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rfl

theorem tau_not_mem_range_rho {K : Type} [Field K] : tau ∉ (rho (K := K)).range := by
  rintro ⟨z, hz⟩
  have hX : ∀ X : Matrix (Fin 2) (Fin 2) K,
      (z.val.1 : Matrix (Fin 2) (Fin 2) K) * X * ((z.val.2⁻¹ : GL (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = Xᵀ := fun X =>
    congrArg (fun g : DeterminantIsometries K => g.val X) hz
  set A := (z.val.1 : Matrix (Fin 2) (Fin 2) K)
  set Bi := ((z.val.2⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
  have h1 : A * Bi = 1 := by
    have := hX 1
    rwa [Matrix.mul_one, Matrix.transpose_one] at this
  have h1' : Bi * A = 1 := mul_eq_one_comm.mp h1
  have hmul : ∀ X Y : Matrix (Fin 2) (Fin 2) K, (X * Y)ᵀ = Xᵀ * Yᵀ := fun X Y => by
    rw [← hX, ← hX, ← hX]
    calc A * (X * Y) * Bi = A * X * (Bi * A) * Y * Bi := by
          rw [h1', Matrix.mul_one, Matrix.mul_assoc A X Y]
      _ = A * X * Bi * (A * Y * Bi) := by simp only [Matrix.mul_assoc]
  have key := hmul !![0, 1; 0, 0] !![0, 0; 1, 0]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) key
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem card_GL_two_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nat.card (GL (Fin 2) K) = 480 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card]; exact hK
  rw [Matrix.card_GL_field 2, hq]
  simp [Fin.prod_univ_two]

theorem card_range_rho_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nat.card (rho (K := K)).range = 14400 := by
  have h1 := card_equalDeterminants_mul K
  have h2 := Subgroup.card_ker_mul_card_range (rho (K := K))
  rw [card_ker_rho] at h2
  have hU : Nat.card Kˣ = 4 := by rw [Nat.card_units, hK]
  rw [hU, card_GL_two_five hK] at h1
  rw [hU] at h2
  omega

theorem two_pow_seven_dvd_card_det {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    2 ^ 7 ∣ Nat.card (DeterminantIsometries K) := by
  set H := (rho (K := K)).range with hHdef
  have hH := card_range_rho_five hK
  set N := normalizer (H : Set (DeterminantIsometries K)) with hNdef
  have htauN : tau ∈ N := by
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact tau_conj_mem_range_rho
    · intro hh
      have := tau_conj_mem_range_rho hh
      rwa [tau_inv, ← mul_assoc, ← mul_assoc, tau_mul_tau, one_mul, mul_assoc, tau_mul_tau,
        mul_one] at this
  have hHN : H ≤ N := Subgroup.le_normalizer
  have : (H.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  set t : N ⧸ H.subgroupOf N := QuotientGroup.mk ⟨tau, htauN⟩
  have ht1 : t ≠ 1 := by
    intro h
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
    exact tau_not_mem_range_rho h
  have ht2 : t ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : (⟨tau, htauN⟩ : N) ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, sq, tau_mul_tau]
      rfl)
    rw [this, QuotientGroup.mk_one]
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have h2Q : 2 ∣ Nat.card (N ⧸ H.subgroupOf N) := by
    have h := orderOf_dvd_natCard t
    rwa [hto] at h
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf N)
  have hsub : Nat.card (H.subgroupOf N) = 14400 := by
    rw [← hH]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
  have hN : 2 * 14400 ∣ Nat.card N := by
    rw [hcard, hsub]
    exact Nat.mul_dvd_mul_right h2Q _
  exact ((by norm_num : 2 ^ 7 ∣ 2 * 14400).trans hN).trans (Subgroup.card_subgroup_dvd_card _)

theorem card_fixed_dvd_card_inf_mul {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z) :
    Nat.card (fixedSubgroup ψ) ∣ Nat.card ↥(Z ⊓ fixedSubgroup ψ) *
      Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
  let φ : fixedSubgroup ψ →*
      fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv) :=
    { toFun := fun x => ⟨QuotientGroup.mk' Z x, by
        change CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv (QuotientGroup.mk' Z x) =
          QuotientGroup.mk' Z x
        rw [CatalogueBFixedCentralQuotient.onQuotient_mk]
        exact congrArg _ x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hkr := Subgroup.card_ker_mul_card_range φ
  let ι : φ.ker →* ↥(Z ⊓ fixedSubgroup ψ) :=
    { toFun := fun x => ⟨((x : fixedSubgroup ψ) : X), by
        have h1 : φ x = 1 := x.2
        have h2 : QuotientGroup.mk' Z ((x : fixedSubgroup ψ) : X) = 1 :=
          congrArg Subtype.val h1
        exact Subgroup.mem_inf.mpr ⟨(QuotientGroup.eq_one_iff _).mp h2, (x : fixedSubgroup ψ).2⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  rw [← hkr]
  exact Nat.mul_dvd_mul (Subgroup.card_dvd_of_injective ι hι)
    (Subgroup.card_subgroup_dvd_card _)

theorem card_dvd_two_of_le {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) :
    Nat.card G ∣ 2 := by
  have h0 : 0 < Nat.card G := Nat.card_pos
  rcases (by omega : Nat.card G = 1 ∨ Nat.card G = 2) with h1 | h1 <;> rw [h1]
  exact one_dvd 2

end FiveList

open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem oddFiveL45SplitInput_holds : OddFiveL45SplitInput := by
  intro K _ _ hK A hsymm hS hA
  classical
  have hp : (5 : ℕ).Prime := by norm_num
  have hK1 : Nat.card K = 5 ^ 1 := by rw [hK, pow_one]
  have : CharP K 5 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp le_rfl hK1
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 5]
    norm_num
  set Z := center (SpecialLinearGroup (Fin 4) K)
  set ψ := CatalogueBHigherLinearAction.slConjugation 4 K A * slGraphAut 4 K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction 4 K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin 4) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk 4 K A g
  have hfix : ∀ x : GL (Fin 4) K, A * glGraphAut 4 K x * A⁻¹ = x ↔
      glTranspose 4 K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut 4 K x = (glTranspose 4 K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose 4 K x * A⁻¹ * x =
          glTranspose 4 K x * A⁻¹ * (A * (glTranspose 4 K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose 4 K x)⁻¹ * A⁻¹ =
          A * (glTranspose 4 K x)⁻¹ * (glTranspose 4 K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  set IR := CatalogueBGraphForm.isometryGroup 4 K A⁻¹ with hIR
  set SLr := CatalogueBGeneralLinear.specialLinearRange 4 K with hSLr
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL = IR ⊓ SLr := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
        CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have hR := transpose_inv_of_transpose_eq A hsymm
  let Φ : IR ≃* TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹) :=
    (isometryGroupEquiv A⁻¹).symm.trans
      (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
  obtain ⟨S, hSd, hSQ⟩ := hS
  obtain ⟨-, e, -, -, -⟩ := CatalogueBOrthogonalFourSplit.split_four_determinant_form_isometry
    (matrixQuadraticForm A⁻¹) (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
    (by rw [Module.finrank_fin_fun]) S hSd hSQ
  have h7 : 2 ^ 7 ∣ Nat.card IR := by
    rw [Nat.card_congr (Φ.trans e).toEquiv]
    exact FiveList.two_pow_seven_dvd_card_det hK
  let dI : IR →* Kˣ := Matrix.GeneralLinearGroup.det.comp IR.subtype
  have hsq1 : ∀ g : IR, dI g * dI g = 1 := fun g => by
    have hg : glTranspose 4 K (g : GL (Fin 4) K) * A⁻¹ * g = A⁻¹ := g.2
    have h1 := congrArg Matrix.GeneralLinearGroup.det hg
    rw [map_mul, map_mul] at h1
    have h2 : Matrix.GeneralLinearGroup.det (glTranspose 4 K (g : GL (Fin 4) K)) =
        Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) := by
      apply Units.ext
      simp only [Matrix.GeneralLinearGroup.val_det_apply, CatalogueBGraphForm.glTranspose_matrix,
        Matrix.det_transpose]
    rw [h2] at h1
    change Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) *
      Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) = 1
    have h3 : Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) *
        Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) * Matrix.GeneralLinearGroup.det A⁻¹ =
        1 * Matrix.GeneralLinearGroup.det A⁻¹ := by
      rw [one_mul, mul_right_comm, h1]
    exact mul_right_cancel h3
  have hpm1 : ∀ u ∈ dI.range, u = 1 ∨ u = -1 := by
    rintro u ⟨g, rfl⟩
    have h1 := congrArg Units.val (hsq1 g)
    rw [Units.val_mul, Units.val_one] at h1
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext (by rw [h, Units.val_neg, Units.val_one]))
  have hm : (-1 : Kˣ) ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    have h2 : (2 : K) = 0 := by linear_combination -h'
    exact Ring.two_ne_zero hodd h2
  have hrange : Nat.card dI.range ≤ 2 := by
    have hle : dI.range ≤ Subgroup.zpowers (-1 : Kˣ) := by
      intro u hu
      rcases hpm1 u hu with h | h
      · rw [h]
        exact one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    have ho : orderOf (-1 : Kˣ) = 2 := orderOf_eq_prime (by rw [neg_one_sq]) hm
    calc Nat.card dI.range ≤ Nat.card (Subgroup.zpowers (-1 : Kˣ)) :=
          Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, ho]
  have hIRdvd : Nat.card IR ∣ 2 * Nat.card dI.ker := by
    rw [← Subgroup.card_ker_mul_card_range dI, mul_comm]
    exact Nat.mul_dvd_mul_right (FiveList.card_dvd_two_of_le hrange) _
  have hker : Nat.card dI.ker = Nat.card (fixedSubgroup ψ) := by
    have h1 : (dI.ker).map IR.subtype = IR ⊓ SLr := by
      ext y
      constructor
      · rintro ⟨g, hg, rfl⟩
        refine Subgroup.mem_inf.mpr ⟨g.2, ?_⟩
        have hdet : Matrix.GeneralLinearGroup.det (g : GL (Fin 4) K) = 1 := hg
        have hdv : ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).det = 1 := by
          have := congrArg Units.val hdet
          simpa using this
        exact ⟨⟨(g : GL (Fin 4) K).val, hdv⟩, Units.ext rfl⟩
      · intro hy
        obtain ⟨hyI, ⟨x, rfl⟩⟩ := Subgroup.mem_inf.mp hy
        refine ⟨⟨_, hyI⟩, ?_, rfl⟩
        change Matrix.GeneralLinearGroup.det (SpecialLinearGroup.toGL x) = 1
        apply Units.ext
        simp
    have e1 : Nat.card ((dI.ker).map IR.subtype) = Nat.card dI.ker :=
      Subgroup.card_map_of_injective IR.subtype_injective
    rw [← e1, h1, ← hmap, Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective]
  have hpmZ : ∀ z ∈ Z ⊓ fixedSubgroup ψ,
      (z : Matrix (Fin 4) (Fin 4) K) = 1 ∨ (z : Matrix (Fin 4) (Fin 4) K) = -1 := by
    intro z hz
    obtain ⟨hzZ, hzF⟩ := Subgroup.mem_inf.mp hz
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hzZ
    have hzI : SpecialLinearGroup.toGL z ∈ IR :=
      (Subgroup.mem_inf.mp (hmap ▸ ⟨z, hzF, rfl⟩ : SpecialLinearGroup.toGL z ∈ IR ⊓ SLr)).1
    have h1 : (glTranspose 4 K (SpecialLinearGroup.toGL z) * A⁻¹ *
        SpecialLinearGroup.toGL z).val = (A⁻¹ : GL (Fin 4) K).val := congrArg Units.val hzI
    rw [Units.val_mul, Units.val_mul, CatalogueBGraphForm.glTranspose_matrix] at h1
    have hzv : (SpecialLinearGroup.toGL z).val = Matrix.scalar (Fin 4) r := hr.symm
    rw [hzv] at h1
    have h2 : (Matrix.scalar (Fin 4) r)ᵀ * (A⁻¹ : GL (Fin 4) K).val * Matrix.scalar (Fin 4) r =
        (r * r) • (A⁻¹ : GL (Fin 4) K).val := by
      rw [Matrix.scalar_apply, Matrix.diagonal_transpose]
      ext i j
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
      ring
    rw [h2] at h1
    have h3 : (r * r) • ((A⁻¹ : GL (Fin 4) K).val * (A : GL (Fin 4) K).val) =
        (A⁻¹ : GL (Fin 4) K).val * (A : GL (Fin 4) K).val := by
      rw [← smul_mul_assoc, h1]
    rw [Units.inv_mul] at h3
    have h4 := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) h3
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
    rcases mul_self_eq_one_iff.mp h4 with h5 | h5
    · left
      rw [← hr, h5, map_one]
    · right
      rw [← hr, h5, map_neg, map_one]
  have hneg : (-1 : Matrix (Fin 4) (Fin 4) K) ≠ 1 := by
    intro h
    have h' := congrArg (fun M : Matrix (Fin 4) (Fin 4) K => M 0 0) h
    simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h'
    have h2 : (2 : K) = 0 := by linear_combination -h'
    exact Ring.two_ne_zero hodd h2
  have hZf : Nat.card ↥(Z ⊓ fixedSubgroup ψ) ≤ 2 := by
    let fz : ↥(Z ⊓ fixedSubgroup ψ) → Bool :=
      fun z => decide (((z : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1)
    have hfz : Function.Injective fz := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      rcases hpmZ a a.2 with ha | ha <;> rcases hpmZ b b.2 with hb | hb
      · rw [ha, hb]
      · exfalso
        have h1 : fz a = true := by simp only [fz, ha, decide_true]
        have h2 : fz b = false := by simp only [fz, hb, hneg, decide_false]
        rw [h1, h2] at hab
        exact absurd hab (by decide)
      · exfalso
        have h1 : fz a = false := by simp only [fz, ha, hneg, decide_false]
        have h2 : fz b = true := by simp only [fz, hb, decide_true]
        rw [h1, h2] at hab
        exact absurd hab (by decide)
      · rw [ha, hb]
    calc Nat.card ↥(Z ⊓ fixedSubgroup ψ) ≤ Nat.card Bool := Nat.card_le_card_of_injective fz hfz
      _ = 2 := by rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hZ2 := FiveList.card_dvd_two_of_le hZf
  have hfixd := FiveList.card_fixed_dvd_card_inf_mul Z ψ hinv
  have hF : Nat.card (fixedSubgroup (pureGraphAction 4 K A)) =
      Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
    rw [heq]
  rw [hF]
  have h2F : Nat.card (fixedSubgroup ψ) ∣
      2 * Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) :=
    hfixd.trans (Nat.mul_dvd_mul_right hZ2 _)
  set F' := Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv))
  have hA1 : 2 * Nat.card dI.ker ∣ 2 * (2 * F') := by
    rw [hker]
    exact Nat.mul_dvd_mul_left 2 h2F
  have h128 : 2 ^ 7 ∣ 4 * F' := by
    rw [show 4 * F' = 2 * (2 * F') by ring]
    exact h7.trans (hIRdvd.trans hA1)
  exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4)
    (by rw [show 4 * 32 = 2 ^ 7 by norm_num]; exact h128)

section Bound

theorem catSL2OddLieBound_two_of_twelve
    (hGLS : ComponentClassification.CatLeaf.GLS3OddLieAutComponentsInput)
    (hPSU : OddFiveSL2BoundFamilyInput .PSU) (hPSp : OddFiveSL2BoundFamilyInput .PSp)
    (hOO : OddFiveSL2BoundFamilyInput .POmegaOdd) (hOP : OddFiveSL2BoundFamilyInput .POmegaPlus)
    (hOM : OddFiveSL2BoundFamilyInput .POmegaMinus) (hG2 : OddFiveSL2BoundFamilyInput .G2)
    (hF4 : OddFiveSL2BoundFamilyInput .F4) (hE6 : OddFiveSL2BoundFamilyInput .E6)
    (hE7 : OddFiveSL2BoundFamilyInput .E7) (hE8 : OddFiveSL2BoundFamilyInput .E8)
    (h2E6 : OddFiveSL2BoundFamilyInput .twistedE6)
    (h3D4 : OddFiveSL2BoundFamilyInput .trialityD4) : CatSL2OddLieBound 2 :=
  catSL2OddLieBound_two_of_remaining hGLS oddFiveL45SplitInput_holds hPSU hPSp hOO hOP hOM hG2
    hF4 hE6 hE7 hE8 h2E6 h3D4

end Bound

end CFSG.SeitzReduction.RankOne
