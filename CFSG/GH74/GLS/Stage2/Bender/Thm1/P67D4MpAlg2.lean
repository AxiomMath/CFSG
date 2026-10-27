module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4FixedLine
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnA2Fam
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MpLA
public import CFSG.GH74.GLS.Stage2.OddAut.LangR
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.Stage2.OddAut
open scoped Matrix MatrixGroups

theorem mp_perm_values (p : Equiv.Perm (Fin 3)) :
    (p 0 = 0 ∧ p 1 = 1 ∧ p 2 = 2) ∨ (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 2) ∨
    (p 0 = 0 ∧ p 1 = 2 ∧ p 2 = 1) ∨ (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 0) ∨
    (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 1) ∨ (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 0) := by
  have h01 : p 0 ≠ p 1 := fun h => absurd (p.injective h) (by decide)
  have h02 : p 0 ≠ p 2 := fun h => absurd (p.injective h) (by decide)
  have h12 : p 1 ≠ p 2 := fun h => absurd (p.injective h) (by decide)
  generalize p 0 = a at h01 h02 ⊢
  generalize p 1 = b at h01 h12 ⊢
  generalize p 2 = c at h02 h12 ⊢
  revert a b c
  decide

theorem mp_la5 {L : Type} [Field L] (da db : Fin 3 → L) (ha0 : ∀ i, da i ≠ 0)
    (hb0 : ∀ i, db i ≠ 0)
    (hreg : ∀ i j : Fin 3, i ≠ j → da i / da j ≠ 1 ∧ (da i / da j) ^ 3 = 1)
    (hsame : ∀ i j : Fin 3, i ≠ j → db i / db j = da i / da j)
    (U : Matrix (Fin 3) (Fin 3) L) (hU : U.det = 1) (r : L) (hr : r ≠ 0)
    (h : U * Matrix.diagonal da = r • (Matrix.diagonal db * U)) :
    (∀ i j : Fin 3, i ≠ j → U i j = 0) ∨
    (∃ D : Fin 3 → L, (∀ i, D i ≠ 0) ∧ U = Matrix.diagonal D * (la_n01 * la_n12)) ∨
    (∃ D : Fin 3 → L, (∀ i, D i ≠ 0) ∧ U = Matrix.diagonal D * (la_n12 * la_n01)) := by
  have hd' : ∀ i j : Fin 3, i ≠ j → db i ≠ db j := by
    intro i j hij heq
    have h1 := hsame i j hij
    rw [heq, div_self (hb0 j)] at h1
    exact (hreg i j hij).1 h1.symm
  obtain ⟨p, hp, hrel⟩ := la_monomial_of_regular_conj da db hd' U (by rw [hU]; exact one_ne_zero)
    r hr h
  have hsame' : ∀ j k : Fin 3, j ≠ k → da j / da k = da (p j) / da (p k) := by
    intro j k hjk
    have h1 : da j / da k = db (p j) / db (p k) := by
      rw [hrel j, hrel k]
      have := hb0 (p k)
      field_simp
    rw [h1]
    exact hsame (p j) (p k) (fun h => hjk (p.injective h))
  have hnoswap : ∀ j k : Fin 3, j ≠ k → p j = k → p k = j → False := by
    intro j k hjk hpj hpk
    have h1 := hsame' j k hjk
    rw [hpj, hpk] at h1
    obtain ⟨hne, hcube⟩ := hreg j k hjk
    have hq0 : da j / da k ≠ 0 := div_ne_zero (ha0 j) (ha0 k)
    have h2 : da k / da j = (da j / da k)⁻¹ := (inv_div _ _).symm
    rw [h2] at h1
    have h3 : (da j / da k) * (da j / da k) = 1 := by
      calc (da j / da k) * (da j / da k) = (da j / da k) * (da j / da k)⁻¹ := by
            rw [← h1]
        _ = 1 := mul_inv_cancel₀ hq0
    apply hne
    calc da j / da k = (da j / da k) * ((da j / da k) * (da j / da k)) := by rw [h3, mul_one]
      _ = (da j / da k) ^ 3 := by ring
      _ = 1 := hcube
  have hUp : ∀ j, U (p j) j ≠ 0 := by
    intro j h0
    have hcol : ∀ i, U i j = 0 := by
      intro i
      by_contra hi
      have := hp i j hi
      rw [this] at hi
      exact hi h0
    have := Matrix.det_eq_zero_of_column_eq_zero j hcol
    rw [hU] at this
    exact one_ne_zero this
  have hz : ∀ i j, i ≠ p j → U i j = 0 := fun i j hij => by
    by_contra hne
    exact hij (hp i j hne)
  rcases mp_perm_values p with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · left
    intro i j hij
    exact hz i j (by
      intro h
      apply hij
      rw [h]
      fin_cases j <;> simp [h0, h1, h2])
  · exact (hnoswap 0 1 (by decide) h0 h1).elim
  · exact (hnoswap 1 2 (by decide) h1 h2).elim
  · right; left
    have e0 := hUp 0
    have e1 := hUp 1
    have e2 := hUp 2
    rw [h0] at e0
    rw [h1] at e1
    rw [h2] at e2
    refine ⟨![U 0 2, -U 1 0, -U 2 1], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [e0, e1, e2]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [la_n01, la_n12, Matrix.mul_apply, Matrix.diagonal_apply, hz _ _, h0, h1, h2]
  · right; right
    have e0 := hUp 0
    have e1 := hUp 1
    have e2 := hUp 2
    rw [h0] at e0
    rw [h1] at e1
    rw [h2] at e2
    refine ⟨![U 0 1, U 1 2, U 2 0], ?_, ?_⟩
    · intro i
      fin_cases i <;> simp [e0, e1, e2]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [la_n01, la_n12, Matrix.mul_apply, Matrix.diagonal_apply, hz _ _, h0, h1, h2]
  · exact (hnoswap 0 2 (by decide) h0 h2).elim

def mpV0 : WeylGroup TwistTag.D4.tag := (coxeterSystem TwistTag.D4.tag).wordProd [0, 2, 1, 3]

theorem mp_v0_inv : (coxeterSystem TwistTag.D4.tag).wordProd [3, 1, 2, 0] = mpV0⁻¹ := by
  have := (coxeterSystem TwistTag.D4.tag).wordProd_reverse [0, 2, 1, 3]
  simpa [mpV0] using this

def mpN01 (L : Type) [Field L] : SL(3, L) :=
  ⟨la_n01, by simp [la_n01, Matrix.det_fin_three]⟩

def mpN12 (L : Type) [Field L] : SL(3, L) :=
  ⟨la_n12, by simp [la_n12, Matrix.det_fin_three]⟩

theorem mp_conj_scalar {L : Type} [Field L] (da db : Fin 3 → Lˣ) (U : SL(3, L))
    (h : ∀ X : SL(3, L), conjDiag3 db X = U * conjDiag3 da (U⁻¹ * X * U) * U⁻¹) :
    ∃ r : L, r ≠ 0 ∧ (U : Matrix (Fin 3) (Fin 3) L) * Matrix.diagonal (fun i => (da i : L)) =
      r • (Matrix.diagonal (fun i => (db i : L)) * (U : Matrix (Fin 3) (Fin 3) L)) := by
  set Ug : GL (Fin 3) L := Matrix.SpecialLinearGroup.toGL U with hUg
  set Pg : GL (Fin 3) L := Ug * diagGL3 da * Ug⁻¹ with hPg
  set Mg : GL (Fin 3) L := (diagGL3 db)⁻¹ * Pg with hMg
  have hcomm : ∀ X : SL(3, L), Mg * Matrix.SpecialLinearGroup.toGL X =
      Matrix.SpecialLinearGroup.toGL X * Mg := by
    intro X
    have h1 := congrArg Matrix.SpecialLinearGroup.toGL (h X)
    rw [toGL_conjDiag3, map_mul, map_mul, toGL_conjDiag3, map_mul, map_mul, map_inv] at h1
    have key : diagGL3 db * Matrix.SpecialLinearGroup.toGL X * (diagGL3 db)⁻¹ =
        Pg * Matrix.SpecialLinearGroup.toGL X * Pg⁻¹ := by
      rw [h1]
      simp only [hPg, hUg]
      group
    calc Mg * Matrix.SpecialLinearGroup.toGL X
        = (diagGL3 db)⁻¹ * (Pg * Matrix.SpecialLinearGroup.toGL X * Pg⁻¹) * Pg := by
          simp only [hMg]
          group
      _ = (diagGL3 db)⁻¹ * (diagGL3 db * Matrix.SpecialLinearGroup.toGL X *
            (diagGL3 db)⁻¹) * Pg := by rw [key]
      _ = Matrix.SpecialLinearGroup.toGL X * Mg := by
          simp only [hMg]
          group
  have hmat : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij t) :
        GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = 1 + t • Matrix.single i j (1 : L) := by
    intro i j hij t
    ext a b
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]
  obtain ⟨r, hr⟩ := la_scalar_of_comm_transvections (Mg : Matrix (Fin 3) (Fin 3) L)
    (fun i j hij => by
      have := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L))
        (hcomm (Matrix.SpecialLinearGroup.transvection hij 1))
      simp only [Units.val_mul, hmat, one_smul] at this
      exact this)
  have hr0 : r ≠ 0 := by
    intro h0
    have h1 : (Mg : Matrix (Fin 3) (Fin 3) L) * ((Mg⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
        = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hr, h0, zero_smul, zero_mul] at h1
    exact zero_ne_one h1
  refine ⟨r, hr0, ?_⟩
  have h2 : Pg * Ug = Ug * diagGL3 da := by
    simp only [hPg]
    group
  have h3 : Pg = diagGL3 db * Mg := by
    simp only [hMg]
    group
  have h4 := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h2
  have h5 := congrArg (fun G : GL (Fin 3) L => (G : Matrix (Fin 3) (Fin 3) L)) h3
  simp only [Units.val_mul] at h4 h5
  rw [h5, hr] at h4
  change ((Matrix.diagonal fun i => (db i : L)) * (r • (1 : Matrix (Fin 3) (Fin 3) L))) *
    (U : Matrix (Fin 3) (Fin 3) L) = (U : Matrix (Fin 3) (Fin 3) L) *
      Matrix.diagonal (fun i => (da i : L)) at h4
  rw [← h4, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

section A2Std


theorem mp_d4A2Rep_weylElt_zero (L : Type) [Field L] :
    ((d4A2Rep L ⟨weylElt Tag.D4 L 0 1, weylElt_mem_subsystemGroup zero_mem_d4SuppA2 1⟩ :
      SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  have hx : (0 : Fin Tag.D4.rank) ∈ d4SuppA2 := zero_mem_d4SuppA2
  have e : (⟨weylElt Tag.D4 L 0 1, weylElt_mem_subsystemGroup hx 1⟩ :
      subsystemGroup Tag.D4 L d4SuppA2) =
      ⟨xUnit Tag.D4 L 0 1, xUnit_mem_subsystemGroup hx 1⟩ *
        ⟨yUnit Tag.D4 L 0 (-1), yUnit_mem_subsystemGroup hx (-1)⟩ *
          ⟨xUnit Tag.D4 L 0 1, xUnit_mem_subsystemGroup hx 1⟩ := by
    apply Subtype.ext
    show weylElt Tag.D4 L 0 1 = xUnit Tag.D4 L 0 1 * yUnit Tag.D4 L 0 (-1) * xUnit Tag.D4 L 0 1
    rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
    simp
  rw [e]
  simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul, coe_d4A2Rep,
    d4A2Mat_x0, d4A2Mat_y0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Matrix.single_apply]

theorem mp_d4A2Rep_weylElt_two (L : Type) [Field L] :
    ((d4A2Rep L ⟨weylElt Tag.D4 L 2 1, weylElt_mem_subsystemGroup two_mem_d4SuppA2 1⟩ :
      SL(3, L)) : Matrix (Fin 3) (Fin 3) L) = !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  have hx : (2 : Fin Tag.D4.rank) ∈ d4SuppA2 := two_mem_d4SuppA2
  have e : (⟨weylElt Tag.D4 L 2 1, weylElt_mem_subsystemGroup hx 1⟩ :
      subsystemGroup Tag.D4 L d4SuppA2) =
      ⟨xUnit Tag.D4 L 2 1, xUnit_mem_subsystemGroup hx 1⟩ *
        ⟨yUnit Tag.D4 L 2 (-1), yUnit_mem_subsystemGroup hx (-1)⟩ *
          ⟨xUnit Tag.D4 L 2 1, xUnit_mem_subsystemGroup hx 1⟩ := by
    apply Subtype.ext
    show weylElt Tag.D4 L 2 1 = xUnit Tag.D4 L 2 1 * yUnit Tag.D4 L 2 (-1) * xUnit Tag.D4 L 2 1
    rw [CFSG.LieType.Chevalley.weylElt_eq_xUnit_mul]
    simp
  rw [e]
  simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul, coe_d4A2Rep,
    d4A2Mat_x2, d4A2Mat_y2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply,
    Matrix.single_apply]

end A2Std

theorem mp_rot_A (x : Fin TwistTag.D4.tag.rank → ℤ) :
    (mpV0 * simple TwistTag.D4.tag 0 * mpV0⁻¹ *
      (mpV0 * simple TwistTag.D4.tag 2 * mpV0⁻¹)) • x = d4MatThreeA.mulVec x := by
  have e : mpV0 * simple TwistTag.D4.tag 0 * mpV0⁻¹ *
      (mpV0 * simple TwistTag.D4.tag 2 * mpV0⁻¹) =
      (coxeterSystem TwistTag.D4.tag).wordProd ([0, 2, 1, 3] ++ [0, 2] ++ [3, 1, 2, 0]) := by
    have h02 : (coxeterSystem TwistTag.D4.tag).wordProd [0, 2] =
        simple TwistTag.D4.tag 0 * simple TwistTag.D4.tag 2 := by
      rw [show ([0, 2] : List (Fin TwistTag.D4.tag.rank)) = [0] ++ [2] from rfl,
        CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
        CoxeterSystem.wordProd_singleton]
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, mp_v0_inv, h02]
    show _ = mpV0 * (simple TwistTag.D4.tag 0 * simple TwistTag.D4.tag 2) * mpV0⁻¹
    group
  rw [e]
  refine weyl_smul_eq_mulVec (fun j => ?_) x
  rw [wordProd_smul]
  revert j
  decide +kernel

theorem mp_rot_B (x : Fin TwistTag.D4.tag.rank → ℤ) :
    (mpV0 * simple TwistTag.D4.tag 2 * mpV0⁻¹ *
      (mpV0 * simple TwistTag.D4.tag 0 * mpV0⁻¹)) • x = d4MatThreeB.mulVec x := by
  have e : mpV0 * simple TwistTag.D4.tag 2 * mpV0⁻¹ *
      (mpV0 * simple TwistTag.D4.tag 0 * mpV0⁻¹) =
      (coxeterSystem TwistTag.D4.tag).wordProd ([0, 2, 1, 3] ++ [2, 0] ++ [3, 1, 2, 0]) := by
    have h20 : (coxeterSystem TwistTag.D4.tag).wordProd [2, 0] =
        simple TwistTag.D4.tag 2 * simple TwistTag.D4.tag 0 := by
      rw [show ([2, 0] : List (Fin TwistTag.D4.tag.rank)) = [2] ++ [0] from rfl,
        CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
        CoxeterSystem.wordProd_singleton]
    rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, mp_v0_inv, h20]
    show _ = mpV0 * (simple TwistTag.D4.tag 2 * simple TwistTag.D4.tag 0) * mpV0⁻¹
    group
  rw [e]
  refine weyl_smul_eq_mulVec (fun j => ?_) x
  rw [wordProd_smul]
  revert j
  decide +kernel

noncomputable def mpSigma0 : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ :=
  fun i j => mpV0 • d4Chain i j

noncomputable def mpRho0 (L : Type) [Field L] : SL(3, L) →* ModGL TwistTag.D4.tag L :=
  (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0)).toMonoidHom.comp
    (d4rhoStd L)

noncomputable def mpDiag {L : Type} [Field L] (b : Fin TwistTag.D4.tag.rank → Lˣ) :
    Fin 3 → Lˣ := fun i => rootChar b (mpSigma0 i 0)

theorem mp_frame0 (L : Type) [Field L] : IsA2Frame (mpRho0 L) mpSigma0 :=
  (d4Std_frame' L).transport mpV0

theorem mp_torus0 (L : Type) [Field L] (b : Fin TwistTag.D4.tag.rank → Lˣ) (A : SL(3, L)) :
    rootDiagUnit TwistTag.D4.tag b * mpRho0 L A * (rootDiagUnit TwistTag.D4.tag b)⁻¹ =
      mpRho0 L (conjDiag3 (mpDiag b) A) :=
  (mp_frame0 L).torus b A

theorem mp_ratio (L : Type) [Field L] (b : Fin TwistTag.D4.tag.rank → Lˣ) (i j : Fin 3) :
    rootChar b (mpSigma0 i j) = mpDiag b i * (mpDiag b j)⁻¹ := by
  rw [(mp_frame0 L).eq_sub i j, rootChar_sub]
  rfl

theorem mp_v0_smul0 :
    mpV0 • (Pi.single 0 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 0 1 := by
  rw [mpV0, wordProd_smul]
  exact d4LongA2_wordValues.1

theorem mp_v0_smul2 :
    mpV0 • (Pi.single 2 1 : Fin TwistTag.D4.tag.rank → ℤ) = d4LongVec 1 1 := by
  rw [mpV0, wordProd_smul]
  exact d4LongA2_wordValues.2

theorem mp_sigma0_set : {r | ∃ i j : Fin 3, i ≠ j ∧ r = mpSigma0 i j} = d4LongA2 := by
  obtain ⟨s01, s12, s02, s10, s21, s20⟩ := d4_long_values mpV0 mp_v0_smul0 mp_v0_smul2
  ext r
  rw [d4LongA2_eq]
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, hab, rfl⟩
    match a, b, hab with
    | 0, 0, h => exact absurd rfl h
    | 0, 1, _ => exact Or.inl s01
    | 0, 2, _ => exact Or.inr (Or.inr (Or.inl s02))
    | 1, 0, _ => exact Or.inr (Or.inr (Or.inr (Or.inl s10)))
    | 1, 1, h => exact absurd rfl h
    | 1, 2, _ => exact Or.inr (Or.inl s12)
    | 2, 0, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr s20))))
    | 2, 1, _ => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl s21))))
    | 2, 2, h => exact absurd rfl h
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, 1, by decide, s01.symm⟩
    · exact ⟨1, 2, by decide, s12.symm⟩
    · exact ⟨0, 2, by decide, s02.symm⟩
    · exact ⟨1, 0, by decide, s10.symm⟩
    · exact ⟨2, 1, by decide, s21.symm⟩
    · exact ⟨2, 0, by decide, s20.symm⟩

theorem mp_sigma0_mem {i j : Fin 3} (hij : i ≠ j) : mpSigma0 i j ∈ d4LongA2 := by
  rw [← mp_sigma0_set]
  exact ⟨i, j, hij, rfl⟩

theorem mp_rhoStd_N01 (L : Type) [Field L] :
    d4rhoStd L (mpN01 L) = weylElt TwistTag.D4.tag L 0 1 := by
  have e : d4A2Rep L ⟨weylElt Tag.D4 L 0 1,
      weylElt_mem_subsystemGroup zero_mem_d4SuppA2 1⟩ = mpN01 L :=
    Subtype.ext (mp_d4A2Rep_weylElt_zero L)
  rw [← e]
  exact d4rhoStd_d4A2Rep _

theorem mp_rhoStd_N12 (L : Type) [Field L] :
    d4rhoStd L (mpN12 L) = weylElt TwistTag.D4.tag L 2 1 := by
  have e : d4A2Rep L ⟨weylElt Tag.D4 L 2 1,
      weylElt_mem_subsystemGroup two_mem_d4SuppA2 1⟩ = mpN12 L :=
    Subtype.ext (mp_d4A2Rep_weylElt_two L)
  rw [← e]
  exact d4rhoStd_d4A2Rep _

theorem mp_image_torus {L : Type} [Field L] {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ torusGroup TwistTag.D4.tag L) :
    weylQuotientHom TwistTag.D4.tag L ⟨g, torusGroup_le_monomialSubgroup hg⟩ = 1 :=
  weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hg)

theorem mp_image_conj (L : Type) [Field L] (i : Fin TwistTag.D4.tag.rank) :
    ∃ h : canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0 * weylElt TwistTag.D4.tag L i 1 *
        (canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0)⁻¹ ∈
          monomialSubgroup TwistTag.D4.tag L,
      weylQuotientHom TwistTag.D4.tag L ⟨_, h⟩ = mpV0 * simple TwistTag.D4.tag i * mpV0⁻¹ := by
  have hN := canonicalRep_mem_monomialSubgroup (τ := TwistTag.D4.tag) L mpV0
  have hW := weylElt_mem_monomialSubgroup (τ := TwistTag.D4.tag) (R := L) i
  have hπN : weylQuotientHom TwistTag.D4.tag L
      ⟨canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0, hN⟩ = mpV0 :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep mpV0)
  have hπW : weylQuotientHom TwistTag.D4.tag L ⟨weylElt TwistTag.D4.tag L i 1, hW⟩ =
      simple TwistTag.D4.tag i :=
    weylQuotientHom_eq (mapsRootLines_weylElt i)
  refine ⟨mul_mem (mul_mem hN hW) (inv_mem hN), ?_⟩
  have e : (⟨_, mul_mem (mul_mem hN hW) (inv_mem hN)⟩ : monomialSubgroup TwistTag.D4.tag L) =
      ⟨_, hN⟩ * ⟨_, hW⟩ * ⟨_, hN⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, hπN, hπW]

theorem mp_image_N01 (L : Type) [Field L] :
    ∃ h : mpRho0 L (mpN01 L) ∈ monomialSubgroup TwistTag.D4.tag L,
      weylQuotientHom TwistTag.D4.tag L ⟨mpRho0 L (mpN01 L), h⟩ =
        mpV0 * simple TwistTag.D4.tag 0 * mpV0⁻¹ := by
  have e : mpRho0 L (mpN01 L) = canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0 *
      weylElt TwistTag.D4.tag L 0 1 * (canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0)⁻¹ := by
    rw [← mp_rhoStd_N01 L]
    rfl
  rw [e]
  exact mp_image_conj L 0

theorem mp_image_N12 (L : Type) [Field L] :
    ∃ h : mpRho0 L (mpN12 L) ∈ monomialSubgroup TwistTag.D4.tag L,
      weylQuotientHom TwistTag.D4.tag L ⟨mpRho0 L (mpN12 L), h⟩ =
        mpV0 * simple TwistTag.D4.tag 2 * mpV0⁻¹ := by
  have e : mpRho0 L (mpN12 L) = canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0 *
      weylElt TwistTag.D4.tag L 2 1 * (canonicalRep (coxeterSystem TwistTag.D4.tag) L mpV0)⁻¹ := by
    rw [← mp_rhoStd_N12 L]
    rfl
  rw [e]
  exact mp_image_conj L 2

theorem mp_image_prod {L : Type} [Field L] {g h₁ h₂ : ModGL TwistTag.D4.tag L}
    (hg : g ∈ torusGroup TwistTag.D4.tag L) (m₁ : h₁ ∈ monomialSubgroup TwistTag.D4.tag L)
    (m₂ : h₂ ∈ monomialSubgroup TwistTag.D4.tag L) :
    ∃ hm : g * (h₁ * h₂) ∈ monomialSubgroup TwistTag.D4.tag L,
      weylQuotientHom TwistTag.D4.tag L ⟨g * (h₁ * h₂), hm⟩ =
        weylQuotientHom TwistTag.D4.tag L ⟨h₁, m₁⟩ *
          weylQuotientHom TwistTag.D4.tag L ⟨h₂, m₂⟩ := by
  have mg := torusGroup_le_monomialSubgroup hg
  refine ⟨mul_mem mg (mul_mem m₁ m₂), ?_⟩
  have e : (⟨g * (h₁ * h₂), mul_mem mg (mul_mem m₁ m₂)⟩ : monomialSubgroup TwistTag.D4.tag L) =
      ⟨g, mg⟩ * (⟨h₁, m₁⟩ * ⟨h₂, m₂⟩) := rfl
  rw [e, map_mul, map_mul, mp_image_torus hg, one_mul]

theorem mp_iff_of_rot {L : Type} [Field L] {u : ModGL TwistTag.D4.tag L}
    (hm : u ∈ monomialSubgroup TwistTag.D4.tag L) (M : D4Mat)
    (hM : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨u, hm⟩ • x = M.mulVec x)
    (hM1 : ∃ x, M.mulVec x ≠ x) :
    u ∈ torusGroup TwistTag.D4.tag L ↔ weylQuotientHom TwistTag.D4.tag L ⟨u, hm⟩ = 1 := by
  constructor
  · intro hT
    exact weylQuotientHom_eq (mapsRootLines_of_mem_torusGroup hT)
  · intro h1
    exfalso
    obtain ⟨x, hx⟩ := hM1
    apply hx
    rw [← hM x, h1, one_smul]

theorem d4_A2_conj_monomial {L : Type} [Field L] (u : ModGL TwistTag.D4.tag L)
    (hu : u ∈ rootSpan TwistTag.D4.tag L d4LongA2) (a b : Fin TwistTag.D4.tag.rank → Lˣ)
    (hreg : ∀ α ∈ d4LongA2, rootChar a α ≠ 1 ∧ rootChar a α ^ 3 = 1)
    (hsame : ∀ α ∈ d4LongA2, rootChar b α = rootChar a α)
    (hconj : u * rootDiagUnit TwistTag.D4.tag a * u⁻¹ = rootDiagUnit TwistTag.D4.tag b) :
    ∃ hm : u ∈ monomialSubgroup TwistTag.D4.tag L,
      (weylQuotientHom TwistTag.D4.tag L ⟨u, hm⟩ = 1 ∨
        (∀ x, weylQuotientHom TwistTag.D4.tag L ⟨u, hm⟩ • x = d4MatThreeA.mulVec x) ∨
        ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨u, hm⟩ • x = d4MatThreeB.mulVec x) ∧
      (u ∈ torusGroup TwistTag.D4.tag L ↔
        weylQuotientHom TwistTag.D4.tag L ⟨u, hm⟩ = 1) := by
  classical
  have hfr := mp_frame0 L
  obtain ⟨U, rfl⟩ : u ∈ (mpRho0 L).range := by
    rw [hfr.range, mp_sigma0_set]
    exact hu
  have hrel : ∀ X : SL(3, L), conjDiag3 (mpDiag b) X =
      U * conjDiag3 (mpDiag a) (U⁻¹ * X * U) * U⁻¹ := by
    intro X
    have e1 := mp_torus0 L b X
    have e2 := mp_torus0 L a (U⁻¹ * X * U)
    apply hfr.injective
    rw [← e1, map_mul, map_mul, ← e2]
    simp only [map_mul, map_inv, ← hconj]
    group
  obtain ⟨r, hr0, hUD⟩ := mp_conj_scalar (mpDiag a) (mpDiag b) U hrel
  have hdetU : (U : Matrix (Fin 3) (Fin 3) L).det = 1 := U.2
  have hreg' : ∀ i j : Fin 3, i ≠ j → (mpDiag a i : L) / (mpDiag a j : L) ≠ 1 ∧
      ((mpDiag a i : L) / (mpDiag a j : L)) ^ 3 = 1 := by
    intro i j hij
    obtain ⟨h1, h2⟩ := hreg _ (mp_sigma0_mem hij)
    rw [mp_ratio L a i j] at h1 h2
    constructor
    · intro h
      apply h1
      apply Units.ext
      simpa [div_eq_mul_inv] using h
    · have := congrArg Units.val h2
      simpa [div_eq_mul_inv, Units.val_pow_eq_pow_val] using this
  have hsame' : ∀ i j : Fin 3, i ≠ j → (mpDiag b i : L) / (mpDiag b j : L) =
      (mpDiag a i : L) / (mpDiag a j : L) := by
    intro i j hij
    have h := hsame _ (mp_sigma0_mem hij)
    rw [mp_ratio L b i j, mp_ratio L a i j] at h
    have := congrArg Units.val h
    simpa [div_eq_mul_inv] using this
  rcases mp_la5 (fun i => (mpDiag a i : L)) (fun i => (mpDiag b i : L))
      (fun i => (mpDiag a i).ne_zero) (fun i => (mpDiag b i).ne_zero) hreg' hsame' U hdetU r hr0
      hUD with hdiag | ⟨D, hD0, hUm⟩ | ⟨D, hD0, hUm⟩
  · have hT : mpRho0 L U ∈ torusGroup TwistTag.D4.tag L := hfr.diag U hdiag
    exact ⟨torusGroup_le_monomialSubgroup hT, Or.inl (mp_image_torus hT),
      ⟨fun _ => mp_image_torus hT, fun _ => hT⟩⟩
  · have hdetD : (Matrix.diagonal D).det = 1 := by
      have h1 := congrArg Matrix.det hUm
      rw [Matrix.det_mul, hdetU] at h1
      have h2 : (la_n01 * la_n12 : Matrix (Fin 3) (Fin 3) L).det = 1 := by
        rw [Matrix.det_mul]
        simp [la_n01, la_n12, Matrix.det_fin_three]
      rw [h2, mul_one] at h1
      exact h1.symm
    obtain ⟨Dsl, hDsl⟩ : ∃ Dsl : SL(3, L), (Dsl : Matrix (Fin 3) (Fin 3) L) =
        Matrix.diagonal D := ⟨⟨Matrix.diagonal D, hdetD⟩, rfl⟩
    have hU' : U = Dsl * (mpN01 L * mpN12 L) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hDsl]
      exact hUm
    have hT : mpRho0 L Dsl ∈ torusGroup TwistTag.D4.tag L :=
      hfr.diag _ (fun i j hij => by rw [hDsl]; simp [Matrix.diagonal_apply_ne _ hij])
    obtain ⟨m1, i1⟩ := mp_image_N01 L
    obtain ⟨m2, i2⟩ := mp_image_N12 L
    obtain ⟨hm, him⟩ := mp_image_prod hT m1 m2
    have e : mpRho0 L U = mpRho0 L Dsl *
        (mpRho0 L (mpN01 L) * mpRho0 L (mpN12 L)) := by
      rw [hU', map_mul, map_mul]
    have hact : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨mpRho0 L Dsl *
        (mpRho0 L (mpN01 L) * mpRho0 L (mpN12 L)), hm⟩ • x = d4MatThreeA.mulVec x := by
      intro x
      rw [him, i1, i2]
      exact mp_rot_A x
    rw [e]
    exact ⟨hm, Or.inr (Or.inl hact),
      mp_iff_of_rot hm d4MatThreeA hact ⟨Pi.single 0 1, by decide +kernel⟩⟩
  · have hdetD : (Matrix.diagonal D).det = 1 := by
      have h1 := congrArg Matrix.det hUm
      rw [Matrix.det_mul, hdetU] at h1
      have h2 : (la_n12 * la_n01 : Matrix (Fin 3) (Fin 3) L).det = 1 := by
        rw [Matrix.det_mul]
        simp [la_n01, la_n12, Matrix.det_fin_three]
      rw [h2, mul_one] at h1
      exact h1.symm
    obtain ⟨Dsl, hDsl⟩ : ∃ Dsl : SL(3, L), (Dsl : Matrix (Fin 3) (Fin 3) L) =
        Matrix.diagonal D := ⟨⟨Matrix.diagonal D, hdetD⟩, rfl⟩
    have hU' : U = Dsl * (mpN12 L * mpN01 L) := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hDsl]
      exact hUm
    have hT : mpRho0 L Dsl ∈ torusGroup TwistTag.D4.tag L :=
      hfr.diag _ (fun i j hij => by rw [hDsl]; simp [Matrix.diagonal_apply_ne _ hij])
    obtain ⟨m1, i1⟩ := mp_image_N12 L
    obtain ⟨m2, i2⟩ := mp_image_N01 L
    obtain ⟨hm, him⟩ := mp_image_prod hT m1 m2
    have e : mpRho0 L U = mpRho0 L Dsl *
        (mpRho0 L (mpN12 L) * mpRho0 L (mpN01 L)) := by
      rw [hU', map_mul, map_mul]
    have hact : ∀ x, weylQuotientHom TwistTag.D4.tag L ⟨mpRho0 L Dsl *
        (mpRho0 L (mpN12 L) * mpRho0 L (mpN01 L)), hm⟩ • x = d4MatThreeB.mulVec x := by
      intro x
      rw [him, i1, i2]
      exact mp_rot_B x
    rw [e]
    exact ⟨hm, Or.inr (Or.inr hact),
      mp_iff_of_rot hm d4MatThreeB hact ⟨Pi.single 0 1, by decide +kernel⟩⟩

end CFSG.GH74.GLS.Stage2.Bender.Thm1
