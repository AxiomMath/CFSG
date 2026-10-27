module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915K2f
public import CFSG.RankThree.SubgroupLists.CentralThreeLift
public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.L915

open Matrix CFSG.LocalAnalysis.ComponentInitial Subgroup
open scoped commutatorElement

section Conj

theorem exists_conj_t3 {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    {s : LinearFlag.projectiveSL 3 F} (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    ∃ g : LinearFlag.projectiveSL 3 F, g * LinearFlag.proj 3 F t3 * g⁻¹ = s := by
  have h2 := two_ne_zero_of_odd_card' hF
  obtain ⟨A, hAs, hA2⟩ := CFSG.RankThree.SubgroupLists.exists_lift_pow_eq_one
    (G := SpecialLinearGroup (Fin 3) F) (Z := LinearFlag.scalars 3 F)
    (LinearFlag.scalars_le_center 3 F)
    (fun z hz => CFSG.Wreathed.OddLinearThreeCentralizerCore.center_cube_eq_one F z
      (LinearFlag.scalars_le_center 3 F hz))
    (n := 2) (by norm_num) s (by rw [pow_two]; exact hs2)
  have hA2' : A * A = 1 := by rw [← pow_two]; exact hA2
  have hA1 : A ≠ 1 := by
    intro h
    apply hs1
    rw [← hAs, h]
    rfl
  let t : GL (Fin 3) F := Matrix.SpecialLinearGroup.toGL A
  have ht2 : t * t = 1 := by rw [← map_mul, hA2', map_one]
  have ht1 : t ≠ 1 := fun h =>
    hA1 (Matrix.SpecialLinearGroup.toGL_injective (h.trans (map_one _).symm))
  have hdet : (t : Matrix (Fin 3) (Fin 3) F).det = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]; exact A.2
  obtain ⟨P, hP⟩ := CFSG.RankThree.SubgroupLists.exists_conj_negDiag3 h2 ht2 ht1 hdet
  let c : F := (((Matrix.GeneralLinearGroup.det P)⁻¹ : Fˣ) : F)
  let Dm : Matrix (Fin 3) (Fin 3) F := Matrix.diagonal ![1, 1, c]
  let Pm : Matrix (Fin 3) (Fin 3) F := (P : Matrix (Fin 3) (Fin 3) F) * Dm
  have hPdet : Pm.det = 1 := by
    have h1 : ((Matrix.GeneralLinearGroup.det P : Fˣ) : F) = (P : Matrix (Fin 3) (Fin 3) F).det :=
      Matrix.GeneralLinearGroup.val_det_apply P
    have h3 : ((Matrix.GeneralLinearGroup.det P : Fˣ) : F) * c = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [Matrix.det_mul, Matrix.det_diagonal, ← h1]
    simpa [Fin.prod_univ_three] using h3
  have htP : (t : Matrix (Fin 3) (Fin 3) F) * (P : Matrix (Fin 3) (Fin 3) F) =
      (P : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![-1, -1, 1] := by
    have : t * P = P * CFSG.RankThree.SubgroupLists.negDiag3 F := by rw [← hP]; group
    have := congrArg (fun u : GL (Fin 3) F => (u : Matrix (Fin 3) (Fin 3) F)) this
    simpa [CFSG.RankThree.SubgroupLists.coe_negDiag3] using this
  have hAP : (A : Matrix (Fin 3) (Fin 3) F) * Pm =
      Pm * !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    have hAt : (A : Matrix (Fin 3) (Fin 3) F) = (t : Matrix (Fin 3) (Fin 3) F) :=
      (Matrix.SpecialLinearGroup.coe_GL_coe_matrix A).symm
    simp only [Pm]
    rw [← Matrix.mul_assoc, hAt, htP, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dm, Matrix.mul_apply, Fin.sum_univ_three]
  let Psl : SpecialLinearGroup (Fin 3) F := ⟨Pm, hPdet⟩
  have hAPsl : A * Psl = Psl * t3 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_t3]
    exact hAP
  refine ⟨LinearFlag.proj 3 F Psl, ?_⟩
  rw [← map_mul, ← map_inv, ← map_mul]
  have : Psl * t3 * Psl⁻¹ = A := by rw [← hAPsl]; group
  rw [this]
  exact hAs

end Conj

section Block

variable {F : Type} [Field F]

@[expose] def blockSL : SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 3) F :=
  betaSL.comp Matrix.SpecialLinearGroup.toGL

theorem coe_blockSL (A : SpecialLinearGroup (Fin 2) F) :
    ((blockSL A : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(A : Matrix (Fin 2) (Fin 2) F) 0 0, (A : Matrix (Fin 2) (Fin 2) F) 0 1, 0;
         (A : Matrix (Fin 2) (Fin 2) F) 1 0, (A : Matrix (Fin 2) (Fin 2) F) 1 1, 0; 0, 0, 1] := by
  ext i j
  have hd : Matrix.GeneralLinearGroup.det (Matrix.SpecialLinearGroup.toGL A) = 1 := by
    ext; simp
  fin_cases i <;> fin_cases j <;> simp [blockSL, coe_betaSL, blockM, hd]

theorem blockSL_eq_one_of_mem_scalars {A : SpecialLinearGroup (Fin 2) F}
    (h : blockSL A ∈ LinearFlag.scalars 3 F) : A = 1 := by
  obtain ⟨c, -, hc⟩ := h
  rw [coe_blockSL] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e11 := congrFun (congrFun hc 1) 1
  have e22 := congrFun (congrFun hc 2) 2
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  simp at e00 e11 e22 e01 e10
  have hc1 : (c : F) = 1 := e22.symm
  rw [hc1] at e00 e11
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e11, e01, e10]

theorem blockSL_comm_t3 (A : SpecialLinearGroup (Fin 2) F) : blockSL A * t3 = t3 * blockSL A := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_t3, coe_blockSL]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

end Block

section Lift

variable {X : Type} [Group X] {F : Type} [Field F] [Finite F]

theorem exists_perfect_lift_centralizer (hZ : Odd (Nat.card ↥(center X))) (hF : Odd (Nat.card F))
    (h4 : ∃ s : Finset F, s.card = 4)
    (ι : (X ⧸ center X) ≃* LinearFlag.projectiveSL 3 F) {x : X} (hx : x * x = 1) (hx1 : x ≠ 1) :
    ∃ Y : Subgroup X, Y ≤ centralizer ({x} : Set X) ∧ Group.IsPerfect ↥Y ∧
      ∃ φ : ↥Y →* SpecialLinearGroup (Fin 2) F, Function.Surjective φ ∧
        ∀ a : ↥Y, φ a = 1 → (a : X) ∈ center X := by
  have hs2 : ι (QuotientGroup.mk x) * ι (QuotientGroup.mk x) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, hx, QuotientGroup.mk_one, map_one]
  have hs1 : ι (QuotientGroup.mk x) ≠ 1 := by
    intro h
    have : (QuotientGroup.mk x : X ⧸ center X) = 1 := ι.injective (h.trans (map_one ι).symm)
    exact hx1 (eq_one_of_sq_eq_one_of_odd_center hZ ((QuotientGroup.eq_one_iff x).mp this) hx)
  obtain ⟨g, hg⟩ := exists_conj_t3 hF hs2 hs1
  let ψ₀ : SpecialLinearGroup (Fin 2) F →* X ⧸ center X :=
    (MulAut.conj (ι.symm g)).toMonoidHom.comp
      (ι.symm.toMonoidHom.comp ((LinearFlag.proj 3 F).comp blockSL))
  have hψ : ∀ A, ψ₀ A = ι.symm g * ι.symm (LinearFlag.proj 3 F (blockSL A)) * (ι.symm g)⁻¹ :=
    fun A => by simp [ψ₀, MulAut.conj_apply]
  have hψinj : Function.Injective ψ₀ := by
    rw [injective_iff_map_eq_one]
    intro A hA
    rw [hψ] at hA
    have h1 : ι.symm (LinearFlag.proj 3 F (blockSL A)) = 1 := by
      have := mul_inv_eq_one.mp hA
      simpa using this
    have h2 : LinearFlag.proj 3 F (blockSL A) = 1 := ι.symm.injective (h1.trans (map_one ι.symm).symm)
    exact blockSL_eq_one_of_mem_scalars (LinearFlag.proj_eq_one_iff.mp h2)
  have hmk : (QuotientGroup.mk x : X ⧸ center X) =
      ι.symm g * ι.symm (LinearFlag.proj 3 F t3) * (ι.symm g)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hg]
    exact (ι.symm_apply_apply _).symm
  have hψcomm : ∀ A, ψ₀ A * (QuotientGroup.mk x : X ⧸ center X) =
      (QuotientGroup.mk x : X ⧸ center X) * ψ₀ A := by
    intro A
    rw [hψ, hmk]
    have : ι.symm (LinearFlag.proj 3 F (blockSL A)) * ι.symm (LinearFlag.proj 3 F t3) =
        ι.symm (LinearFlag.proj 3 F t3) * ι.symm (LinearFlag.proj 3 F (blockSL A)) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, blockSL_comm_t3]
    calc ι.symm g * ι.symm (LinearFlag.proj 3 F (blockSL A)) * (ι.symm g)⁻¹ *
          (ι.symm g * ι.symm (LinearFlag.proj 3 F t3) * (ι.symm g)⁻¹)
        = ι.symm g * (ι.symm (LinearFlag.proj 3 F (blockSL A)) *
            ι.symm (LinearFlag.proj 3 F t3)) * (ι.symm g)⁻¹ := by group
      _ = ι.symm g * (ι.symm (LinearFlag.proj 3 F t3) *
            ι.symm (LinearFlag.proj 3 F (blockSL A))) * (ι.symm g)⁻¹ := by rw [this]
      _ = _ := by group
  have hSLperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.special_linear_dimension_two_perfect h4
  have hRperf : Group.IsPerfect ↥ψ₀.range :=
    Group.IsPerfect.ofSurjective (f := ψ₀.rangeRestrict) ψ₀.rangeRestrict_surjective
  set Y₀ : Subgroup X := ψ₀.range.comap (QuotientGroup.mk' (center X)) with hY₀
  have hY₀c : ∀ a ∈ Y₀, ⁅a, x⁆ ∈ center X := by
    intro a ha
    obtain ⟨A, hA⟩ := ha
    have h1 : (QuotientGroup.mk' (center X)) ⁅a, x⁆ = 1 := by
      rw [map_commutatorElement]
      have : (QuotientGroup.mk' (center X)) a * (QuotientGroup.mk' (center X)) x =
          (QuotientGroup.mk' (center X)) x * (QuotientGroup.mk' (center X)) a := by
        rw [← hA]
        exact hψcomm A
      exact commutatorElement_eq_one_iff_mul_comm.mpr this
    exact (QuotientGroup.eq_one_iff _).mp h1
  refine ⟨⁅Y₀, Y₀⁆, ?_, ?_, ?_⟩
  · refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commutatorElement_eq_one_iff_mul_comm.mp (comm_comm_eq_one a b x (hY₀c a ha) (hY₀c b hb))
  · exact CFSG.RankThree.SubgroupLists.isPerfect_commutator_comap (G := X) (Z := center X)
      (le_refl _) ψ₀.range
  · have hmapY : (⁅Y₀, Y₀⁆).map (QuotientGroup.mk' (center X)) = ψ₀.range :=
      CFSG.RankThree.SubgroupLists.map_commutator_comap (G := X) (Z := center X) ψ₀.range
    have hmem : ∀ a : ↥(⁅Y₀, Y₀⁆), (QuotientGroup.mk' (center X)) (a : X) ∈ ψ₀.range := fun a => by
      rw [← hmapY]
      exact ⟨a, a.2, rfl⟩
    let f₁ : ↥(⁅Y₀, Y₀⁆) →* ↥ψ₀.range :=
      ((QuotientGroup.mk' (center X)).comp (⁅Y₀, Y₀⁆).subtype).codRestrict ψ₀.range hmem
    let φ : ↥(⁅Y₀, Y₀⁆) →* SpecialLinearGroup (Fin 2) F :=
      (MonoidHom.ofInjective hψinj).symm.toMonoidHom.comp f₁
    refine ⟨φ, ?_, ?_⟩
    · intro A
      have hA : ψ₀ A ∈ (⁅Y₀, Y₀⁆).map (QuotientGroup.mk' (center X)) := by
        rw [hmapY]; exact ⟨A, rfl⟩
      obtain ⟨a, ha, haA⟩ := hA
      refine ⟨⟨a, ha⟩, ?_⟩
      apply hψinj
      have h1 : (MonoidHom.ofInjective hψinj) (φ ⟨a, ha⟩) = f₁ ⟨a, ha⟩ := by simp [φ]
      have h2 : ψ₀ (φ ⟨a, ha⟩) = (QuotientGroup.mk' (center X)) a := congrArg Subtype.val h1
      exact h2.trans haA
    · intro a ha
      have h1 : (MonoidHom.ofInjective hψinj) (φ a) = f₁ a := by simp [φ]
      rw [ha, map_one] at h1
      have h3 : (QuotientGroup.mk' (center X)) (a : X) = 1 := congrArg Subtype.val h1.symm
      exact (QuotientGroup.eq_one_iff _).mp h3

end Lift

end CFSG.GH74.GLS.Stage2.Bender.Thm2.L915
