module

public import CFSG.ClassicalInvolution.WeakCT.AutExtend
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelSylow
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem rootTorusSL2_eq_thetaDiag_gen {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (c : Fˣ) :
    rootTorusSL2 .E7 F β c = rootDiagUnit .E7 (thetaDiag β c) := by
  obtain ⟨-, hdH, -, -, hact, -, -, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport .E7 F hβ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hdH c)
  rw [ha]
  congr 1
  funext i
  have h1 := (hact c).2 (Pi.single i 1) (isRoot_single .E7 i)
  rw [ha] at h1
  have h2 : (((rootDiagUnit .E7 a : ModGL .E7 F) : Module.End F (RootModule .E7 F))
      (rootVec .E7 F (Pi.single i 1))) = ((a i : Fˣ) : F) • rootVec .E7 F (Pi.single i 1) := by
    change rootDiag a (rootVec .E7 F (Pi.single i 1)) = _
    have hs : rootChar a (Pi.single i 1 : Fin (Tag.rank .E7) → ℤ) = a i := by
      have := rootChar_nsmul_single a i 1
      rwa [one_smul, pow_one] at this
    rw [rootDiag_rootVec _ (isRoot_single .E7 i), hs]
  rw [h2] at h1
  have hne : rootVec .E7 F (Pi.single i 1) ≠ 0 := by
    rw [rootVec_eq_single_of_isRoot (isRoot_single .E7 i)]
    exact Finsupp.single_ne_zero.2 one_ne_zero
  have h3 := smul_left_injective F hne h1
  have h4 : 2 * iform β (Pi.single i 1) / iform β β = iform β (Pi.single i 1) := by
    rw [iform_self_isRoot_E7 hβ]
    omega
  rw [h4] at h3
  exact Units.ext h3


theorem diagConj2_uSL_gen (a : Fˣ) (c : F) : diagConj2 a 1 (uSL c) = uSL ((a : F) * c) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_diagConj2, coe_uSL, Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagConj2_vSL_gen (a : Fˣ) (c : F) :
    diagConj2 a 1 (vSL c) = vSL (((a⁻¹ : Fˣ) : F) * c) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_diagConj2, coe_vSL, Matrix.mul_apply, Matrix.diagonal_apply, mul_comm]

theorem rootDiagUnit_conj_rootSL2_gen (b : Fin (Tag.rank .E7) → Fˣ) {β : Fin (Tag.rank .E7) → ℤ}
    (hβ : IsRoot .E7 β) (A : SL2 F) :
    rootDiagUnit .E7 b * rootSL2 .E7 F β A * (rootDiagUnit .E7 b)⁻¹ =
      rootSL2 .E7 F β (diagConj2 (rootChar b β) 1 A) := by
  have h : (MulAut.conj (rootDiagUnit .E7 b)).toMonoidHom.comp (rootSL2 .E7 F β) =
      (rootSL2 .E7 F β).comp (diagConj2 (rootChar b β) 1).toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change rootDiagUnit .E7 b * rootSL2 .E7 F β (uSL c) * (rootDiagUnit .E7 b)⁻¹ =
          rootSL2 .E7 F β (diagConj2 (rootChar b β) 1 (uSL c))
        rw [diagConj2_uSL_gen]
        exact (CFSG.LieType.AlgebraicGroups.rootDiagUnit_conj_rootSL2 b hβ c).1
      · change rootDiagUnit .E7 b * rootSL2 .E7 F β (vSL c) * (rootDiagUnit .E7 b)⁻¹ =
          rootSL2 .E7 F β (diagConj2 (rootChar b β) 1 (vSL c))
        rw [diagConj2_vSL_gen]
        exact (CFSG.LieType.AlgebraicGroups.rootDiagUnit_conj_rootSL2 b hβ c).2
  exact DFunLike.congr_fun h A


theorem levi_conj_rootSL2_eq {n : ModGL .E7 F} (hn : n ∈ parabolicLevi .E7 F JE7) :
    ∃ l : Fˣ, ∀ B : SL2 F, n * rootSL2 .E7 F thetaE7 B * n⁻¹ =
      rootSL2 .E7 F thetaE7 (diagConj2 l 1 B) := by
  obtain ⟨l, hu, hv⟩ := exists_levi_conj_rootSL2_thetaE7 hn
  refine ⟨l, fun B => ?_⟩
  have h : (MulAut.conj n).toMonoidHom.comp (rootSL2 .E7 F thetaE7) =
      (rootSL2 .E7 F thetaE7).comp (diagConj2 l 1).toMonoidHom :=
    MonoidHom.eq_of_eqOn_dense sl2_closure_upper_lower fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change n * rootSL2 .E7 F thetaE7 (uSL c) * n⁻¹ =
          rootSL2 .E7 F thetaE7 (diagConj2 l 1 (uSL c))
        rw [diagConj2_uSL_gen]
        exact hu c
      · change n * rootSL2 .E7 F thetaE7 (vSL c) * n⁻¹ =
          rootSL2 .E7 F thetaE7 (diagConj2 l 1 (vSL c))
        rw [diagConj2_vSL_gen]
        exact hv c
  exact DFunLike.congr_fun h B

theorem lower_left_eq_zero_of_conj_uSL {a : Fˣ} (ha : a ^ 2 ≠ 1) {A : SL2 F}
    (h : A * uSL (a : F) * A⁻¹ = diagConj2 a 1 (A * uSL 1 * A⁻¹)) :
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  have h10 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_diagConj2, coe_uSL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply] at h10
  simp at h10
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have ha1 : (a : F) ^ 2 - 1 ≠ 0 := by
    intro h
    apply ha
    apply Units.ext
    simpa [sub_eq_zero] using h
  set c : F := (A : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d : F := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have h2 : c ^ 2 * ((a : F) ^ 2 - 1) = 0 := by
    field_simp at h10
    linear_combination (-1 : F) * h10
  have h3 : c ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_right ha1
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h3


theorem upper_right_eq_zero_of_conj_vSL {a : Fˣ} (ha : a ^ 2 ≠ 1) {A : SL2 F}
    (h : A * vSL (((a⁻¹ : Fˣ) : F)) * A⁻¹ = diagConj2 a 1 (A * vSL 1 * A⁻¹)) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
  have h01 := congrArg (fun M : SL2 F => (M : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_diagConj2, coe_vSL, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply] at h01
  simp at h01
  have ha0 : (a : F) ≠ 0 := a.ne_zero
  have ha1 : (a : F) ^ 2 - 1 ≠ 0 := by
    intro h
    apply ha
    apply Units.ext
    simpa [sub_eq_zero] using h
  set b : F := (A : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set d : F := (A : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have h2 : b ^ 2 * ((a : F) ^ 2 - 1) = 0 := by
    field_simp at h01
    linear_combination h01
  have h3 : b ^ 2 = 0 := (mul_eq_zero.1 h2).resolve_right ha1
  exact pow_eq_zero_iff (two_ne_zero) |>.1 h3


theorem diagConj2_comm_one (l a : Fˣ) (X : SL2 F) :
    diagConj2 l 1 (diagConj2 a 1 X) = diagConj2 a 1 (diagConj2 l 1 X) := by
  refine SL2_ext ?_ ?_ ?_ ?_ <;>
    simp [coe_diagConj2, Matrix.mul_apply, Matrix.diagonal_apply] <;> ring

theorem conj_comm_conj {G : Type*} [Group G] {g τ : G} (h : g * τ = τ * g) (X : G) :
    g * (τ * X * τ⁻¹) * g⁻¹ = τ * (g * X * g⁻¹) * τ⁻¹ := by
  have h' : τ⁻¹ * g⁻¹ = g⁻¹ * τ⁻¹ := by
    rw [← mul_inv_rev, ← mul_inv_rev, h]
  calc g * (τ * X * τ⁻¹) * g⁻¹ = (g * τ) * X * (τ⁻¹ * g⁻¹) := by group
    _ = (τ * g) * X * (g⁻¹ * τ⁻¹) := by rw [h, h']
    _ = τ * (g * X * g⁻¹) * τ⁻¹ := by group

theorem mem_parabolicLevi_of_commute_diag (hF : ringChar F ≠ 2) {y : ModGL .E7 F}
    (hyG : y ∈ adjointGroup .E7 F)
    (hyd : y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) =
      rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : Fˣ)) * y)
    {b : Fin (Tag.rank .E7) → Fˣ} (hb : rootChar b thetaE7 ^ 2 ≠ 1)
    (hyb : y * rootDiagUnit .E7 b = rootDiagUnit .E7 b * y) :
    y ∈ parabolicLevi .E7 F JE7 := by
  have hρinj : Function.Injective (rootSL2 .E7 F thetaE7) :=
    ((exceptional_Lang_root_rank_one_data .E7 F thetaE7).2.2.2.2.2.2.2.1 hF).1
  have hcT : y ∈ toralCentralizer .E7 F (thetaDiag thetaE7 (-1 : Fˣ)) := by
    rw [mem_toralCentralizer]
    refine ⟨hyG, ?_⟩
    rw [mul_inv_eq_iff_eq_mul]
    exact hyd.symm
  obtain ⟨n, hn, A, rfl⟩ :=
    toralRootGroup_le_leviMulRank1 hF (toralCentralizer_le_toralRootGroup_thetaE7 hF hcT)
  obtain ⟨l, hl⟩ := levi_conj_rootSL2_eq hn
  set a := rootChar b thetaE7 with ha
  have key : ∀ B : SL2 F, A * diagConj2 a 1 B * A⁻¹ = diagConj2 a 1 (A * B * A⁻¹) := by
    intro B
    have e1 : (n * rootSL2 .E7 F thetaE7 A) * (rootDiagUnit .E7 b * rootSL2 .E7 F thetaE7 B *
        (rootDiagUnit .E7 b)⁻¹) * (n * rootSL2 .E7 F thetaE7 A)⁻¹ =
        rootSL2 .E7 F thetaE7 (diagConj2 l 1 (A * diagConj2 a 1 B * A⁻¹)) := by
      rw [rootDiagUnit_conj_rootSL2_gen b isRoot_thetaE7, ← ha, ← hl]
      simp only [map_mul, map_inv]
      group
    have e2 : rootDiagUnit .E7 b * ((n * rootSL2 .E7 F thetaE7 A) * rootSL2 .E7 F thetaE7 B *
        (n * rootSL2 .E7 F thetaE7 A)⁻¹) * (rootDiagUnit .E7 b)⁻¹ =
        rootSL2 .E7 F thetaE7 (diagConj2 a 1 (diagConj2 l 1 (A * B * A⁻¹))) := by
      have : (n * rootSL2 .E7 F thetaE7 A) * rootSL2 .E7 F thetaE7 B *
          (n * rootSL2 .E7 F thetaE7 A)⁻¹ =
          rootSL2 .E7 F thetaE7 (diagConj2 l 1 (A * B * A⁻¹)) := by
        rw [← hl]
        simp only [map_mul, map_inv]
        group
      rw [this, rootDiagUnit_conj_rootSL2_gen b isRoot_thetaE7, ← ha]
    rw [conj_comm_conj hyb, e2] at e1
    have e4 := hρinj e1
    rw [← diagConj2_comm_one l a] at e4
    exact ((diagConj2 l 1).injective e4).symm
  have hc0 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    refine lower_left_eq_zero_of_conj_uSL hb ?_
    have := key (uSL 1)
    rwa [diagConj2_uSL_gen, mul_one] at this
  have hb0 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    refine upper_right_eq_zero_of_conj_vSL hb ?_
    have := key (vSL 1)
    rwa [diagConj2_vSL_gen, mul_one] at this
  have hdet := det_SL2 A
  rw [hc0, mul_zero, sub_zero] at hdet
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have hAH : A = HSL (Units.mk0 _ hA00) := by
    refine SL2_ext ?_ ?_ ?_ ?_ <;> simp [coe_HSL, hc0, hb0]
    exact eq_inv_of_mul_eq_one_right hdet
  rw [hAH]
  exact mul_mem hn (torusGroup_le_parabolicLevi JE7
    ((exceptional_Lang_root_rank_one_torus_transport .E7 F isRoot_thetaE7).2.1 _))

end CFSG.ClassicalInvolution.ModelFacts.E7Model
