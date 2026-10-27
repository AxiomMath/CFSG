module

public import CFSG.LieType.Chevalley.E7Three.Cycle
public import CFSG.RankThree.PartOne.KA5L.Torus
public import CFSG.HardMathSupport.Timmesfeld.Steinberg.ThreeCharCentralizer
public import CFSG.LieType.Chevalley.E7Three.Images

public noncomputable section

set_option autoImplicit false

namespace CFSG.LieType.Chevalley.E7Three.Centralizer

open Matrix CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.PartOne.KA5L CFSG.RankThree.PartOne.KE CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Chevalley.E7Three.Weyl CFSG.LieType.Chevalley.E7Three.Cube
  CFSG.LieType.Chevalley.E7Three.PauliWords CFSG.LieType.Chevalley.E7Three.Product
  CFSG.LieType.Chevalley.E7Three.Frames CFSG.HardMathSupport.Timmesfeld.CrossChar

open scoped MatrixGroups

variable {K : Type} [Field K] [CharP K 2]

variable (K) in
@[expose] def upperSL3 : SL(3, K) →* SL(6, K) := blockSL K 6 3 0 (by omega)

variable (K) in
@[expose] def lowerSL3 : SL(3, K) →* SL(6, K) := blockSL K 6 3 3 (by omega)

theorem theta_zero (w : NativeFrame K) : theta w 0 = (a5Frame K).comp (upperSL3 K) := by
  refine CFSG.LieType.CurtisTits.hom_ext_of_iSup_eq_top (iSup_range_blockSL2 (K := K) 2) ?_
  rintro i ⟨_, A, rfl⟩
  fin_cases i
  · have h := DFunLike.congr_fun (w.block0 0) A
    have h' := DFunLike.congr_fun (a5Frame_comp_blockSL2 K 0) A
    simp only [MonoidHom.comp_apply] at h h'
    change theta w 0 (blockSL K 3 2 0 (by omega) A) =
      a5Frame K (blockSL K 6 3 0 (by omega) (blockSL K 3 2 0 (by omega) A))
    rw [blockSL_comp_apply]
    change (w.rho 0) (conjDiag3Hom (w.diag 0) (blockSL K 3 2 0 (by omega) A)) = _
    rw [h]
    change _ = a5Frame K (blockSL2 K 5 0 A)
    rw [h', ← CFSG.RankThree.PartOne.KLAY.rootSL2_single]
    rfl
  · have h := DFunLike.congr_fun (w.block1 0) A
    have h' := DFunLike.congr_fun (a5Frame_comp_blockSL2 K 1) A
    simp only [MonoidHom.comp_apply] at h h'
    change theta w 0 (blockSL K 3 2 1 (by omega) A) =
      a5Frame K (blockSL K 6 3 0 (by omega) (blockSL K 3 2 1 (by omega) A))
    rw [blockSL_comp_apply]
    change (w.rho 0) (conjDiag3Hom (w.diag 0) (blockSL K 3 2 1 (by omega) A)) = _
    rw [h]
    change _ = a5Frame K (blockSL2 K 5 1 A)
    rw [h', ← CFSG.RankThree.PartOne.KLAY.rootSL2_single]
    rfl

theorem theta_one (w : NativeFrame K) : theta w 1 = (a5Frame K).comp (lowerSL3 K) := by
  refine CFSG.LieType.CurtisTits.hom_ext_of_iSup_eq_top (iSup_range_blockSL2 (K := K) 2) ?_
  rintro i ⟨_, A, rfl⟩
  fin_cases i
  · have h := DFunLike.congr_fun (w.block0 1) A
    have h' := DFunLike.congr_fun (a5Frame_comp_blockSL2 K 3) A
    simp only [MonoidHom.comp_apply] at h h'
    change theta w 1 (blockSL K 3 2 0 (by omega) A) =
      a5Frame K (blockSL K 6 3 3 (by omega) (blockSL K 3 2 0 (by omega) A))
    rw [blockSL_comp_apply]
    change (w.rho 1) (conjDiag3Hom (w.diag 1) (blockSL K 3 2 0 (by omega) A)) = _
    rw [h]
    change _ = a5Frame K (blockSL2 K 5 3 A)
    rw [h', ← CFSG.RankThree.PartOne.KLAY.rootSL2_single]
    rfl
  · have h := DFunLike.congr_fun (w.block1 1) A
    have h' := DFunLike.congr_fun (a5Frame_comp_blockSL2 K 4) A
    simp only [MonoidHom.comp_apply] at h h'
    change theta w 1 (blockSL K 3 2 1 (by omega) A) =
      a5Frame K (blockSL K 6 3 3 (by omega) (blockSL K 3 2 1 (by omega) A))
    rw [blockSL_comp_apply]
    change (w.rho 1) (conjDiag3Hom (w.diag 1) (blockSL K 3 2 1 (by omega) A)) = _
    rw [h]
    change _ = a5Frame K (blockSL2 K 5 4 A)
    rw [h', ← CFSG.RankThree.PartOne.KLAY.rootSL2_single]
    rfl

theorem prodHom_eq (w : NativeFrame K) (f : Fin 3 → SL(3, K)) :
    prodHom w f = a5Frame K (upperSL3 K (f 0) * lowerSL3 K (f 1)) * theta w 2 (f 2) := by
  rw [prodHom_apply, theta_zero, theta_one, map_mul]
  rfl

theorem scalarWord_eq (w : NativeFrame K) (ζ : Kˣ) :
    (scalarWord ζ : ModGL .E7 K) =
      a5Frame K (upperSL3 K (centralWord ζ) * lowerSL3 K (centralWord ζ)) := by
  rw [← Images.prodHom_central w ζ, prodHom_eq]
  simp

theorem pairedWord_eq (w : NativeFrame K) (ζ : Kˣ) :
    (pairedWord ζ : ModGL .E7 K) =
      a5Frame K (upperSL3 K (diagonalWord ζ) * lowerSL3 K (diagonalWord ζ)) *
        theta w 2 (diagonalWord ζ) := by
  rw [← Images.prodHom_diagonal w ζ, prodHom_eq]
  rfl

theorem cyclic_eq (w : NativeFrame K) :
    (cyclic (K := K) : ModGL .E7 K) =
      a5Frame K (upperSL3 K cycleWord * lowerSL3 K cycleWord) * theta w 2 (cycleWord ^ 2) := by
  rw [← Cycle.prodHom_cycle w, prodHom_eq]
  rfl

theorem isRoot_e7ExtVec_none : IsRoot .E7 (e7ExtVec none) := by
  rw [isRoot_iff_exists_e7RootVec]
  decide +kernel

theorem theta_two_centralWord (w : NativeFrame K) (ζ : Kˣ) (hζ : ζ ^ 3 = 1) :
    theta w 2 (centralWord ζ) = (scalarWord ζ : ModGL .E7 K) := by
  have h0 := DFunLike.congr_fun (w.block0 2) (HSL ζ)
  have h1 := DFunLike.congr_fun (w.block1 2) (HSL (ζ ^ 2))
  simp only [MonoidHom.comp_apply] at h0 h1
  rw [centralWord, map_mul]
  change (w.rho 2) (conjDiag3Hom (w.diag 2) (blockSL K 3 2 0 (by omega) (HSL ζ))) *
    (w.rho 2) (conjDiag3Hom (w.diag 2) (blockSL K 3 2 1 (by omega) (HSL (ζ ^ 2)))) = _
  rw [h0, h1, scalarWord_val ζ hζ]
  change rootSL2 .E7 K (e7ExtVec none) (HSL ζ) *
    rootSL2 .E7 K (Pi.single (e7Index 0) 1) (HSL (ζ ^ 2)) = _
  rw [rootSL2_HSL_eq isRoot_e7ExtVec_none, CFSG.RankThree.PartOne.KLAY.rootSL2_single,
    simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
  congr 1
  funext i
  have key : ∀ i : Fin Tag.E7.rank,
      (corootPair (e7ExtVec none) (Pi.single i 1) + 2 * Tag.E7.cartan (e7Index 0) i) %
        ((3 : ℕ) : ℤ) = scalarExp i % ((3 : ℕ) : ℤ) := by
    decide +kernel
  rw [Pi.mul_apply, show (ζ ^ 2 : Kˣ) = ζ ^ (2 : ℤ) from (zpow_natCast ζ 2).symm,
    ← _root_.zpow_mul, ← _root_.zpow_add, zpow_eq_zpow_emod' _ hζ, key i,
    ← zpow_eq_zpow_emod' _ hζ]
  rfl

theorem conjDiag3_conjDiag3_inv (d : Fin 3 → Kˣ) (A : SL(3, K)) :
    conjDiag3 d (conjDiag3 d⁻¹ A) = A := by
  apply Subtype.ext
  rw [coe_conjDiag3, coe_conjDiag3]
  have h1 : (diagGL3 d : Matrix (Fin 3) (Fin 3) K) * (diagGL3 d⁻¹ : Matrix (Fin 3) (Fin 3) K) = 1 := by
    simp [diagGL3, Matrix.diagonal_mul_diagonal]
  have h2 : (((diagGL3 d⁻¹)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (((diagGL3 d)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← Units.val_mul, ← _root_.mul_inv_rev]
    have : diagGL3 d * diagGL3 d⁻¹ = 1 := Units.ext h1
    rw [this, inv_one, Units.val_one]
  calc (diagGL3 d : Matrix (Fin 3) (Fin 3) K) *
        ((diagGL3 d⁻¹ : Matrix (Fin 3) (Fin 3) K) * A * (((diagGL3 d⁻¹)⁻¹ : GL (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K)) * (((diagGL3 d)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      = ((diagGL3 d : Matrix (Fin 3) (Fin 3) K) * (diagGL3 d⁻¹ : Matrix (Fin 3) (Fin 3) K)) * A *
          ((((diagGL3 d⁻¹)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (((diagGL3 d)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) := by
        simp only [Matrix.mul_assoc]
    _ = A := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem range_theta_two (w : NativeFrame K) :
    (theta w 2).range =
      rootSpan .E7 K {r | ∃ i j : Fin 3, i ≠ j ∧ r = nativeA2Roots 2 i j} := by
  rw [← (w.isFrame 2).range]
  apply le_antisymm
  · rintro _ ⟨A, rfl⟩
    exact ⟨conjDiag3 (w.diag 2) A, rfl⟩
  · rintro _ ⟨A, rfl⟩
    refine ⟨conjDiag3 (w.diag 2)⁻¹ A, ?_⟩
    change (w.rho 2) (conjDiag3 (w.diag 2) (conjDiag3 (w.diag 2)⁻¹ A)) = _
    rw [conjDiag3_conjDiag3_inv]

theorem rootSubgroup_a5Root_le (a b : Fin 6) (hab : a ≠ b) :
    rootSubgroup .E7 K (a5Root a b) ≤ (a5Frame K).range := by
  obtain ⟨ε, hε⟩ := a5Frame_transv (L := K) a b hab
  rw [rootSubgroup, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩
  refine ⟨Matrix.SpecialLinearGroup.transvection hab (((ε⁻¹ : Kˣ) : K) * c), ?_⟩
  rw [hε, ← mul_assoc, Units.mul_inv, one_mul]

theorem a5_or_a2_of_three_dvd : ∀ m : Fin 126,
    CFSG.RankThree.PartOne.KE.e7RootVec m (e7Index 2) % 3 = 0 →
      (∃ a b : Fin 6, a ≠ b ∧ CFSG.RankThree.PartOne.KE.e7RootVec m = a5Root a b) ∨
        ∃ i j : Fin 3, i ≠ j ∧ CFSG.RankThree.PartOne.KE.e7RootVec m = nativeA2Roots 2 i j := by
  decide +kernel

theorem rootChar_scalar (ζ : Kˣ) (α : Fin Tag.E7.rank → ℤ) :
    rootChar (cubeChar ζ scalarExp) α = ζ ^ α (e7Index 2) := by
  change ∏ i : Fin 7, (ζ ^ scalarExp i) ^ α i = ζ ^ α 2
  simp [Fin.prod_univ_seven, scalarExp]
  rfl

theorem torusElt_two_mem [IsAlgClosed K] (w : NativeFrame K) (u : Kˣ) :
    torusElt .E7 K (e7Index 2) u ∈ (a5Frame K).range ⊔ (theta w 2).range := by
  obtain ⟨v0, hv0⟩ := IsAlgClosed.exists_pow_nat_eq ((u⁻¹ : Kˣ) : K) (n := 3) (by norm_num)
  have hv0' : v0 ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hv0
    exact (u⁻¹).ne_zero hv0.symm
  set v : Kˣ := Units.mk0 v0 hv0' with hvdef
  have hv : v ^ (-3 : ℤ) = u := by
    have h3 : v ^ 3 = u⁻¹ := Units.ext (by simp [hvdef, hv0])
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, _root_.zpow_neg, zpow_natCast, h3, inv_inv]
  have hθ : theta w 2 (blockSL K 3 2 0 (by omega) (HSL v)) =
      ((List.finRange Tag.E7.rank).map fun j => torusElt .E7 K j (v ^ e7ExtVec none j)).prod := by
    have h0 := DFunLike.congr_fun (w.block0 2) (HSL v)
    simp only [MonoidHom.comp_apply] at h0
    change (w.rho 2) (conjDiag3Hom (w.diag 2) (blockSL K 3 2 0 (by omega) (HSL v))) = _
    rw [h0, list_prod_torusElt_eq_rootDiagUnit]
    change rootSL2 .E7 K (e7ExtVec none) (HSL v) = _
    rw [rootSL2_HSL_eq isRoot_e7ExtVec_none]
    congr 1
    funext l
    have key : ∀ l : Fin Tag.E7.rank, corootPair (e7ExtVec none) (Pi.single l 1) =
        ∑ j, e7ExtVec none j * Tag.E7.cartan j l := by
      decide +kernel
    rw [cartanChar, key l]
    simp only [← _root_.zpow_mul]
    rw [Finset.prod_zpow_eq_zpow_sum]
  have hmem : ((List.finRange Tag.E7.rank).map
      fun j => torusElt .E7 K j (v ^ e7ExtVec none j)).prod ∈
        (a5Frame K).range ⊔ (theta w 2).range := by
    rw [← hθ]
    exact Subgroup.mem_sup_right ⟨_, rfl⟩
  have ha (j : Fin 5) (t : Kˣ) : torusElt .E7 K (a5chain j) t ∈
      (a5Frame K).range ⊔ (theta w 2).range :=
    Subgroup.mem_sup_left ⟨_, a5Frame_blockSL2_HSL j t⟩
  have h0 (t : Kˣ) : torusElt .E7 K (e7Index 0) t ∈ (a5Frame K).range ⊔ (theta w 2).range :=
    Subgroup.mem_sup_right ⟨_, Images.theta_diagonal_two w t⟩
  rw [show (List.finRange Tag.E7.rank) = [0, 1, 2, 3, 4, 5, 6] from rfl] at hmem
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hmem
  set S := (a5Frame K).range ⊔ (theta w 2).range
  have e : torusElt .E7 K 2 (v ^ e7ExtVec none 2) =
      (torusElt .E7 K 1 (v ^ e7ExtVec none 1))⁻¹ * ((torusElt .E7 K 0 (v ^ e7ExtVec none 0))⁻¹ *
        (torusElt .E7 K 0 (v ^ e7ExtVec none 0) * (torusElt .E7 K 1 (v ^ e7ExtVec none 1) *
          (torusElt .E7 K 2 (v ^ e7ExtVec none 2) * (torusElt .E7 K 3 (v ^ e7ExtVec none 3) *
            (torusElt .E7 K 4 (v ^ e7ExtVec none 4) * (torusElt .E7 K 5 (v ^ e7ExtVec none 5) *
              torusElt .E7 K 6 (v ^ e7ExtVec none 6)))))))) *
      (torusElt .E7 K 3 (v ^ e7ExtVec none 3) * (torusElt .E7 K 4 (v ^ e7ExtVec none 4) *
        (torusElt .E7 K 5 (v ^ e7ExtVec none 5) * torusElt .E7 K 6 (v ^ e7ExtVec none 6))))⁻¹ := by
    group
  have hc2 : v ^ e7ExtVec none 2 = u := hv
  rw [hc2] at e
  change torusElt .E7 K 2 u ∈ S
  rw [e]
  refine S.mul_mem (S.mul_mem (S.inv_mem (ha 0 _)) (S.mul_mem (S.inv_mem (h0 _)) ?_))
    (S.inv_mem (S.mul_mem (ha 1 _) (S.mul_mem (ha 2 _) (S.mul_mem (ha 3 _) (ha 4 _)))))
  rw [hc2] at hmem
  exact hmem

section Steinberg

theorem toralCentralizer_scalar_le [IsAlgClosed K] (w : NativeFrame K) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot ζ 3) :
    toralCentralizer .E7 K (cubeChar ζ scalarExp) ≤ (a5Frame K).range ⊔ (theta w 2).range := by
  have h3 : ∀ i, cubeChar ζ scalarExp i ^ 3 = 1 := fun i => by
    rw [cubeChar, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
      hζ.pow_eq_one, _root_.one_zpow]
  rw [CFSG.HardMathSupport.Timmesfeld.Steinberg.toralCentralizer_eq_toralRootGroup_E7_three K _ h3,
    toralRootGroup]
  refine sup_le ?_ ?_
  ·
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, u⟩, rfl⟩
    change torusElt .E7 K i u ∈ _
    fin_cases i
    · exact Subgroup.mem_sup_right ⟨_, Images.theta_diagonal_two w u⟩
    · exact Subgroup.mem_sup_left ⟨_, a5Frame_blockSL2_HSL 0 u⟩
    · exact torusElt_two_mem w u
    · exact Subgroup.mem_sup_left ⟨_, a5Frame_blockSL2_HSL 1 u⟩
    · exact Subgroup.mem_sup_left ⟨_, a5Frame_blockSL2_HSL 2 u⟩
    · exact Subgroup.mem_sup_left ⟨_, a5Frame_blockSL2_HSL 3 u⟩
    · exact Subgroup.mem_sup_left ⟨_, a5Frame_blockSL2_HSL 4 u⟩
  ·
    refine iSup₂_le fun α hα => ?_
    obtain ⟨hαr, hα1⟩ := hα
    rw [rootChar_scalar] at hα1
    have h3 : α (e7Index 2) % 3 = 0 := by
      have := (hζ.zpow_eq_one_iff_dvd _).1 hα1
      omega
    obtain ⟨m, rfl⟩ := isRoot_iff_exists_e7RootVec.1 hαr
    rcases a5_or_a2_of_three_dvd m h3 with ⟨a, b, hab, he⟩ | ⟨i, j, hij, he⟩
    · rw [he]
      exact (rootSubgroup_a5Root_le a b hab).trans le_sup_left
    · rw [he]
      refine le_trans ?_ le_sup_right
      rw [range_theta_two]
      exact le_iSup₂_of_le (nativeA2Roots 2 i j) ⟨i, j, hij, rfl⟩ le_rfl

end Steinberg

end CFSG.LieType.Chevalley.E7Three.Centralizer
