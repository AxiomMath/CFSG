module

public import CFSG.ClassicalInvolution.Phan.Phan3D4Check
public import CFSG.ClassicalInvolution.Phan.Phan3ASound
public import CFSG.ClassicalInvolution.RouteD.GapsOrthExcl
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open scoped MatrixGroups
open Matrix.SpecialLinearGroup CFSG.CosetTable CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.WeakCT (blockSL coe_blockSL)

section Field

variable {K : Type} [Field K]

theorem charP_three (hK : Nat.card K = 3) : CharP K 3 := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite K
  obtain ⟨p, hp⟩ := CharP.exists K
  obtain ⟨n, hpp, hn⟩ := FiniteField.card K p
  have hc : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card, hK]
  have hd : p ∣ 3 := by
    rw [← hc, hn]
    exact dvd_pow_self p n.ne_zero
  have h3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 hd
  rw [h3] at hp
  exact hp

noncomputable def zmodToK (hK : Nat.card K = 3) : ZMod 3 →+* K :=
  haveI := charP_three hK
  ZMod.castHom (dvd_refl 3) K

theorem zmodToK_bijective (hK : Nat.card K = 3) : Function.Bijective (zmodToK hK) := by
  have hfin : Finite K := Nat.finite_of_card_ne_zero (by omega)
  refine (zmodToK hK).injective.bijective_of_nat_card_le ?_
  rw [hK, Nat.card_zmod]

noncomputable def zmodEquiv (hK : Nat.card K = 3) : ZMod 3 ≃+* K :=
  RingEquiv.ofBijective (zmodToK hK) (zmodToK_bijective hK)

end Field

@[expose] noncomputable def sl3Gen (K : Type) [Field K] : Fin 4 → SL(3, K) :=
  ![transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K),
    transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : K),
    transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : K),
    transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : K)]

theorem wordVal_sl3Gen_rels_zmod : ∀ r ∈ sl3Rels, wordVal (sl3Gen (ZMod 3)) r = 1 := by
  decide +kernel

variable {K : Type} [Field K]

theorem sl3Gen_eq_map (hK : Nat.card K = 3) (i : Fin 4) :
    sl3Gen K i = Matrix.SpecialLinearGroup.map (zmodToK hK) (sl3Gen (ZMod 3) i) := by
  fin_cases i <;>
    simp [sl3Gen, Matrix.SpecialLinearGroup.map_transvection]

theorem wordVal_sl3Gen_rels (hK : Nat.card K = 3) : ∀ r ∈ sl3Rels, wordVal (sl3Gen K) r = 1 := by
  intro r hr
  have h : sl3Gen K = fun i => Matrix.SpecialLinearGroup.map (zmodToK hK) (sl3Gen (ZMod 3) i) :=
    funext (sl3Gen_eq_map hK)
  rw [h, wordVal_map (Matrix.SpecialLinearGroup.map (zmodToK hK)) (sl3Gen (ZMod 3)) r,
    wordVal_sl3Gen_rels_zmod r hr, map_one]

theorem eq_zero_or_one_or_neg_one (hK : Nat.card K = 3) (c : K) : c = 0 ∨ c = 1 ∨ c = -1 := by
  obtain ⟨n, rfl⟩ := (zmodToK_bijective hK).2 c
  have h : n = 0 ∨ n = 1 ∨ n = -1 := by revert n; decide
  rcases h with rfl | rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (Or.inl (map_one _))
  · exact Or.inr (Or.inr ((map_neg (zmodToK hK) (1 : ZMod 3)).trans (by rw [map_one])))

theorem sl3Gen_closure (hK : Nat.card K = 3) :
    Subgroup.closure (Set.range (sl3Gen K)) = ⊤ := by
  set H := Subgroup.closure (Set.range (sl3Gen K)) with hH
  have g0 : transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K) ∈ H :=
    Subgroup.subset_closure ⟨0, rfl⟩
  have g1 : transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : K) ∈ H :=
    Subgroup.subset_closure ⟨1, rfl⟩
  have g2 : transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : K) ∈ H :=
    Subgroup.subset_closure ⟨2, rfl⟩
  have g3 : transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : K) ∈ H :=
    Subgroup.subset_closure ⟨3, rfl⟩
  have g02 : transvection (show (0 : Fin 3) ≠ 2 by decide) (1 : K) ∈ H := by
    have := commutatorElement_transvection (show (0 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 2 by decide) (show (0 : Fin 3) ≠ 2 by decide) (1 : K) 1
    rw [mul_one] at this
    rw [← this, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem g0 g2) (H.inv_mem g0)) (H.inv_mem g2)
  have g20 : transvection (show (2 : Fin 3) ≠ 0 by decide) (1 : K) ∈ H := by
    have := commutatorElement_transvection (show (2 : Fin 3) ≠ 1 by decide)
      (show (1 : Fin 3) ≠ 0 by decide) (show (2 : Fin 3) ≠ 0 by decide) (1 : K) 1
    rw [mul_one] at this
    rw [← this, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem g3 g1) (H.inv_mem g3)) (H.inv_mem g1)
  have hall : ∀ (i j : Fin 3) (hij : i ≠ j), transvection hij (1 : K) ∈ H := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
  rw [eq_top_iff, ← closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 3) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  rcases eq_zero_or_one_or_neg_one hK c with rfl | rfl | rfl
  · rw [transvection_coeff_zero]
    exact H.one_mem
  · exact hall i j hij
  · rw [← transvection_inv]
    exact H.inv_mem (hall i j hij)

theorem sl2_closure (hK : Nat.card K = 3) :
    Subgroup.closure {transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : K),
      transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : K)} = ⊤ := by
  set H := Subgroup.closure {transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : K),
      transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : K)} with hH
  have g0 : transvection (show (0 : Fin 2) ≠ 1 by decide) (1 : K) ∈ H :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have g1 : transvection (show (1 : Fin 2) ≠ 0 by decide) (1 : K) ∈ H :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hall : ∀ (i j : Fin 2) (hij : i ≠ j), transvection hij (1 : K) ∈ H := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | assumption
  rw [eq_top_iff, ← closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin 2) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨⟨i, j, hij, c⟩, rfl⟩
  rw [Matrix.TransvectionStruct.toSpecialLinearGroup_mk]
  rcases eq_zero_or_one_or_neg_one hK c with rfl | rfl | rfl
  · rw [transvection_coeff_zero]
    exact H.one_mem
  · exact hall i j hij
  · rw [← transvection_inv]
    exact H.inv_mem (hall i j hij)

theorem blockSL_t01_zero (c : K) :
    blockSL K 3 2 0 (by omega) (transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      transvection (show (0 : Fin 3) ≠ 1 by decide) c := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [coe_blockSL, Phan.blockMat, Phan.blockSel, Matrix.mul_apply, Fin.sum_univ_two,
      transvection_coe, Matrix.single_apply]

theorem blockSL_t10_zero (c : K) :
    blockSL K 3 2 0 (by omega) (transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      transvection (show (1 : Fin 3) ≠ 0 by decide) c := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [coe_blockSL, Phan.blockMat, Phan.blockSel, Matrix.mul_apply, Fin.sum_univ_two,
      transvection_coe, Matrix.single_apply]

theorem blockSL_t01_one (c : K) :
    blockSL K 3 2 1 (by omega) (transvection (show (0 : Fin 2) ≠ 1 by decide) c) =
      transvection (show (1 : Fin 3) ≠ 2 by decide) c := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [coe_blockSL, Phan.blockMat, Phan.blockSel, Matrix.mul_apply, Fin.sum_univ_two,
      transvection_coe, Matrix.single_apply]

theorem blockSL_t10_one (c : K) :
    blockSL K 3 2 1 (by omega) (transvection (show (1 : Fin 2) ≠ 0 by decide) c) =
      transvection (show (2 : Fin 3) ≠ 1 by decide) c := by
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [coe_blockSL, Phan.blockMat, Phan.blockSel, Matrix.mul_apply, Fin.sum_univ_two,
      transvection_coe, Matrix.single_apply]

theorem B12_eq_closure [Finite K] (hK : Nat.card K = 3) :
    WeakCT.B12 K = Subgroup.closure {sl3Gen K 0, sl3Gen K 1} := by
  rw [WeakCT.B12, MonoidHom.range_eq_map, ← sl2_closure hK, MonoidHom.map_closure, Set.image_pair,
    blockSL_t01_zero, blockSL_t10_zero]
  rfl

theorem B23_eq_closure [Finite K] (hK : Nat.card K = 3) :
    WeakCT.B23 K = Subgroup.closure {sl3Gen K 2, sl3Gen K 3} := by
  rw [WeakCT.B23, MonoidHom.range_eq_map, ← sl2_closure hK, MonoidHom.map_closure, Set.image_pair,
    blockSL_t01_one, blockSL_t10_one]
  rfl

theorem card_sl3 (hK : Nat.card K = 3) : Nat.card SL(3, K) = 5616 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  rw [RouteD.Gaps.card_SL_three, hK]
  norm_num

theorem sl3_lift_of_card (hK : Nat.card K = 3)
    (h : Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616) {X : Type} [Group X]
    (x : Fin 4 → X) (hx : ∀ r ∈ sl3Rels, wordVal x r = 1) :
    ∃ θ : SL(3, K) →* X, ∀ i, θ (sl3Gen K i) = x i := by
  obtain ⟨hfin, hle⟩ := h
  let p : PG 4 sl3Rels →* SL(3, K) := PresentedGroup.toGroup (f := sl3Gen K) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact wordVal_sl3Gen_rels hK w hw)
  have hp : ∀ i, p (PresentedGroup.of i) = sl3Gen K i := fun i => PresentedGroup.toGroup.of _
  have hsurj : Function.Surjective p := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← sl3Gen_closure hK, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨PresentedGroup.of i, hp i⟩
  have hbij : Function.Bijective p := by
    have := hfin
    refine hsurj.bijective_of_nat_card_le ?_
    rw [card_sl3 hK]
    exact hle
  let e : PG 4 sl3Rels ≃* SL(3, K) := MulEquiv.ofBijective p hbij
  let q : PG 4 sl3Rels →* X := PresentedGroup.toGroup (f := x) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact hx w hw)
  refine ⟨q.comp e.symm.toMonoidHom, fun i => ?_⟩
  have : e.symm (sl3Gen K i) = PresentedGroup.of i := by
    rw [← hp i]
    exact e.symm_apply_apply (PresentedGroup.of i)
  show q (e.symm (sl3Gen K i)) = x i
  rw [this]
  exact PresentedGroup.toGroup.of _

theorem sl3_lift (hK : Nat.card K = 3) (h : sl3OrderCheck = true) {X : Type} [Group X]
    (x : Fin 4 → X) (hx : ∀ r ∈ sl3Rels, wordVal x r = 1) :
    ∃ θ : SL(3, K) →* X, ∀ i, θ (sl3Gen K i) = x i :=
  sl3_lift_of_card hK (card_le_of_subsetCheckCC_nil sl3Rels h) x hx

theorem sl3_ker_le_center {X : Type} [Group X] (θ : SL(3, K) →* X) (m : Fin 4)
    (h1 : θ (sl3Gen K m) ≠ 1) : θ.ker ≤ Subgroup.center SL(3, K) := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
    (RankThree.Classical2.isQuasisimple_specialLinearGroup (K := K) (n := 3) le_rfl) θ.ker with
    h | h
  · exact h
  · exact absurd (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top (sl3Gen K m))) h1

theorem sl3Gen_zmod_not_comm : ∀ m : Fin 4,
    sl3Gen (ZMod 3) m * sl3Gen (ZMod 3) (![1, 0, 3, 2] m) ≠
      sl3Gen (ZMod 3) (![1, 0, 3, 2] m) * sl3Gen (ZMod 3) m := by
  decide +kernel

theorem sl3Gen_not_central (hK : Nat.card K = 3) (m : Fin 4) :
    sl3Gen K m ∉ Subgroup.center SL(3, K) := by
  intro hc
  have h := Subgroup.mem_center_iff.mp hc (sl3Gen K (![1, 0, 3, 2] m))
  apply sl3Gen_zmod_not_comm m
  have hinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) (zmodToK hK)) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact Matrix.map_injective (zmodToK_bijective hK).1 this
  apply hinj
  rw [map_mul, map_mul, ← sl3Gen_eq_map hK, ← sl3Gen_eq_map hK]
  exact h.symm

theorem sl3_hom_eq_one_of_gen (hK : Nat.card K = 3) {X : Type} [Group X] (θ : SL(3, K) →* X)
    (m : Fin 4) (h : θ (sl3Gen K m) = 1) : θ = 1 := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple
    (RankThree.Classical2.isQuasisimple_specialLinearGroup (K := K) (n := 3) le_rfl) θ.ker with
    h1 | h1
  · exact absurd (h1 (MonoidHom.mem_ker.mpr h)) (sl3Gen_not_central hK m)
  · exact MonoidHom.ext fun x => MonoidHom.mem_ker.mp (h1 ▸ Subgroup.mem_top x)

theorem linearBlockStandardPair_of_hom [Finite K] (hK : Nat.card K = 3) {X : Type} [Group X]
    (θ : SL(3, K) →* X) (hker : θ.ker ≤ Subgroup.center SL(3, K)) {U V : Subgroup X}
    (hU : Subgroup.closure {θ (sl3Gen K 0), θ (sl3Gen K 1)} = U)
    (hV : Subgroup.closure {θ (sl3Gen K 2), θ (sl3Gen K 3)} = V) :
    WeakCT.LinearBlockStandardPair K θ.range U V := by
  have h1 : ∀ H : Subgroup SL(3, K), H.map (MulAut.conj (1 : SL(3, K))⁻¹).toMonoidHom = H := by
    intro H
    ext x
    simp
  refine ⟨θ, 1, rfl, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [h1, B12_eq_closure hK, MonoidHom.map_closure, Set.image_pair]
    exact hU
  · rw [h1, B23_eq_closure hK, MonoidHom.map_closure, Set.image_pair]
    exact hV

end CFSG.ClassicalInvolution.Phan.Q3G
