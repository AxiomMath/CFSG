module

public import CFSG.RankThree.Chevalley.SteinbergBIE6FiniteLayers
public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionLie
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerActionN1Common
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeS
public import CFSG.LargeExtraspecial.S63CD4Iso
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylow

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.E6
open scoped Matrix MatrixGroups

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.Exceptional


variable {K : Type} [Field K]

theorem weylElt_one_eq_layer {ψ : SL(3, K) →* ModGL Tag.E6 K} {J : Set (Fin Tag.E6.rank)}
    {i j : Fin Tag.E6.rank} (h : IsA2Layer ψ J i j) :
    weylElt Tag.E6 K i 1 = ψ (Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1) := by
  rw [Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, h.x_i, h.y_i]
  simp

theorem weylElt_one_eq_layer' {ψ : SL(3, K) →* ModGL Tag.E6 K} {J : Set (Fin Tag.E6.rank)}
    {i j : Fin Tag.E6.rank} (h : IsA2Layer ψ J i j) :
    weylElt Tag.E6 K j 1 = ψ (Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 *
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-1) *
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1) := by
  rw [Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, h.x_j, h.y_j]
  simp

@[expose] def wA : SL(3, K) :=
  Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1 *
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) *
      Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) 1

@[expose] def wB : SL(3, K) :=
  Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1 *
      Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-1) *
      Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) 1

theorem coe_wA : ((wA : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = !![0, 1, 0; -1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wA, Matrix.SpecialLinearGroup.coe_mul, coe_transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem coe_wB : ((wB : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = !![1, 0, 0; 0, 0, 1; 0, -1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wB, Matrix.SpecialLinearGroup.coe_mul, coe_transvection, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

theorem wA_wB_pow_three : ((wA : SL(3, K)) * wB) ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.SpecialLinearGroup.coe_mul, coe_wA, coe_wB, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply]

theorem wB_wA_pow_three : ((wB : SL(3, K)) * wA) ^ 3 = 1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_pow]
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.SpecialLinearGroup.coe_mul, coe_wA, coe_wB, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply]

theorem a2Inv_comm (X Y : SL(3, K)) : a2Inv₁ K X * a2Inv₂ K Y = a2Inv₂ K Y * a2Inv₁ K X := by
  have h1 : twoA2Mul K (X, 1) = a2Inv₁ K X := by rw [twoA2Mul_eq, map_one, mul_one]
  have h2 : twoA2Mul K (1, Y) = a2Inv₂ K Y := by rw [twoA2Mul_eq, map_one, one_mul]
  have h3 : twoA2Mul K (X, 1) * twoA2Mul K (1, Y) = twoA2Mul K (1, Y) * twoA2Mul K (X, 1) := by
    rw [← map_mul, ← map_mul]
    simp
  rw [h1, h2] at h3
  exact h3

theorem orbitWord_E6_zero :
    TwistTag.E6.orbitWord ⟨0, by decide⟩ = [⟨0, by decide⟩, ⟨5, by decide⟩] := by rfl
theorem orbitWord_E6_one :
    TwistTag.E6.orbitWord ⟨1, by decide⟩ = [⟨2, by decide⟩, ⟨4, by decide⟩] := by rfl

theorem layers_cube :
    ((a2Inv₁ K wA * a2Inv₂ K wB) * (a2Inv₁ K wB * a2Inv₂ K wA)) ^ 3 = (1 : ModGL Tag.E6 K) := by
  have e : (a2Inv₁ K wA * a2Inv₂ K wB) * (a2Inv₁ K wB * a2Inv₂ K wA) =
      a2Inv₁ K (wA * wB) * a2Inv₂ K (wB * wA) := by
    rw [map_mul, map_mul]
    calc a2Inv₁ K wA * a2Inv₂ K wB * (a2Inv₁ K wB * a2Inv₂ K wA)
        = a2Inv₁ K wA * (a2Inv₂ K wB * a2Inv₁ K wB) * a2Inv₂ K wA := by simp only [mul_assoc]
      _ = a2Inv₁ K wA * (a2Inv₁ K wB * a2Inv₂ K wB) * a2Inv₂ K wA := by
          rw [a2Inv_comm wB wB]
      _ = a2Inv₁ K wA * a2Inv₁ K wB * (a2Inv₂ K wB * a2Inv₂ K wA) := by simp only [mul_assoc]
  rw [e, Commute.mul_pow (a2Inv_comm _ _), ← map_pow, ← map_pow, wA_wB_pow_three, wB_wA_pow_three,
    map_one, map_one, mul_one]

theorem orbitN_E6_prod_cubed (σ : K →+* K) :
    (((orbitN TwistTag.E6 K σ ⟨0, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K) *
      ((orbitN TwistTag.E6 K σ ⟨1, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
        ModGL TwistTag.E6.tag K)) ^ 3 = 1 := by
  rw [coe_orbitN_one, coe_orbitN_one, orbitWord_E6_zero, orbitWord_E6_one]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have n0 : weylElt TwistTag.E6.tag K ⟨0, by decide⟩ 1 = a2Inv₁ K wA :=
    weylElt_one_eq_layer isA2Layer_a2Inv₁
  have n2 : weylElt TwistTag.E6.tag K ⟨2, by decide⟩ 1 = a2Inv₁ K wB :=
    weylElt_one_eq_layer' isA2Layer_a2Inv₁
  have n4 : weylElt TwistTag.E6.tag K ⟨4, by decide⟩ 1 = a2Inv₂ K wA :=
    weylElt_one_eq_layer isA2Layer_a2Inv₂
  have n5 : weylElt TwistTag.E6.tag K ⟨5, by decide⟩ 1 = a2Inv₂ K wB :=
    weylElt_one_eq_layer' isA2Layer_a2Inv₂
  rw [n0, n2, n4, n5]
  exact layers_cube


theorem isPGroup_closure_of_conj_commute {G : Type*} [Group G] {x y : G} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (h01 : Commute x (y * x * y⁻¹)) (h02 : Commute x (y ^ 2 * x * (y ^ 2)⁻¹))
    (h12 : Commute (y * x * y⁻¹) (y ^ 2 * x * (y ^ 2)⁻¹)) :
    IsPGroup 3 (Subgroup.closure {x, y}) := by
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : G, x₁ = y * x * y⁻¹ := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : G, x₂ = y ^ 2 * x * (y ^ 2)⁻¹ := ⟨_, rfl⟩
  rw [← hx₁] at h01 h12
  rw [← hx₂] at h02 h12
  have hx₁3 : x₁ ^ 3 = 1 := by rw [hx₁, conj_pow, hx, mul_one, mul_inv_cancel]
  have hx₂3 : x₂ ^ 3 = 1 := by rw [hx₂, conj_pow, hx, mul_one, mul_inv_cancel]
  have hzp : ∀ g : G, g ^ 3 = 1 → IsPGroup 3 (Subgroup.zpowers g) := fun g hg =>
    IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one hg)
  have hcz : ∀ a b : G, Commute a b →
      Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    intro a b hab
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer (Subgroup.zpowers b : Set G) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hab.symm.zpow_left m).eq
  set N : Subgroup G := Subgroup.closure {x, x₁, x₂} with hN
  have hNle : N ≤ (Subgroup.zpowers x ⊔ Subgroup.zpowers x₁) ⊔ Subgroup.zpowers x₂ := by
    rw [hN, Subgroup.closure_le]
    rintro g (rfl | rfl | rfl)
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hN01 : IsPGroup 3 (Subgroup.zpowers x ⊔ Subgroup.zpowers x₁ : Subgroup G) :=
    (hzp x hx).to_sup_of_normal_right' (hzp x₁ hx₁3) (hcz x x₁ h01)
  have hNp : IsPGroup 3 N := by
    refine IsPGroup.to_le (K := (Subgroup.zpowers x ⊔ Subgroup.zpowers x₁) ⊔ Subgroup.zpowers x₂)
      ?_ hNle
    exact hN01.to_sup_of_normal_right' (hzp x₂ hx₂3)
      (sup_le (hcz x x₂ h02) (hcz x₁ x₂ h12))
  have hxN : x ∈ N := Subgroup.subset_closure (by simp)
  have hx₁N : x₁ ∈ N := Subgroup.subset_closure (by simp)
  have hx₂N : x₂ ∈ N := Subgroup.subset_closure (by simp)
  have hconj : ∀ h ∈ N, y * h * y⁻¹ ∈ N := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem g hg =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with hg | hg | hg
      · rw [hg, ← hx₁]; exact hx₁N
      · have : y * g * y⁻¹ = x₂ := by rw [hg, hx₁, hx₂, pow_two]; group
        rw [this]; exact hx₂N
      · have : y * g * y⁻¹ = x := by
          have e : y * g * y⁻¹ = y ^ 3 * x * (y ^ 3)⁻¹ := by rw [hg, hx₂, pow_two, pow_succ, pow_two]; group
          rw [e, hy]; simp
        rw [this]; exact hxN
    | one => simp
    | mul a b _ _ ha hb =>
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]; exact N.mul_mem ha hb
    | inv a _ ha =>
      have : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [this]; exact N.inv_mem ha
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set G) := by
    refine (Subgroup.zpowers_le).2 ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hconj h, fun hh => ?_⟩
    have h3 := hconj _ (hconj _ hh)
    have : y * (y * (y * h * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * h * (y * y * y)⁻¹ := by group
    rwa [this, ← pow_three', hy, inv_one, one_mul, mul_one] at h3
  refine IsPGroup.to_le (IsPGroup.to_sup_of_normal_right' (hzp y hy) hNp hnorm) ?_
  rw [Subgroup.closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.mem_sup_right hxN
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)


section Main

variable (σ : K →+* K)

open scoped commutatorElement

theorem exists_noncomm_threeGroup_E6 :
    ∃ x y : graphFixedRootGroup TwistTag.E6 K σ,
      IsPGroup 3 (Subgroup.closure {x, y}) ∧ x * y ≠ y * x := by
  classical
  obtain ⟨R, -, -, -, -, -, hRrange, hRC, hRker, -⟩ :=
    exceptional_fixed_rank_one_central_image TwistTag.E6 K σ ⟨2, by decide⟩
  have hle : RingHom.eqLocusField σ (RingHom.id K) ≤
      orbitField TwistTag.E6 K σ ⟨2, by decide⟩ := fun c hc => by
    rw [mem_orbitField]
    exact (pow_one σ).symm ▸ hc
  obtain ⟨incl, hincl⟩ : ∃ incl : SL2 (RingHom.eqLocusField σ (RingHom.id K)) →*
      SL2 (orbitField TwistTag.E6 K σ ⟨2, by decide⟩),
      ∀ X, ((incl X : SL2 (orbitField TwistTag.E6 K σ ⟨2, by decide⟩)) :
        Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ ⟨2, by decide⟩)) =
          ((X : Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField σ (RingHom.id K)))).map
            (Subfield.inclusion hle) :=
    ⟨Matrix.SpecialLinearGroup.map (Subfield.inclusion hle), fun X => rfl⟩
  have hj : ∀ k, (TwistTag.E6.perm ^ k) (TwistTag.E6.orbitMin ⟨2, by decide⟩) =
      ⟨3, by decide⟩ := fun k => by
    have h := TwistTag.E6.perm_pow_mem_orbit (TwistTag.E6.orbitMin_mem ⟨2, by decide⟩) k
    have h3 : TwistTag.E6.orbit ⟨2, by decide⟩ = {⟨3, by decide⟩} := by decide
    rwa [h3, Finset.mem_singleton] at h
  have hRQ : R.range ≤ rootSubgroup TwistTag.E6.tag K (Pi.single ⟨3, by decide⟩ 1) ⊔
      rootSubgroup TwistTag.E6.tag K (-Pi.single ⟨3, by decide⟩ 1) := by
    rw [hRrange, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitX]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_single]
      exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨_, rfl⟩)
    · rw [SetLike.mem_coe]
      dsimp only
      rw [coe_orbitY]
      refine Subgroup.list_prod_mem _ fun x hx => ?_
      obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
      rw [hj k, ← pinnedX_neg_single]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨_, rfl⟩)
  have hNC : ∀ a, (orbitN TwistTag.E6 K σ a 1 : ModGL TwistTag.E6.tag K) ∈
      graphFixedRootGroup TwistTag.E6 K σ := fun a => by
    rw [orbitN, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
      (orbitX_mem_graphFixedPosUnipotent _ σ a _)) (graphFixedNegUnipotent_le_graphFixedRootGroup
        _ K σ (orbitY_mem_graphFixedNegUnipotent _ σ a _)))
      (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
        (orbitX_mem_graphFixedPosUnipotent _ σ a _))
  set N₀ : ModGL TwistTag.E6.tag K :=
    ((orbitN TwistTag.E6 K σ ⟨0, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
      ModGL TwistTag.E6.tag K) with hN₀
  set N₁ : ModGL TwistTag.E6.tag K :=
    ((orbitN TwistTag.E6 K σ ⟨1, by decide⟩ 1 : adjointGroup TwistTag.E6.tag K) :
      ModGL TwistTag.E6.tag K) with hN₁
  have hy3 : (N₀ * N₁) ^ 3 = 1 := orbitN_E6_prod_cubed σ
  have hyC : N₀ * N₁ ∈ graphFixedRootGroup TwistTag.E6 K σ := mul_mem (hNC _) (hNC _)
  obtain ⟨hroot, hcheck⟩ := e6_four_roots_check
  have he3 : (Pi.single ⟨3, by decide⟩ 1 : Fin TwistTag.E6.tag.rank → ℤ) =
      e6Vec ![0, 0, 0, 1, 0, 0] := by decide +kernel
  obtain ⟨-, hf1, -⟩ := e6_fold_roots
  have hf2 : [⟨1, by decide⟩, ⟨0, by decide⟩].foldl
      (fun v a => TwistTag.E6.orbitReflection a • v) (e6Vec ![1, 0, 1, 1, 1, 1]) =
      e6Vec ![0, 0, 1, 1, 1, 0] := by
    simp only [TwistTag.orbitReflection, wordProd_smul]
    decide +kernel
  have hconjL : ∀ {β : Fin TwistTag.E6.tag.rank → ℤ}, IsRoot TwistTag.E6.tag β →
      ∀ g ∈ rootSubgroup TwistTag.E6.tag K β ⊔ rootSubgroup TwistTag.E6.tag K (-β),
      N₀ * N₁ * g * (N₀ * N₁)⁻¹ ∈
        rootSubgroup TwistTag.E6.tag K ([⟨1, by decide⟩, ⟨0, by decide⟩].foldl
          (fun v a => TwistTag.E6.orbitReflection a • v) β) ⊔
        rootSubgroup TwistTag.E6.tag K (-([⟨1, by decide⟩, ⟨0, by decide⟩].foldl
          (fun v a => TwistTag.E6.orbitReflection a • v) β)) := by
    intro β hβ g hg
    rw [← map_conj_orbitN_list_rootPair TwistTag.E6 σ [⟨1, by decide⟩, ⟨0, by decide⟩] hβ]
    refine ⟨g, hg, ?_⟩
    simp [MulAut.conj_apply, hN₀, hN₁, mul_assoc]
    rfl
  set M : SL2 (RingHom.eqLocusField σ (RingHom.id K)) := orderThreeSL _ with hM
  set x₀ : ModGL TwistTag.E6.tag K := R (incl M) with hx₀
  have hx₀L : x₀ ∈ rootSubgroup TwistTag.E6.tag K (e6Vec ![0, 0, 0, 1, 0, 0]) ⊔
      rootSubgroup TwistTag.E6.tag K (-(e6Vec ![0, 0, 0, 1, 0, 0])) := by
    rw [← he3]
    exact hRQ ⟨_, rfl⟩
  have hRC' : R.range ≤ graphFixedRootGroup TwistTag.E6 K σ := hRrange ▸ hRC
  have hx₀C : x₀ ∈ graphFixedRootGroup TwistTag.E6 K σ := hRC' ⟨_, rfl⟩
  have hcomm : ∀ i j : Fin 4, i ≠ j → ∀ {x y : ModGL TwistTag.E6.tag K},
      x ∈ rootSubgroup TwistTag.E6.tag K ((![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i) ⊔
        rootSubgroup TwistTag.E6.tag K (-((![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) i)) →
      y ∈ rootSubgroup TwistTag.E6.tag K ((![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) j) ⊔
        rootSubgroup TwistTag.E6.tag K (-((![e6Vec ![0, 0, 0, 1, 0, 0], e6Vec ![0, 0, 1, 1, 1, 0],
        e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] : Fin 4 → _) j)) →
      x * y = y * x := by
    intro i j hij x y hx hy
    obtain ⟨h0, hp, hm⟩ := hcheck i j hij
    exact commute_of_mem_rootPair_of_check (hroot i) (hroot j) h0 hp hm hx hy
  have hrt : ∀ i : Fin 4, IsRoot TwistTag.E6.tag ((![e6Vec ![0, 0, 0, 1, 0, 0],
      e6Vec ![0, 0, 1, 1, 1, 0], e6Vec ![1, 0, 1, 1, 1, 1], e6Vec ![1, 2, 2, 3, 2, 1]] :
        Fin 4 → _) i) := fun i => RootOps.isRootB_iff.1 (hroot i)
  have hx₁L : N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹ ∈ rootSubgroup TwistTag.E6.tag K
      (e6Vec ![1, 0, 1, 1, 1, 1]) ⊔ rootSubgroup TwistTag.E6.tag K (-(e6Vec ![1, 0, 1, 1, 1, 1])) := by
    have h := hconjL (β := e6Vec ![0, 0, 0, 1, 0, 0]) (hrt 0) x₀ hx₀L
    rw [hf1] at h
    exact h
  have hx₂L : N₀ * N₁ * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * (N₀ * N₁)⁻¹ ∈
      rootSubgroup TwistTag.E6.tag K (e6Vec ![0, 0, 1, 1, 1, 0]) ⊔
        rootSubgroup TwistTag.E6.tag K (-(e6Vec ![0, 0, 1, 1, 1, 0])) := by
    have h := hconjL (β := e6Vec ![1, 0, 1, 1, 1, 1]) (hrt 2) _ hx₁L
    rw [hf2] at h
    exact h
  have c01 : x₀ * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) = (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * x₀ :=
    hcomm 0 2 (by decide) hx₀L hx₁L
  have c02 : x₀ * (N₀ * N₁ * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * (N₀ * N₁)⁻¹) =
      (N₀ * N₁ * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * (N₀ * N₁)⁻¹) * x₀ :=
    hcomm 0 1 (by decide) hx₀L hx₂L
  have c12 : (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * (N₀ * N₁ * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * (N₀ * N₁)⁻¹) =
      (N₀ * N₁ * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) * (N₀ * N₁)⁻¹) * (N₀ * N₁ * x₀ * (N₀ * N₁)⁻¹) :=
    hcomm 2 1 (by decide) hx₁L hx₂L
  have hx3 : x₀ ^ 3 = 1 := by
    rw [hx₀, ← map_pow, ← map_pow, hM, orderThreeSL_pow_three, map_one, map_one]
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ModGL TwistTag.E6.tag K, y₀ = N₀ * N₁ := ⟨_, rfl⟩
  rw [← hy₀] at hy3 hyC hx₁L hx₂L c01 c02 c12
  clear_value N₀ N₁ x₀
  have hsq : y₀ ^ 2 * x₀ * (y₀ ^ 2)⁻¹ = y₀ * (y₀ * x₀ * y₀⁻¹) * y₀⁻¹ := by
    rw [pow_two]; group
  refine ⟨⟨x₀, hx₀C⟩, ⟨y₀, hyC⟩, ?_, ?_⟩
  · refine isPGroup_closure_of_conj_commute (Subtype.ext ?_) (Subtype.ext ?_) ?_ ?_ ?_
    · simpa using hx3
    · simpa using hy3
    · exact Subtype.ext c01
    · exact Subtype.ext (by
        show x₀ * (y₀ ^ 2 * x₀ * (y₀ ^ 2)⁻¹) = (y₀ ^ 2 * x₀ * (y₀ ^ 2)⁻¹) * x₀
        rw [hsq]; exact c02)
    · exact Subtype.ext (by
        show (y₀ * x₀ * y₀⁻¹) * (y₀ ^ 2 * x₀ * (y₀ ^ 2)⁻¹) =
          (y₀ ^ 2 * x₀ * (y₀ ^ 2)⁻¹) * (y₀ * x₀ * y₀⁻¹)
        rw [hsq]; exact c12)
  · intro hxy
    have h1 : x₀ * y₀ = y₀ * x₀ := congrArg Subtype.val hxy
    have hx₁eq : y₀ * x₀ * y₀⁻¹ = x₀ := by rw [← h1]; group
    have hx₀L2 : x₀ ∈ rootSubgroup TwistTag.E6.tag K (e6Vec ![1, 0, 1, 1, 1, 1]) ⊔
        rootSubgroup TwistTag.E6.tag K (-(e6Vec ![1, 0, 1, 1, 1, 1])) := hx₁eq ▸ hx₁L
    set E : SL2 (RingHom.eqLocusField σ (RingHom.id K)) :=
      ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ with hE
    have hEL : R (incl E) ∈ rootSubgroup TwistTag.E6.tag K (e6Vec ![0, 0, 0, 1, 0, 0]) ⊔
        rootSubgroup TwistTag.E6.tag K (-(e6Vec ![0, 0, 0, 1, 0, 0])) := by
      rw [← he3]
      exact hRQ ⟨_, rfl⟩
    have hcE : R (incl E) * x₀ = x₀ * R (incl E) := hcomm 0 2 (by decide) hEL hx₀L2
    have hEM : R (incl (E * M)) = R (incl (M * E)) := by
      rw [map_mul, map_mul, map_mul, map_mul, ← hx₀]
      exact hcE
    have hker : (incl (E * M))⁻¹ * incl (M * E) ∈ R.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hEM, inv_mul_cancel]
    obtain ⟨l, hl2, hl⟩ := hRker _ hker
    have hB : (((incl (M * E) : SL2 (orbitField TwistTag.E6 K σ ⟨2, by decide⟩)) :
        Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ ⟨2, by decide⟩))) =
        (l : orbitField TwistTag.E6 K σ ⟨2, by decide⟩) •
          (((incl (E * M) : SL2 (orbitField TwistTag.E6 K σ ⟨2, by decide⟩)) :
            Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ ⟨2, by decide⟩))) := by
      have : incl (M * E) = incl (E * M) * ((incl (E * M))⁻¹ * incl (M * E)) := by group
      rw [this, Matrix.SpecialLinearGroup.coe_mul, hl, Matrix.mul_smul, Matrix.mul_one]
    have h00 := congrFun (congrFun hB 0) 0
    have hME0 : ((M * E : SL2 (RingHom.eqLocusField σ (RingHom.id K))) :
        Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) 0 0 = 0 := by
      change (!![0, -1; 1, -1] * !![1, 1; 0, 1] :
        Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) 0 0 = 0
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hEM0 : ((E * M : SL2 (RingHom.eqLocusField σ (RingHom.id K))) :
        Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) 0 0 = 1 := by
      change (!![1, 1; 0, 1] * !![0, -1; 1, -1] :
        Matrix (Fin 2) (Fin 2) (RingHom.eqLocusField σ (RingHom.id K))) 0 0 = 1
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hME : (((incl (M * E) : SL2 (orbitField TwistTag.E6 K σ ⟨2, by decide⟩)) :
        Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ ⟨2, by decide⟩))) 0 0 = 0 := by
      rw [hincl, Matrix.map_apply, hME0, map_zero]
    have hEMe : (((incl (E * M) : SL2 (orbitField TwistTag.E6 K σ ⟨2, by decide⟩)) :
        Matrix (Fin 2) (Fin 2) (orbitField TwistTag.E6 K σ ⟨2, by decide⟩))) 0 0 = 1 := by
      rw [hincl, Matrix.map_apply, hEM0, map_one]
    rw [hME, Matrix.smul_apply, hEMe, smul_eq_mul, mul_one] at h00
    rw [← h00] at hl2
    simp at hl2

end Main


open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction
  (N1E6 N1TwE6 not_isMulCommutative_of_noncomm_pSubgroup)
open CFSG.Blueprint (ChevalleyExceptionalModel UntwistedChevalleyModel TwistedChevalleyModel)

theorem n1TwE6_holds : N1TwE6 := by
  intro S _ _ ℓ f hmodel _ T hT hTi
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hmodel
  have hm' : TwistedChevalleyModel S TwistTag.E6 (ℓ ^ f) := hm
  obtain ⟨F, _, _, σ, -, -, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hp hf hm'
  obtain ⟨x, y, hxy, hne⟩ := exists_noncomm_threeGroup_E6 σ
  refine not_isMulCommutative_of_noncomm_pSubgroup (H := (Subgroup.closure {x, y}).map e.toMonoidHom)
    (hxy.map e.toMonoidHom) (a := e x) (b := e y) ?_ ?_ ?_ hT hTi
  · exact ⟨x, Subgroup.subset_closure (by simp), rfl⟩
  · exact ⟨y, Subgroup.subset_closure (by simp), rfl⟩
  · intro h
    exact hne (e.injective (by simpa using h))

theorem n1E6_holds : N1E6 := by
  intro S _ _ ℓ f hmodel _ T hT hTi
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hmodel
  have hm' : UntwistedChevalleyModel S Tag.E6 (ℓ ^ f) := hm
  obtain ⟨F, _, _, -, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hm'
  obtain ⟨x, y, hxy, hne⟩ := exists_noncomm_threeGroup_E6 (RingHom.id F)
  have hle : graphFixedRootGroup TwistTag.E6 F (RingHom.id F) ≤ adjointGroup Tag.E6 F :=
    (graphFixedRootGroup_le _ _ _).trans inf_le_left
  let φ : graphFixedRootGroup TwistTag.E6 F (RingHom.id F) →* S :=
    e.toMonoidHom.comp (Subgroup.inclusion hle)
  have hφ : Function.Injective φ := e.injective.comp (Subgroup.inclusion_injective hle)
  refine not_isMulCommutative_of_noncomm_pSubgroup (H := (Subgroup.closure {x, y}).map φ)
    (hxy.map φ) (a := φ x) (b := φ y) ?_ ?_ ?_ hT hTi
  · exact ⟨x, Subgroup.subset_closure (by simp), rfl⟩
  · exact ⟨y, Subgroup.subset_closure (by simp), rfl⟩
  · intro h
    exact hne (hφ (by simpa using h))


theorem not_isMulCommutative_sylow_of_perfect_center {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hperf : commutator R = ⊤) {z : R} (hz : z ∈ Subgroup.center R)
    (hzp : orderOf z = p) (P : Sylow p R) : ¬ IsMulCommutative (P : Subgroup R) := by
  intro hcomm
  classical
  let H : Subgroup R := P
  haveI : H.FiniteIndex := inferInstance
  let ϕ : H →* Abelianization H := Abelianization.of
  let T : R →* Abelianization H := MonoidHom.transfer ϕ
  have hT : T z = 1 := by
    have hz' : z ∈ commutator R := by rw [hperf]; trivial
    exact MonoidHom.mem_ker.1 (Abelianization.commutator_subset_ker T hz')
  have key : ∀ (k : ℕ) (g₀ : R), g₀⁻¹ * z ^ k * g₀ ∈ H → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center R := Subgroup.pow_mem _ hz k
    rw [Subgroup.mem_center_iff] at hc
    rw [hc g₀⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have h1 := MonoidHom.transfer_eq_pow ϕ z key
  have hinj : Function.Injective ϕ := by
    rw [← MonoidHom.ker_eq_bot_iff, Abelianization.ker_of]
    exact (commutator_eq_bot_iff H).2 hcomm
  have hpow : ((⟨z ^ H.index, MonoidHom.transfer_eq_pow_aux z key⟩ : H)) = 1 := by
    apply hinj
    rw [← h1, map_one]
    exact hT
  have hdvd : p ∣ H.index := by
    have h2 : z ^ H.index = 1 := congrArg Subtype.val hpow
    rw [← hzp]
    exact orderOf_dvd_of_pow_eq_one h2
  exact Sylow.not_dvd_index P hdvd

theorem exists_noncomm_pSubgroup_of_perfect_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (R : Subgroup G) (hperf : commutator R = ⊤) {z : R}
    (hz : z ∈ Subgroup.center R) (hzp : orderOf z = p) :
    ∃ H : Subgroup G, IsPGroup p H ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  obtain ⟨P⟩ : Nonempty (Sylow p R) := inferInstance
  have hnc := not_isMulCommutative_sylow_of_perfect_center hperf hz hzp P
  refine ⟨(P : Subgroup R).map R.subtype, P.isPGroup'.map _, ?_⟩
  by_contra hcon
  push Not at hcon
  exact hnc ⟨⟨fun a b => Subtype.ext (Subtype.ext (hcon _ ⟨a, a.2, rfl⟩ _ ⟨b, b.2, rfl⟩))⟩⟩


section D4

open CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.Lattice
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.ComponentInitial (finite_field_prime_power_characteristic)
open scoped Pointwise

theorem exists_perfect_center_three_D4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hℓ3 : ℓ ≠ 3)
    (hq2 : 2 < ℓ ^ f) (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {d : ℕ}
    (hd : (d : ℤ) = ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * (ℓ ^ f : ℕ) + 1) (h3d : 3 ∣ d)
    (hgcd : Int.gcd 3 (((ℓ ^ f : ℕ) : ℤ) - ε) = 3) :
    ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), commutator R = ⊤ ∧
      ∃ z ∈ Subgroup.center R, orderOf z = 3 := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  let Ω := AlgebraicClosure K
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  set Fr : Ω →+* Ω := iterateFrobenius Ω ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨-, ⟨g, hgG, hFg⟩, -, hrest⟩ :=
    triality_three_six_tori_Sylow_and_root_kernels hℓ hf K hK σ hσ Ω Fr hFr hε hd
  obtain ⟨hTin, -, -⟩ := hrest g hgG hFg
  have h3Ω : ((3 : ℕ) : Ω) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff Ω ℓ 3).1 h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this)
  haveI : NeZero ((3 : ℕ) : Ω) := ⟨h3Ω⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.prim (M := Ω) (n := 3)
  have hμ : Nat.card (rootsOfUnity 3 Ω) = 3 := hζ0.card_rootsOfUnity
  haveI : Finite (rootsOfUnity 3 Ω) := Nat.finite_of_card_ne_zero (by rw [hμ]; norm_num)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := rootsOfUnity 3 Ω) 3 (by rw [hμ])
  have hζ3 : (ζ : Ωˣ) ^ 3 = 1 := (mem_rootsOfUnity 3 (ζ : Ωˣ)).1 ζ.2
  have hζ1 : (ζ : Ωˣ) ≠ 1 := by
    intro h
    have : ζ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hζ
    omega
  have hζd : (ζ : Ωˣ) ^ (d : ℤ) = 1 := by
    rw [zpow_natCast]
    obtain ⟨m, hm⟩ := h3d
    rw [hm, pow_mul, hζ3, one_pow]
  set a : Fin TwistTag.D4.tag.rank → Ωˣ := threeSixTuple ((ℓ ^ f : ℕ) : ℤ) ε ((ζ : Ωˣ), 1) with ha_def
  have ha : rootDiagUnit TwistTag.D4.tag a ∈ threeSixTorus Ω Fr ε := by
    rw [rootDiagUnit_mem_threeSixTorus_iff' Fr hFr hε]
    refine ⟨rfl, ?_, ?_⟩
    · rw [← hd]; exact hζd
    · exact one_zpow _
  obtain ⟨x, hx⟩ : g * rootDiagUnit TwistTag.D4.tag a * g⁻¹ ∈ (threeSixEmb K Ω σ).range :=
    hTin ⟨rootDiagUnit TwistTag.D4.tag a, ha, rfl⟩
  have ha3 : a ^ 3 = 1 := by
    rw [ha_def, ← map_pow]
    have : (((ζ : Ωˣ), (1 : Ωˣ)) ^ 3 : Ωˣ × Ωˣ) = 1 := by
      rw [Prod.pow_def, hζ3, one_pow]; rfl
    rw [this, map_one]
  have ha1 : a ≠ 1 := fun h => hζ1 (by simpa [ha_def, threeSixTuple_values] using congrFun h 0)
  have hord : orderOf (rootDiagUnit TwistTag.D4.tag a) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · change (rootDiagUnitHom TwistTag.D4.tag Ω a) ^ 3 = 1
      rw [← map_pow, ha3, map_one]
    · intro h
      exact ha1 (rootDiagUnit_injective (by rw [h, rootDiagUnit_one]))
  have hfix := (rootDiagUnit_mem_threeSixTorus_iff Fr hFr hε a).1 ha
  have hne : (survivingRoots a).Nonempty :=
    ⟨Pi.single (⟨1, by decide⟩ : Fin TwistTag.D4.tag.rank) 1,
      isRoot_single _ _, by rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single]; rfl⟩
  obtain ⟨i, hi⟩ := survivingRoots_eq_sigma_of_nonempty hε hfix ha1 hne
  obtain ⟨v, hv⟩ : ∃ v : WeylGroup Tag.D4, (fun α => v • α) '' d4A2Sigma = survivingRoots a := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hcomp, -⟩ := triality_three_six_unimodular_A2_root_partition
    obtain ⟨-, -, -, -, -, w, -, -, hw⟩ := hcomp i
    exact ⟨w, by rw [hi, d4A2Sigma_eq_trialityStdA2, ← hw]⟩
  obtain ⟨-, -, hR, -, -, hq, hZ, -⟩ :=
    triality_three_six_singular_fixed_centralizers_gen hℓ hf K hK σ hσ Ω Fr hFr hε hd g hgG hFg
      (p := 3) Nat.prime_three (by norm_num) hℓ3 hq2 a ha hord v hv x hx
  refine ⟨threeSixSingularR Ω K σ Fr ε v g, Group.isPerfect_def.1 hq.1, ?_⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.center (threeSixSingularR Ω K σ Fr ε v g)) 3 (by rw [hZ, hgcd])
  exact ⟨(z : threeSixSingularR Ω K σ Fr ε v g), z.2, by rw [Subgroup.orderOf_coe]; exact hz⟩

theorem exists_noncomm_three_of_ne_three {ℓ f : ℕ} (hℓ3 : ℓ ≠ 3) (hq2 : 2 < ℓ ^ f) {S : Type}
    [Group S] [Finite S] (hmodel : ChevalleyExceptionalModel S .trialityD4 ℓ f) :
    ∃ H : Subgroup S, IsPGroup 3 H ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨⟨hp, hf, -⟩, hm⟩ := hmodel
  have hm' : TwistedChevalleyModel S TwistTag.D4 (ℓ ^ f) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hp hf hm'
  let σe : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hK3 : Nat.card K = (ℓ ^ f) ^ 3 := hK
  have hσe : ∀ c, σe c = c ^ (ℓ ^ f) := hσ
  have hq3 : (ℓ ^ f) % 3 ≠ 0 := by
    intro h
    have h3 : 3 ∣ ℓ ^ f := Nat.dvd_of_mod_eq_zero h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  obtain ⟨R, hR, z, hz, hzo⟩ : ∃ R : Subgroup (graphFixedRootGroup TwistTag.D4 K σe.toRingHom),
      commutator R = ⊤ ∧ ∃ z ∈ Subgroup.center R, orderOf z = 3 := by
    have hq12 : (ℓ ^ f) % 3 = 1 ∨ (ℓ ^ f) % 3 = 2 := by omega
    rcases hq12 with h | h
    · obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = 3 * k + 1 := ⟨ℓ ^ f / 3, by omega⟩
      refine exists_perfect_center_three_D4 hp hf hℓ3 hq2 K hK3 σe hσe (ε := 1) (Or.inl rfl)
        (d := 9 * k ^ 2 + 9 * k + 3) ?_ ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩ ?_
      · rw [hk]; push_cast; ring
      · have h3 : ((ℓ ^ f : ℕ) : ℤ) - 1 = 3 * (k : ℤ) := by rw [hk]; push_cast; ring
        rw [h3]
        simpa using Int.gcd_mul_left 3 1 (k : ℤ)
    · obtain ⟨k, hk⟩ : ∃ k, ℓ ^ f = 3 * k + 2 := ⟨ℓ ^ f / 3, by omega⟩
      refine exists_perfect_center_three_D4 hp hf hℓ3 hq2 K hK3 σe hσe (ε := -1) (Or.inr rfl)
        (d := 9 * k ^ 2 + 9 * k + 3) ?_ ⟨3 * k ^ 2 + 3 * k + 1, by ring⟩ ?_
      · rw [hk]; push_cast; ring
      · have h3 : ((ℓ ^ f : ℕ) : ℤ) - (-1) = 3 * ((k : ℤ) + 1) := by rw [hk]; push_cast; ring
        rw [h3]
        simpa using Int.gcd_mul_left 3 1 ((k : ℤ) + 1)
  obtain ⟨H, hH, a, ha, b, hb, hab⟩ := exists_noncomm_pSubgroup_of_perfect_center R hR hz hzo
  let e' : graphFixedRootGroup TwistTag.D4 K σe.toRingHom ≃* S := e
  refine ⟨H.map e'.toMonoidHom, hH.map _, e' a, ⟨a, ha, rfl⟩, e' b, ⟨b, hb, rfl⟩, ?_⟩
  intro h
  exact hab (e'.injective (by rw [map_mul, map_mul]; exact h))


theorem d4_orbitReflection_zero_single_two :
    TwistTag.D4.orbitReflection ⟨0, by decide⟩ • (Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 :
      Fin TwistTag.D4.tag.rank → ℤ) = threeSixVec 1 1 1 1 := by
  simp only [TwistTag.orbitReflection, wordProd_smul]
  decide +kernel

theorem pi_single_two_eq : (Pi.single (⟨2, by decide⟩ : Fin TwistTag.D4.tag.rank) 1 :
    Fin TwistTag.D4.tag.rank → ℤ) = threeSixVec 0 0 1 0 := by
  funext i
  fin_cases i <;> rfl

theorem exists_noncomm_pSubgroup_char_three {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    ∃ H : Subgroup (graphFixedRootGroup TwistTag.D4 K σ), IsPGroup 3 H ∧
      ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]; exact pow_ne_zero _ (pow_ne_zero _ (by norm_num)))
  have hcard := (triality_both_orientations_exact_finite_order 3 f Nat.prime_three hf K hK 1
    (Or.inl rfl) σ (by simpa using hσ)).2.2
  have hU : IsPGroup 3 (graphFixedPosUnipotent TwistTag.D4 K σ) :=
    IsPGroup.of_card (n := 12 * f) (by rw [hcard, ← pow_mul]; ring_nf)
  have hj : ∀ k, (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin ⟨1, by decide⟩) =
      ⟨2, by decide⟩ := fun k => by
    have h := TwistTag.D4.perm_pow_mem_orbit (TwistTag.D4.orbitMin_mem ⟨1, by decide⟩) k
    have h3 : TwistTag.D4.orbit ⟨1, by decide⟩ = {⟨2, by decide⟩} := by decide
    rwa [h3, Finset.mem_singleton] at h
  have hcardO : (TwistTag.D4.orbit ⟨1, by decide⟩).card = 1 := by decide
  have hx₀eq : ((orbitX TwistTag.D4 K σ ⟨1, by decide⟩ 1 : adjointGroup TwistTag.D4.tag K) :
      ModGL TwistTag.D4.tag K) = pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 := by
    rw [coe_orbitX, ← pi_single_two_eq, pinnedX_single]
    simp [hcardO, hj]
  have hx₀U : pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 ∈
      graphFixedPosUnipotent TwistTag.D4 K σ :=
    hx₀eq ▸ orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ _ _
  have hx₀C : pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 ∈
      graphFixedRootGroup TwistTag.D4 K σ :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ hx₀U
  have hNC : ((orbitN TwistTag.D4 K σ ⟨0, by decide⟩ 1 : adjointGroup TwistTag.D4.tag K) :
      ModGL TwistTag.D4.tag K) ∈ graphFixedRootGroup TwistTag.D4 K σ :=
    orbitN_mem_graphFixedRootGroup _ σ _ _
  have hNw := canonicalRep_orbitReflection_eq_orbitN TwistTag.D4 σ (K := K) ⟨0, by decide⟩
  have hα : IsRoot TwistTag.D4.tag (threeSixVec 0 0 1 0) := RootOps.isRootB_iff.1 (by decide +kernel)
  have hβ : IsRoot TwistTag.D4.tag (threeSixVec 1 1 1 1) := RootOps.isRootB_iff.1 (by decide +kernel)
  have hθ : IsRoot TwistTag.D4.tag (threeSixVec 0 0 1 0 + threeSixVec 1 1 1 1) :=
    RootOps.isRootB_iff.1 (by decide +kernel)
  have hne : threeSixVec 0 0 1 0 ≠ threeSixVec 1 1 1 1 := by decide +kernel
  have hne' : threeSixVec 0 0 1 0 ≠ -threeSixVec 1 1 1 1 := by decide +kernel
  have hheight : 0 < height (threeSixVec 1 1 1 1) := by decide +kernel
  have hw : TwistTag.D4.orbitReflection ⟨0, by decide⟩ • threeSixVec 0 0 1 0 =
      threeSixVec 1 1 1 1 := by
    rw [← pi_single_two_eq]
    exact d4_orbitReflection_zero_single_two
  set N : ModGL TwistTag.D4.tag K := ((orbitN TwistTag.D4 K σ ⟨0, by decide⟩ 1 :
    adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) with hN
  have hNmap := (canonical_weyl_root_transport TwistTag.D4.tag K).2.1
    (TwistTag.D4.orbitReflection ⟨0, by decide⟩) (threeSixVec 0 0 1 0) hα
  have hyβ : N * pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 * N⁻¹ ∈
      rootSubgroup TwistTag.D4.tag K (threeSixVec 1 1 1 1) := by
    rw [← hw, ← hNmap]
    refine ⟨pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1,
      mem_rootSubgroup.2 ⟨1, rfl⟩, ?_⟩
    rw [hNw]
    rfl
  obtain ⟨c, hc⟩ := mem_rootSubgroup.1 hyβ
  obtain ⟨hε, hform⟩ := (simply_laced_root_commutator_unit TwistTag.D4.tag (Or.inl rfl) hα hβ hne
    hne').1 hθ
  have key := hform K 1 c
  have hyU : N * pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 * N⁻¹ ∈
      graphFixedPosUnipotent TwistTag.D4 K σ := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hle : rootSubgroup TwistTag.D4.tag K (threeSixVec 1 1 1 1) ≤
          posUnipotent TwistTag.D4.tag K :=
        le_biSup (rootSubgroup TwistTag.D4.tag K)
          (show threeSixVec 1 1 1 1 ∈ {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α} from
            ⟨hβ, hheight⟩)
      exact hle hyβ
    · exact graphFixedRootGroup_le _ K σ (mul_mem (mul_mem hNC hx₀C) (inv_mem hNC))
  let φ : ↥(graphFixedPosUnipotent TwistTag.D4 K σ) →* ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
    Subgroup.inclusion (graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ)
  refine ⟨φ.range, hU.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective,
    φ ⟨_, hx₀U⟩, ⟨_, rfl⟩, φ ⟨_, hyU⟩, ⟨_, rfl⟩, ?_⟩
  intro h
  have h' : pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 * (N * pinnedX TwistTag.D4.tag K
      (threeSixVec 0 0 1 0) 1 * N⁻¹) = (N * pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 *
        N⁻¹) * pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 :=
    congrArg (fun z : ↥(graphFixedRootGroup TwistTag.D4 K σ) => (z : ModGL TwistTag.D4.tag K)) h
  rw [← hc] at h'
  have h1 := commutatorElement_eq_one_iff_mul_comm.2 h'
  rw [key] at h1
  have h2 : pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0 + threeSixVec 1 1 1 1)
      ((commConst TwistTag.D4.tag (threeSixVec 0 0 1 0) (threeSixVec 1 1 1 1) (1, 1) : K) * 1 * c) =
      pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0 + threeSixVec 1 1 1 1) 0 := by
    rw [h1, pinnedX_zero]
  have h3 := pinnedX_injective _ _ _ h2
  have hc0 : c = 0 := by
    rcases hε with hε | hε <;> rw [hε] at h3 <;> simpa using h3
  rw [hc0, pinnedX_zero] at hc
  have h4 : pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 = 1 := by
    have : N * pinnedX TwistTag.D4.tag K (threeSixVec 0 0 1 0) 1 * N⁻¹ = 1 := hc.symm
    simpa using this
  rw [← pinnedX_zero (R := K) (α := threeSixVec 0 0 1 0)] at h4
  exact one_ne_zero (pinnedX_injective _ _ _ h4)




theorem exists_noncomm_three_of_char_three {f : ℕ} (hf : 1 ≤ f) {S : Type} [Group S] [Finite S]
    (hmodel : ChevalleyExceptionalModel S .trialityD4 3 f) :
    ∃ H : Subgroup S, IsPGroup 3 H ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  obtain ⟨⟨hp, -, -⟩, hm⟩ := hmodel
  have hm' : TwistedChevalleyModel S TwistTag.D4 (3 ^ f) := hm
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_of_twisted_prime hp hf hm'
  obtain ⟨H, hH, a, ha, b, hb, hab⟩ := exists_noncomm_pSubgroup_char_three hf K hK σ hσ
  refine ⟨H.map e.toMonoidHom, hH.map _, e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, ?_⟩
  intro h
  exact hab (e.injective (by rw [map_mul, map_mul]; exact h))

end D4

section Two


open CFSG.Quasithin CFSG.Open CFSG.AGLEmbedding.D4Two

theorem commutes_genA_genB : commutes genA genB = false := by decide +kernel

theorem ofMat_toMat (A : Array GF8) (hA : A.size = 64) : ofMat (toMat A) = A := by
  apply Array.ext
  · simp [ofMat, hA]
  · intro i h1 h2
    have hi : i < 64 := by simpa [ofMat] using h1
    simp only [ofMat, toMat, Matrix.of_apply, Array.getElem_ofFn]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    congr 1
    omega

theorem wordGL_A_B_noncomm : wordGL wordA * wordGL wordB ≠ wordGL wordB * wordGL wordA := by
  intro h
  have h1 := congrArg (fun g : GL (Fin 8) GF8 => (g : Matrix (Fin 8) (Fin 8) GF8)) h
  simp only [Units.val_mul, coe_wordGL_A, coe_wordGL_B] at h1
  rw [← toMat_mulArr, ← toMat_mulArr] at h1
  have h2 : mulArr genA genB = mulArr genB genA := by
    have := congrArg ofMat h1
    rwa [ofMat_toMat _ (size_mulArr _ _), ofMat_toMat _ (size_mulArr _ _)] at this
  have h3 := commutes_genA_genB
  simp [commutes, h2] at h3

theorem exists_noncomm_three_of_two {S : Type} [Group S] [Finite S]
    (hmodel : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 2 1) :
    ∃ H : Subgroup S, IsPGroup 3 H ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hL : CFSG.Blueprint.LieModel S .trialityD4 0 2 1 :=
    Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hmodel⟩)
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 S hL
  obtain ⟨hle, hcard, -⟩ := sylowGroup_facts
  let P : Subgroup trialityGroup8 := sylowGroup.subgroupOf trialityGroup8
  have hP : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard])
  let a : trialityGroup8 := ⟨wordGL wordA, wordGL_mem _⟩
  let b : trialityGroup8 := ⟨wordGL wordB, wordGL_mem _⟩
  have haP : a ∈ P := Subgroup.subset_closure (Or.inl rfl)
  have hbP : b ∈ P := Subgroup.subset_closure (Or.inr rfl)
  refine ⟨P.map e.symm.toMonoidHom, hP.map _, e.symm a, ⟨a, haP, rfl⟩, e.symm b, ⟨b, hbP, rfl⟩, ?_⟩
  intro h
  have h' : a * b = b * a := e.symm.injective (by rw [map_mul, map_mul]; exact h)
  exact wordGL_A_B_noncomm (congrArg Subtype.val h')

end Two

section Final


open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction (N13D4)

theorem n13D4_holds : N13D4 := by
  intro S _ _ ℓ f hmodel T hT hTi
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : ℓ.Prime := hmodel.1.1
  have hf : 1 ≤ f := hmodel.1.2.1
  obtain ⟨H, hH, a, ha, b, hb, hab⟩ :
      ∃ H : Subgroup S, IsPGroup 3 H ∧ ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a := by
    by_cases hℓ3 : ℓ = 3
    · subst hℓ3
      exact exists_noncomm_three_of_char_three hf hmodel
    · by_cases hq2 : 2 < ℓ ^ f
      · exact exists_noncomm_three_of_ne_three hℓ3 hq2 hmodel
      · have hℓ2 : ℓ = 2 := by
          have h1 := Nat.le_self_pow (show f ≠ 0 by omega) ℓ
          have h2 := hp.two_le
          omega
        subst hℓ2
        have hf1 : f = 1 := by
          by_contra hne
          have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        subst hf1
        exact exists_noncomm_three_of_two hmodel
  exact not_isMulCommutative_of_noncomm_pSubgroup hH ha hb hab hT hTi

end Final

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.InnerAction.Exceptional
