module

public import CFSG.LieType.SteinbergBROddLinearThreeParabolic
public import CFSG.LieType.SteinbergBRBlockParabolicDInfSolvable
public import CFSG.LieType.SteinbergBRSemidirectSLEven
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearSmall

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SemidirectProduct

variable {F : Type*} [Field F]

variable (F) in
@[expose] noncomputable def leftTheta {n d e : ℕ} (h : d + e = n)
    (s : SpecialLinearGroup (Fin n) F) :
    Multiplicative (Matrix (Fin d) (Fin e) F) ⋊[phiL F (Fin e)] SpecialLinearGroup (Fin d) F →*
      SpecialLinearGroup (Fin n) F :=
  (transportSL F h s).toMonoidHom.comp (thetaL F (Fin d) (Fin e))

variable (F) in
@[expose] noncomputable def rightTheta {n d e : ℕ} (h : d + e = n)
    (s : SpecialLinearGroup (Fin n) F) :
    Multiplicative (Matrix (Fin d) (Fin e) F) ⋊[phiR F (Fin d)] SpecialLinearGroup (Fin e) F →*
      SpecialLinearGroup (Fin n) F :=
  (transportSL F h s).toMonoidHom.comp (thetaR F (Fin d) (Fin e))

theorem leftTheta_spec {n d e : ℕ} [NeZero e] (h : d + e = n)
    (hres : CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) =
      (parJL F (Fin d) (Fin e)).subgroupOf parQ)
    {s : SpecialLinearGroup (Fin n) F} {W : Submodule F (Fin n → F)}
    (hs : (flagSpace n F d).map (mulVecLin s.val) = W) :
    Function.Injective (leftTheta F h s) ∧
    (leftTheta F h s).range = (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
    ((leftTheta F h s).comp inl).range = radU F W ∧
    (leftTheta F h s).range ⊓ scalars n F = ⊥ ∧
    (leftTheta F h s).range = (parJL F (Fin d) (Fin e)).map (transportSL F h s).toMonoidHom := by
  have hJ := perfectResidual_stabilizer_eq h hs parJL_le_parQ hres
  have hrange : (leftTheta F h s).range =
      (parJL F (Fin d) (Fin e)).map (transportSL F h s).toMonoidHom := by
    rw [leftTheta, MonoidHom.range_comp]
    rfl
  refine ⟨(transportSL F h s).injective.comp thetaL_injective, hrange.trans hJ.symm, ?_, ?_,
    hrange⟩
  · have hcomp : (leftTheta F h s).comp inl =
        (transportSL F h s).toMonoidHom.comp (uniHom F (Fin d) (Fin e)) :=
      MonoidHom.ext fun x => congrArg (transportSL F h s) (SemidirectProduct.lift_inl _ _ _ x)
    rw [hcomp, MonoidHom.range_comp]
    exact map_uniHom_range_transport h hs
  · rw [hrange]
    exact map_inf_scalars_eq_bot_right h s fun g hg => (mem_parJL.1 hg).2

theorem rightTheta_spec {n d e : ℕ} [NeZero d] (h : d + e = n)
    (hres : CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) =
      (parJR F (Fin d) (Fin e)).subgroupOf parQ)
    {s : SpecialLinearGroup (Fin n) F} {W : Submodule F (Fin n → F)}
    (hs : (flagSpace n F d).map (mulVecLin s.val) = W) :
    Function.Injective (rightTheta F h s) ∧
    (rightTheta F h s).range = (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype ∧
    ((rightTheta F h s).comp inl).range = radU F W ∧
    (rightTheta F h s).range ⊓ scalars n F = ⊥ ∧
    (rightTheta F h s).range = (parJR F (Fin d) (Fin e)).map (transportSL F h s).toMonoidHom := by
  have hJ := perfectResidual_stabilizer_eq h hs parJR_le_parQ hres
  have hrange : (rightTheta F h s).range =
      (parJR F (Fin d) (Fin e)).map (transportSL F h s).toMonoidHom := by
    rw [rightTheta, MonoidHom.range_comp]
    rfl
  refine ⟨(transportSL F h s).injective.comp thetaR_injective, hrange.trans hJ.symm, ?_, ?_,
    hrange⟩
  · have hcomp : (rightTheta F h s).comp inl =
        (transportSL F h s).toMonoidHom.comp (uniHom F (Fin d) (Fin e)) :=
      MonoidHom.ext fun x => congrArg (transportSL F h s) (SemidirectProduct.lift_inl _ _ _ x)
    rw [hcomp, MonoidHom.range_comp]
    exact map_uniHom_range_transport h hs
  · rw [hrange]
    exact map_inf_scalars_eq_bot_left h s fun g hg => (mem_parJR.1 hg).2

theorem coe_parJL_eq {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    ((parJL F a b : Subgroup (SpecialLinearGroup (a ⊕ b) F)) : Set _) =
      {M : SpecialLinearGroup (a ⊕ b) F |
        M.val.toBlocks₂₁ = 0 ∧ M.val.toBlocks₁₁.det = 1 ∧ M.val.toBlocks₂₂ = 1} := by
  ext M
  rw [SetLike.mem_coe, mem_parJL, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hQ, h22⟩
    have hdet := det_eq_of_mem_parQ hQ
    rw [h22, det_one, mul_one] at hdet
    exact ⟨hQ, hdet, h22⟩
  · rintro ⟨hQ, -, h22⟩
    exact ⟨hQ, h22⟩

theorem coe_parJR_eq {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] :
    ((parJR F a b : Subgroup (SpecialLinearGroup (a ⊕ b) F)) : Set _) =
      {M : SpecialLinearGroup (a ⊕ b) F |
        M.val.toBlocks₂₁ = 0 ∧ M.val.toBlocks₁₁ = 1 ∧ M.val.toBlocks₂₂.det = 1} := by
  ext M
  rw [SetLike.mem_coe, mem_parJR, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hQ, h11⟩
    have hdet := det_eq_of_mem_parQ hQ
    rw [h11, det_one, one_mul] at hdet
    exact ⟨hQ, h11, hdet⟩
  · rintro ⟨hQ, h11, -⟩
    exact ⟨hQ, h11⟩

theorem even_structure_of_param [Finite F] {n m : ℕ} (hm : 2 ≤ m)
    (h3 : 3 ≤ m ∨ ∃ s : Finset F, s.card = 4)
    (hZ : Subgroup.center (SpecialLinearGroup (Fin m) F) = ⊥)
    {N : Type*} [CommGroup N] [Finite N] (hN : IsPGroup 2 N)
    {φ : SpecialLinearGroup (Fin m) F →* MulAut N}
    {J : Subgroup (SpecialLinearGroup (Fin n) F)} {B : Subgroup (projectiveSL n F)}
    (θ : N ⋊[φ] SpecialLinearGroup (Fin m) F →* SpecialLinearGroup (Fin n) F)
    (hθ : Function.Injective θ) (hJ : θ.range = J) (hJZ : J ⊓ scalars n F = ⊥)
    (hB : B = J.map (proj n F)) :
    Nonempty (N ⋊[φ] SpecialLinearGroup (Fin m) F ≃* B) ∧
    (θ.comp inl).range.map (proj n F) ≤ B ∧
    CFSG.solvableRadical B = ((θ.comp inl).range.map (proj n F)).subgroupOf B ∧
    CFSG.pCore 2 B = CFSG.solvableRadical B ∧
    Nonempty (B ⧸ CFSG.solvableRadical B ≃* projectiveSL m F) ∧
    Nat.card ((θ.comp inl).range.map (proj n F)) = Nat.card N ∧
    Nat.card B = Nat.card N * Nat.card (SpecialLinearGroup (Fin m) F) := by
  have hπ : proj n F = QuotientGroup.mk' (scalars n F) := rfl
  have hinjOn := injOn_mk_of_inf_eq_bot hJZ
  have hinj : Function.Injective ((proj n F).comp θ) := fun x y hxy =>
    hθ (hinjOn (hJ ▸ ⟨x, rfl⟩) (hJ ▸ ⟨y, rfl⟩) hxy)
  have hrange : ((proj n F).comp θ).range = B := by
    rw [MonoidHom.range_comp, hJ, hB]
  let Φ : N ⋊[φ] SpecialLinearGroup (Fin m) F ≃* B :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  have hcomp : B.subtype.comp Φ.toMonoidHom = (proj n F).comp θ :=
    MonoidHom.ext fun _ => rfl
  obtain ⟨hRad, hO2, hcard, ⟨hquot⟩⟩ := semidirect_SL_even_structure hm h3 hZ hN Φ
  have hbar : (θ.comp inl).range.map (proj n F) = (((proj n F).comp θ).comp inl).range := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.map_map]
  have hle : (θ.comp inl).range.map (proj n F) ≤ B := by
    rw [hB, ← hJ]
    refine Subgroup.map_mono ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨inl x, rfl⟩
  refine ⟨⟨Φ⟩, hle, ?_, hO2, ⟨hquot.trans (QuotientGroup.quotientMulEquivOfEq
    (scalars_eq_center m F).symm)⟩, ?_, hcard⟩
  · apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hle, hRad, Subgroup.map_map, hcomp, hbar,
      MonoidHom.range_comp]
  · rw [hbar, ← Nat.card_congr (MonoidHom.ofInjective (f := ((proj n F).comp θ).comp inl)
      (hinj.comp inl_injective)).toEquiv]

theorem two_not_dvd_card_scalars [Finite F] [CharP F 2] {n : ℕ} [NeZero n] :
    ¬ 2 ∣ Nat.card (scalars n F) := by
  intro hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  obtain ⟨c, -, hgc⟩ := g.2
  have hg2 : g ^ 2 = 1 := by
    rw [← hg]
    exact pow_orderOf_eq_one g
  have hc2 : (c : F) ^ 2 = 1 := by
    have h := congrArg (fun x : scalars n F =>
      ((x : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) 0 0) hg2
    change ((g : SpecialLinearGroup (Fin n) F) ^ 2).val 0 0 =
      (1 : Matrix (Fin n) (Fin n) F) 0 0 at h
    rw [Matrix.SpecialLinearGroup.coe_pow, hgc, ← map_pow, scalar_apply, diagonal_apply_eq,
      one_apply_eq] at h
    exact h
  have hc1 : (c : F) = 1 := by
    have h := sub_pow_char (p := 2) (c : F) 1
    rw [hc2, one_pow, sub_self] at h
    exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)
  have hg1 : g = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (g : SpecialLinearGroup (Fin n) F).val = 1
    rw [hgc, hc1, map_one]
  rw [hg1, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem two_not_dvd_prod_pow_sub_one {q : ℕ} (hq : 2 ∣ q) (hq1 : 1 ≤ q) (s : Finset ℕ)
    (hs : ∀ j ∈ s, j ≠ 0) : ¬ 2 ∣ ∏ j ∈ s, (q ^ j - 1) := by
  rw [Nat.prime_two.prime.dvd_finsetProd_iff]
  rintro ⟨j, hj, h⟩
  exact not_dvd_pow_sub_one Nat.prime_two hq (hs j hj) hq1 h

theorem two_part_ratio {q n d : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    (hcase : (n = 3 ∧ 4 ≤ q) ∨ (q = 2 ∧ (n = 4 ∨ n = 5) ∧ (n, d) ≠ (4, 2))) :
    q ^ (n * (n - 1) / 2) = (if q = 2 ∧ n = 5 ∧ (d = 2 ∨ d = 3) then 2 else 1) *
      q ^ (d * (n - d) + max d (n - d) * (max d (n - d) - 1) / 2) := by
  rcases hcase with ⟨rfl, hq4⟩ | ⟨rfl, rfl | rfl, hne⟩
  · interval_cases d <;> norm_num
  · interval_cases d
    · decide
    · exact absurd rfl hne
    · decide
  · interval_cases d <;> decide

end CFSG.LieType.SteinbergBR.BlockPar

namespace CFSG.LieType

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag SemidirectProduct
  CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar

theorem linear_small_parabolic_perfect_residual_structure {F : Type*} [Field F] [Finite F]
    (hF : Even (Nat.card F)) {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n)
    (hcase : (n = 3 ∧ 4 ≤ Nat.card F) ∨ (Nat.card F = 2 ∧ (n = 4 ∨ n = 5) ∧ (n, d) ≠ (4, 2)))
    (W : Submodule F (Fin n → F)) (hW : finrank F W = d)
    {P B : Subgroup (projectiveSL n F)}
    (hP : P = (stabilizer W).map (proj n F))
    (hB : B = (CFSG.perfectResidual P).map P.subtype) :
    (d = max d (n - d) →
      Nonempty (Multiplicative (Matrix (Fin d) (Fin (n - d)) F) ⋊[phiL F (Fin (n - d))]
        SpecialLinearGroup (Fin d) F ≃* B) ∧
      ∀ s : SpecialLinearGroup (Fin n) F, (flagSpace n F d).map (mulVecLin s.val) = W →
        (B : Set (projectiveSL n F)) =
          (fun M => proj n F (transportSL F (Nat.add_sub_of_le hdn.le) s M)) ''
            {M : SpecialLinearGroup (Fin d ⊕ Fin (n - d)) F |
              M.val.toBlocks₂₁ = 0 ∧ M.val.toBlocks₁₁.det = 1 ∧ M.val.toBlocks₂₂ = 1}) ∧
    (n - d = max d (n - d) →
      Nonempty (Multiplicative (Matrix (Fin d) (Fin (n - d)) F) ⋊[phiR F (Fin d)]
        SpecialLinearGroup (Fin (n - d)) F ≃* B) ∧
      ∀ s : SpecialLinearGroup (Fin n) F, (flagSpace n F d).map (mulVecLin s.val) = W →
        (B : Set (projectiveSL n F)) =
          (fun M => proj n F (transportSL F (Nat.add_sub_of_le hdn.le) s M)) ''
            {M : SpecialLinearGroup (Fin d ⊕ Fin (n - d)) F |
              M.val.toBlocks₂₁ = 0 ∧ M.val.toBlocks₁₁ = 1 ∧ M.val.toBlocks₂₂.det = 1}) ∧
    (radU F W).map (proj n F) ≤ B ∧
    CFSG.pCore 2 B = CFSG.solvableRadical B ∧
    CFSG.solvableRadical B = ((radU F W).map (proj n F)).subgroupOf B ∧
    Nonempty (B ⧸ CFSG.solvableRadical B ≃* projectiveSL (max d (n - d)) F) ∧
    Nonempty (projectiveSL (max d (n - d)) F ≃* SpecialLinearGroup (Fin (max d (n - d))) F) ∧
    Nat.card ((radU F W).map (proj n F)) = Nat.card F ^ (d * (n - d)) ∧
    ordProj[2] (Nat.card B) =
      Nat.card F ^ (d * (n - d) + max d (n - d) * (max d (n - d) - 1) / 2) ∧
    ordProj[2] (Nat.card (projectiveSL n F)) = Nat.card F ^ (n * (n - 1) / 2) ∧
    ordProj[2] (Nat.card (projectiveSL n F)) =
      (if Nat.card F = 2 ∧ n = 5 ∧ (d = 2 ∨ d = 3) then 2 else 1) * ordProj[2] (Nat.card B) ∧
    ordProj[2] (Nat.card (projectiveSL n F)) / ordProj[2] (Nat.card B) =
      if Nat.card F = 2 ∧ n = 5 ∧ (d = 2 ∨ d = 3) then 2 else 1 := by
  classical
  have hchar : ringChar F = 2 := by
    have := Fintype.ofFinite F
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, ← Nat.even_iff]
    exact hF
  have : CharP F 2 := ringChar.of_eq hchar
  obtain ⟨f, hf0, hqf⟩ : ∃ f : ℕ, f ≠ 0 ∧ Nat.card F = 2 ^ f := by
    have := Fintype.ofFinite F
    obtain ⟨k, -, hk⟩ := FiniteField.card F 2
    exact ⟨k, k.ne_zero, by rw [Nat.card_eq_fintype_card, hk]⟩
  have hq1 : 1 ≤ Nat.card F := Nat.card_pos
  have hq2 : 2 ∣ Nat.card F := hqf ▸ dvd_pow_self 2 hf0
  have hpow : ∀ k, Nat.card F ^ k = 2 ^ (f * k) := fun k => by rw [hqf, pow_mul]
  have hord : ∀ k x, ¬ 2 ∣ x → ordProj[2] (Nat.card F ^ k * x) = Nat.card F ^ k :=
    fun k x hx => by
      rw [hpow k]
      exact ordProj_prime_pow_mul Nat.prime_two _ hx
  have hodd : ∀ k, ¬ 2 ∣ ∏ j ∈ Finset.Icc 2 k, (Nat.card F ^ j - 1) := fun k =>
    two_not_dvd_prod_pow_sub_one hq2 hq1 _ fun j hj => by
      have := (Finset.mem_Icc.1 hj).1
      omega
  have h4 : 4 ≤ Nat.card F → ∃ s : Finset F, s.card = 4 := fun hq4 => by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card]; omega)
    exact ⟨s, hs⟩
  have hde : d + (n - d) = n := Nat.add_sub_of_le hdn.le
  set J := (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype with hJdef
  have hBJ : B = J.map (proj n F) := by
    rw [hB, hP]
    exact (map_perfectResidual_subgroup _ _).symm
  obtain ⟨s₀, hs₀⟩ := exists_map_flagSpace_eq W
  rw [hW] at hs₀
  have hordP : ordProj[2] (Nat.card (projectiveSL n F)) = Nat.card F ^ (n * (n - 1) / 2) := by
    have : NeZero n := ⟨by omega⟩
    have hmul := Nat.ordProj_mul 2 (Nat.card_pos (α := projectiveSL n F)).ne'
      (Nat.card_pos (α := scalars n F)).ne'
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup, card_SL_eq (by omega),
      Nat.factorization_eq_zero_of_not_dvd two_not_dvd_card_scalars, pow_zero, mul_one,
      hord _ _ (hodd n)] at hmul
    exact hmul.symm
  have hratio := two_part_ratio hd hdn hcase
  have h2d : 2 * d ≠ n := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, rfl | rfl, hne⟩
    · omega
    · have : d ≠ 2 := fun h => hne (by rw [h])
      omega
    · omega
  rcases lt_or_gt_of_ne h2d with hlt | hgt
  ·
    have hmax : max d (n - d) = n - d := max_eq_right (by omega)
    have hm2 : 2 ≤ n - d := by omega
    have hm3 : 3 ≤ n - d ∨ ∃ s : Finset F, s.card = 4 := by
      rcases hcase with ⟨rfl, hq4⟩ | ⟨-, hn, -⟩
      · exact Or.inr (h4 hq4)
      · left
        omega
    have hGL : Group.IsSolvable (GL (Fin d) F) := by
      refine CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable d F
        ?_
      rcases hcase with ⟨rfl, -⟩ | ⟨hq, hn, -⟩
      · left
        omega
      · by_cases hd1 : d = 1
        · exact Or.inl hd1
        · exact Or.inr ⟨by omega, Or.inl hq⟩
    have hZ : Subgroup.center (SpecialLinearGroup (Fin (n - d)) F) = ⊥ := by
      refine center_SL_eq_bot_of_charTwo (by omega) ?_
      rcases hcase with ⟨rfl, -⟩ | ⟨hq, -, -⟩
      · left
        omega
      · exact Or.inr hq
    have : NeZero d := ⟨by omega⟩
    have : Nontrivial (Fin (n - d)) := Fin.nontrivial_iff_two_le.2 hm2
    have hSL : commutator (SpecialLinearGroup (Fin (n - d)) F) = ⊤ :=
      (CFSG.LinearGroups.special_linear_isPerfect hm2 hm3).commutator_eq_top
    have hres := perfectResidual_parQ_eq_parJR_of_isSolvable hGL hSL
    obtain ⟨hinj, hrange, hU, hZ', -⟩ := rightTheta_spec hde hres hs₀
    have hJZ : J ⊓ scalars n F = ⊥ := by
      rw [hrange] at hZ'
      exact hZ'
    obtain ⟨⟨Φ⟩, hle, hRad, hO2, ⟨hquot⟩, hcardU, hcardB⟩ := even_structure_of_param hm2 hm3 hZ
      (isPGroup_multiplicative_matrix d (n - d)) (rightTheta F hde s₀) hinj hrange hJZ hBJ
    rw [hU] at hle hRad hcardU
    have hordB : ordProj[2] (Nat.card B) =
        Nat.card F ^ (d * (n - d) + (n - d) * (n - d - 1) / 2) := by
      rw [hcardB, card_multiplicative_matrix, card_SL_eq (by omega), mul_comm (n - d) d,
        ← mul_assoc, ← pow_add]
      exact hord _ _ (hodd _)
    rw [hmax] at hratio ⊢
    have hprod : ordProj[2] (Nat.card (projectiveSL n F)) =
        (if Nat.card F = 2 ∧ n = 5 ∧ (d = 2 ∨ d = 3) then 2 else 1) *
          ordProj[2] (Nat.card B) := by
      rw [hordP, hordB]
      exact hratio
    refine ⟨fun h => absurd h (by omega), fun _ => ⟨⟨Φ⟩, fun s hs => ?_⟩, hle, hO2, hRad,
      ⟨hquot⟩, ⟨(QuotientGroup.quotientMulEquivOfEq (by rw [scalars_eq_center, hZ])).trans
        QuotientGroup.quotientBot⟩, ?_, hordB, hordP, hprod, ?_⟩
    · obtain ⟨-, hrange_s, -, -, hJs⟩ := rightTheta_spec hde hres hs
      have hJ' : J = _ := hrange_s.symm.trans hJs
      rw [hBJ, hJ', Subgroup.coe_map, Subgroup.coe_map, coe_parJR_eq, Set.image_image]
      rfl
    · rw [hcardU, card_multiplicative_matrix, mul_comm]
    · rw [hprod]
      exact Nat.mul_div_cancel _ (pow_pos two_pos _)
  ·
    have hmax : max d (n - d) = d := max_eq_left (by omega)
    have hm2 : 2 ≤ d := by omega
    have hm3 : 3 ≤ d ∨ ∃ s : Finset F, s.card = 4 := by
      rcases hcase with ⟨rfl, hq4⟩ | ⟨-, hn, -⟩
      · exact Or.inr (h4 hq4)
      · left
        omega
    have hGL : Group.IsSolvable (GL (Fin (n - d)) F) := by
      refine CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_small_solvable
        (n - d) F ?_
      rcases hcase with ⟨rfl, -⟩ | ⟨hq, hn, -⟩
      · left
        omega
      · by_cases hd1 : n - d = 1
        · exact Or.inl hd1
        · exact Or.inr ⟨by omega, Or.inl hq⟩
    have hZ : Subgroup.center (SpecialLinearGroup (Fin d) F) = ⊥ := by
      refine center_SL_eq_bot_of_charTwo (by omega) ?_
      rcases hcase with ⟨rfl, -⟩ | ⟨hq, -, -⟩
      · left
        omega
      · exact Or.inr hq
    have : NeZero (n - d) := ⟨by omega⟩
    have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.2 hm2
    have hSL : commutator (SpecialLinearGroup (Fin d) F) = ⊤ :=
      (CFSG.LinearGroups.special_linear_isPerfect hm2 hm3).commutator_eq_top
    have hres := perfectResidual_parQ_eq_parJL_of_isSolvable hGL hSL
    obtain ⟨hinj, hrange, hU, hZ', -⟩ := leftTheta_spec hde hres hs₀
    have hJZ : J ⊓ scalars n F = ⊥ := by
      rw [hrange] at hZ'
      exact hZ'
    obtain ⟨⟨Φ⟩, hle, hRad, hO2, ⟨hquot⟩, hcardU, hcardB⟩ := even_structure_of_param hm2 hm3 hZ
      (isPGroup_multiplicative_matrix d (n - d)) (leftTheta F hde s₀) hinj hrange hJZ hBJ
    rw [hU] at hle hRad hcardU
    have hordB : ordProj[2] (Nat.card B) = Nat.card F ^ (d * (n - d) + d * (d - 1) / 2) := by
      rw [hcardB, card_multiplicative_matrix, card_SL_eq (by omega), mul_comm (n - d) d,
        ← mul_assoc, ← pow_add]
      exact hord _ _ (hodd _)
    rw [hmax] at hratio ⊢
    have hprod : ordProj[2] (Nat.card (projectiveSL n F)) =
        (if Nat.card F = 2 ∧ n = 5 ∧ (d = 2 ∨ d = 3) then 2 else 1) *
          ordProj[2] (Nat.card B) := by
      rw [hordP, hordB]
      exact hratio
    refine ⟨fun _ => ⟨⟨Φ⟩, fun s hs => ?_⟩, fun h => absurd h (by omega), hle, hO2, hRad,
      ⟨hquot⟩, ⟨(QuotientGroup.quotientMulEquivOfEq (by rw [scalars_eq_center, hZ])).trans
        QuotientGroup.quotientBot⟩, ?_, hordB, hordP, hprod, ?_⟩
    · obtain ⟨-, hrange_s, -, -, hJs⟩ := leftTheta_spec hde hres hs
      have hJ' : J = _ := hrange_s.symm.trans hJs
      rw [hBJ, hJ', Subgroup.coe_map, Subgroup.coe_map, coe_parJL_eq, Set.image_image]
      rfl
    · rw [hcardU, card_multiplicative_matrix, mul_comm]
    · rw [hprod]
      exact Nat.mul_div_cancel _ (pow_pos two_pos _)

end CFSG.LieType
