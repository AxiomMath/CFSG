module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2FiveListBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerPSL
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBPureGraph

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_iff_isComponent_subgroupOf
  isComponentOf_map_of_injective)

namespace FiveList

theorem lieModel_of_isComponent_GL {k : Type} [Field k] [Finite k] {p j : ℕ} (hp : p.Prime)
    (hj : 1 ≤ j) (hk : Nat.card k = p ^ j) {n : ℕ} (hn : 1 ≤ n) {L : Subgroup (GL (Fin n) k)}
    (hL : IsComponent L) :
    StatedLieAdmissible .PSL n p j ∧ LieModel (L ⧸ center L) .PSL n p j := by
  by_cases hsmall : n = 1 ∨ n = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
  · have := CatalogueBGeneralLinear.generalLinear_small_solvable n k hsmall
    exact absurd hL (CatLeafProof.OddInner.not_isComponent_of_isSolvable L)
  obtain ⟨hn2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters n k hn hsmall
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k hn2 h22 h23
    L hL.2
  have hadm : StatedLieAdmissible .PSL n p j :=
    CatLeafProof.OddInner.admissible_PSL hp hj hn2 (by rw [← hk]; exact h22)
      (by rw [← hk]; exact h23)
  refine ⟨hadm, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hSL : LieModel (SpecialLinearGroup (Fin (m + 1)) k ⧸ center _) .PSL (m + 1) p j :=
    Or.inl ⟨by decide,
      LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩
  exact lieModel_centerQuotient_of_mulEquiv
    (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective) hSL

theorem exists_component_factor {G₁ G₂ : Type} [Group G₁] [Group G₂] [Finite G₁] [Finite G₂]
    {L : Subgroup (G₁ × G₂)} (hL : IsComponent L) :
    (∃ M : Subgroup G₁, IsComponent M ∧ Nonempty (L ≃* M)) ∨
      (∃ M : Subgroup G₂, IsComponent M ∧ Nonempty (L ≃* M)) := by
  rcases LocalAnalysis.ComponentInitial.CentralQuotientLift.fst_eq_or_snd_eq_of_isComponent_prod
      hL with h2 | h1
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component (MulEquiv.refl _) hL h2
    exact Or.inl ⟨_, hρc, ⟨MonoidHom.ofInjective hρi⟩⟩
  · obtain ⟨ρ, hρi, hρc, -⟩ := OddClassSelector.restrict_component MulEquiv.prodComm hL h1
    exact Or.inr ⟨_, hρc, ⟨MonoidHom.ofInjective hρi⟩⟩

theorem exists_component_glSubgroup {n : ℕ} {K : Type} [Field K] [Finite K]
    (ψ : MulAut (SpecialLinearGroup (Fin n) K))
    (hinv : (center (SpecialLinearGroup (Fin n) K)).map ψ.toMonoidHom = center _)
    (G₀ : Subgroup (GL (Fin n) K))
    (hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      G₀ ⊓ CatalogueBGeneralLinear.specialLinearRange n K)
    {L : Subgroup (fixedSubgroup
      (CatalogueBFixedCentralQuotient.onQuotient (center (SpecialLinearGroup (Fin n) K)) ψ hinv))}
    (hL : IsComponent L) :
    ∃ N : Subgroup G₀, IsComponent N ∧ Nonempty (L ⧸ center L ≃* N ⧸ center N) := by
  obtain ⟨M, hM, ⟨eLM⟩⟩ := CatLeafProof.exists_component_of_quotientFixed _ le_rfl ψ hinv hL
  have hMF : Assembly.IsComponentOf (M.map (fixedSubgroup ψ).subtype) (fixedSubgroup ψ) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le M)).2 ?_
    have hMM : (M.map (fixedSubgroup ψ).subtype).subgroupOf (fixedSubgroup ψ) = M :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) M
    rw [hMM]
    exact hM
  have h1 := isComponentOf_map_of_injective hMF SpecialLinearGroup.toGL
    SpecialLinearGroup.toGL_injective
  rw [hmap] at h1
  have hnormal : ((G₀ ⊓ CatalogueBGeneralLinear.specialLinearRange n K).subgroupOf G₀).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨-, hxS⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨(g * x * g⁻¹).2, ?_⟩
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using
      (CatalogueBGeneralLinear.specialLinearRangeNormal n K).conj_mem _ hxS (g : GL (Fin n) K)
  have h2 := OddClassSelector.isComponentOf_of_normal_le h1 inf_le_left hnormal
  have h3 := (isComponentOf_iff_isComponent_subgroupOf h2.1).1 h2
  let eMN := ((M.equivMapOfInjective (fixedSubgroup ψ).subtype (subtype_injective _)).trans
      ((M.map (fixedSubgroup ψ).subtype).equivMapOfInjective SpecialLinearGroup.toGL
        SpecialLinearGroup.toGL_injective)).trans (Subgroup.subgroupOfEquivOfLe h2.1).symm
  exact ⟨_, h3, ⟨eLM.trans (QuotientGroup.congr _ _ eMN (Subgroup.map_center_eq eMN))⟩⟩

theorem card_fixed_dvd_card_mul {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (ψ : MulAut X) (hinv : Z.map ψ.toMonoidHom = Z) :
    Nat.card (fixedSubgroup ψ) ∣
      Nat.card Z * Nat.card (fixedSubgroup
        (CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv)) := by
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
  let ι : φ.ker →* Z :=
    { toFun := fun x => ⟨((x : fixedSubgroup ψ) : X), by
        have h1 : φ x = 1 := x.2
        have h2 : QuotientGroup.mk' Z ((x : fixedSubgroup ψ) : X) = 1 :=
          congrArg Subtype.val h1
        exact (QuotientGroup.eq_one_iff _).mp h2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hι : Function.Injective ι := fun a b hab => by
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext h1)
  rw [← hkr]
  exact Nat.mul_dvd_mul (Subgroup.card_dvd_of_injective ι hι)
    (Subgroup.card_subgroup_dvd_card _)

theorem index_specialLinearRange {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K] :
    (CatalogueBGeneralLinear.specialLinearRange n K).index = Nat.card Kˣ := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 := Subgroup.card_mul_index (CatalogueBGeneralLinear.specialLinearRange n K)
  have h2 : Nat.card (CatalogueBGeneralLinear.specialLinearRange n K) =
      Nat.card (SpecialLinearGroup (Fin n) K) :=
    (Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv).symm
  have h3 := Matrix.card_SL_mul_card_units (n := Fin n) (R := K)
  rw [h2, ← h3] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem card_center_SL_five {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 5) :
    Nat.card (center (SpecialLinearGroup (Fin n) K)) ∣ 4 ∧
      (n = 3 → Nat.card (center (SpecialLinearGroup (Fin n) K)) = 1) := by
  classical
  have hU : Nat.card Kˣ = 4 := by rw [Nat.card_units, hK]
  have e := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin n) (R := K)
  rw [Nat.card_congr e.toEquiv]
  refine ⟨hU ▸ Subgroup.card_subgroup_dvd_card _, fun hn => ?_⟩
  subst hn
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => ?_⟩, inferInstance⟩
  have key : ∀ z : rootsOfUnity (max (Fintype.card (Fin 3)) 1) K, z = 1 := fun z => by
    have h3 : (z : Kˣ) ^ 3 = 1 := by
      have := z.2
      rw [mem_rootsOfUnity] at this
      simpa using this
    have h4 : (z : Kˣ) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := Kˣ) (x := (z : Kˣ))
      rwa [hU] at this
    have h1 : (z : Kˣ) = 1 := by
      calc (z : Kˣ) = (z : Kˣ) ^ 4 * ((z : Kˣ) ^ 3)⁻¹ := by group
        _ = 1 := by rw [h3, h4]; simp
    exact Subtype.ext h1
  rw [key a, key b]

theorem dvd_card_fixed_of_inner_two {n r t : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) (hr : r = 2) (ht : 1 ≤ t) (hnt : r + t = n) (A : GL (Fin n) K)
    (e : Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ≃* GL (Fin r) K × GL (Fin t) K)
    (hinv : (center (SpecialLinearGroup (Fin n) K)).map (slConjugation n K A).toMonoidHom =
      center _)
    (hmap : (fixedSubgroup (slConjugation n K A)).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K) :
    32 ∣ Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (slConjugation n K A) hinv)) := by
  classical
  subst hr
  have : Fintype K := Fintype.ofFinite K
  have hq : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card]; exact hK
  set C := Subgroup.centralizer ({A} : Set (GL (Fin n) K)) with hCdef
  set SLr := CatalogueBGeneralLinear.specialLinearRange n K with hSLr
  set Fq := Nat.card (fixedSubgroup (CatalogueBFixedCentralQuotient.onQuotient
      (center (SpecialLinearGroup (Fin n) K)) (slConjugation n K A) hinv)) with hFq
  have hC : Nat.card C = 480 * Nat.card (GL (Fin t) K) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Matrix.card_GL_field 2, hq]
    simp [Fin.prod_univ_two]
  have h4 : 4 ^ t ∣ Nat.card (GL (Fin t) K) := by
    rw [Matrix.card_GL_field t, hq]
    have hfac : ∀ i : Fin t, 4 ∣ 5 ^ t - 5 ^ (i : ℕ) := fun i => by
      apply Nat.dvd_of_mod_eq_zero
      apply Nat.sub_mod_eq_zero_of_mod_eq
      rw [Nat.pow_mod, Nat.pow_mod 5 (i : ℕ)]
      norm_num
    calc 4 ^ t = ∏ _i : Fin t, 4 := by simp
      _ ∣ _ := Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => hfac i)
  have : SLr.Normal := CatalogueBGeneralLinear.specialLinearRangeNormal n K
  have hrel : SLr.relIndex C ∣ 4 := by
    have h := Subgroup.relIndex_dvd_index_of_normal SLr C
    rwa [hSLr, index_specialLinearRange (by omega), Nat.card_units, hK] at h
  have hCSL : Nat.card C = Nat.card (fixedSubgroup (slConjugation n K A)) * SLr.relIndex C := by
    have h1 := Subgroup.card_mul_index (SLr.subgroupOf C)
    have h2 : Nat.card (SLr.subgroupOf C) = Nat.card (fixedSubgroup (slConjugation n K A)) := by
      rw [← Subgroup.inf_subgroupOf_right SLr C,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, inf_comm, ← hmap,
        Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective]
    rw [← h1, h2]
    rfl
  have hfix := card_fixed_dvd_card_mul (center (SpecialLinearGroup (Fin n) K))
    (slConjugation n K A) hinv
  obtain ⟨hZ4, hZ1⟩ := card_center_SL_five (n := n) hK
  have hmain : 480 * 4 ^ t ∣
      Nat.card (center (SpecialLinearGroup (Fin n) K)) * Fq * 4 := by
    have h := Nat.mul_dvd_mul_left 480 h4
    rw [← hC, hCSL] at h
    exact h.trans (Nat.mul_dvd_mul hfix hrel)
  have h480 : 480 ∣ Fq := by
    rcases Nat.lt_or_ge t 2 with ht2 | ht2
    · have ht1 : t = 1 := by omega
      rw [hZ1 (by omega), ht1, one_mul, pow_one] at hmain
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) hmain
    · have h16' : 16 ∣ 4 ^ t := by
        have := pow_dvd_pow 4 ht2
        simpa using this
      have h16 : 480 * 16 ∣ 480 * 4 ^ t := Nat.mul_dvd_mul_left 480 h16'
      have h' : Nat.card (center (SpecialLinearGroup (Fin n) K)) * Fq * 4 ∣ 16 * Fq := by
        have := Nat.mul_dvd_mul (Nat.mul_dvd_mul_right hZ4 Fq) (dvd_refl 4)
        rwa [show 4 * Fq * 4 = 16 * Fq by ring] at this
      have h'' := (h16.trans hmain).trans h'
      rw [mul_comm 480 16] at h''
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h''
  exact (by norm_num : 32 ∣ 480).trans h480

end FiveList

section Classes


theorem false_of_fiveA5_inner_psl {n : ℕ} {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 5 ^ f) (hadm : StatedLieAdmissible .PSL n 5 f) (A : GL (Fin n) K)
    (hA : orderOf (innerDiagonalAction n K A) = 2)
    (h : FiveA5Group (fixedSubgroup (innerDiagonalAction n K A))) : False := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hp2 : (5 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hparameter : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    right
    rw [hK]
    exact Nat.le_self_pow (by omega) 5
  have hne : innerDiagonalAction n K A ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hsq2 : innerDiagonalAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  obtain ⟨hmk, -, c, hc⟩ :=
    CatalogueBHigherLinearInner.inner_involution_projective_data n K hn hparameter A hne hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : innerDiagonalAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact innerDiagonalAction_mk n K A g
  have h' := h.of_eq heq
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      Subgroup.centralizer ({A} : Set (GL (Fin n) K)) ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [toGL_slConjugation] at h1
      calc SpecialLinearGroup.toGL g * A =
          (A * SpecialLinearGroup.toGL g * A⁻¹) * A := by rw [h1]
        _ = A * SpecialLinearGroup.toGL g := by group
    · intro hy
      obtain ⟨hyC, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation, ← Subgroup.mem_centralizer_singleton_iff.mp hyC,
        mul_inv_cancel_right]
  obtain ⟨L, hL, hLm⟩ := h'.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := FiveList.exists_component_glSubgroup ψ hinv _ hmap hL
  have hNm : LieModel (N ⧸ center N) .PSL 2 2 2 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  have hodd : Odd (Nat.card K) := by
    rw [hK]
    exact Odd.pow (by decide)
  have h2 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  by_cases hsquare : IsSquare c.val
  · obtain ⟨b, -, hr, hs, hrs, e, -⟩ :=
      CatalogueBProjectiveInvolution.square_projective_centralizer_structure n hn A c h2 hmk hc
        hsquare
    have hN' := LocalCores.isComponent_map_mulEquiv e hN
    have hN'm : LieModel ((N.map e.toMonoidHom) ⧸ center (N.map e.toMonoidHom)) .PSL 2 2 2 :=
      FiveList.lieModel_centerQuotient_of_mulEquiv (N.equivMapOfInjective _ e.injective) hNm
    rcases FiveList.exists_component_factor hN' with ⟨M, hM, ⟨eM⟩⟩ | ⟨M, hM, ⟨eM⟩⟩
    · obtain ⟨hadmr, hmodr⟩ := FiveList.lieModel_of_isComponent_GL hp hf hK hr hM
      obtain ⟨-, hr2, h5⟩ := eq_five_of_lieModel_PSL_two_two
        (FiveList.lieModel_centerQuotient_of_mulEquiv eM hN'm) hp2 hadmr hmodr
      have hK5 : Nat.card K = 5 := by rw [hK, eq_one_of_five_pow_eq_five h5, pow_one]
      exact h'.not_dvd (FiveList.dvd_card_fixed_of_inner_two hK5 hr2 hs hrs A e hinv hmap)
    · obtain ⟨hadms, hmods⟩ := FiveList.lieModel_of_isComponent_GL hp hf hK hs hM
      obtain ⟨-, hs2, h5⟩ := eq_five_of_lieModel_PSL_two_two
        (FiveList.lieModel_centerQuotient_of_mulEquiv eM hN'm) hp2 hadms hmods
      have hK5 : Nat.card K = 5 := by rw [hK, eq_one_of_five_pow_eq_five h5, pow_one]
      exact h'.not_dvd (FiveList.dvd_card_fixed_of_inner_two hK5 hs2 hr (by omega) A
        (e.trans MulEquiv.prodComm) hinv hmap)
  · let : Fact (¬ IsSquare c.val) := ⟨hsquare⟩
    let : Finite (CatalogueBProjectiveQuadratic.extension c.val) :=
      CatalogueBProjectiveInvolution.quadraticExtension_finite c.val
    have hm := (CatalogueBProjectiveQuadratic.nonsquare_matrix_dimension n hn A c hc
      hsquare).2
    let eQ := CatalogueBProjectiveQuadratic.matrixCentralizerQuadraticEquiv A c hc
    have hN' := LocalCores.isComponent_map_mulEquiv eQ hN
    obtain ⟨hadmE, hmodE⟩ := FiveList.lieModel_of_isComponent_GL hp (j := 2 * f) (by omega)
      (by rw [CatLeafProof.OddInner.card_extension, hK, ← pow_mul, mul_comm]) hm hN'
    obtain ⟨-, -, h5⟩ := eq_five_of_lieModel_PSL_two_two
      (FiveList.lieModel_centerQuotient_of_mulEquiv (N.equivMapOfInjective _ eQ.injective) hNm)
      hp2 hadmE hmodE
    have := eq_one_of_five_pow_eq_five h5
    omega

theorem eq_of_fiveA5_field_psl {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K] {f : ℕ}
    (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1)
    (h : FiveA5Group (fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))) :
    n = 2 ∧ f = 2 := by
  have hp : (5 : ℕ).Prime := by norm_num
  have hpodd : Odd 5 := by decide
  have hf2 := CatLeafProof.two_le_of_ringEquiv_ne_one hp hf hK hσ
  have hpar : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    right
    rw [hK]
    exact Nat.le_self_pow (by omega) 5
  obtain ⟨heven, hσc, H, hα⟩ := CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy
    n K 5 f hp hpodd hf hK hn hpar A σ hσ hsq
  have hσ2 : σ ^ 2 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun x => ?_
    rw [sq, RingAut.mul_apply, hσc, hσc, ← pow_mul, ← sq, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.1 heven), ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction n K H)
      (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      n K H) (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) = _).trans hα.symm
  let Ψ' : fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ) ≃*
      fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (CatLeafProof.fixedSubgroupCongrEquiv _ _).symm
  obtain ⟨L, hL, hLm⟩ := (h.of_mulEquiv Ψ').1
  have hL2 := CatLeafProof.isPComponent_two_of_isComponent hL
  obtain ⟨hcard, -, hsmall, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components n hn K σ hσ2 hσ
  have hcardk : Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 5 ^ (f / 2) := by
    have h2 : Nat.card K = (5 ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
    rw [hcard] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  by_cases hex : n = 2 ∧ (Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ∨
      Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 3)
  · exact absurd hL2 (hsmall hex 2 Nat.prime_two _)
  obtain ⟨E⟩ := hiso hex 2 Nat.prime_two _ hL2
  have he : 1 ≤ f / 2 := by omega
  have hadm : StatedLieAdmissible .PSL n 5 (f / 2) := by
    refine ⟨hp, he, hn, fun h => ?_, fun h => ?_⟩
    · have h1 : 5 ^ (f / 2) = 2 := (Prod.mk.inj h).2
      have hodd : Odd (5 ^ (f / 2)) := hpodd.pow
      rw [h1] at hodd
      exact absurd hodd (by decide)
    · exact hex ⟨(Prod.mk.inj h).1, Or.inr (hcardk.trans (Prod.mk.inj h).2)⟩
  have hstated : StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin n)
      (CatalogueBHigherLinearField.fixedField K σ)) .PSL n 5 (f / 2) :=
    ⟨hadm, CatalogueBHigherLinearField.fixedField K σ, inferInstance, inferInstance, hcardk,
      ⟨projectiveSpecialLinearGroupEquivStatedProj n _⟩⟩
  have := (LieType.Simplicity.fam_PSL_simplicity _ n 5 (f / 2) hstated).2
  have hmod : LieModel (L ⧸ center L) .PSL n 5 (f / 2) :=
    FiveList.lieModel_centerQuotient_of_simple (CatLeafProof.exists_mul_ne_of_isQuasisimple hL.1 E)
      E (Or.inl ⟨by decide, hstated⟩)
  obtain ⟨-, hn2, h5⟩ := eq_five_of_lieModel_PSL_two_two hLm (by norm_num) hadm hmod
  have h1 := eq_one_of_five_pow_eq_five h5
  refine ⟨hn2, ?_⟩
  obtain ⟨k, hk⟩ := heven
  omega

theorem false_of_fiveA5_graphField_psl {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K]
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 5 ^ f) (A : GL (Fin n) K) (σ : K ≃+* K)
    (hσ : σ ≠ 1) (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2)
    (h : FiveA5Group (fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ))) : False := by
  have : Fact (5 : ℕ).Prime := ⟨by norm_num⟩
  have hp : (5 : ℕ).Prime := by norm_num
  have hpodd : Odd 5 := by decide
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  have hne1 : CatalogueBGraphField.graphFieldAction n K A σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨-, hhalf, hunitary, -, -, -, hcomp⟩ :=
    CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native n K 5 f
      hpodd hf hK hn A σ hσ hne1 hsq
  obtain ⟨L, hL, hLm⟩ := h.1
  let Ψt : fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ) ≃*
      CatalogueBGraphField.twistedFixedPSL n K A σ := MulEquiv.refl _
  have hL' : IsComponent (L.map Ψt.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψt hL
  have hL'm := FiveList.lieModel_centerQuotient_of_mulEquiv
    (L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective) hLm
  obtain ⟨-, ⟨E⟩⟩ := hcomp 2 Nat.prime_two _ (CatLeafProof.isPComponent_two_of_isComponent hL')
  obtain ⟨eQ⟩ := CatLeafProof.nonempty_projectiveSpecialUnitary_equiv_statedProj (n := n)
    hunitary
  have hadm : StatedLieAdmissible .PSU n 5 (f / 2) := by
    refine ⟨hp, hhalf, hn, fun h => ?_⟩
    have h1 : 5 ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (5 ^ (f / 2)) := hpodd.pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (5 ^ (f / 2)) K)) .PSU n 5
      (f / 2) := ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n 5 (f / 2) hstated).2
  have hmod : LieModel ((L.map Ψt.toMonoidHom) ⧸ center (L.map Ψt.toMonoidHom)) .PSU n 5 (f / 2) :=
    FiveList.lieModel_centerQuotient_of_simple
      (CatLeafProof.exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ)) (E.trans eQ)
      (Or.inl ⟨by decide, hstated⟩)
  obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hL'm (by norm_num) hadm hmod
  exact absurd h1 (by decide)

@[expose] def OddFivePSLGraphInput : Prop :=
  ∀ (n : ℕ) (K : Type) [Field K] [Finite K] (f : ℕ), Nat.card K = 5 ^ f → 1 ≤ f → 3 ≤ n →
    ∀ A : GL (Fin n) K, orderOf (CatalogueBGraphForm.pureGraphAction n K A) = 2 →
      FiveA5Group (fixedSubgroup (CatalogueBGraphForm.pureGraphAction n K A)) → n = 3 ∧ f = 1

theorem oddFiveSL2ListFamilyInput_PSL_of_graph (hgraph : OddFivePSLGraphInput) :
    OddFiveSL2ListFamilyInput .PSL := by
  intro J _ _ hJ hna n f hadm hJm τ hτ
  have hF := fiveA5Group_of_catSL2Hyp hτ
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CatLeafProof.nonempty_mulEquiv_psl_of_lieModel hadm hJm
  have hf : 1 ≤ f := hadm.2.1
  have hn : 2 ≤ n := hadm.2.2.1
  have hβ : orderOf (MulAut.congr e τ) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective τ).trans hτ.1
  have hβ2 : MulAut.congr e τ ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one _
  have hFβ := hF.congr e
  suffices hnf : (n = 2 ∧ f = 2) ∨ (n = 3 ∧ f = 1) by
    rcases hnf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl hJm
    · exact Or.inr (Or.inl hJm)
  have hsemi : ∀ (A : GL (Fin n) K) (σ : K ≃+* K),
      MulAut.congr e τ = CatalogueBLinearSemilinear.semilinearAction n K A σ →
        n = 2 ∧ f = 2 := by
    intro A σ hAσ
    by_cases hσ : σ = 1
    · subst hσ
      rw [CatalogueBLinearSemilinear.semilinearAction_one_field] at hAσ
      exact (false_of_fiveA5_inner_psl hK hadm A (hAσ ▸ hβ) (hFβ.of_eq hAσ)).elim
    · exact eq_of_fiveA5_field_psl hn hf hK A σ hσ (hAσ ▸ hβ2) (hFβ.of_eq hAσ)
  rcases (by omega : n = 2 ∨ 3 ≤ n) with rfl | hn3
  · obtain ⟨A, σ, hAσ⟩ := CatLeafProof.psl_two_normal_form (MulAut.congr e τ)
    exact Or.inl (hsemi A σ hAσ)
  · obtain ⟨-, hgen⟩ := LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
      (K := K) hn3
    obtain ⟨A, σ, ε, hε, hAσε⟩ :=
      hgen (MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K).symm (MulAut.congr e τ))
    have hβ' : MulAut.congr e τ = MulAut.congr (CatalogueBLinearHigherB.nativeEquiv n K)
        (LocalAnalysis.ComponentInitial.LinearFlag.conjAut n K A *
          LocalAnalysis.ComponentInitial.LinearFlag.fieldAut n K σ *
            LocalAnalysis.ComponentInitial.LinearFlag.dualAut n K ^ ε) := by
      rw [← hAσε]
      ext x
      simp
    interval_cases ε
    · rw [pow_zero, mul_one, CatalogueBLinearHigherB.congr_semilinear] at hβ'
      exact Or.inl (hsemi A σ hβ')
    · rw [pow_one] at hβ'
      by_cases hσ : σ = 1
      · subst hσ
        rw [map_one, mul_one, CatalogueBLinearHigherB.congr_pureGraph] at hβ'
        exact Or.inr (hgraph n K f hK hf hn3 A (hβ' ▸ hβ) (hFβ.of_eq hβ'))
      · rw [CatalogueBLinearHigherB.congr_graphField] at hβ'
        exact (false_of_fiveA5_graphField_psl hn3 hf hK A σ hσ (hβ' ▸ hβ)
          (hFβ.of_eq hβ')).elim

theorem FiveList.lieModel_of_isComponent_statedSp {k : Type} [Field k] [Finite k] {p j : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = p ^ j) {m : ℕ} (hm : 2 ≤ m)
    {L : Subgroup (StatedSp m k)} (hL : IsComponent L) :
    StatedLieAdmissible .PSp m p j ∧ LieModel (L ⧸ center L) .PSp m p j := by
  have hadm := CatLeafProof.OddInner.admissible_PSp hp hp2 hj hm
  refine ⟨hadm, ?_⟩
  obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple
    (LieType.Universal.Symplectic.isQuasisimple_of_admissible m k hadm hk) hL
  exact FiveList.lieModel_centerQuotient_of_mulEquiv Subgroup.topEquiv.symm
    (Or.inl ⟨by decide, LieType.Universal.Symplectic.statedClassicalModel_center_quotient m k
      hadm hk⟩)

@[expose] def OddFiveOrthComponentInput : Prop :=
  ∀ (k W : Type) [Field k] [Finite k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (e : ℕ), 1 ≤ e → Nat.card k = 5 ^ e → ∀ Q₀ : QuadraticForm k W,
    Q₀.polarBilin.Nondegenerate → 3 ≤ Module.finrank k W →
    ∀ M : Subgroup (TauCeti.QuadraticMap.orthogonalGroup Q₀), IsComponent M →
      LieModel (M ⧸ center M) .PSL 2 2 2 →
        e = 1 ∧ (Module.finrank k W = 3 ∨ Module.finrank k W = 4)

@[expose] def OddFiveL45GraphInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 5 → ∀ A : GL (Fin 4) K,
    orderOf (CatalogueBGraphForm.pureGraphAction 4 K A) = 2 →
      ¬ FiveA5Group (fixedSubgroup (CatalogueBGraphForm.pureGraphAction 4 K A))

open CatalogueBGraphForm (glGraphAut glTranspose slGraphAut pureGraphAction) in
open CatalogueBLinearHigherB in
theorem oddFivePSLGraphInput_of_orth (hO : OddFiveOrthComponentInput)
    (h45 : OddFiveL45GraphInput) : OddFivePSLGraphInput := by
  intro n K _ _ f hK hf hn A hA h
  have hp : (5 : ℕ).Prime := by norm_num
  have : CharP K 5 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hodd : ringChar K ≠ 2 := by
    rw [ringChar.eq K 5]
    norm_num
  have hsq2 : pureGraphAction n K A ^ 2 = 1 := by
    rw [← hA, pow_orderOf_eq_one]
  have hform := CatalogueBGraphForm.pureGraph_involution_form_data n K hn hodd A hsq2
  set Z := center (SpecialLinearGroup (Fin n) K)
  set ψ := slConjugation n K A * slGraphAut n K
  have hinv : Z.map ψ.toMonoidHom = Z := Subgroup.map_center_eq ψ
  have heq : pureGraphAction n K A = CatalogueBFixedCentralQuotient.onQuotient Z ψ hinv := by
    refine MulEquiv.ext fun x => ?_
    induction x using QuotientGroup.induction_on with
    | H g =>
      rw [show ((g : SpecialLinearGroup (Fin n) K ⧸ Z)) = QuotientGroup.mk' Z g from rfl,
        CatalogueBFixedCentralQuotient.onQuotient_mk]
      exact CatalogueBGraphForm.pureGraphAction_mk n K A g
  have hfix : ∀ x : GL (Fin n) K, A * glGraphAut n K x * A⁻¹ = x ↔
      glTranspose n K x * A⁻¹ * x = A⁻¹ := by
    intro x
    have hT : glGraphAut n K x = (glTranspose n K x)⁻¹ := (inv_inv _).symm
    rw [hT]
    constructor
    · intro h
      calc glTranspose n K x * A⁻¹ * x =
          glTranspose n K x * A⁻¹ * (A * (glTranspose n K x)⁻¹ * A⁻¹) := by rw [h]
        _ = A⁻¹ := by group
    · intro h
      calc A * (glTranspose n K x)⁻¹ * A⁻¹ =
          A * (glTranspose n K x)⁻¹ * (glTranspose n K x * A⁻¹ * x) := by rw [h]
        _ = x := by group
  have hmap : (fixedSubgroup ψ).map SpecialLinearGroup.toGL =
      CatalogueBGraphForm.isometryGroup n K A⁻¹ ⊓
        CatalogueBGeneralLinear.specialLinearRange n K := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ⟨g, rfl⟩⟩
      have h1 : SpecialLinearGroup.toGL (ψ g) = SpecialLinearGroup.toGL g :=
        congrArg _ (show ψ g = g from hg)
      rw [MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut] at h1
      exact (hfix _).mp h1
    · intro hy
      obtain ⟨hyI, ⟨g, rfl⟩⟩ := Subgroup.mem_inf.mp hy
      refine ⟨g, ?_, rfl⟩
      change ψ g = g
      apply SpecialLinearGroup.toGL_injective
      rw [MulAut.mul_apply, toGL_slConjugation, CatalogueBGraphForm.toGL_slGraphAut]
      exact (hfix _).mpr hyI
  have h' := h.of_eq heq
  obtain ⟨L, hL, hLm⟩ := h'.1
  obtain ⟨N, hN, ⟨eN⟩⟩ := FiveList.exists_component_glSubgroup ψ hinv _ hmap hL
  have hNm : LieModel (N ⧸ center N) .PSL 2 2 2 := LieType.CurtisTits.lieModel_of_mulEquiv eN hLm
  rcases hform with hsymm | ⟨halt, -⟩
  · have hR := transpose_inv_of_transpose_eq A hsymm
    let Φ : CatalogueBGraphForm.isometryGroup n K A⁻¹ ≃*
        TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹) :=
      (isometryGroupEquiv A⁻¹).symm.trans
        (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd A⁻¹ hR).symm)
    have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
    have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
    obtain ⟨hf1, hn34⟩ := hO K (Fin n → K) f hf hK (matrixQuadraticForm A⁻¹)
      (polarBilin_matrixQuadraticForm_nondegenerate hodd A⁻¹ hR)
      (by rw [Module.finrank_fin_fun]; exact hn) _ hN' hN'm
    rw [Module.finrank_fin_fun] at hn34
    rcases hn34 with h3 | h4
    · exact ⟨h3, hf1⟩
    · exfalso
      subst h4
      exact h45 K (by rw [hK, hf1, pow_one]) A hA h
  · exfalso
    have hR := transpose_inv_of_transpose_eq_neg A halt
    have hB := matrixForm_isAlt hodd A⁻¹ hR
    have hnd := matrixForm_nondegenerate A⁻¹
    obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic
      (matrixForm A⁻¹) hB hnd
    obtain ⟨eS⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp (matrixForm A⁻¹) hB hnd hdm
    rw [Module.finrank_fin_fun] at hdm
    let Φ := (isometryGroupEquiv A⁻¹).symm.trans eS
    have hN' := LocalCores.isComponent_map_mulEquiv Φ hN
    have hN'm := FiveList.lieModel_centerQuotient_of_mulEquiv
      (N.equivMapOfInjective Φ.toMonoidHom Φ.injective) hNm
    obtain ⟨hadmS, hmodS⟩ := FiveList.lieModel_of_isComponent_statedSp hp (by norm_num) hf hK
      (by omega) hN'
    obtain ⟨h1, -, -⟩ := eq_five_of_lieModel_PSL_two_two hN'm (by norm_num) hadmS hmodS
    exact absurd h1 (by decide)

end Classes

end CFSG.SeitzReduction.RankOne
