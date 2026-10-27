module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4LayerA
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutF
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4OutII

public noncomputable section

namespace CFSG.ComponentClassification.CatFactsSp4

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag Subgroup
open CatalogueBSymplecticB CatalogueBAlternatingIsometry

theorem card_le_two_of_forall {G : Type*} [Group G] [Finite G] {Z : Subgroup G} {u : G}
    (h : ∀ z ∈ Z, z = 1 ∨ z = u) : Nat.card Z ≤ 2 := by
  have hsub : (Z : Set G) ⊆ {1, u} := fun z hz => by
    rcases h z hz with h | h <;> simp [h]
  calc Nat.card Z = (Z : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ({1, u} : Set G).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({u} : Set G).ncard + 1 := Set.ncard_insert_le 1 {u}
    _ = 2 := by rw [Set.ncard_singleton]

theorem card_center_SL2_le (F : Type*) [Field F] [Finite F] :
    Nat.card (center (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ 2 := by
  refine card_le_two_of_forall (u := (⟨-1, by simp [det_fin_two]⟩ :
    Matrix.SpecialLinearGroup (Fin 2) F)) fun z hz => ?_
  obtain ⟨r, hr, hzr⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).mp hz
  rw [Fintype.card_fin, pow_two] at hr
  rcases mul_self_eq_one_iff.mp hr with rfl | rfl
  · left
    ext i j
    rw [← hzr]
    simp [Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
  · right
    ext i j
    rw [← hzr]
    by_cases hij : i = j <;> simp [hij, Matrix.scalar_apply]

variable {K : Type} [Field K]

theorem card_center_fixOf_nonsquare {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (A : gsp 2 K) {d : K} (hd0 : d ≠ 0) (hdsq : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • 1)
    (hμ : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ * formJ 2 K *
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = d • formJ 2 K) :
    Nat.card (center (fixOf (conjSp 2 K A))) ≤ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hp.pos f).ne')
  set Ag : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K) :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv (matrixLinIso (A : GL (Fin 2 ⊕ Fin 2) K))
    with hAgdef
  have hAg : ∀ v, (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) v =
      ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v := fun v => rfl
  have hdim : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 2 * 2 := finrank_standard
  have hAns : ∀ c : K, (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) ≠ c • 1 := by
    intro c hc
    apply hdsq c
    set e : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 with he
    have h1 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e =
        c • e := by
      have := LinearMap.congr_fun hc e
      rwa [hAg] at this
    have h2 : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        (((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ e) =
        d • e := by rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
    rw [h1, mulVec_smul, h1, smul_smul] at h2
    have h3 := congrFun h2 (Sum.inl 0)
    simp only [he, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h3
    rw [sq]
    exact h3
  have hAA' : (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) * (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) =
      d • 1 := by
    apply LinearMap.ext
    intro v
    rw [Module.End.mul_apply, hAg, hAg, mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
    rfl
  have hμ' : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)ᵀ *
      formJ 2 K * ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) =
      ((Units.mk0 d hd0 : Kˣ) : K) • formJ 2 K := by rw [Units.val_mk0]; exact hμ
  have hAμ : ∀ v w, pairedSympForm K 2 ((Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      ((Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)) w) = d * pairedSympForm K 2 v w := fun v w =>
    matrix_similitude _ (Units.mk0 d hd0) hμ' v w
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure
    hp hp2 hf hK (r := 2) (by norm_num) hdim SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate hAns hd0 hAA' hAμ
  obtain ⟨-, hF, hcard, hfinrank, -, -, -, -, hpos, -⟩ := hnonsplit hdsq
  obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos (div_self hd0)
  let : Field (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K))) :=
    hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField
      (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))) := by
    rw [hcard]
    exact ((hp.odd_of_ne_two hp2).pow).pow
  have := finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField (Ag : Module.End K (Fin 2 ⊕ Fin 2 → K)))
      (Fin 2 ⊕ Fin 2 → K) :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  let e := (fixOfConjSpEquiv A).trans (evaluationIsometryEquiv (pairedSympForm K 2) Ag
    (isometryGroup BE) (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w) (mem_isometryGroup_iff BE) hiff)
  obtain ⟨e'⟩ := exists_planeIsometryEquivSL BE hBEalt hBEnd (by omega)
  rw [Nat.card_congr (Subgroup.centerCongr (e.trans e')).toEquiv]
  exact card_center_SL2_le _

theorem card_center_fixOf_field [Finite K] (hodd : Odd (Nat.card K)) (A : gsp 2 K)
    (σ : K ≃+* K) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (d : Kˣ)
    (hd : (A : GL (Fin 2 ⊕ Fin 2) K) *
        CatalogueBHigherLinearField.glFieldEquiv (Fin 2 ⊕ Fin 2) σ (A : GL (Fin 2 ⊕ Fin 2) K) =
      GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) d) :
    Nat.card (center (fixOf (conjSp 2 K A * fieldSp 2 K σ))) ≤ 2 := by
  have h2 := two_ne_zero_of_odd_card hodd
  set μ := multiplierUnit A with hμdef
  have hμ := multiplierUnit_spec A
  have hdim : 0 < Module.finrank K (Fin 2 ⊕ Fin 2 → K) := by rw [finrank_standard]; norm_num
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2
    hσ1 h2 hdim (pairedSympForm K 2) SymplecticFlag.pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ)
    μ d (semilinearCoordMap_smul _ σ) (semilinearCoordMap_form _ σ μ hμ)
    (semilinearCoordMap_sq _ σ hσ2 d hd)
  obtain ⟨-, -, -, -, hfin, hfinrank, -, hB0alt, hB0nd, -, e₂, -⟩ := hall b c hb hc
  let e₁ : fixOf (conjSp 2 K A * fieldSp 2 K σ) ≃* semilinearSymplecticCentralizer
      (pairedSympForm K 2) (semilinearCoordMap (A : GL (Fin 2 ⊕ Fin 2) K) σ) :=
    ((statedSpIsometryEquiv (r := 2) (K := K)).subgroupMap _).trans
      (MulEquiv.subgroupCongr (map_fixOf_conjSp_fieldSp A σ))
  rw [finrank_standard] at hfinrank
  obtain ⟨m, hm, ⟨e₃⟩⟩ := exists_isometryEquiv_symplectic _ hB0alt hB0nd
  have hm2 : m = 2 := by omega
  subst hm2
  have hkodd := CatalogueBOrthogonalFieldFixed.subfield_card_odd hodd
    (CatalogueBLinearTwoDescent.fixedSubfield K σ)
  have h2k := two_ne_zero_of_odd_card hkodd
  let e₄ := MulEquiv.subgroupCongr (ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic (n := 2)
    (K := CatalogueBLinearTwoDescent.fixedSubfield K σ)).symm
  rw [Nat.card_congr (Subgroup.centerCongr (((e₁.trans e₂).trans e₃).trans e₄)).toEquiv,
    LieType.Universal.Symplectic.center_eq, card_spScalars h2k]

theorem isSimpleGroup_map_fixOf [Finite K] (h2 : (2 : K) ≠ 0) (θ : MulAut (StatedSp 2 K))
    (hZ : ∀ z ∈ spScalars 2 K, θ z = z) (hQ : CFSG.IsQuasisimple (fixOf θ))
    (hc : Nat.card (center (fixOf θ)) ≤ 2) : IsSimpleGroup ((fixOf θ).map (proj 2 K)) := by
  have hle : spScalars 2 K ≤ fixOf θ := fun z hz => hZ z hz
  have hker : (fixProj θ).ker = center (fixOf θ) := by
    apply Subgroup.eq_of_le_of_card_ge (ker_fixProj_le_center θ)
    rw [ker_fixProj, Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, card_spScalars h2]
    exact hc
  have : IsSimpleGroup (fixOf θ ⧸ center (fixOf θ)) := hQ.2.1
  exact ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (fixProj θ)
      ((proj 2 K).subgroupMap_surjective (fixOf θ)))).symm.isSimpleGroup

theorem layerOf_fixOf_eq [Finite K] (h2 : (2 : K) ≠ 0) (θ : MulAut (StatedSp 2 K))
    {α : MulAut (StatedProj (StatedSp 2 K))} (hθα : ∀ g, α (proj 2 K g) = proj 2 K (θ g))
    (hZ : ∀ z ∈ spScalars 2 K, θ z = z) (hQ : CFSG.IsQuasisimple (fixOf θ))
    (h4 : 4 ∣ Nat.card (fixOf θ)) : layerOf (fixOf α) = (fixOf θ).map (proj 2 K) := by
  have hq : CFSG.IsQuasisimple ((fixOf θ).map (proj 2 K)) :=
    LocalCores.isQuasisimple_of_surjective hQ (fixProj θ)
      ((proj 2 K).subgroupMap_surjective (fixOf θ)) (ker_fixProj_le_center θ)
  have he : Even (Nat.card ((fixOf θ).map (proj 2 K))) := by
    have hc := card_map_fixOf_mul_two h2 θ hZ
    obtain ⟨m, hm⟩ := h4
    refine ⟨m, ?_⟩
    omega
  refine layerOf_eq_of_unique (map_fixOf_le θ hθα)
    (isPComponent_two_of_quasisimple' (map_fixOf_le θ hθα) hq
      (map_fixOf_normal θ hθα).isSubnormal he) fun M hMX hM => ?_
  exact eq_map_fixOf_of_isPComponent θ hθα hQ hMX hM

end CFSG.ComponentClassification.CatFactsSp4
