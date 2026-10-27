module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviBaseChange
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetSix
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinear

public section

namespace CFSG.SeitzReduction.E6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv)

section Entrywise

variable {n : ℕ} {k K : Type} [Field k] [Field K]

theorem map_slConjugation (ι : k →+* K) (A : GL (Fin n) k)
    (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Matrix.SpecialLinearGroup.map ι (CatalogueBHigherLinearAction.slConjugation n k A g) =
      CatalogueBHigherLinearAction.slConjugation n K (Matrix.GeneralLinearGroup.map ι A)
        (Matrix.SpecialLinearGroup.map ι g) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CatalogueBHigherLinearAction.slConjugation_matrix,
    CatalogueBHigherLinearAction.slConjugation_matrix, ← map_inv, RingHom.mapMatrix_apply,
    Matrix.map_mul, Matrix.map_mul, Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem map_slFieldAut (ι : k →+* K) {ρ : k ≃+* k} {ρ' : K ≃+* K}
    (h : ∀ c, ρ' (ι c) = ι (ρ c)) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Matrix.SpecialLinearGroup.map ι (CatalogueBHigherLinearField.slFieldAut (Fin n) k ρ g) =
      CatalogueBHigherLinearField.slFieldAut (Fin n) K ρ' (Matrix.SpecialLinearGroup.map ι g) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  change ι (CatalogueBHigherLinearField.slFieldEquiv (Fin n) ρ g i j) =
    CatalogueBHigherLinearField.slFieldEquiv (Fin n) ρ' (Matrix.SpecialLinearGroup.map ι g) i j
  rw [CatalogueBHigherLinearField.slFieldEquiv_entry, CatalogueBHigherLinearField.slFieldEquiv_entry,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, h]

theorem map_slGraphAut (ι : k →+* K) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Matrix.SpecialLinearGroup.map ι (CatalogueBGraphForm.slGraphAut n k g) =
      CatalogueBGraphForm.slGraphAut n K (Matrix.SpecialLinearGroup.map ι g) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CatalogueBGraphForm.slGraphAut_matrix,
    CatalogueBGraphForm.slGraphAut_matrix, ← map_inv, Matrix.SpecialLinearGroup.map_apply_coe]
  rfl

theorem conjAut_mul_fieldAut_mul_dualAut_pow_eq (A : GL (Fin n) K) (ρ : K ≃+* K) (ε : ℕ) :
    conjAut n K A * fieldAut n K ρ * dualAut n K ^ ε =
      descendAut n K (CatalogueBHigherLinearAction.slConjugation n K A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) K ρ * CatalogueBGraphForm.slGraphAut n K ^ ε) := by
  simp only [LinearFlag.conjAut, LinearFlag.fieldAut, LinearFlag.dualAut, map_mul, map_pow,
    MonoidHom.comp_apply]

theorem map_std_apply (ι : k →+* K) (A : GL (Fin n) k) {ρ : k ≃+* k} {ρ' : K ≃+* K}
    (h : ∀ c, ρ' (ι c) = ι (ρ c)) {ε : ℕ} (hε : ε ≤ 1) (g : Matrix.SpecialLinearGroup (Fin n) k) :
    Matrix.SpecialLinearGroup.map ι ((CatalogueBHigherLinearAction.slConjugation n k A *
        CatalogueBHigherLinearField.slFieldAut (Fin n) k ρ *
          CatalogueBGraphForm.slGraphAut n k ^ ε) g) =
      (CatalogueBHigherLinearAction.slConjugation n K (Matrix.GeneralLinearGroup.map ι A) *
        CatalogueBHigherLinearField.slFieldAut (Fin n) K ρ' *
          CatalogueBGraphForm.slGraphAut n K ^ ε) (Matrix.SpecialLinearGroup.map ι g) := by
  interval_cases ε
  · simp only [pow_zero, mul_one, MulAut.mul_apply]
    rw [map_slConjugation, map_slFieldAut ι h]
  · simp only [pow_one, MulAut.mul_apply]
    rw [map_slConjugation, map_slFieldAut ι h, map_slGraphAut]

end Entrywise

theorem mulAut_congr_apply_apply {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (f : MulAut X)
    (y : Y) : MulAut.congr φ f y = φ (f (φ.symm y)) :=
  rfl

section Model

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def a5LeviProjEquiv : projectiveSL 6 K ≃* a5Levi K :=
  (CatalogueBLinearHigherB.nativeEquiv 6 K).trans (a5LeviEquiv K)

variable {K}

theorem a5LeviProjEquiv_proj (g : Matrix.SpecialLinearGroup (Fin 6) K) :
    a5LeviProjEquiv K (proj 6 K g) = slToA5Levi g := by
  refine Subtype.ext ?_
  rw [a5LeviProjEquiv, MulEquiv.trans_apply, CatalogueBLinearHigherB.nativeEquiv_proj,
    coe_a5LeviEquiv_mk]
  rfl

@[expose] noncomputable def a5LeviFieldAut (σ : K ≃+* K) : MulAut (a5Levi K) :=
  MulAut.congr (a5LeviProjEquiv K) (fieldAut 6 K σ)

theorem a5LeviFieldAut_apply (σ : K ≃+* K) (x : a5Levi K) :
    a5LeviFieldAut σ x = a5LeviBaseChange (σ : K →+* K) x := by
  obtain ⟨g, rfl⟩ := slToA5Levi_surjective x
  rw [a5LeviBaseChange_slToA5Levi, a5LeviFieldAut, mulAut_congr_apply_apply,
    ← a5LeviProjEquiv_proj g, MulEquiv.symm_apply_apply, fieldAut_proj, a5LeviProjEquiv_proj]
  rfl

theorem fixedSubgroup_a5LeviFieldAut {k : Type} [Field k] [Finite k] [CharP k 2] (ι : k →+* K)
    {σ : K ≃+* K} (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) (hσ : ∀ x : K, σ (σ x) = x) :
    fixedSubgroup (a5LeviFieldAut σ) = (a5LeviBaseChange ι).range := by
  rw [MonoidHom.range_eq_map, map_a5LeviBaseChange_eq_eqLocus ι (σ : K →+* K) hfix hσ]
  ext x
  change a5LeviFieldAut σ x = x ↔ a5LeviBaseChange (σ : K →+* K) x = x
  rw [a5LeviFieldAut_apply]

theorem commutator_top_a5Levi (k : Type) [Field k] [Finite k] [CharP k 2] :
    ⁅(⊤ : Subgroup (a5Levi k)), (⊤ : Subgroup (a5Levi k))⁆ = (⊤ : Subgroup (a5Levi k)) :=
  (isQuasisimple_a5Levi (K := k)).1.commutator_eq_top

theorem exists_mulAut_a5LeviBaseChange_comm {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) (δ : MulAut (a5Levi k)) :
    ∃ δ' : MulAut (a5Levi K), ∀ g, δ' (a5LeviBaseChange ι g) = a5LeviBaseChange ι (δ g) := by
  obtain ⟨A, ρ, ε, hε, hδ⟩ := (automorphism_generation (K := k) (by norm_num : 3 ≤ 6)).2
    (MulAut.congr (a5LeviProjEquiv k).symm δ)
  obtain ⟨ρ', hρ'⟩ := F4Pilot.exists_ringEquiv_comp_eq ι ρ
  refine ⟨MulAut.congr (a5LeviProjEquiv K) (conjAut 6 K (Matrix.GeneralLinearGroup.map ι A) *
    fieldAut 6 K ρ' * dualAut 6 K ^ ε), fun x => ?_⟩
  obtain ⟨g, rfl⟩ := slToA5Levi_surjective x
  have hδg : δ (slToA5Levi g) = a5LeviProjEquiv k
      ((conjAut 6 k A * fieldAut 6 k ρ * dualAut 6 k ^ ε) (proj 6 k g)) := by
    rw [← hδ, mulAut_congr_apply_apply, MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
      a5LeviProjEquiv_proj]
  rw [hδg, a5LeviBaseChange_slToA5Levi, mulAut_congr_apply_apply,
    ← a5LeviProjEquiv_proj (Matrix.SpecialLinearGroup.map ι g), MulEquiv.symm_apply_apply,
    conjAut_mul_fieldAut_mul_dualAut_pow_eq, descendAut_proj,
    conjAut_mul_fieldAut_mul_dualAut_pow_eq, descendAut_proj, a5LeviProjEquiv_proj,
    a5LeviProjEquiv_proj, a5LeviBaseChange_slToA5Levi, map_std_apply ι A hρ' hε]

end Model

theorem fixedSubgroup_mulAut_conj {X : Type*} [Group X] (z : X) :
    fixedSubgroup (MulAut.conj z) = centralizer ({z} : Set X) := by
  ext y
  change z * y * z⁻¹ = y ↔ y ∈ centralizer ({z} : Set X)
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

section Descent

variable {K : Type} [Field K] [Finite K]

theorem not_mem_range_conj_of_isComponent [CharP K 2] {e f₀ : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {β : MulAut (projectiveSL 6 K)} (hβ : β * β = 1)
    {C : Subgroup (fixedSubgroup β)} (hC : IsComponent C) (hCm : LieModel C .PSL 6 2 f₀)
    (hf₀ : f₀ ≠ e) :
    β ∉ (MulAut.conj : projectiveSL 6 K →* MulAut (projectiveSL 6 K)).range := by
  rintro ⟨z, rfl⟩
  set χ := a5LeviProjEquiv K with hχ
  have hZ : center (projectiveSL 6 K) = ⊥ := by
    rw [← map_center_eq χ.symm, center_a5Levi_eq_bot, Subgroup.map_bot]
  have hzz : z * z = 1 := by
    have h2 : z * z ∈ center (projectiveSL 6 K) := by
      rw [mem_center_iff]
      intro y
      have h3 := DFunLike.congr_fun hβ y
      rw [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (z * z) = z * (z * y * z⁻¹) * z⁻¹ * (z * z) := by rw [h3]
        _ = z * z * y := by group
    rw [hZ, mem_bot] at h2
    exact h2
  by_cases hz1 : z = 1
  ·
    subst hz1
    have htop : fixedSubgroup (MulAut.conj (1 : projectiveSL 6 K)) = ⊤ := by
      rw [map_one]
      exact eq_top_iff.2 fun y _ => rfl
    let ε₀ : fixedSubgroup (MulAut.conj (1 : projectiveSL 6 K)) ≃* a5Levi K :=
      ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).trans χ
    have : IsSimpleGroup (fixedSubgroup (MulAut.conj (1 : projectiveSL 6 K))) :=
      have : IsSimpleGroup (a5Levi K) := isSimpleGroup_a5Levi
      ε₀.isSimpleGroup
    have hCtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hC
    let εC : C ≃* a5Levi K := ((MulEquiv.subgroupCongr hCtop).trans Subgroup.topEquiv).trans ε₀
    have hCe : LieModel C .PSL 6 2 e :=
      LieType.CurtisTits.lieModel_of_mulEquiv εC.symm (lieModel_a5Levi hK)
    have hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL 6 2 e :=
      ⟨Nat.prime_two, he, by norm_num, by simp, by simp⟩
    obtain ⟨-, -, he'⟩ := LinearPilot.slmEvenTypeDetAt_six C f₀ .PSL 6 e hCm hadm hCe
    exact hf₀ he'.symm
  ·
    have hzord : orderOf z = 2 := orderOf_eq_prime (by rw [sq, hzz]) hz1
    let Ψ : fixedSubgroup (MulAut.conj z) ≃* centralizer ({z} : Set (projectiveSL 6 K)) :=
      MulEquiv.subgroupCongr (fixedSubgroup_mulAut_conj z)
    exact OutcomeLocal.even_linear_involution_centralizers_component_free he (by norm_num) hK z
      hzord _ (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hC)

theorem exists_eq_conj_mul_fieldAut_mul_conj_inv_of_isComponent {e f₀ : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {β : MulAut (projectiveSL 6 K)} (hβ : β * β = 1)
    {C : Subgroup (fixedSubgroup β)} (hC : IsComponent C) (hCm : LieModel C .PSL 6 2 f₀)
    (hf₀ : f₀ ≠ e) :
    ∃ H : GL (Fin 6) K, β = conjAut 6 K H * fieldAut 6 K σ * (conjAut 6 K H)⁻¹ := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two he hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβi := not_mem_range_conj_of_isComponent he hK hβ hC hCm hf₀
  have hβ1 : β ≠ 1 := fun h => hβi ⟨1, by rw [map_one, h]⟩
  have hβord : orderOf β = 2 := orderOf_eq_prime (by rw [sq, hβ]) hβ1
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  set ν := CatalogueBLinearHigherB.nativeEquiv 6 K with hν
  have htrans : ∀ γ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K),
      MulAut.congr ν β = γ → ∃ C' : Subgroup (fixedSubgroup γ), IsComponent C' ∧
        LieModel C' .PSL 6 2 f₀ ∧ LieModel (C' ⧸ center C') .PSL 6 2 f₀ := by
    intro γ hγ
    let Ψ : fixedSubgroup β ≃* fixedSubgroup γ :=
      (fixedSubgroupCongrEquiv ν β).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hγ))
    have hC' := CFSG.LocalCores.isComponent_map_mulEquiv Ψ hC
    have hm : LieModel (C.map Ψ.toMonoidHom) .PSL 6 2 f₀ :=
      LieType.CurtisTits.lieModel_of_mulEquiv (C.equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hCm
    exact ⟨_, hC', hm, LinearPilot.lieModel_quotient_center_of_center_eq_bot
      (F4Pilot.center_eq_bot_of_isQuasisimple hC'.1 (LinearPilot.isSimpleGroup_of_lieModel_PSL hm))
        hm⟩
  have hordν : ∀ γ : MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 6) K),
      MulAut.congr ν β = γ → orderOf γ = 2 := fun γ hγ => by
    rw [← hγ]
    exact (orderOf_injective (MulAut.congr ν).toMonoidHom (MulAut.congr ν).injective β).trans hβord
  obtain ⟨A, ρ, ε, hε, hβA⟩ := (automorphism_generation (K := K) (by norm_num : 3 ≤ 6)).2 β
  interval_cases ε
  ·
    rw [pow_zero, mul_one] at hβA
    by_cases hρ : ρ = 1
    · exfalso
      rw [hρ, map_one, mul_one] at hβA
      have h2 : conjAut 6 K A ^ 2 = 1 := by rw [← hβA, sq, hβ]
      have h1 : conjAut 6 K A ≠ 1 := by rw [← hβA]; exact hβ1
      obtain ⟨t, -, ht⟩ := OutcomeLocal.exists_involution_eq_conjAut (by norm_num) A h2 h1
      exact hβi ⟨t, by rw [hβA, ht]⟩
    · have hsq : (conjAut 6 K A * fieldAut 6 K ρ) ^ 2 = 1 := by rw [← hβA, sq, hβ]
      obtain ⟨-, hρpow, H, hH⟩ :=
        even_linear_field_involution_descent he hK (by norm_num) A ρ hρ hsq
      obtain ⟨-, hσpow⟩ := even_and_eq_pow_of_involution he hK hσ1 hσσ
      have hρσ : ρ = σ := RingEquiv.ext fun x => by rw [hρpow, hσpow]
      exact ⟨H, by rw [hβA, hH, hρσ]⟩
  ·
    rw [pow_one] at hβA
    exfalso
    by_cases hρ : ρ = 1
    · rw [hρ, map_one, mul_one] at hβA
      have hγ : MulAut.congr ν β = CatalogueBGraphForm.pureGraphAction 6 K A := by
        rw [hβA, CatalogueBLinearHigherB.congr_pureGraph]
      obtain ⟨C', hC', -, hC'q⟩ := htrans _ hγ
      rcases F4Pilot.psl_graph_cases he hK (by norm_num) A (hordν _ hγ) with
        ⟨r, hr, -, ⟨Φ⟩⟩ | hch
      · exact LinearPilot.no_component_statedSp LinearPilot.slmEvenTypeDetAt_six hK hr Φ hC'
          (by norm_num) hC'q
      · exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch C'
          (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hC')
    · have hγ : MulAut.congr ν β = CatalogueBGraphField.graphFieldAction 6 K A ρ := by
        rw [hβA, CatalogueBLinearHigherB.congr_graphField]
      obtain ⟨C', hC', -, hC'q⟩ := htrans _ hγ
      obtain ⟨hadm', hmD⟩ := LinearPilot.psl_graphField_pComponents (by norm_num) he hK A ρ hρ
        (hordν _ hγ) C' (LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hC')
      obtain ⟨htt, -, -⟩ := LinearPilot.typeDet_of_simple LinearPilot.slmEvenTypeDetAt_six hC'.1
        (LinearPilot.isSimpleGroup_of_lieModel_PSU hmD) hC'q hadm' hmD
      exact absurd htt (by decide)

end Descent

section Normalize

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit
  [CharP K 2] in
theorem natCard_lt_of_fix {k : Type} [Field k] [Finite k] (ι : k →+* K) {σ : K ≃+* K}
    (hσ : σ ≠ 1) (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) : Nat.card k < Nat.card K := by
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra hall
    exact hσ (RingEquiv.ext fun x => not_not.1 fun h => hall ⟨x, h⟩)
  have hns : ¬Function.Surjective ι := fun hs => hc ((hfix c).2 (hs c))
  by_contra hle
  exact hns (ι.injective.bijective_of_nat_card_le (not_lt.1 hle)).2

theorem exists_mulEquiv_a5LeviBaseChange_eq {k : Type} [Field k] [Finite k] [CharP k 2]
    (ι : k →+* K) {σ : K ≃+* K} (hσ : orderOf σ = 2)
    (hfix : ∀ x : K, σ x = x ↔ x ∈ Set.range ι) {M : Type} [Group M] (ψ : a5Levi K ≃* M)
    {θ : MulAut M} (hθ : θ * θ = 1) (ε : a5Levi k →* M) (hε : Function.Injective ε)
    (hεr : ε.range = perfectCore (MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M))) :
    ∃ ψ' : a5Levi K ≃* M, ∀ g, ψ' (a5LeviBaseChange ι g) = ε g := by
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    exact absurd hσ (by norm_num)
  have hσσ : σ * σ = 1 := by rw [← sq, ← hσ, pow_orderOf_eq_one]
  have hσσx : ∀ x : K, σ (σ x) = x := fun x => by rw [← RingAut.mul_apply, hσσ]; rfl
  obtain ⟨e, he, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨f₀, -, hk⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := k)
  have hf₀ : f₀ ≠ e := by
    rintro rfl
    exact absurd (hk.trans hK.symm) (natCard_lt_of_fix ι hσ1 hfix).ne
  set Λ := a5LeviProjEquiv K with hΛ
  set χ : M ≃* projectiveSL 6 K := ψ.symm.trans Λ.symm with hχ
  set β₀ := MulAut.congr χ θ with hβ₀def
  have hβ₀ : β₀ * β₀ = 1 := by rw [hβ₀def, ← map_mul, hθ, map_one]
  set F := fixedSubgroup θ with hF
  set D₀ := perfectCore F with hD₀
  have hD₀F : D₀ ≤ F := CFSG.Quasithin.perfectCore_le F
  let eD₀ : a5Levi k ≃* D₀.subgroupOf F :=
    ((MonoidHom.ofInjective hε).trans (MulEquiv.subgroupCongr hεr)).trans
      (subgroupOfEquivOfLe hD₀F).symm
  have hcomp : IsComponent (D₀.subgroupOf F) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv eD₀ isQuasisimple_a5Levi,
      (CFSG.Quasithin.perfectCore_normal F).isSubnormal⟩
  have hm : LieModel (D₀.subgroupOf F) .PSL 6 2 f₀ :=
    LieType.CurtisTits.lieModel_of_mulEquiv eD₀ (lieModel_a5Levi hk)
  let Ψ := fixedSubgroupCongrEquiv χ θ
  obtain ⟨H, hH⟩ := exists_eq_conj_mul_fieldAut_mul_conj_inv_of_isComponent he hK hσ hβ₀
    (CFSG.LocalCores.isComponent_map_mulEquiv Ψ hcomp)
    (LieType.CurtisTits.lieModel_of_mulEquiv
      ((D₀.subgroupOf F).equivMapOfInjective Ψ.toMonoidHom Ψ.injective) hm) hf₀
  set γ := MulAut.congr Λ (conjAut 6 K H) with hγ
  set ψ₁ : a5Levi K ≃* M := γ.trans ψ with hψ₁
  have hχψ₁ : ∀ y, χ (ψ₁ y) = conjAut 6 K H (Λ.symm y) := fun y => by
    rw [hχ, hψ₁, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hγ,
      mulAut_congr_apply_apply, MulEquiv.symm_apply_apply]
  have hθψ₁ : ∀ x, θ (ψ₁ x) = ψ₁ (a5LeviFieldAut σ x) := by
    intro x
    apply χ.injective
    have h1 : χ (θ (ψ₁ x)) = β₀ (χ (ψ₁ x)) := by
      rw [hβ₀def, mulAut_congr_apply_apply, MulEquiv.symm_apply_apply]
    rw [h1, hH, hχψ₁, hχψ₁, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, a5LeviFieldAut, mulAut_congr_apply_apply,
      MulEquiv.symm_apply_apply]
  have hfixθ : MonoidHom.eqLocus θ.toMonoidHom (MonoidHom.id M) =
      (a5LeviBaseChange ι).range.map ψ₁.toMonoidHom := by
    ext y
    obtain ⟨x, rfl⟩ := ψ₁.surjective y
    rw [mem_map_equiv, ψ₁.symm_apply_apply, ← fixedSubgroup_a5LeviFieldAut ι hfix hσσx]
    change θ (ψ₁ x) = ψ₁ x ↔ a5LeviFieldAut σ x = x
    rw [hθψ₁]
    exact ψ₁.injective.eq_iff
  have hperf : ⁅(a5LeviBaseChange ι).range.map ψ₁.toMonoidHom,
      (a5LeviBaseChange ι).range.map ψ₁.toMonoidHom⁆ =
        (a5LeviBaseChange ι).range.map ψ₁.toMonoidHom := by
    rw [← map_commutator, MonoidHom.range_eq_map, ← map_commutator, commutator_top_a5Levi]
  have hrange : ε.range = (ψ₁.toMonoidHom.comp (a5LeviBaseChange ι)).range := by
    rw [hεr, hfixθ, CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf, MonoidHom.range_comp]
  have hinj₁ : Function.Injective (ψ₁.toMonoidHom.comp (a5LeviBaseChange ι)) :=
    ψ₁.injective.comp (a5LeviBaseChange_injective ι)
  set δ : MulAut (a5Levi k) := ((MonoidHom.ofInjective hε).trans
    (MulEquiv.subgroupCongr hrange)).trans (MonoidHom.ofInjective hinj₁).symm with hδdef
  have hδ : ∀ g, ψ₁ (a5LeviBaseChange ι (δ g)) = ε g := by
    intro g
    have h1 := (MonoidHom.ofInjective hinj₁).apply_symm_apply
      (MulEquiv.subgroupCongr hrange (MonoidHom.ofInjective hε g))
    have h2 := congrArg Subtype.val h1
    rw [MonoidHom.ofInjective_apply] at h2
    exact h2
  obtain ⟨δ', hδ'⟩ := exists_mulAut_a5LeviBaseChange_comm ι δ
  exact ⟨δ'.trans ψ₁, fun g => by rw [MulEquiv.trans_apply, hδ', hδ]⟩

end Normalize

end CFSG.SeitzReduction.E6Pilot
