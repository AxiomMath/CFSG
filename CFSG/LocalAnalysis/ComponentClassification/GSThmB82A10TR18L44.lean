module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TR18Defs
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotAutU
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalModelFactsCharTwo
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEvenPSLGraph
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.RankThree.PartOne.KC.LinearSubfieldFixedPoints
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryTwoFieldData
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedL34

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace L44

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

private theorem exists_equiv_projectiveSL {S : Type} [Group S]
    (hL : Blueprint.LieModel S .PSL 4 2 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ 2 ∧
      Nonempty (S ≃* projectiveSL 4 K) := by
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := hL.statedClassicalModel (by decide)
  exact ⟨K, inferInstance, inferInstance, hK, ⟨eT.trans
    ((Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 4 K))⟩⟩

variable {K : Type} [Field K] [Finite K]

private theorem conjAut_mem_range_conj (hK : Nat.card K = 2 ^ 2) (A : GL (Fin 4) K) :
    conjAut 4 K A ∈ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
  refine conjAut_mem_range_conj_of_det_eq_pow (μ := Matrix.GeneralLinearGroup.det A) ?_
  have h3 : Matrix.GeneralLinearGroup.det A ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := Matrix.GeneralLinearGroup.det A)
    rw [Nat.card_units K, hK] at h
    simpa using h
  rw [pow_succ, h3, one_mul]

private theorem eq_one_of_commute {S : Type} [Group S] (e : S ≃* projectiveSL 4 K) {g : S}
    (hg : ∀ x : S, g * x = x * g) : g = 1 := by
  have hc : e g ∈ Subgroup.center (projectiveSL 4 K) := Subgroup.mem_center_iff.2 fun y => by
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, hg x]
  rw [RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num), Subgroup.mem_bot] at hc
  exact e.injective (hc.trans (map_one e).symm)

private theorem coreActionKernel_eq_bot {S : Type} [Group S] [Finite S] {F T : Subgroup S}
    (hF : IsSimpleGroup F) (hC : ∀ g : S, (∀ x ∈ F, g * x = x * g) → g = 1) (hTF : T ≤ F)
    (hT : IsPComponent 2 (T.subgroupOf F))
    (hcard : Nat.card (↥T ⧸ Open.fusionZStar ↥T) ≠ 1) : coreActionKernel T = ⊥ := by
  have htop : T.subgroupOf F = ⊤ := GrSLit.eq_top_of_isPComponent_of_isSimpleGroup hT
  have hFT : F ≤ T := fun x hx => by
    have h : (⟨x, hx⟩ : F) ∈ T.subgroupOf F := htop ▸ Subgroup.mem_top _
    exact h
  obtain rfl : T = F := le_antisymm hTF hFT
  have hO : pPrimeCore 2 ↥T = ⊥ := by
    rcases hF.eq_bot_or_eq_top_of_normal (pPrimeCore 2 ↥T) with h | h
    · exact h
    · refine absurd ?_ hcard
      have hZ : Open.fusionZStar ↥T = ⊤ :=
        eq_top_iff.2 (h ▸ Sol78.pPrimeCore_le_fusionZStar ↥T)
      rw [hZ]
      exact Subgroup.index_top
  rw [eq_bot_iff]
  intro g hg
  obtain ⟨-, hg⟩ := mem_coreActionKernel.1 hg
  rw [Subgroup.mem_bot]
  refine hC g fun x hx => ?_
  have h1 := hg x hx
  rw [hO, Subgroup.map_bot, Subgroup.mem_bot] at h1
  calc g * x = g * x * (x⁻¹ * g⁻¹ * x * g) := by rw [h1, mul_one]
    _ = x * g := by group

private theorem field_case (hK : Nat.card K = 2 ^ 2) {β : MulAut (projectiveSL 4 K)}
    {A : GL (Fin 4) K} {σ : K ≃+* K} (hσ : σ ≠ 1) (hβ : β = conjAut 4 K A * fieldAut 4 K σ)
    (hβ2 : β ^ 2 = 1)
    (hβo : β ∉ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range) :
    IsSimpleGroup (fixedSubgroup β) ∧
      ∀ g : projectiveSL 4 K, (∀ x ∈ fixedSubgroup β, g * x = x * g) → g = 1 := by
  obtain ⟨-, hσpow, H, hβH⟩ :=
    even_linear_field_involution_descent (by norm_num) hK (by norm_num) A σ hσ (hβ ▸ hβ2)
  rw [← hβ] at hβH
  have hx4 : ∀ x : K, x ^ 4 = x := fun x => by
    have := Fintype.ofFinite K
    have h := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, hK] at h
  have hσ2 : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [sq, RingAut.mul_apply, hσpow, hσpow, ← pow_mul]
    exact hx4 x
  set k := CatalogueBHigherLinearField.fixedField K σ
  have hk : ∀ x, x ∈ k ↔ σ x = x := CatalogueBHigherLinearField.mem_fixedField K σ
  have hpK : ¬ 2 ∣ Nat.card Kˣ := by
    rw [Nat.card_units K, hK]
    decide
  have hfix := RankThree.PartOne.KCLinearSubfield.fixed_points_eq_range hk (n := 4)
    (by norm_num) (RankThree.PartOne.KCLinearSubfield.root_descent_of_not_dvd Nat.prime_two hk
      hσ2 hpK)
  have hFφ : fixedSubgroup (fieldAut 4 K σ) =
      (RankThree.PartOne.linearSubfieldInclusion 4 k).range :=
    Subgroup.ext fun x => Set.ext_iff.1 hfix x
  have hc : MulAut.congr (conjAut 4 K H) (fieldAut 4 K σ) = β :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (conjAut 4 K H) (fieldAut 4 K σ) =
      conjAut 4 K H * fieldAut 4 K σ * (conjAut 4 K H)⁻¹).trans hβH.symm
  have hFβ : fixedSubgroup β =
      (fixedSubgroup (fieldAut 4 K σ)).map (conjAut 4 K H).toMonoidHom := by
    rw [← hc]
    exact ExcSelector.fixedSubgroup_congr _ _
  refine ⟨?_, fun g hg => ?_⟩
  · have := (RankThree.PartOne.simple_nonabelian_range_linearSubfieldInclusion (K := K)
      (n := 4) (by norm_num) k).1
    exact (((CatLeafProof.fixedSubgroupCongrEquiv (conjAut 4 K H) (fieldAut 4 K σ)).trans
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))).symm.trans
      (MulEquiv.subgroupCongr hFφ)).isSimpleGroup
  · set c : MulAut (projectiveSL 4 K) := conjAut 4 K H
    set h : projectiveSL 4 K := c⁻¹ g
    have hhc : ∀ y ∈ fixedSubgroup (fieldAut 4 K σ), h * y = y * h := by
      intro y hy
      have hy' : c y ∈ fixedSubgroup β := by
        rw [hFβ]
        exact ⟨y, hy, rfl⟩
      have h1 := congrArg (fun z => c⁻¹ z) (hg _ hy')
      simp only [map_mul, MulAut.inv_apply_self] at h1
      exact h1
    have hmem : MulAut.conj h ∈ fixingSubgroup (MulAut (projectiveSL 4 K))
        ((RankThree.PartOne.linearSubfieldInclusion 4 k).range : Set (projectiveSL 4 K)) := by
      rw [mem_fixingSubgroup_iff]
      intro y hy
      rw [MulAut.smul_def, MulAut.conj_apply, hhc y (by rw [hFφ]; exact hy),
        mul_inv_cancel_right]
    rw [RankThree.PartOne.fixingSubgroup_range_linearSubfieldInclusion hk (by norm_num)] at hmem
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hφ2 : fieldAut 4 K σ ^ 2 = 1 := by rw [← map_pow, hσ2, map_one]
    rw [zpow_eq_zpow_emod' m hφ2, Nat.cast_ofNat] at hm
    have hh1 : h = 1 := by
      rcases Int.emod_two_eq_zero_or_one m with h0 | h0
      · rw [h0, zpow_zero] at hm
        exact RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)
          (hm.symm.trans (map_one _).symm)
      · exfalso
        rw [h0, zpow_one] at hm
        obtain ⟨z, hz⟩ := conjAut_mem_range_conj hK H
        apply hβo
        refine ⟨z * h * z⁻¹, ?_⟩
        rw [map_mul, map_mul, map_inv, hz, ← hm, hβH]
    have hgh : g = c h := (MulAut.apply_inv_self _ c g).symm
    rw [hgh, hh1, map_one]

private theorem graph_case (hK : Nat.card K = 2 ^ 2) (A : GL (Fin 4) K)
    (hsq : (conjAut 4 K A * dualAut 4 K) ^ 2 = 1) {X : Type} [Group X] [Finite X]
    (Ψ : X ≃* fixedSubgroup (conjAut 4 K A * dualAut 4 K)) {P : Subgroup X}
    (hP : IsPComponent 2 P) : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 979200 := by
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by norm_num) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨H, C, -, hconj, hCcase⟩, -⟩ :=
    UnitaryHigher.even_linear_pure_graph_involution_normal_forms (by norm_num) hK (by norm_num)
      A hsq
  have hc2 : MulAut.congr (conjAut 4 K H) (conjAut 4 K C * dualAut 4 K) =
      conjAut 4 K A * dualAut 4 K :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (conjAut 4 K H) (conjAut 4 K C * dualAut 4 K) =
      _).trans hconj.symm
  let Ψ' : X ≃* fixedSubgroup (conjAut 4 K C * dualAut 4 K) :=
    Ψ.trans ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc2)).symm.trans
      (CatLeafProof.fixedSubgroupCongrEquiv _ _).symm)
  rcases hCcase with ⟨h1, -⟩ | ⟨r, hr, hJ, -⟩
  ·
    exfalso
    have hβ : conjAut 4 K C * dualAut 4 K = dualAut 4 K := by
      rw [show C = 1 from Units.ext h1, map_one, one_mul]
    have hch : IsCharacteristicP 2 (fixedSubgroup (conjAut 4 K C * dualAut 4 K)) := by
      rw [hβ]
      exact CatLeafProof.isCharacteristicP_fixed_dualAut (by norm_num) hK le_rfl (by decide)
    exact CatLeafProof.not_isPComponent_of_isCharacteristicP
      (isCharacteristicP_of_mulEquiv Ψ'.symm hch) P hP
  ·
    obtain rfl : r = 2 := by omega
    obtain ⟨Φ⟩ := CatLeafProof.nonempty_fixed_canonical_equiv (by norm_num) hK (by norm_num) C
      (Or.inr ⟨2, hr, hJ⟩)
    have : Finite (GL (Fin 2 ⊕ Fin 2) K) := Finite.of_injective Units.val Units.val_injective
    let eSp : FourGroupEvenCanonical.matrixIsometryGroup (C : Matrix (Fin 4) (Fin 4) K) ≃*
        Open.StatedSp 2 K :=
      (MulEquiv.subgroupCongr (congrArg FourGroupEvenCanonical.matrixIsometryGroup hJ)).trans
        (OutcomeLocal.blockSwapIsometryEquivStatedSp (by norm_num))
    obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
      SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
        (X := Open.StatedSp 2 K) hK (by norm_num) ⟨MulEquiv.refl _⟩
    have : IsSimpleGroup (Open.StatedProj (Open.StatedSp 2 K)) :=
      ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
        (Or.inl (Or.inr (by rw [hK]; norm_num)))
    obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple_equiv
      (((Ψ'.trans Φ).trans eSp).trans eProj.symm) hP
    rw [Nat.card_congr eZ.toEquiv, Nat.card_congr eProj.toEquiv,
      SymplecticFlag.card_statedSp_two, hK]
    norm_num

private theorem graphField_case (hK : Nat.card K = 2 ^ 2) (A : GL (Fin 4) K) {σ : K ≃+* K}
    (hσ : σ ≠ 1) (hsq : CatalogueBGraphField.graphFieldAction 4 K A σ ^ 2 = 1) {X : Type}
    [Group X] [Finite X] (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction 4 K A σ))
    {P : Subgroup X} (hP : IsPComponent 2 P) : Nat.card (↥P ⧸ Open.fusionZStar ↥P) = 25920 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ψt : X ≃* CatalogueBGraphField.twistedFixedPSL 4 K A σ := Ψ
  have hP' := isPComponent_map_of_isPComponent 2 Ψt hP
  obtain ⟨-, ⟨E⟩⟩ :=
    CatalogueBGraphField.graphField_involution_fixed_pComponent_projectiveSpecialUnitary
      4 K (by norm_num) A σ hσ hsq (fun h => by simp at h) 2 Nat.prime_two _ hP'
  obtain ⟨hσ2, -⟩ :=
    CatalogueBGraphField.graphField_involution_conjugacy 4 K (by norm_num) A σ hσ hsq
  obtain ⟨-, hσc⟩ := even_and_eq_pow_of_involution (by norm_num) hK hσ (by rw [← sq]; exact hσ2)
  have hunitary : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσeq : σ = CatalogueBUnitaryTwo.unitaryFieldConjugation 2 1 hunitary :=
    RingEquiv.ext fun c => by rw [hσc, CatalogueBUnitaryTwo.unitaryFieldConjugation_apply]
  subst hσeq
  obtain ⟨eQ⟩ := CatLeafProof.nonempty_projectiveSpecialUnitary_equiv_statedProj (n := 4) hunitary
  have hadm : Open.StatedLieAdmissible .PSU 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
  have hstated :
      Open.StatedClassicalModel (Open.StatedProj (Open.StatedSU 4 (2 ^ 1) K)) .PSU 4 2 1 :=
    ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ 4 2 1 hstated).2
  obtain ⟨eZ⟩ := GrSLit.nonempty_fusionZStar_equiv_of_simple hP
    (((P.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ)
  rw [Nat.card_congr eZ.toEquiv, (Timmesfeld.card_statedClassicalModel_two hstated).2.1 rfl]
  decide

end L44

open L44 in
theorem outerNotSylowCentral_l44 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hL : Blueprint.LieModel S .PSL 4 2 2) : OuterNotSylowCentral S := by
  intro σ _ T hT
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL hL
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by norm_num) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact SeitzReduction.LinearPilot.mem_range_conj_of_fix_sylow_of_mulEquiv (by norm_num) e T σ hT

open L44 CFSG.LocalAnalysis.ComponentInitial LinearFlag in
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup) in
theorem fixedA8KernelTrivial_l44 {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (hL : Blueprint.LieModel S .PSL 4 2 2) : FixedA8KernelTrivial S := by
  intro Q hQ hQ2 T hTF hT hcard
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_equiv_projectiveSL hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : ∀ g : S, (∀ x : S, g * x = x * g) → g = 1 := fun g hg => eq_one_of_commute e hg
  have hcard1 : Nat.card (↥T ⧸ Open.fusionZStar ↥T) ≠ 1 := by
    rw [hcard]
    norm_num
  have hP : Nat.card (↥(T.subgroupOf (EvenPump.autFixed Q)) ⧸
      Open.fusionZStar ↥(T.subgroupOf (EvenPump.autFixed Q))) = 20160 := by
    obtain ⟨φ⟩ :=
      GrSLit.nonempty_fusionZStar_equiv_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hTF)
    rw [Nat.card_congr φ.toEquiv, hcard]
  have : Finite (MulAut S) :=
    Finite.of_injective (fun σ : MulAut S => (σ : S → S)) fun a b h => MulEquiv.ext (congrFun h)
  rcases (show Nat.card Q = 1 ∨ Nat.card Q = 2 by
    have := Nat.card_pos (α := Q)
    omega) with h1 | h2
  ·
    have hQb : Q = ⊥ := Subgroup.card_eq_one.1 h1
    have hFtop : EvenPump.autFixed Q = ⊤ := by
      refine eq_top_iff.2 fun l _ => EvenPump.mem_autFixed.2 fun r hr => ?_
      rw [hQb, Subgroup.mem_bot] at hr
      rw [hr, MulAut.one_apply]
    have hFs : IsSimpleGroup ↥(EvenPump.autFixed Q) :=
      ((MulEquiv.subgroupCongr hFtop).trans Subgroup.topEquiv).isSimpleGroup
    exact coreActionKernel_eq_bot hFs (fun g hg => hZ g fun x => hg x (hFtop ▸ Subgroup.mem_top x))
      hTF hT hcard1
  ·
    obtain ⟨⟨q, hqQ⟩, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (show Q ≠ ⊥ from fun h => by
      rw [h, Subgroup.card_bot] at h2
      norm_num at h2)
    have hq1 : q ≠ 1 := fun h => hq1 (Subtype.ext (by simpa using h))
    have hq2 : q * q = 1 := hQ q hqQ
    have hQq : zpowers q = Q := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hqQ) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hq2) hq1, h2])
    have hFq : ∀ l, l ∈ EvenPump.autFixed Q ↔ q l = l := by
      intro l
      rw [EvenPump.mem_autFixed]
      refine ⟨fun h => h q hqQ, fun h r hr => ?_⟩
      have hle : Q ≤ MulAction.stabilizer (MulAut S) l := by
        rw [← hQq, Subgroup.zpowers_le]
        exact MulAction.mem_stabilizer_iff.2 h
      exact MulAction.mem_stabilizer_iff.1 (hle hr)
    by_cases hin : q ∈ (MulAut.conj : S →* MulAut S).range
    ·
      exfalso
      obtain ⟨u, rfl⟩ := hin
      have huu : u * u = 1 := hZ _ fun x => by
        have h := congrArg (fun φ : MulAut S => φ x)
          (show MulAut.conj (u * u) = 1 by rw [map_mul]; exact hq2)
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc u * u * x = (u * u * x * (u * u)⁻¹) * (u * u) := by group
          _ = x * (u * u) := by rw [h]
      have hu : orderOf u = 2 :=
        orderOf_eq_prime (by rw [sq]; exact huu) fun h => hq1 (by rw [h, map_one])
      have hFC : EvenPump.autFixed Q = centralizer ({u} : Set S) := by
        ext l
        rw [hFq l, mem_centralizer_singleton_iff, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
          eq_comm]
      have hch := RankTwoClassical.isCharacteristicP_centralizer_of_psl_model
        (hL.statedClassicalModel (by decide)) u hu
      exact CatLeafProof.not_isPComponent_of_isCharacteristicP
        (isCharacteristicP_of_mulEquiv (MulEquiv.subgroupCongr hFC.symm) hch) _ hT
    ·
      set β := MulAut.congr e q with hβdef
      have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, sq, hq2, map_one]
      have hβo : β ∉ (MulAut.conj : projectiveSL 4 K →* MulAut (projectiveSL 4 K)).range := by
        rintro ⟨y, hy⟩
        refine hin ⟨e.symm y, (MulAut.congr e).injective ?_⟩
        rw [SeitzReduction.LinearPilot.mulAut_congr_conj, MulEquiv.apply_symm_apply, hy]
      have hFq' : EvenPump.autFixed Q = fixedSubgroup q := Subgroup.ext fun l => hFq l
      let Ψ : ↥(EvenPump.autFixed Q) ≃* ↥(fixedSubgroup β) :=
        (MulEquiv.subgroupCongr hFq').trans (CatLeafProof.fixedSubgroupCongrEquiv e q)
      obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 4) (by norm_num)
      obtain ⟨A, σ, ε, hε, hβeq⟩ := hgen β
      interval_cases ε
      · rw [pow_zero, mul_one] at hβeq
        by_cases hσ : σ = 1
        ·
          rw [hσ, map_one, mul_one] at hβeq
          exact absurd (hβeq ▸ conjAut_mem_range_conj hK A) hβo
        ·
          obtain ⟨hFs, hCβ⟩ := field_case hK hσ hβeq hβ2 hβo
          have hFs' : IsSimpleGroup ↥(EvenPump.autFixed Q) := Ψ.isSimpleGroup
          refine coreActionKernel_eq_bot hFs' (fun g hg => ?_) hTF hT hcard1
          have hg1 : e g = 1 := hCβ (e g) fun y hy => by
            rw [hβdef, ExcSelector.fixedSubgroup_congr] at hy
            obtain ⟨x, hx, rfl⟩ := hy
            change e g * e x = e x * e g
            rw [← map_mul, ← map_mul, hg x ((hFq x).2 hx)]
          exact e.injective (hg1.trans (map_one e).symm)
      · rw [pow_one] at hβeq
        exfalso
        by_cases hσ : σ = 1
        ·
          rw [hσ, map_one, mul_one] at hβeq
          have h := graph_case hK A (hβeq ▸ hβ2)
            (Ψ.trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβeq))) hT
          rw [hP] at h
          norm_num at h
        ·
          have hnat : MulAut.congr (CatalogueBLinearHigherB.nativeEquiv 4 K) β =
              CatalogueBGraphField.graphFieldAction 4 K A σ := by
            rw [hβeq]
            exact CatalogueBLinearHigherB.congr_graphField A σ
          have hsq : CatalogueBGraphField.graphFieldAction 4 K A σ ^ 2 = 1 := by
            rw [← hnat, ← map_pow, hβ2, map_one]
          have h := graphField_case hK A hσ hsq
            ((Ψ.trans (CatLeafProof.fixedSubgroupCongrEquiv _ β)).trans
              (MulEquiv.subgroupCongr (congrArg fixedSubgroup hnat))) hT
          rw [hP] at h
          norm_num at h

end CFSG.ComponentClassification.GSThmB.A10T
