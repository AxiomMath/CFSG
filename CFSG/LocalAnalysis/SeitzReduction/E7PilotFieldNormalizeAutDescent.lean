module

public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAut
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafEvenNoComponent
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatEvenClassicalOmega
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatTypeDet

public section

namespace CFSG.SeitzReduction.E7Pilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.Quasithin (perfectCore)

section Components

theorem isComponent_lieModel_perfectCore {G : Type} [Group G] {H : Subgroup G} {X : Type}
    [Group X] {t : StatedLieTag} {n g : ℕ} (hX : LieModel X t n 2 g) (hXq : CFSG.IsQuasisimple X)
    (e : perfectCore H ≃* X) :
    CFSG.IsComponent ((perfectCore H).subgroupOf H) ∧
      LieModel ((perfectCore H).subgroupOf H) t n 2 g := by
  let eD : (perfectCore H).subgroupOf H ≃* X :=
    (Subgroup.subgroupOfEquivOfLe (CFSG.Quasithin.perfectCore_le H)).trans e
  exact ⟨⟨(LocalAnalysis.ComponentInitial.isQuasisimple_congr eD).2 hXq,
    (CFSG.Quasithin.perfectCore_normal H).isSubnormal⟩,
    LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hX⟩

theorem false_of_component_of_statedSp {X : Type} [Group X]
    [Finite X] {F : Type} [Field F] [Finite F] {g r : ℕ} (hF : Nat.card F = 2 ^ g) (hg : 1 ≤ g)
    (hr : 3 ≤ r) (Φ : X ≃* StatedSp r F) {D : Subgroup X} (hD : CFSG.IsComponent D) {m f : ℕ}
    (hDm : LieModel D .POmegaPlus m 2 f) : False := by
  have : CharP F 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hg hF
  have hcond : (Infinite F ∨ 4 ≤ Nat.card F) ∨ (Nat.card F = 3 ∧ 2 ≤ r) ∨
      (Nat.card F = 2 ∧ 3 ≤ r) := by
    rcases (by omega : g = 1 ∨ 2 ≤ g) with rfl | hg2
    · exact Or.inr (Or.inr ⟨by rw [hF, pow_one], hr⟩)
    · refine Or.inl (Or.inr ?_)
      rw [hF]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg2
  have hS := ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F r (by omega) hcond
  obtain ⟨-, -, -, -, ⟨eProj⟩⟩ :=
    SymmetricLocal.small_standard_source_even_simple_symplectic_parameters_stated
      (X := StatedSp r F) hF (by omega) ⟨MulEquiv.refl _⟩
  have hadm : StatedLieAdmissible .PSp r 2 g := ⟨Nat.prime_two, hg, by omega, fun h => by
    rw [Prod.mk.injEq] at h
    omega⟩
  have hXs : IsSimpleGroup X := (Φ.trans eProj.symm).isSimpleGroup
  have hmX : LieModel X .PSp r 2 g :=
    Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, ⟨Φ.trans eProj.symm⟩⟩
  have hDtop := F4Pilot.eq_top_of_isComponent_of_isSimpleGroup hD
  let eD : D ≃* X := (MulEquiv.subgroupCongr hDtop).trans Subgroup.topEquiv
  obtain ⟨htt, -, -⟩ := OmegaPilot.lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
    (Or.inl rfl) hDm (Or.inl (by decide)) (LieType.CurtisTits.lieModel_of_mulEquiv eD.symm hmX) rfl
  exact absurd htt (by decide)

theorem fixedSubgroup_mulAut_conj_eq {G : Type*} [Group G] (z : G) :
    fixedSubgroup (MulAut.conj z) = centralizer ({z} : Set G) := by
  ext y
  change z * y * z⁻¹ = y ↔ y ∈ centralizer ({z} : Set G)
  rw [mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact eq_comm

end Components

section Model

variable {F : Type} [Field F] [Finite F] {n f : ℕ}

theorem statedClassicalModel_coordinatePlus (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (hn : 4 ≤ n) :
    StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n F)) .POmegaPlus n 2 f :=
  ⟨⟨Nat.prime_two, hf, hn⟩, F, inferInstance, inferInstance, hF,
    ⟨(coordinatePlusWitnessEquiv F (MulEquiv.refl _)).symm⟩⟩

theorem lieModel_coordinatePlus (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f) (hn : 4 ≤ n) :
    LieModel (matrixProjectiveDerived (coordinateQuadPlus n F)) .POmegaPlus n 2 f :=
  Or.inl ⟨by decide, statedClassicalModel_coordinatePlus hf hF hn⟩

theorem isQuasisimple_coordinatePlus (hn : 3 ≤ n) :
    CFSG.IsQuasisimple (matrixProjectiveDerived (coordinateQuadPlus n F)) := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F hn
  obtain ⟨hs, hnab⟩ := matrix_simple_nonabelian (by omega : 0 < 2 * n) hQ hT
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1

theorem commutator_top_coordinatePlus (hn : 3 ≤ n) :
    ⁅(⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F))),
      (⊤ : Subgroup (matrixProjectiveDerived (coordinateQuadPlus n F)))⁆ = ⊤ := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n F hn
  obtain ⟨hs, hnab⟩ := matrix_simple_nonabelian (by omega : 0 < 2 * n) hQ hT
  exact commutator_top_of_isSimpleGroup hnab

end Model

section Field

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem nonempty_mulEquiv_pairDescentDerived (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) {P : Subgroup (fixedSubgroup α)} (hP : IsPComponent 2 P) :
    Nonempty (P ≃* pairDescentDerived hS) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  obtain ⟨-, -, hsimple, heven, ext, -, -, hinj, hinn, hNC, hnormal, hcent⟩ :=
    evenOrthogonalFieldCentralizer_of_regular hf hK hn Q hQ hT hE α hα hα2 S hS hSα hσ1
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  set N := (extKappa Q ext).range with hNdef
  set Y := OuterAutomorphisms.inner (matrixProjectiveDerived Q) ⊓ Subgroup.centralizer {α}
    with hYdef
  have hNY : N ≤ Y := fun x hx =>
    Subgroup.mem_inf.mpr ⟨hinn hx, (Subgroup.mem_inf.mp (hNC hx)).2⟩
  have hYE : Y ≤ matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} :=
    inf_le_inf_right _ (matrixProjective_inner_le_image Q)
  obtain ⟨NY, hNYdef⟩ : ∃ NY : Subgroup Y, NY = N.subgroupOf Y := ⟨_, rfl⟩
  have hNYn : NY.Normal := ⟨fun x hx y => by
    rw [hNYdef, Subgroup.mem_subgroupOf] at hx ⊢
    have hn' := (hnormal.conj_mem ⟨x, hNC hx⟩ hx ⟨y, hYE y.2⟩)
    exact hn'⟩
  have eNY : NY ≃* N := (MulEquiv.subgroupCongr hNYdef).trans (Subgroup.subgroupOfEquivOfLe hNY)
  have eJ : ↥(pairDescentDerived hS) ≃* N := MonoidHom.ofInjective hinj
  have : IsSimpleGroup ↥(pairDescentDerived hS) := hsimple
  have hNYs : IsSimpleGroup NY := (eNY.trans eJ.symm).isSimpleGroup
  have hNY2 : Even (Nat.card NY) := by
    rw [Nat.card_congr (eNY.trans eJ.symm).toEquiv]
    exact heven
  have hα2' : α * α = 1 := by
    have h2 := pow_orderOf_eq_one α
    rw [hα2] at h2
    rw [← pow_two]
    exact h2
  have hCY : ∀ y : Y, (∀ x ∈ NY, y * x = x * y) → y = 1 := by
    intro y hy
    have hyN : (y : MulAut (matrixProjectiveDerived Q)) ∈
        matrixProjectiveImage Q ⊓ Subgroup.centralizer {α} ⊓
          Subgroup.centralizer (N : Set (MulAut (matrixProjectiveDerived Q))) := by
      refine Subgroup.mem_inf.mpr ⟨hYE y.2, Subgroup.mem_centralizer_iff.mpr fun n hn => ?_⟩
      have h1 := hy ⟨n, hNY hn⟩ (by rw [hNYdef]; exact hn)
      exact (congrArg Subtype.val h1).symm
    rw [hcent, Subgroup.mem_zpowers_iff] at hyN
    obtain ⟨i, hi⟩ := hyN
    apply Subtype.ext
    rcases Int.even_or_odd i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [← two_mul, _root_.zpow_mul, zpow_two, hα2', _root_.one_zpow] at hi
      exact hi.symm
    · exfalso
      rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, hα2', _root_.one_zpow, one_mul,
        zpow_one] at hi
      exact hout (hi ▸ (Subgroup.mem_inf.mp y.2).1)
  have hPY := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
    (fixedInnerEquiv hcj α) hP
  have hPeq : P.map (fixedInnerEquiv hcj α).toMonoidHom = NY :=
    CatLeafProof.eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hPY
  exact ⟨((P.equivMapOfInjective (fixedInnerEquiv hcj α).toMonoidHom
    (fixedInnerEquiv hcj α).injective).trans (MulEquiv.subgroupCongr hPeq)).trans
      (eNY.trans eJ.symm)⟩

theorem nonempty_derived_mulEquiv_of_isometry {k W : Type} [Field k] [AddCommGroup W]
    [Module k W] {g d : ℕ} (hg : 1 ≤ g) (hk : Nat.card k = 2 ^ g) (hd : 1 ≤ d)
    {Q₀ : QuadraticForm k W} (Qc : QuadraticForm k (Fin d → k)) (ψ : Q₀.IsometryEquiv Qc)
    (hQc : Qc.polarBilin.Nondegenerate)
    (hTc : ∃ T : Submodule k (Fin d → k), finrank k T = 3 ∧ ∀ x ∈ T, Qc x = 0)
    (hEc : ⁅TauCeti.QuadraticMap.orthogonalGroup Qc, TauCeti.QuadraticMap.orthogonalGroup Qc⁆ =
      elementaryGroup Qc) :
    Nonempty (↥⁅TauCeti.QuadraticMap.orthogonalGroup Q₀,
      TauCeti.QuadraticMap.orthogonalGroup Q₀⁆ ≃* matrixProjectiveDerived Qc) := by
  have hZ := (evenOrthogonalRealization_of_regular hg hk hd Qc hQc hTc hEc).1
  have e1 := (Subgroup.equivMapOfInjective _
    (LinearEquiv.autCongr ψ.toLinearEquiv).toMonoidHom
    (LinearEquiv.autCongr ψ.toLinearEquiv).injective).trans
      (MulEquiv.subgroupCongr
        (CatalogueBOrthogonalPointIsometry.derivedOrthogonal_map_isometry ψ))
  have e2 := ((matrixDerived Qc).equivMapOfInjective matrixLinearIso.toMonoidHom
    matrixLinearIso.injective).trans
      (MulEquiv.subgroupCongr (CatalogueBOrthogonalFixedTransfer.matrixDerived_map Qc))
  exact ⟨e1.trans (e2.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm)⟩

end Field

section Plus

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem exists_conj_eq_fieldAutT_of_plus (hn : 3 ≤ n)
    {S : similarityPairs (coordinateQuadPlus n K)}
    (hS : S ∈ unitMultiplierPairs (coordinateQuadPlus n K))
    (hσσ : S.val.right * S.val.right = 1) (hσ1 : S.val.right ≠ 1)
    (hTT : ∀ v, pairSemilinearMap S.val (pairSemilinearMap S.val v) = v)
    (b : Basis (Fin n ⊕ Fin n) (descentField S.val.right) (pairFix S))
    (hb : ∀ x y : Fin n → descentField S.val.right,
      pairDescentForm hS (∑ i, x i • b (.inl i) + ∑ i, y i • b (.inr i)) = ∑ i, x i * y i) :
    ∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ψ * matrixProjectiveConjugationHom _ S * ψ⁻¹ =
        fieldAutT (coordinateQuadPlus n K) S.val.right (coordinateQuadPlus_fieldMap n _) := by
  have hQ : (coordinateQuadPlus n K).polarBilin.Nondegenerate :=
    (regular_coordinateQuadPlus n K hn).1
  obtain ⟨-, hbij, -, -, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  let φe := LinearEquiv.ofBijective (LinearMap.liftBaseChange K (pairFix S).subtype) hbij
  let bK : Basis (Fin n ⊕ Fin n) K (Fin (2 * n) → K) := (b.baseChange K).map φe
  have hbK : ∀ a, bK a = ((b a : pairFix S) : Fin (2 * n) → K) := fun a => by
    simp only [bK, Basis.map_apply, Basis.baseChange_apply]
    change LinearMap.liftBaseChange K (pairFix S).subtype (1 ⊗ₜ b a) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  have hfix : ∀ a, coordinateSemilinearMap S.val (bK a) = bK a := fun a => by
    rw [hbK]
    exact (b a).2
  obtain ⟨M, hM, hMS⟩ := CFSG.RankThree.PartOne.KCOrthogonalDescent.exists_extension_matrix
    (plusIndexEquiv n) S.val bK hfix
  have hMv : ∀ v, matrixLinearIso M v = fun j => bK.equivFun v ((plusIndexEquiv n).symm j) := hM
  have hagree : (coordinateQuadPlus n K).comp (matrixLinearIso M).symm.toLinearMap =
      coordinateQuadPlus n K := by
    apply eq_of_agree (descentField S.val.right)
    intro c
    rw [QuadraticMap.comp_apply]
    set w : pairFix S := ∑ a, c (plusIndexEquiv n a) • b a with hw
    have hwK : (w : Fin (2 * n) → K) =
        ∑ a, ((c (plusIndexEquiv n a) : descentField S.val.right) : K) • bK a := by
      rw [hw, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hbK]
      rfl
    have hpre : (matrixLinearIso M).symm.toLinearMap (vecIncl (descentField S.val.right) c) =
        (w : Fin (2 * n) → K) := by
      change (matrixLinearIso M).symm (vecIncl (descentField S.val.right) c) = _
      rw [LinearEquiv.symm_apply_eq, hMv]
      funext j
      rw [hwK]
      have h2 := bK.repr_sum_self
        (fun a => ((c (plusIndexEquiv n a) : descentField S.val.right) : K))
      simp only [Basis.equivFun_apply, h2, vecIncl, Equiv.apply_symm_apply]
    rw [hpre, ← coe_descentForm (pairSemilinearMap_quad hS) w,
      isExtension_coordinateQuadPlus n (descentField S.val.right) c]
    congr 1
    have hw' : w = ∑ i, c (plusIndexEquiv n (.inl i)) • b (.inl i) +
        ∑ i, c (plusIndexEquiv n (.inr i)) • b (.inr i) := by
      rw [hw, Fintype.sum_sum_type]
    change pairDescentForm hS w = _
    rw [hw', hb, coordinateQuadPlus_apply]
  have hiso : ∀ v, coordinateQuadPlus n K (matrixLinearIso M v) =
      ((1 : Kˣ) : K) * coordinateQuadPlus n K v := by
    intro v
    have h1 := congrArg (fun F : QuadraticForm K (Fin (2 * n) → K) => F (matrixLinearIso M v))
      hagree
    simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h1
    rw [Units.val_one, one_mul, h1]
  set Θ := CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv
    (coordinateQuadPlus n K) (coordinateQuadPlus n K) M 1 hiso with hΘ
  refine ⟨Θ, ?_⟩
  have hconj := CFSG.RankThree.PartOne.KCOrthogonalDescent.matrixProjectiveSimilarityEquiv_conj
    (coordinateQuadPlus n K) (coordinateQuadPlus n K) M 1 hiso S
    (fieldPair (coordinateQuadPlus n K) S.val.right (coordinateQuadPlus_fieldMap n _)) rfl rfl hMS
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := Θ.surjective x
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply, hconj]
  rfl

end Plus

section Descent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem exists_conj_eq_fieldAutT {σ : K ≃+* K} (hσ : orderOf σ = 2) (hn : 5 ≤ n) {X : Type}
    [Group X] {g : ℕ} (hX : LieModel X .POmegaPlus n 2 g) (hXq : CFSG.IsQuasisimple X)
    (hXK : Nat.card X ≠ Nat.card (matrixProjectiveDerived (coordinateQuadPlus n K)))
    {β : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))} (hβ : β * β = 1)
    (hP : Nonempty (perfectCore (fixedSubgroup β) ≃* X)) :
    ∃ ψ : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)),
      ψ * β * ψ⁻¹ = fieldAutT (coordinateQuadPlus n K) σ (coordinateQuadPlus_fieldMap n σ) := by
  obtain ⟨f, hf, hK⟩ := F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := K)
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadPlus n K (by omega)
  have hE := commutator_coordinateQuadPlus n K (by omega)
  have hβim : β ∈ matrixProjectiveImage (coordinateQuadPlus n K) := by
    rw [CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_plus K n hn]
    exact Subgroup.mem_top β
  obtain ⟨e₀⟩ := hP
  obtain ⟨hD, hDm⟩ := isComponent_lieModel_perfectCore hX hXq e₀
  have hDp := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  by_cases hβ1 : β = 1
  · exfalso
    subst hβ1
    have htop : fixedSubgroup (1 : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K))) =
        ⊤ := by
      ext x
      exact ⟨fun _ => Subgroup.mem_top x, fun _ => rfl⟩
    have hcore : perfectCore (fixedSubgroup
        (1 : MulAut (matrixProjectiveDerived (coordinateQuadPlus n K)))) = ⊤ := by
      rw [htop]
      exact CFSG.Quasithin.perfectCore_eq_self_of_perfect
        (commutator_top_coordinatePlus (by omega))
    apply hXK
    rw [← Nat.card_congr e₀.toEquiv, hcore, Subgroup.card_top]
  have hβ2 : orderOf β = 2 := orderOf_eq_prime (by rw [pow_two]; exact hβ) hβ1
  obtain ⟨-, -, -, huniq, F, hF, hker, -, hinv⟩ :=
    evenOrthogonalRealization_of_regular hf hK (by omega : 1 ≤ 2 * n) _ hQ hT hE
  obtain ⟨S, ⟨hS, hSβ⟩, -⟩ := huniq β hβim
  obtain ⟨hSS, hTT, hright⟩ := hinv β hβim hβ2 S hS hSβ
  have hcj := UnbalancingLocal.EvenOrthogonalComponents.conj_injective_matrixProjectiveDerived
    hQ hT hE
  by_cases hinn : β ∈ OuterAutomorphisms.inner (matrixProjectiveDerived (coordinateQuadPlus n K))
  · exfalso
    obtain ⟨z, hz⟩ := hinn
    have hz1 : z ≠ 1 := fun h => hβ1 (by rw [← hz, h, map_one])
    have hz2 : orderOf z = 2 := by
      refine orderOf_eq_prime ?_ hz1
      apply hcj
      rw [map_pow, hz, pow_two, hβ, map_one]
    have hfree := CatLeaf.involutionCentralizersComponentFree_orthogonal (Or.inl rfl)
      (statedClassicalModel_coordinatePlus (n := n) hf hK (by omega))
    have heq : fixedSubgroup β = centralizer ({z} : Set _) := by
      rw [← hz]
      exact fixedSubgroup_mulAut_conj_eq z
    exact hfree z hz2 _ (CatLeaf.isComponent_map_mulEquiv (MulEquiv.subgroupCongr heq) hD)
  rcases hright with hσ1 | ⟨hord, huniqσ, -⟩
  ·
    exfalso
    have hmem : (⟨matrixProjectiveConjugationHom _ S, ⟨S, rfl⟩⟩ :
        matrixProjectiveImage (coordinateQuadPlus n K)) ∈ F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ1]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) = β := hs.trans hSβ
    have hs2 : orderOf (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)) = 2 := by
      rw [hs']
      exact hβ2
    have hso : matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s) ∉
        OuterAutomorphisms.inner _ := by
      rw [hs']
      exact hinn
    have heq : fixedSubgroup β =
        fixedSubgroup (matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)) := by
      rw [hs']
    rcases F4Pilot.omega_linear_fixed hf hK (by omega) hQ hT hE s hs2 hso with hΦ | hch
    · obtain ⟨Φ⟩ := hΦ
      exact false_of_component_of_statedSp hK hf (by omega : 3 ≤ n - 1)
        ((MulEquiv.subgroupCongr heq).trans Φ) hD hDm
    · exact CatLeafProof.not_isPComponent_of_isCharacteristicP hch _
        (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
          (MulEquiv.subgroupCongr heq) hDp)
  have hσS : σ = S.val.right := huniqσ σ hσ
  have hσ1 : S.val.right ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact absurd hord (by norm_num)
  have hσσ : S.val.right * S.val.right = 1 := by
    have h1 := congrArg (fun y : similarityPairs (coordinateQuadPlus n K) => y.val.right) hSS
    rw [Subgroup.coe_mul, Subgroup.coe_one] at h1
    exact h1
  obtain ⟨hfin, -, -, hQ₀, -, -, -, -⟩ := even_quadratic_semilinear_involution_descent hσσ hσ1 hQ
    (T := pairSemilinearMap S.val) hTT (pairSemilinearMap_quad hS)
  have : FiniteDimensional (descentField S.val.right) (pairFix S) := finite_fixSpace
  have hdim : Module.finrank (descentField S.val.right) (pairFix S) = 2 * n := by
    rw [hfin, Module.finrank_fin_fun]
  rcases (finite_even_regular_quadratic_normal_forms (pairDescentForm hS) hQ₀).2.2.1 n
      (by omega) hdim with ⟨b, hb⟩ | ⟨β', γ', -, hroot, b, hb⟩
  ·
    obtain ⟨ψ, hψ⟩ := exists_conj_eq_fieldAutT_of_plus (by omega) hS hσσ hσ1 hTT b hb
    refine ⟨ψ, ?_⟩
    rw [← hSβ, hψ, hσS]
  ·
    exfalso
    obtain ⟨g', hg', hk'⟩ :=
      F4Pilot.exists_natCard_eq_two_pow_of_charTwo (K := descentField S.val.right)
    obtain ⟨eP⟩ := nonempty_mulEquiv_pairDescentDerived hf hK (by omega) hQ hT hE hβim hβ2 hinn
      hS hSβ hσ1 hDp
    have hreg := regular_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega) hroot
    obtain ⟨eM⟩ := nonempty_derived_mulEquiv_of_isometry hg' hk' (by omega) _
      ((minusBasisIsometry b hb).trans
        (coordinateMinusIsometry n (descentField S.val.right) (by omega) β' γ'))
      hreg.1 hreg.2 (commutator_coordinateQuadMinus n (descentField S.val.right) β' γ' (by omega)
        hroot)
    have hmM : LieModel (matrixProjectiveDerived (coordinateQuadMinus n (descentField S.val.right)
        (by omega) β' γ')) .POmegaMinus n 2 g' :=
      Or.inl ⟨by decide, ⟨Nat.prime_two, hg', by omega⟩, descentField S.val.right, inferInstance,
        inferInstance, hk', β', γ', hroot,
        ⟨(coordinateMinusWitnessEquiv _ (by omega) β' γ' (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨htt, -, -⟩ := OmegaPilot.lieModel_POmega_two_unique_classicalOrSuzuki_of_card_eq
      (Or.inl rfl) hDm (Or.inl (by decide))
      (LieType.CurtisTits.lieModel_of_mulEquiv (eP.trans eM).symm hmM) rfl
    exact absurd htt (by decide)

end Descent

end CFSG.SeitzReduction.E7Pilot
