module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR8Tori
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatEvenOuterOmega
import CFSG.LocalAnalysis.SeitzReduction.CentralizerComponents
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR8Instances

public section

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG Subgroup QuadraticMap Matrix Module CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification
open CFSG.ComponentClassification.CatLeafProof (fixedSubgroupCongrEquiv fixedInnerEquiv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.ComponentClassification.UnbalancedCatalog.OmegaRadical
open CFSG.SeitzReduction.LinearPilot (SpFixedOrNoPComponent spFixedOrNoPComponent_of_mulEquiv)

@[expose] def PComponentUnique (X : Type) [Group X] : Prop :=
  ∀ P P' : Subgroup X, IsPComponent 2 P → IsPComponent 2 P' → P = P'

theorem pComponentUnique_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : PComponentUnique Y) : PComponentUnique X := by
  intro P P' hP hP'
  exact map_injective e.injective
    (h _ _ (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP)
      (LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 e hP'))

theorem spFixedOrUnique_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {g : ℕ}
    (h : SpFixedOrNoPComponent Y g ∨ PComponentUnique Y) :
    SpFixedOrNoPComponent X g ∨ PComponentUnique X := by
  rcases h with h | h
  · exact Or.inl (spFixedOrNoPComponent_of_mulEquiv e h)
  · exact Or.inr (pComponentUnique_of_mulEquiv e h)

variable {K : Type} [Field K] [Finite K] {f n : ℕ}

theorem pComponentUnique_field (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (hn : 4 ≤ n) {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : α ∈ matrixProjectiveImage Q) (hα2 : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) {S : similarityPairs Q}
    (hS : S ∈ unitMultiplierPairs Q) (hSα : matrixProjectiveConjugationHom Q S = α)
    (hσ1 : S.val.right ≠ 1) : PComponentUnique (fixedSubgroup α) := by
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
  refine pComponentUnique_of_mulEquiv (fixedInnerEquiv hcj α) fun P P' hP hP' => ?_
  rw [CatLeafProof.eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hP,
    CatLeafProof.eq_of_isPComponent_of_normal_simple hNYn hNYs hNY2 hCY hP']

theorem spFixedOrUnique_of_not_inner (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) (hn : 4 ≤ n)
    {Q : QuadraticForm K (Fin (2 * n) → K)} (hQ : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin (2 * n) → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      elementaryGroup Q)
    (hconj : ∀ α : MulAut (matrixProjectiveDerived Q), α * α = 1 →
      ∃ β, β⁻¹ * α * β ∈ matrixProjectiveImage Q)
    (α : MulAut (matrixProjectiveDerived Q)) (hα : orderOf α = 2)
    (hout : α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q)) :
    SpFixedOrNoPComponent (fixedSubgroup α) f ∨ PComponentUnique (fixedSubgroup α) := by
  have : CharP K 2 :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf hK
  have := finite_mulAut_matrixProjectiveDerived Q
  have hαα : α * α = 1 := by
    have h2 := pow_orderOf_eq_one α
    rw [hα] at h2
    rw [← pow_two]
    exact h2
  obtain ⟨β, hβ⟩ := hconj α hαα
  have hc : MulAut.congr β⁻¹ α = β⁻¹ * α * β := MulEquiv.ext fun _ => rfl
  have hγ2 : orderOf (β⁻¹ * α * β) = 2 := by
    rw [← hc]
    exact (orderOf_injective (MulAut.congr β⁻¹).toMonoidHom (MulAut.congr β⁻¹).injective
      α).trans hα
  have hγo : β⁻¹ * α * β ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [← hc, LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hout
  refine spFixedOrUnique_of_mulEquiv ((fixedSubgroupCongrEquiv β⁻¹ α).trans
    (MulEquiv.subgroupCongr (congrArg fixedSubgroup hc))) ?_
  obtain ⟨S, hS, hSγ⟩ := exists_unit_rep hβ
  by_cases hσ : S.val.right = 1
  · obtain ⟨-, -, -, -, F, hF, hker, -, -⟩ :=
      evenOrthogonalRealization_of_regular hf hK (by omega) Q hQ hT hE
    have hmem : (⟨matrixProjectiveConjugationHom Q S, ⟨S, rfl⟩⟩ : matrixProjectiveImage Q) ∈
        F.ker := by
      rw [MonoidHom.mem_ker, hF, hσ]
    rw [hker, Subgroup.mem_subgroupOf] at hmem
    obtain ⟨s, hs⟩ := hmem
    have hs' : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) =
        β⁻¹ * α * β := hs.trans hSγ
    have hs2 : orderOf (matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s)) = 2 := by
      rw [hs']
      exact hγ2
    have hso : matrixProjectiveConjugationHom Q (matrixIsometryInclusion Q s) ∉
        OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
      rw [hs']
      exact hγo
    refine spFixedOrUnique_of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hs'.symm)) ?_
    rcases F4Pilot.omega_linear_fixed hf hK hn hQ hT hE s hs2 hso with hΦ | hch
    · exact Or.inl (Or.inl ⟨K, inferInstance, inferInstance, n - 1, hK, by omega, hΦ⟩)
    · exact Or.inl (Or.inr (CatLeafProof.not_isPComponent_of_isCharacteristicP hch))
  · exact Or.inr (pComponentUnique_field hf hK hn hQ hT hE hβ hγ2 hγo hS hSγ hσ)

omit [Finite K] in
theorem spFixedOrUnique_of_lieModel_POmegaPlus {J : Type} [Group J] {e : ℕ}
    (hadm : StatedLieAdmissible .POmegaPlus n 2 e) (hm : LieModel J .POmegaPlus n 2 e)
    (α : MulAut J) (hα : orderOf α = 2) (hαo : α ∉ (MulAut.conj : J →* MulAut J).range) :
    SpFixedOrNoPComponent (fixedSubgroup α) e ∨ PComponentUnique (fixedSubgroup α) := by
  have hC : StatedClassicalModel J .POmegaPlus n 2 e :=
    EvenOrthSelector.statedModel_of_lieModel (by decide) hm
  have hf : 1 ≤ e := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨K, _, _, Q, hK, hQ, hT, hE, hconj, ⟨eJ⟩⟩ :=
    EvenOrthSelector.exists_coordinate_witness (Or.inl rfl) hC
  have hβ : orderOf (MulAut.congr eJ α) = 2 :=
    (orderOf_injective (MulAut.congr eJ).toMonoidHom (MulAut.congr eJ).injective α).trans hα
  have hβo : MulAut.congr eJ α ∉ OuterAutomorphisms.inner (matrixProjectiveDerived Q) := by
    rw [LocalAnalysis.ComponentInitial.FixedFourGroup.congr_mem_inner_iff]
    exact hαo
  exact spFixedOrUnique_of_mulEquiv (fixedSubgroupCongrEquiv eJ α)
    (spFixedOrUnique_of_not_inner hf hK hn hQ hT hE hconj _ hβ hβo)

omit [Finite K] in
theorem forall_isPComponent_eq_of_not_inner {m : ℕ} (hdet : OmegaEvenTypeDetAt m) {S : Type}
    [Group S] [Finite S] {f : ℕ} (hS : LieModel S .POmegaPlus m 2 (2 * f)) {σ : MulAut S}
    (hσ : orderOf σ = 2) (hout : σ ∉ (MulAut.conj : S →* MulAut S).range) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) {D : Subgroup (fixedSubgroup σ)}
    (hD : IsComponent D) (hDm : LieModel (D ⧸ center D) tag m 2 f) :
    center D = ⊥ ∧ LieModel D tag m 2 f ∧
      ∀ P : Subgroup (fixedSubgroup σ), IsPComponent 2 P → P = D := by
  have hadm : StatedLieAdmissible .POmegaPlus m 2 (2 * f) :=
    statedLieAdmissible_of_lieModel_POmega (Or.inl rfl) hS
  have hDp : IsPComponent 2 D := LocalAnalysis.ComponentInitial.isPComponent_two_of_isComponent hD
  rcases omega_plus_fixed_exact hadm hS σ hσ hout with h | ⟨-, hF⟩
  · exact (false_of_spFixedOrNoPComponent_omega hdet htag h hD hDm).elim
  obtain ⟨t', ht', -, hmD⟩ := hF D hDp
  have hZ : center D = ⊥ := F4Pilot.center_eq_bot_of_isQuasisimple hD.1
    (LinearPilot.isSimpleGroup_of_lieModel_POmega ht' hmD)
  refine ⟨hZ, LieType.CurtisTits.lieModel_of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hDm, ?_⟩
  rcases spFixedOrUnique_of_lieModel_POmegaPlus hadm hS σ hσ hout with h | hU
  · exact (false_of_spFixedOrNoPComponent_omega hdet htag h hD hDm).elim
  · exact fun P hP => hU P D hP hDp

@[expose] def OmegaNeighbourAlternativeField {Y : Type} [Group Y] (s : Y) (D Kc : Subgroup Y)
    (m f : ℕ) (tag : StatedLieTag) : Prop :=
  D ≤ Kc ⊔ Kc.map (MulAut.conj s).toMonoidHom ∧
    ((Kc.map (MulAut.conj s).toMonoidHom = Kc ∧ D < Kc ∧ s ∉ Kc ∧
        ∃ hsN : s ∈ normalizer (Kc : Set Y),
          Kc.normalizerMonoidHom ⟨s, hsN⟩ ∉ (MulAut.conj : Kc →* MulAut Kc).range ∧
          center Kc = ⊥ ∧ LieModel Kc .POmegaPlus m 2 (2 * f) ∧
          ∀ P : Subgroup (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)), IsPComponent 2 P →
            P.map (fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩)).subtype = D.subgroupOf Kc ∧
              LieModel P tag m 2 f) ∨
      (Kc.map (MulAut.conj s).toMonoidHom ≠ Kc ∧
        ⁅Kc, Kc.map (MulAut.conj s).toMonoidHom⁆ = ⊥ ∧ center Kc = ⊥ ∧ Nonempty (Kc ≃* D)))

theorem OmegaNeighbourAlternative.field {Y : Type} [Group Y] [Finite Y]
    (hO : pPrimeCore 2 Y = ⊥) {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y))) {m f : ℕ}
    (hmf : (m, f) ≠ (4, 1)) (hdet : OmegaEvenTypeDetAt m) {tag : StatedLieTag}
    (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus) (hDm : LieModel (D ⧸ center D) tag m 2 f)
    {Kc : Subgroup Y} (hKc : IsComponent Kc) (h : OmegaNeighbourAlternative s D Kc m f) :
    OmegaNeighbourAlternativeField s D Kc m f tag ∧ center D = ⊥ := by
  obtain ⟨hDKK, ⟨hKt, hDK, hsK, ⟨hsN, hout⟩, hZ, hmodel⟩ | ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩ :=
    h.exact hO hKc hmf
  · have hs2 : s ^ 2 = 1 := hs ▸ pow_orderOf_eq_one s
    have hDs : D ≤ centralizer ({s} : Set Y) := hD.1
    have hDc : IsComponent (D.subgroupOf (centralizer ({s} : Set Y))) :=
      (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hDs).1
        ((ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).2 hD)
    have hDcomp := CentralizerComponents.isComponent_subgroupOf_inf_centralizer hDs hDc hDK.le
    obtain ⟨hD'c, hD'm, hD'map, -⟩ :=
      UnitaryPilot.isComponent_fixedSubgroup_of_le_of_lieModel_quotient hsN hDK.le hDs hDcomp hDm
    have hτ2 := orderOf_normalizerMonoidHom_of_not_mem_range hs2 hout
    obtain ⟨hD'Z, hD'L, hall⟩ :=
      forall_isPComponent_eq_of_not_inner hdet hmodel hτ2 hout htag hD'c hD'm
    have hDfix : D.subgroupOf Kc ≤ fixedSubgroup (Kc.normalizerMonoidHom ⟨s, hsN⟩) := by
      rw [F4Pilot.fixedSubgroup_normalizerMonoidHom]
      intro x hx
      exact mem_subgroupOf.mpr (hDs (mem_subgroupOf.mp hx))
    refine ⟨⟨hDKK, .inl ⟨hKt, hDK, hsK, hsN, hout, hZ, hmodel, fun P hP => ?_⟩⟩, ?_⟩
    · rw [hall P hP]
      exact ⟨hD'map, hD'L⟩
    · rw [← map_center_eq (F4Pilot.subgroupOfSubgroupOfEquiv hDK.le hDfix), hD'Z,
        Subgroup.map_bot]
  · refine ⟨⟨hDKK, .inr ⟨hKt, hcomm, hZ, ⟨φ⟩⟩⟩, ?_⟩
    rw [← map_center_eq φ, hZ, Subgroup.map_bot]

theorem neighbour_overgroup_omega_field_of_pPrimeCore_eq_bot {m f : ℕ} (hmf : (m, f) ≠ (4, 1))
    (hcat : OmegaCatalogueClausesAt m) (hdet : OmegaEvenTypeDetAt m) {Y : Type} [Group Y]
    [Finite Y] (hO : pPrimeCore 2 Y = ⊥)
    (hsec : ∀ Kc : Subgroup Y, IsComponent Kc → Catalog (Kc ⧸ center Kc))
    {s : Y} (hs : orderOf s = 2) {D : Subgroup Y}
    (hD : CFSG.Open.IsComponentOf D (centralizer ({s} : Set Y)))
    (hsyl : ∀ U : Subgroup Y, IsPGroup 2 U → U ≤ centralizer (D : Set Y) → Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard D) (hnn : ¬ D.Normal)
    {tag : StatedLieTag} (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus)
    (hDm : LieModel (D ⧸ center D) tag m 2 f) (hZD : Odd (Nat.card (center D))) :
    (∃ Kc : Subgroup Y, IsComponent Kc ∧ OmegaNeighbourAlternativeField s D Kc m f tag) ∧
      (∀ Lc : Subgroup Y, IsComponent Lc → ⁅D, Lc⁆ ≠ ⊥ →
        OmegaNeighbourAlternativeField s D Lc m f tag) ∧ center D = ⊥ := by
  obtain ⟨⟨Kc, hKc, hK⟩, hall⟩ := neighbour_overgroup_omega_of_pPrimeCore_eq_bot hmf hcat hO hsec
    hs hD hsyl hstd hnn htag hDm hZD
  exact ⟨⟨Kc, hKc, (hK.field hO hs hD hmf hdet htag hDm hKc).1⟩,
    fun Lc hLc hDL => ((hall Lc hLc hDL).field hO hs hD hmf hdet htag hDm hLc).1,
    (hK.field hO hs hD hmf hdet htag hDm hKc).2⟩

section Neighbour

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

@[expose] def OmegaHR8FieldAt (t : G) (m f : ℕ) (tag : StatedLieTag) (X D : Subgroup G) : Prop :=
  ∃ htX : t ∈ centralizer (X : Set G),
    (∃ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc ∧
        OmegaNeighbourAlternativeField
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f tag) ∧
      (∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
        IsComponent Kc →
        ⁅(D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))), Kc⁆ ≠ ⊥ →
        OmegaNeighbourAlternativeField
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩)
          ((D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) Kc m f tag) ∧
      center ((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = ⊥

theorem omegaHR8FieldAt_of_seitzSetting (hset : SeitzSetting G L) {m f : ℕ}
    (hmf : (m, f) ≠ (4, 1)) (hcat : OmegaCatalogueClausesAt m) (hdet : OmegaEvenTypeDetAt m)
    {X : Subgroup G} (hX : X ≠ ⊥)
    {t : G} (htX : t ∈ centralizer (X : Set G)) (ht : orderOf t = 2) {D : Subgroup G}
    (hDX : D ≤ centralizer (X : Set G)) (hDq : CFSG.IsQuasisimple D) (hZD : center D = ⊥)
    {tag : StatedLieTag} (htag : tag = .POmegaPlus ∨ tag = .POmegaMinus)
    (hDm : LieModel D tag m 2 f)
    (hcomp : CFSG.Open.IsComponentOf
        ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))))
        (centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩} :
          Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))))))
    (hsyl : ∀ U : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsPGroup 2 U →
      U ≤ centralizer ((D.subgroupOf (centralizer (X : Set G))).map
          (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :
        Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))) →
      Nat.card U ≤ 2)
    (hstd : CFSG.Open.standardComponentIsStandard ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))))
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    OmegaHR8FieldAt t m f tag X D := by
  have hsec : ∀ Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
      IsComponent Kc → Catalog (Kc ⧸ center Kc) := fun Kc hKc =>
    F4Pilot.catalog_center_quotient_of_kProper hset.standardSetting.kProper
      (F4Pilot.centralizer_ne_top_of_ne_bot hset.standardSetting.simple
        hset.standardSetting.nonab hX) hKc.1
  have ht' : orderOf (⟨t, htX⟩ : centralizer (X : Set G)) = 2 := by
    rw [orderOf_mk]
    exact ht
  have hne := ne_bot_of_isQuasisimple hcomp.2.2
  have hDm' := LinearPilot.lieModel_quotient_center_of_center_eq_bot hZD hDm
  exact ⟨htX, neighbour_overgroup_omega_field_of_pPrimeCore_eq_bot hmf hcat hdet
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hsec (orderOf_mk_oddCore ht') hcomp hsyl
    hstd hnn htag (UnitaryPilot.lieModel_quotient_center_map_oddCore_of_isQuasisimple hDX hDq hDm' hne)
    (UnitaryPilot.odd_card_center_map_subgroupOf_oddCore hDX hDq
      (odd_card_center_of_center_eq_bot hZD) hne)⟩

end Neighbour

section Tori

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem omegaHR8FieldAt_pairTorus_of_not_normal (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) (k : Fin n)
    (e : L ≃* matrixProjectiveDerived (coordinateQuadPlus n K)) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    {X : Subgroup G} (hX : X = ((pairTorus (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G} (hDe : D = ((pairPerp (K := K) k).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    OmegaHR8FieldAt t (n - 1) f .POmegaPlus X D := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -, hcard, -, -, hDC, hDq, hZ, hLie, -⟩ :=
    neighbour_data_pairTorus hKc hq hn k e htC hX hDe
  have hXne : X ≠ ⊥ := ne_bot_of_one_lt_card (by rw [hcard]; omega)
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_pairTorus_of_seitzSetting hset hKc hq hn k e htC ht hX htX hDe
  exact omegaHR8FieldAt_of_seitzSetting hset (ne_four_one_of_four_le_card hKc hq _) hcat
    (omegaEvenTypeDetAt _) hXne htX ht (hDC.trans inf_le_left) hDq hZ (Or.inl rfl) hLie hcomp
    hsyl hstd hnn

theorem omegaHR8FieldAt_minusPairTorus (hset : SeitzSetting G L) {n f : ℕ}
    (hcat : OmegaCatalogueClausesAt (n - 1)) {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f)
    (hq : 4 ≤ Nat.card K) (hn : 5 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin (n - 1)) (e : L ≃* matrixProjectiveDerived (coordinateQuadMinus n K (by omega) b c))
    {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X = ((minusPairTorus (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((minusPairPerp (K := K) (by omega) b c k).map e.symm.toMonoidHom).map L.subtype)
    (hnn : ¬ ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))).Normal) :
    OmegaHR8FieldAt t (n - 1) f .POmegaMinus X D := by
  have := LinearPilot.finite_of_card_eq_two_pow hKc
  have := LinearPilot.charP_two_of_card_eq_two_pow hKc
  obtain ⟨-, htX, -, hcard, -, -, hDC, hDq, hZ, hLie, -⟩ :=
    neighbour_data_minusPairTorus hKc hq hn hirr k e htC hX hDe
  have hXne : X ≠ ⊥ := ne_bot_of_one_lt_card (by rw [hcard]; omega)
  obtain ⟨hcomp, hsyl, hstd⟩ :=
    neighbour_standard_minusPairTorus_of_seitzSetting hset hKc hq hn hirr k e htC ht hX htX hDe
  exact omegaHR8FieldAt_of_seitzSetting hset (ne_four_one_of_four_le_card hKc hq _) hcat
    (omegaEvenTypeDetAt _) hXne htX ht (hDC.trans inf_le_left) hDq hZ (Or.inr rfl) hLie hcomp
    hsyl hstd hnn

end Tori

end CFSG.SeitzReduction.OmegaPilot
