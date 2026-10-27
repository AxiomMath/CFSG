module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootGeneric
public import CFSG.LocalAnalysis.EvenBN.GMSK.StatementBender
import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.SteinbergBV

theorem oneOrTwoLayer_of_stdData {G : Type} [Group G] [Finite G]
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {A : Subgroup G}
    (hstd : CFSG.Open.standardComponentIsStandard A) (hnn : ¬ A.Normal) [IsSimpleGroup A]
    (hAna : ∃ x y : A, x * y ≠ y * x)
    (hA4 : ∃ E : Subgroup G, E ≤ A ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4)
    {t : G} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G))) :
    OneOrTwoLayerConclusion A t := by
  obtain ⟨hCt, hAt, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd htA ht
  exact nonnormal_involution_component_layer (pPrimeCore_eq_bot_of_oddCore_eq_bot hO)
    hAna hA4 ht hAt hCt hsyl hnn

theorem exists_four_le_of_subgroup {G : Type*} [Group G] {A : Subgroup G}
    (h : ∃ E : Subgroup A, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4) :
    ∃ E : Subgroup G, E ≤ A ∧ CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hE, hE4⟩ := h
  exact ⟨E.map A.subtype, map_subtype_le E, CFSG.IsElementaryAbelian.map A.subtype,
    by rw [card_map_of_injective A.subtype_injective, hE4]⟩

theorem card_sylow_eq_two_of_relIndex {G : Type*} [Group G] [Finite G] {C : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htC : t ∈ C) (hsyl : ¬ 2 ∣ (zpowers t).relIndex C) (S : Sylow 2 C) :
    Nat.card S = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz : Nat.card ((zpowers t).subgroupOf C) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 htC)).toEquiv, Nat.card_zpowers, ht]
  have hP2 : IsPGroup 2 ((zpowers t).subgroupOf C) :=
    IsPGroup.of_card (n := 1) (by rw [hz, pow_one])
  have hidx : ¬ 2 ∣ ((zpowers t).subgroupOf C).index := by rwa [Subgroup.relIndex] at hsyl
  rw [Nat.card_congr (Sylow.equiv S (hP2.toSylow hidx)).toEquiv]
  exact hz

theorem not_isSimpleGroup_of_mulEquiv_prod {D A : Type*} [Group D] [Group A] [Nontrivial A]
    (ψ : D ≃* A × A) : ¬ IsSimpleGroup D := by
  intro hD
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  set N : Subgroup (A × A) := (⊤ : Subgroup A).prod ⊥ with hN
  have : (N.comap ψ.toMonoidHom).Normal := Subgroup.Normal.comap inferInstance _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap ψ.toMonoidHom) with h | h
  · have hmem : ψ.symm (a, 1) ∈ N.comap ψ.toMonoidHom := by
      simp [hN, Subgroup.mem_prod]
    rw [h, mem_bot] at hmem
    exact ha (by simpa using congrArg ψ hmem)
  · have hmem : ψ.symm (1, a) ∈ N.comap ψ.toMonoidHom := h ▸ mem_top _
    simp [hN, Subgroup.mem_prod] at hmem
    exact ha hmem

theorem surv_conjNormal_of_eq {Surv : ℕ → (D : Type) → [Group D] → MulAut D → Prop} {n : ℕ}
    {G : Type} [Group G] {t : G} {D₁ D₂ : Subgroup G} [D₁.Normal] [D₂.Normal] (h : D₁ = D₂)
    (hs : Surv n D₁ (MulAut.conjNormal t)) : Surv n D₂ (MulAut.conjNormal t) := by
  subst h
  exact hs

theorem sharpOutcomeOf_of_selectorOf {T : StdType}
    {Surv : ℕ → (D : Type) → [Group D] → MulAut D → Prop} (hfacts : StdTypeFacts T)
    (hiso : StdType.IsoInvariant T) (hsel : FixedRootSelectorOf T Surv fun D _ => Catalog D)
    {G : Type} [Group G] [Finite G] (hG : CFSG.SectionRank.IsKGroupCat G)
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {n : ℕ} {A : Subgroup G}
    (hstd : CFSG.Open.standardComponentIsStandard A) (hnn : ¬ A.Normal) (hA : T n A)
    {t : G} (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G))) :
    haveI : (CFSG.layer G).Characteristic := CFSG.LocalCores.layer_characteristic
    OneOrTwoLayerConclusion A t ∧
      (IsSimpleGroup (CFSG.layer G) → Surv n (CFSG.layer G) (MulAut.conjNormal t)) := by
  obtain ⟨hAs, hAna, hE⟩ := hfacts n A hA
  have hconc := oneOrTwoLayer_of_stdData hO hstd hnn hAna (exists_four_le_of_subgroup hE) ht
    htA hsyl
  have : (CFSG.layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  refine ⟨hconc, fun hDs => ?_⟩
  obtain ⟨-, -, -, hDE, -, halt, -⟩ := hconc
  have hDs' : IsSimpleGroup (normalClosure (A : Set G)) :=
    (MulEquiv.subgroupCongr hDE).isSimpleGroup
  rcases halt with ⟨⟨-, -, hAD, hnt⟩, -⟩ |
    ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ψ, -⟩, -⟩
  · obtain ⟨hCt, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hstd htA ht
    obtain ⟨hcat, S, d⟩ := exists_fixedRootDatumOf_of_simple hiso hG hA
      (fun P hPC hP => card_le_two_of_sylow (card_sylow_eq_two_of_relIndex ht htA hsyl) hPC hP)
      ht htA hCt hAD.le hDs' hnt
    exact surv_conjNormal_of_eq hDE (hsel _ hDs' hcat n _ S d)
  · exact (not_isSimpleGroup_of_mulEquiv_prod ψ hDs').elim

theorem gmsUnitary_sharp_of_selector (hfacts : StdTypeFacts T_U3)
    (hsel : FixedRootSelectorOf T_U3 SurvU3 fun D _ => Catalog D)
    {G : Type} [Group G] [Finite G] (hG : CFSG.SectionRank.IsKGroupCat G)
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {n : ℕ} {A : Subgroup G}
    (hA : StdUnitaryData G A n) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G))) :
    SharpOutcome (fun D _ => LieModel D .PSL 3 2 (2 * n)) G A t :=
  sharpOutcomeOf_of_selectorOf hfacts isoInvariant_T_U3 hsel hG hO hA.2.1 hA.2.2.1
    ⟨hA.1, hA.2.2.2⟩ ht htA hsyl

theorem gmsSuzuki_sharp_of_selector (hfacts : StdTypeFacts T_Sz)
    (hsel : FixedRootSelectorOf T_Sz SurvSz fun D _ => Catalog D)
    {G : Type} [Group G] [Finite G] (hG : CFSG.SectionRank.IsKGroupCat G)
    (hO : CFSG.Open.standardComponentOddCore G = ⊥) {n : ℕ} {A : Subgroup G}
    (hA : StdSuzukiData G A n) {t : G} (ht : orderOf t = 2)
    (htA : t ∈ centralizer (A : Set G))
    (hsyl : ¬ 2 ∣ (zpowers t).relIndex (centralizer (A : Set G))) :
    SharpOutcome (fun D _ => LieModel D .PSp 2 2 n) G A t :=
  sharpOutcomeOf_of_selectorOf hfacts isoInvariant_T_Sz hsel hG hO hA.1 hA.2.1 hA.2.2 ht htA
    hsyl

end CFSG.LocalAnalysis.EvenBN.GMSK
