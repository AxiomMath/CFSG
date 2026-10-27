module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporC
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36SporInputs
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBMSpor
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.LocalAnalysis.ComponentClassification.SuzOutComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSporadicCases
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.Sporadic.ONOddCore.LocalComp
public import CFSG.Sporadic.ONOddCore.ONan

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd CFSG.ComponentClassification.RestrictedStd.Spor


theorem rowFor_spor_of_comps_simple {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s)
    (hin : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ t : G, orderOf t = 2 →
        CompsSatisfy (centralizer ({t} : Set G)) fun Y _ => ¬ SmallCentralQuotient Y)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
        α ∉ OuterAutomorphisms.inner G →
        CompsSatisfy (Sporadic.Schreier.fixSub α) fun Y _ => ¬ SmallCentralQuotient Y) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y s := by
  intro G _ _ p m τ K h ⟨e⟩
  exfalso
  have hsimp := h.simple_bar
  obtain ⟨B, hB, hsB⟩ := h.exists_small (h.pPrimeCore_bar_eq_bot hodd e)
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  by_cases hinn : quotAut τ ∈ innAut (G ⧸ center G)
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (Hin.conj_injective_of_center hZ) t, ht]
      exact h.orderOf_bar
    have heq : fixedPoints (quotAut τ) = centralizer ({t} : Set (G ⧸ center G)) := by
      rw [Hin.centralizer_eq_fixedPoints_conj, ht]
    obtain ⟨B', hB', hs'⟩ := exists_isComponent_congr heq hB hsB
    exact hin _ hsimp h.nonabelian_bar ⟨e⟩ t ht2 B' hB' hs'
  · have hsq : quotAut τ * quotAut τ = 1 := by
      have := pow_orderOf_eq_one (quotAut τ)
      rwa [h.orderOf_bar, pow_two] at this
    have heq : fixedPoints (quotAut τ) = Sporadic.Schreier.fixSub (quotAut τ) :=
      (Hin.fixSub_eq_fixedPoints _).symm
    obtain ⟨B', hB', hs'⟩ := exists_isComponent_congr heq hB hsB
    exact hout _ hsimp h.nonabelian_bar ⟨e⟩ _ hsq hinn B' hB' hs'

theorem rowFor_spor_M
    :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .M := by
  refine rowFor_spor_of_comps_simple CatalogueU.sporadicOddCoreFree_M
    (fun G _ _ hGs _ ⟨eG⟩ t ht B hB hsB => ?_) (fun G _ _ hs _ hG α _ hα => ?_)
  · obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput G hGs ⟨eG⟩ t ht B hB
    obtain ⟨eM⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple eG
    have hM : Nat.card (↥B ⧸ center ↥B) ∣ Open.monsterOrder := by
      rw [← YGroups.Y443.natCard_Gmat_eq_monsterOrder, ← Nat.card_congr eM.toEquiv]
      exact (Subgroup.card_quotient_dvd_card _).trans ((Subgroup.card_subgroup_dvd_card B).trans
        (Subgroup.card_subgroup_dvd_card _))
    exact GSThmB.MonsterArith.not_smallCentralQuotient h41 hM hsB
  · exact (hα (CatLeafProof.monsterInnerInput G hs hG α)).elim

theorem rowFor_spor_He (hHe : TBLit.HeldTrivialMultiplier) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .He := by
  intro G _ _ p m τ K h ⟨e⟩
  exact (h.center_ne_bot (hHe G h.quasisimple ⟨e⟩)).elim

theorem rowFor_spor_J3 (hJ3 : HSJ3TwoMultiplierFact) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .J3 := by
  intro G _ _ p m τ K h ⟨e⟩
  exact (h.center_ne_bot (hJ3.2 G h.quasisimple h.center_isPGroup ⟨e⟩)).elim

theorem ne_of_bracket {q a N : ℕ} (ha : a * (a ^ 2 - 1) < 2 * N)
    (hb : 2 * N < (a + 1) * ((a + 1) ^ 2 - 1)) : q * (q ^ 2 - 1) ≠ 2 * N := by
  intro h
  rcases le_or_gt q a with hq | hq
  · have : q * (q ^ 2 - 1) ≤ a * (a ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega
  · have : (a + 1) * ((a + 1) ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem exists_comp_card (h : Config G p m τ K)
    (hO : pPrimeCore 2 ↥(fixedPoints (quotAut τ)) = ⊥) :
    ∃ B : Subgroup ↥(fixedPoints (quotAut τ)), IsComponent B ∧
      ∃ q : ℕ, Nat.card (↥B ⧸ center ↥B) * 2 = q * (q ^ 2 - 1) := by
  obtain ⟨hB, hL⟩ := h.isComponent_bar hO
  obtain ⟨q, -, -, hq⟩ := h.card_bar hO
  refine ⟨_, hB, q, ?_⟩
  have := isSimpleGroup_of_lieModel_psl2 hL
  have hZ := CatLeaf.center_eq_bot_of_simple (nonabelian_of_lieModel_psl2 hL)
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).toEquiv, ← hq]
  congr 1
  exact Nat.card_congr (subgroupOfEquivOfLe h.isTwoComponentIn_bar.1).toEquiv

end Config

theorem exists_comp_card_congr {Y : Type} [Group Y] {H H' : Subgroup Y} (hH : H = H')
    {B : Subgroup ↥H} (hB : IsComponent B) {c : ℕ} (hc : Nat.card (↥B ⧸ center ↥B) = c) :
    ∃ B' : Subgroup ↥H', IsComponent B' ∧ Nat.card (↥B' ⧸ center ↥B') = c := by
  subst hH
  exact ⟨B, hB, hc⟩

theorem rowFor_spor_of_card {s : TauCeti.SporadicName}
    (hodd : CatalogueU.SporadicOddCoreFree s) (S : Set ℕ)
    (hS : ∀ q N : ℕ, N ∈ S → q * (q ^ 2 - 1) ≠ 2 * N)
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → ∀ B : Subgroup ↥(centralizer ({t} : Set G)), IsComponent B →
        Nat.card (↥B ⧸ center ↥B) ∈ S)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ x y : G, x * y ≠ y * x) →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ α : MulAut G, α * α = 1 →
        α ∉ OuterAutomorphisms.inner G → ∀ B : Subgroup ↥(Sporadic.Schreier.fixSub α),
          IsComponent B → Nat.card (↥B ⧸ center ↥B) ∈ S) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y s := by
  intro G _ _ p m τ K h ⟨e⟩
  exfalso
  have hsimp := h.simple_bar
  obtain ⟨B, hB, q, hq⟩ := h.exists_comp_card (h.pPrimeCore_bar_eq_bot hodd e)
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple h.nonabelian_bar
  suffices hmem : Nat.card (↥B ⧸ center ↥B) ∈ S from hS q _ hmem (by rw [← hq]; ring)
  by_cases hinn : quotAut τ ∈ innAut (G ⧸ center G)
  · obtain ⟨t, ht⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (Hin.conj_injective_of_center hZ) t, ht]
      exact h.orderOf_bar
    have heq : fixedPoints (quotAut τ) = centralizer ({t} : Set (G ⧸ center G)) := by
      rw [Hin.centralizer_eq_fixedPoints_conj, ht]
    obtain ⟨B', hB', hc'⟩ := exists_comp_card_congr heq hB rfl
    rw [← hc']
    exact hin _ ⟨e⟩ t ht2 B' hB'
  · have hsq : quotAut τ * quotAut τ = 1 := by
      have := pow_orderOf_eq_one (quotAut τ)
      rwa [h.orderOf_bar, pow_two] at this
    have heq : fixedPoints (quotAut τ) = Sporadic.Schreier.fixSub (quotAut τ) :=
      (Hin.fixSub_eq_fixedPoints _).symm
    obtain ⟨B', hB', hc'⟩ := exists_comp_card_congr heq hB rfl
    rw [← hc']
    exact hout _ hsimp h.nonabelian_bar ⟨e⟩ _ hsq hinn B' hB'

theorem rowFor_spor_ONan
    (hON : SolMax.ONOuterComponentsInput) :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .ONan := by
  refine rowFor_spor_of_card Sporadic.ONOddCore.sporadicOddCoreFree_ONan {20160, 175560}
    (fun q N hN => ?_) (fun G _ _ hG t ht B hB => ?_)
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)
  · rcases hN with rfl | rfl
    · exact ne_of_bracket (a := 34) (by norm_num) (by norm_num)
    · exact ne_of_bracket (a := 70) (by norm_num) (by norm_num)
  · exact Or.inl
      (Sporadic.ONOddCore.cti_on_involution_local_components_projective_linear_quotient_order
        hG t ht B hB)
  · exact Or.inr (hON G hG α hα2 hα B hB)

theorem rowFor_spor_Suz :
    RowFor fun Y _ => NativeSporadic.IsSporadic Y .Suz := by
  refine rowFor_spor_of_card CatalogueU.sporadicOddCoreFree_Suz {20160, 95040, 604800}
    (fun q N hN => ?_) (fun G _ _ ⟨e⟩ t ht B hB => ?_)
    (fun G _ _ _ _ hG α hα2 hα B hB => ?_)
  · rcases hN with rfl | rfl | rfl
    · exact ne_of_bracket (a := 34) (by norm_num) (by norm_num)
    · exact ne_of_bracket (a := 57) (by norm_num) (by norm_num)
    · exact ne_of_bracket (a := 106) (by norm_num) (by norm_num)
  · exact Or.inl
      (Sporadic.SuzOddCore.CTI_Suz_involution_local_components_simple_quotient_order e t ht B hB)
  · rcases SolMax.suzOuterComponentsInput_holds G hG α hα2 hα B hB with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

end CFSG.ComponentClassification.HarrisLit.N36
