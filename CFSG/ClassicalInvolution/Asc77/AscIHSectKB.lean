module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectKA
public import CFSG.ClassicalInvolution.Asc77.AscIH8Graph
public import CFSG.ClassicalInvolution.Asc77.AscIH8Inv
public import CFSG.ClassicalInvolution.Asc77.AscIHSectK

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.ModelFacts (standardPair_plusDatum)
open scoped MatrixGroups

theorem mem_normalizer_map' {K G : Type} [Group K] [Group G] (ψ : K →* G) {R : Subgroup K} {x : K}
    (hx : x ∈ Subgroup.normalizer (R : Set K)) :
    ψ x ∈ Subgroup.normalizer ((R.map ψ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro h
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨x * r * x⁻¹, (hx r).mp hr, by simp⟩
  · rintro ⟨r, hr, hrh⟩
    refine ⟨x⁻¹ * r * x, ?_, ?_⟩
    · exact (hx (x⁻¹ * r * x)).mpr (by simpa [mul_assoc] using hr)
    · simp only [map_mul, map_inv]
      rw [hrh]
      group

section Edge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {t : StatedLieTag}
  {k e : ℕ} (M : Ih8Model p f Ω t k e)

include M

theorem Ih8Model.dstarAdj_of_torus [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hD4 : t ≠ .trialityD4) (hnpsl : ¬ (t = .PSL ∧ k = 2))
    {R₁ R₂ : Subgroup (modelUniv t k p e Fact.out).K} (hR₁ : R₁ ∈ M.cls) (hR₂ : R₂ ∈ M.cls)
    (hne : R₁ ≠ R₂) {v : (modelUniv t k p e Fact.out).K} (hv : v ∈ R₂)
    (hvN : v ∈ Subgroup.normalizer (R₁ : Set _)) {a : ℕ} (hva : orderOf v = 2 ^ a)
    (hcard : 2 * 2 ^ a = 2 ^ (Nat.card SL(2, GaloisField p f)).factorization 2) :
    dstarAdj Ω (R₁.map M.ψ) (R₂.map M.ψ) := by
  have hinj := M.injOn_fund hnpsl (M.cls_sub hR₂)
  have hord : orderOf (M.ψ v) = 2 ^ a := by
    rw [← hva, orderOf_eq_orderOf_iff]
    intro n
    constructor
    · intro h
      exact hinj (v ^ n) (R₂.pow_mem hv n) (by rw [map_pow]; exact h)
    · intro h
      rw [← map_pow, h, map_one]
  have hcardT : Nat.card (Subgroup.zpowers (M.ψ v)) = 2 ^ a := by
    rw [Nat.card_zpowers, hord]
  have hT2 : IsPGroup 2 (Subgroup.zpowers (M.ψ v)) := IsPGroup.of_card hcardT
  have hne' : R₂.map M.ψ ≠ R₁.map M.ψ := fun h =>
    hne (ih8_eq_of_map_eq M.ψ M.ker_le_center (M.cls_perfect hp2 hD4 hq hR₂)
      (M.cls_perfect hp2 hD4 hq hR₁) h).symm
  exact dstarAdj_of_cyclic_two hΩ (M.map_mem hR₂) hne'
    (Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hv)) hT2 inferInstance
    (by rw [hcardT]; exact hcard)
    (Subgroup.zpowers_le.mpr (mem_normalizer_map' M.ψ hvN))

theorem Ih8Model.exists_conj_of_fund (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    ∀ A ∈ Ω, ∀ B ∈ Ω, ∃ g : G, conjSub g A = B := by
  intro A hA B hB
  obtain ⟨RA, hRA, rfl⟩ := (M.mem_iff A).mp hA
  obtain ⟨RB, hRB, rfl⟩ := (M.mem_iff B).mp hB
  obtain ⟨g, hg⟩ := ModelFacts.fundamentalSingleClass t k p e Fact.out
    (ih8_isFundTag_mf M.isFundTag) M.admissible hG2 hD4 RA (M.cls_sub hRA) RB (M.cls_sub hRB)
  exact ⟨M.ψ g, (AscQuot.map_conjSub M.ψ g RA).symm.trans (congrArg (Subgroup.map M.ψ) hg.symm)⟩

theorem Ih8Model.dstarConnected_of_gens (hΩ : HypOmegaMod p f Ω) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {ι : Type} (L : ι → Subgroup (modelUniv t k p e Fact.out).K)
    (i₀ : ι) (hL : ∀ i, L i ∈ M.cls) (hgen : ⨆ i, L i = ⊤)
    (hcomp : ∀ i, (L i).map M.ψ ∈ dstarComp Ω ((L i₀).map M.ψ)) : T3.DStarConnected Ω := by
  have hne : Ω.Nonempty := ⟨_, M.map_mem (hL i₀)⟩
  have hK : (L i₀).map M.ψ ∈ Ω := M.map_mem (hL i₀)
  refine dstarConnected_of_generators hΩ.conjInvariant (M.exists_conj_of_fund hG2 hD4) hK ?_
  rw [eq_top_iff]
  have h1 : (⨆ i, (L i).map M.ψ) = ⊤ := by
    rw [← Subgroup.map_iSup, hgen, Subgroup.map_top, MonoidHom.range_eq_top.mpr M.surj]
  rw [← h1]
  exact iSup_le fun i => le_iSup₂_of_le _ (hcomp i) le_rfl

end Edge

section Nodes

variable (p f : ℕ) [Fact p.Prime]

@[expose] noncomputable def nodeSub (i : Fin 4) :
    Subgroup (modelUniv .POmegaPlus 4 p f Fact.out).K :=
  rankOne (modelUniv .POmegaPlus 4 p f Fact.out).D.rootGroup i

theorem modelUniv_pOmegaPlus_four (hn : 3 ≤ 4) :
    modelUniv .POmegaPlus 4 p f Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn⟩ := rfl

theorem rankOne_mem_fund_of_eq (M₀ : LieUniversal) (hn : 3 ≤ 4)
    (hM₀ : M₀ = ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn⟩)
    (i : Fin M₀.D.rank) :
    rankOne M₀.D.rootGroup i ∈ fundamentalSubgroups .POmegaPlus M₀.D := by
  subst hM₀
  exact rankOne_mem_fundamentalSubgroups_plusDatum (K := GaloisField p f) hn i

theorem nodeSub_mem_fund (i : Fin 4) :
    nodeSub p f i ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D :=
  rankOne_mem_fund_of_eq p f _ (by norm_num) (modelUniv_pOmegaPlus_four p f (by norm_num)) i

theorem iSup_rankOne_of_eq (M₀ : LieUniversal) (hn : 3 ≤ 4)
    (hM₀ : M₀ = ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn⟩) :
    ⨆ i : Fin M₀.D.rank, rankOne M₀.D.rootGroup i = ⊤ := by
  subst hM₀
  exact Balance.iSup_rankOne_eq_top (plusDatum 4 (GaloisField p f) hn)
    (Spin.plusDatum_isCTGroupDatum hn (Spin.plusDatum_iSup_eq_top 4 _ hn))

theorem iSup_nodeSub : ⨆ i : Fin 4, nodeSub p f i = ⊤ :=
  iSup_rankOne_of_eq p f _ (by norm_num) (modelUniv_pOmegaPlus_four p f (by norm_num))

theorem commutes_nodeSub {i j : Fin 4} (h : cartanD 4 i j = 0) :
    Commutes (nodeSub p f i) (nodeSub p f j) :=
  commutes_rankOne_plusDatum (K := GaloisField p f) (by norm_num) h

theorem nodeSub_standardPair :
    ∃ W, LinearBlockStandardPair (GaloisField p f) W (nodeSub p f 0) (nodeSub p f 1) :=
  (standardPair_plusDatum (F := GaloisField p f) (by norm_num) (by norm_num)).2

end Nodes

section OneModFour

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem natCard_units_eq (F : Type) [Field F] [Finite F] : Nat.card Fˣ = Nat.card F - 1 := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]

theorem natCard_galoisField_eq (hf : 1 ≤ f) : Nat.card (GaloisField p f) = p ^ f :=
  GaloisField.card p f (by omega)

theorem Ih8Model.dstarAdj_node_one_mod_four [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1) (M : Ih8Model p f Ω .POmegaPlus 4 f)
    (hne : Ω.Nonempty) :
    dstarAdj Ω ((nodeSub p f 0).map M.ψ) ((nodeSub p f 1).map M.ψ) := by
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.POmegaPlus) ≠ .G2 := by decide
  have hnpsl : ¬ (StatedLieTag.POmegaPlus = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hf1 : 1 ≤ f := M.admissible.2.1
  have hcardF : Nat.card (GaloisField p f) = p ^ f := natCard_galoisField_eq hf1
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by rw [hcardF]; omega
  have hmem : ∀ i, nodeSub p f i ∈ M.cls := fun i =>
    M.fund_subset_cls hne hG2 hD4 (nodeSub_mem_fund p f i)
  obtain ⟨W, hW⟩ := nodeSub_standardPair p f
  have hne01 : nodeSub p f 0 ≠ nodeSub p f 1 := by
    intro h
    refine not_commutes_self_modelFund hp2 M.isFundTag hq M.admissible
      (nodeSub_mem_fund p f 1) fun x hx y hy => ?_
    have hN : ∀ z ∈ nodeSub p f 1,
        z ∈ Subgroup.normalizer ((nodeSub p f 0 : Subgroup _) : Set _) := fun z hz => by
      rw [h]
      exact Subgroup.le_normalizer hz
    exact LinearBlockStandardPair.comm_of_normalizes h4 hW hx hy (hN x hx) (hN y hy)
  obtain ⟨x, hx⟩ := exists_orderOf_eq_two_part (GaloisField p f)ˣ
  obtain ⟨v, hvV, hvN, hvo⟩ := LinearBlockStandardPair.exists_torus_elt hW x
  refine M.dstarAdj_of_torus hΩ hp2 hq hD4 hnpsl (hmem 0) (hmem 1) hne01 hvV hvN
    (a := (Nat.card (GaloisField p f)ˣ).factorization 2) (hvo.trans hx) ?_
  rw [two_pow_sl2_of_one_mod_four (GaloisField p f) (by rw [hcardF]; exact hq4),
    natCard_units_eq]

theorem Ih8Model.dstarAdj_node_commuting [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (M : Ih8Model p f Ω .POmegaPlus 4 f) (hne : Ω.Nonempty) {j : Fin 4}
    (hj : cartanD 4 0 j = 0) :
    dstarAdj Ω ((nodeSub p f 0).map M.ψ) ((nodeSub p f j).map M.ψ) := by
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.POmegaPlus) ≠ .G2 := by decide
  have hmem : ∀ i, nodeSub p f i ∈ M.cls := fun i =>
    M.fund_subset_cls hne hG2 hD4 (nodeSub_mem_fund p f i)
  have hcomm : Commutes (nodeSub p f 0) (nodeSub p f j) := commutes_nodeSub p f hj
  have hne0 : nodeSub p f j ≠ nodeSub p f 0 := by
    intro h
    refine not_commutes_self_modelFund hp2 M.isFundTag hq M.admissible (nodeSub_mem_fund p f 0)
      fun x hx y hy => hcomm x hx y ?_
    rw [h]
    exact hy
  have hne' : (nodeSub p f j).map M.ψ ≠ (nodeSub p f 0).map M.ψ := fun h =>
    hne0 (ih8_eq_of_map_eq M.ψ M.ker_le_center (M.cls_perfect hp2 hD4 hq (hmem j))
      (M.cls_perfect hp2 hD4 hq (hmem 0)) h)
  exact dstarAdj_of_commutes hp2 hΩ (M.map_mem (hmem j)) hne'
    (ih8_commutes_map M.ψ hcomm.symm)

theorem ih8_dstarConnected_of_one_mod_four [Finite G] (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2)
    (hq : 5 ≤ p ^ f) (hq4 : p ^ f % 4 = 1) (M : Ih8Model p f Ω .POmegaPlus 4 f) :
    T3.DStarConnected Ω := by
  by_cases hne : Ω.Nonempty
  swap
  · intro K hK
    exact absurd ⟨K, hK⟩ hne
  have hD4 : (StatedLieTag.POmegaPlus) ≠ .trialityD4 := by decide
  have hG2 : (StatedLieTag.POmegaPlus) ≠ .G2 := by decide
  have hmem : ∀ i, nodeSub p f i ∈ M.cls := fun i =>
    M.fund_subset_cls hne hG2 hD4 (nodeSub_mem_fund p f i)
  refine M.dstarConnected_of_gens hΩ hG2 hD4 (nodeSub p f) 0 hmem (iSup_nodeSub p f) fun i => ?_
  fin_cases i
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (M.dstarAdj_node_one_mod_four hΩ hp2 hq hq4 hne)
  · exact Relation.ReflTransGen.single
      (M.dstarAdj_node_commuting hΩ hp2 hq hne (j := 2) (by decide))
  · exact Relation.ReflTransGen.single
      (M.dstarAdj_node_commuting hΩ hp2 hq hne (j := 3) (by decide))

end OneModFour

end CFSG.ClassicalInvolution.Asc77
