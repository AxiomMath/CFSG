module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2SwapChainRoots
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsSwap

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.Assembly.LowTwoRank
open CFSG.LieType.Ree (ReeTag)

local instance f4PilotQ2SwapChainSylowNeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩


variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem commute_of_mem_rootGroup_of_not_isRoot {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ) (h0 : Adjoint.iform γ δ = 0) (hp : ¬ IsRoot .F4 (γ + δ))
    {a b : adjointGroup .F4 K} (ha : a ∈ (Adjoint.f4Datum K).rootGroup γ)
    (hb : b ∈ (Adjoint.f4Datum K).rootGroup δ) : a * b = b * a := by
  obtain ⟨c, hc⟩ := (mem_rootGroup_iff_pinnedX hγ).1 ha
  obtain ⟨d, hd⟩ := (mem_rootGroup_iff_pinnedX hδ).1 hb
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc, ← hd]
  exact pinnedX_commute_of_iform_eq_zero K hγ hδ h0 hp c d

theorem commute_of_mem_rootGroup {γ δ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ)
    (hδ : IsRoot .F4 δ)
    (h : (Adjoint.iform γ δ = 0 ∧ ¬ IsRoot .F4 (γ + δ)) ∨
      (Adjoint.iform (psiF4 γ) (psiF4 δ) = 0 ∧ ¬ IsRoot .F4 (psiF4 γ + psiF4 δ)))
    {a b : adjointGroup .F4 K} (ha : a ∈ (Adjoint.f4Datum K).rootGroup γ)
    (hb : b ∈ (Adjoint.f4Datum K).rootGroup δ) : a * b = b * a := by
  rcases h with ⟨h0, hp⟩ | ⟨h0, hp⟩
  · exact commute_of_mem_rootGroup_of_not_isRoot hγ hδ h0 hp ha hb
  · have ha' : graphAutF4 K a ∈ (Adjoint.f4Datum K).rootGroup (psiF4 γ) := by
      rw [← map_graphAutF4_rootGroup hγ]
      exact ⟨a, ha, rfl⟩
    have hb' : graphAutF4 K b ∈ (Adjoint.f4Datum K).rootGroup (psiF4 δ) := by
      rw [← map_graphAutF4_rootGroup hδ]
      exact ⟨b, hb, rfl⟩
    apply (graphAutF4 K).injective
    rw [map_mul, map_mul]
    exact commute_of_mem_rootGroup_of_not_isRoot (isRoot_psiF4 hγ) (isRoot_psiF4 hδ) h0 hp ha' hb'

abbrev u12 : List ℕ := [0, 1, 3, 2, 1, 0, 2, 3]

variable (K) in
@[expose] noncomputable def B12 : Subgroup (adjointGroup .F4 K) :=
  (B2Levi K).map (MulAut.conj (wRep K u12)).toMonoidHom

abbrev v0120 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 2, 0]
abbrev v0100 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 0, 0]
abbrev v0110 : Fin (Tag.rank .F4) → ℤ := ![0, 1, 1, 0]
abbrev v0010 : Fin (Tag.rank .F4) → ℤ := ![0, 0, 1, 0]
abbrev v1110 : Fin (Tag.rank .F4) → ℤ := ![1, 1, 1, 0]

abbrev b2List : List (Fin (Tag.rank .F4) → ℤ) :=
  [![0, 1, 0, 0], ![0, 1, 2, 0], ![0, 0, 1, 0], ![0, 1, 1, 0],
    -![0, 1, 0, 0], -![0, 1, 2, 0], -![0, 0, 1, 0], -![0, 1, 1, 0]]

theorem mem_b2List_of_mem_b2LeviRoots {γ : Fin (Tag.rank .F4) → ℤ} (hγ : γ ∈ b2LeviRoots) :
    γ ∈ b2List := by
  obtain ⟨hr, h0, h3⟩ := mem_b2LeviRoots.1 hγ
  have hmem := mem_rootFinset.2 hr
  have key : ∀ v ∈ rootFinset .F4, v 0 = 0 → v 3 = 0 → v ∈ b2List := by decide +kernel
  exact key γ hmem h0 h3

theorem b2List_commute_check : ∀ γ ∈ b2List, ∀ δ ∈ b2List,
    (Adjoint.iform (wordAct u12 γ) δ = 0 ∧ wordAct u12 γ + δ ∉ rootFinset .F4) ∨
      (Adjoint.iform (psiF4 (wordAct u12 γ)) (psiF4 δ) = 0 ∧
        psiF4 (wordAct u12 γ) + psiF4 δ ∉ rootFinset .F4) := by
  decide +kernel

theorem B12_le_centralizer_B2Levi :
    B12 K ≤ centralizer (B2Levi K : Set (adjointGroup .F4 K)) := by
  have hB12 : B12 K = ⨆ γ ∈ b2LeviRoots, (Adjoint.f4Datum K).rootGroup (wordAct u12 γ) := by
    rw [B12, B2Levi_eq_iSup_rootGroup, Subgroup.map_iSup]
    refine iSup_congr fun γ => ?_
    rw [Subgroup.map_iSup]
    exact iSup_congr fun hγ => map_wRep_rootGroup u12 (mem_b2LeviRoots.1 hγ).1
  rw [hB12]
  refine iSup₂_le fun γ hγ => ?_
  rw [le_centralizer_iff, B2Levi_eq_iSup_rootGroup]
  refine iSup₂_le fun δ hδ => ?_
  intro b hb
  rw [mem_centralizer_iff]
  intro a ha
  have hr : IsRoot .F4 γ := (mem_b2LeviRoots.1 hγ).1
  have hrδ : IsRoot .F4 δ := (mem_b2LeviRoots.1 hδ).1
  have hru : IsRoot .F4 (wordAct u12 γ) := by
    rw [← wordW_smul_eq_wordAct]
    exact IsRoot.smul hr _
  have hc := b2List_commute_check γ (mem_b2List_of_mem_b2LeviRoots hγ) δ
    (mem_b2List_of_mem_b2LeviRoots hδ)
  simp only [mem_rootFinset] at hc
  exact commute_of_mem_rootGroup hru hrδ hc ha hb

theorem card_B2Levi (hK : Nat.card K = 2) : Nat.card (B2Levi K) = 720 := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨e6⟩ := SymplecticPilot.nonempty_statedSp_mulEquiv_perm_of_eq hK (m := 2) rfl
  rw [← Nat.card_congr (b2LeviEquiv K).toEquiv, Nat.card_congr e6.toEquiv, Nat.card_perm,
    Nat.card_fin]
  rfl

theorem card_B12 (hK : Nat.card K = 2) : Nat.card (B12 K) = 720 := by
  rw [B12, Subgroup.card_map_of_injective (MulAut.conj _).injective, card_B2Levi hK]

theorem rootSL2_wordAct_le_B12 {β : Fin (Tag.rank .F4) → ℤ} (hβ : β ∈ b2LeviRoots)
    (hβ' : -β ∈ b2LeviRoots) : rootSL2 K (wordAct u12 β) ≤ B12 K := by
  rw [← map_wRep_rootSL2 u12 (mem_b2LeviRoots.1 hβ).1, B12]
  exact Subgroup.map_mono (rootSL2_le_B2Levi hβ hβ')

theorem mem_b2LeviRoots_of_check {β : Fin (Tag.rank .F4) → ℤ} (h : β ∈ rootFinset .F4)
    (h0 : β 0 = 0) (h3 : β 3 = 0) : β ∈ b2LeviRoots :=
  mem_b2LeviRoots.2 ⟨mem_rootFinset.1 h, h0, h3⟩

theorem factorization_720_three : (720 : ℕ).factorization 3 = 2 := by
  rw [Nat.factorization_def _ Nat.prime_three, show (720 : ℕ) = 3 ^ 2 * 80 by norm_num,
    padicValNat.mul (by positivity) (by norm_num), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd (by decide)]

theorem exists_conj_std (hK : Nat.card K = 2) {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) :
    ∃ c ∈ B12 K, ((X₀ ⊔ stdX K).map (graphAutF4 K).toMonoidHom).map
      (MulAut.conj c).toMonoidHom = X₀ ⊔ stdX K := by
  have : Finite (ModGL Tag.F4 K) := finite_modGL
  have : Finite (adjointGroup .F4 K) := inferInstance
  have hX₀' : Nat.card X₀ = Nat.card K + 1 := by rw [hX₀, hK]
  obtain ⟨-, hdis, hXD⟩ : centralizer (X₀ : Set (adjointGroup .F4 K)) = X₀ ⊔ C3Levi K ∧
      Disjoint X₀ (C3Levi K) ∧ X₀ ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)) := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact centralizer_nonsplit hXJ hcyc hX₀'
  have hXr : X₀ ≤ rootSL2 K rootR := by
    rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
    exact hXJ
  have hF := twoStdPairFacts_std K hK
  have h1 : rootSL2 K rootR ≤ B12 K := by
    have := rootSL2_wordAct_le_B12 (K := K) (β := v0120)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
    rwa [show wordAct u12 v0120 = rootR by decide +kernel] at this
  have h2 : rootSL2 K root0122 ≤ B12 K := by
    have := rootSL2_wordAct_le_B12 (K := K) (β := v0100)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
    rwa [show wordAct u12 v0100 = root0122 by decide +kernel]
      at this
  have h3 : rootSL2 K rootS ≤ B12 K := by
    have := rootSL2_wordAct_le_B12 (K := K) (β := v0110)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
    rwa [show wordAct u12 v0110 = rootS by decide +kernel] at this
  have h4 : rootSL2 K v1110 ≤ B12 K := by
    have := rootSL2_wordAct_le_B12 (K := K) (β := v0010)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
      (mem_b2LeviRoots_of_check (by decide +kernel) rfl rfl)
    rwa [show wordAct u12 v0010 =
      v1110 by decide +kernel] at this
  set T := X₀ ⊔ stdX K with hT
  set T' := T.map (graphAutF4 K).toMonoidHom with hT'
  have hTB : T ≤ B12 K := sup_le (hXr.trans h1) (stdX_le_rootSL2.trans h2)
  have hT'B : T' ≤ B12 K := by
    rw [hT', hT, Subgroup.map_sup]
    refine sup_le ((Subgroup.map_mono hXr).trans ?_) ((Subgroup.map_mono stdX_le_rootSL2).trans ?_)
    · rw [map_graphAutF4_rootSL2 isRoot_rootR, psiF4_rootR]
      exact h3
    · rw [map_graphAutF4_rootSL2 isRoot_root0122,
        show psiF4 root0122 = v1110 by decide +kernel]
      exact h4
  have hcT : Nat.card T = 9 := by
    have hAB : stdX K ≤ centralizer (X₀ : Set (adjointGroup .F4 K)) :=
      hF.xPP_le.trans (le_centralizer_iff.1 hXD)
    have hdisj : X₀ ⊓ stdX K = ⊥ :=
      le_bot_iff.1 ((inf_le_inf_left _ hF.xPP_le).trans (disjoint_iff.1 hdis).le)
    have hcX : Nat.card (stdX K) = 3 := card_stdX
    rw [hT, card_sup_eq_mul_of_le_centralizer hAB hdisj, hX₀, hcX]
  have hcT' : Nat.card T' = 9 := by
    rw [hT', Subgroup.card_map_of_injective (f := (graphAutF4 K).toMonoidHom)
      (graphAutF4 K).injective, hcT]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac : (Nat.card (B12 K)).factorization 3 = 2 := by rw [card_B12 hK, factorization_720_three]
  have hcP : Nat.card (T'.subgroupOf (B12 K)) = 3 ^ (Nat.card (B12 K)).factorization 3 := by
    rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT'B).toEquiv, hcT']
    rfl
  have hcQ : Nat.card (T.subgroupOf (B12 K)) = 3 ^ (Nat.card (B12 K)).factorization 3 := by
    rw [hfac, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTB).toEquiv, hcT]
    rfl
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (B12 K) (Sylow.ofCard _ hcP) (Sylow.ofCard _ hcQ)
  refine ⟨g, g.2, ?_⟩
  have hsub : T'.map (MulAut.conj (g : adjointGroup .F4 K)).toMonoidHom ≤ T := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : (⟨y, hT'B hy⟩ : B12 K) ∈ T'.subgroupOf (B12 K) := hy
    have hmem : MulAut.conj g • (⟨y, hT'B hy⟩ : B12 K) ∈
        ((g • Sylow.ofCard _ hcP : Sylow 3 (B12 K)) : Subgroup (B12 K)) := by
      rw [Sylow.coe_subgroup_smul, Sylow.coe_ofCard]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hy'
    rw [hg, Sylow.coe_ofCard, mem_subgroupOf] at hmem
    exact hmem
  refine Subgroup.eq_of_le_of_card_ge hsub ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hcT', hcT]

end CFSG.SeitzReduction.F4Pilot
