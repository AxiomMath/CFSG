module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Fstar
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.FinalFacts
public import CFSG.LocalAnalysis.QuasithinUnique.BenderBranchBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsPSL2More
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsTransport

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped MatrixGroups

theorem involutions_conj_of_iso
    {K : Type} [Group K] [Finite K]
    (h : Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* PSL(2, ZMod 7))) :
    ∀ a b : K, a ≠ 1 → a * a = 1 → b ≠ 1 → b * b = 1 → ∃ k : K, k⁻¹ * a * k = b := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · intro a b ha1 ha2 hb1 hb2
    obtain ⟨g, hg⟩ := alt6_involutions_conj (e a) (e b) (fun h => ha1 (e.injective (by simpa using h)))
      (by rw [← map_mul, ha2, map_one])
      (fun h => hb1 (e.injective (by simpa using h))) (by rw [← map_mul, hb2, map_one])
    exact ⟨e.symm g, e.injective (by simpa using hg)⟩
  · intro a b ha1 ha2 hb1 hb2
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hd : L2pData PSL(2, ZMod 7) :=
      Unc25K1.psl2_l2pData (K := ZMod 7) (p := 7) le_rfl (by simp)
        (Or.inr ⟨by norm_num, 3, by norm_num⟩)
    have hd' : L2pData K := Unc25K1.l2pData_of_mulEquiv e hd
    have hoa : orderOf a = 2 := orderOf_eq_prime (by rwa [← pow_two] at ha2) ha1
    have hob : orderOf b = 2 := orderOf_eq_prime (by rwa [← pow_two] at hb2) hb1
    obtain ⟨k, hk⟩ := hd'.single_class a b hoa hob
    exact ⟨k⁻¹, by simpa using hk⟩

section Components

variable {G : Type} [Group G]

theorem isComponentIn_iff_open {K X : Subgroup G} :
    IsComponentIn K X ↔ CFSG.Open.IsComponentOf K X := by
  constructor
  · rintro ⟨hKX, hc⟩
    have h1 := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      hKX).2 hc
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open K X).1 h1
  · intro h
    have h1 := (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open K X).2 h
    exact ⟨h.1, (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
      h.1).1 h1⟩

variable [Finite G]

theorem not_isComponentIn_of_charTwo {X : Subgroup G} (hX : CharTwo X) (K : Subgroup G) :
    ¬ IsComponentIn K X := by
  intro hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CFSG.IsCharacteristicP 2 ↥X := by
    unfold CFSG.IsCharacteristicP
    exact (centralizer_pCore_le_iff_pCoreOf 2 X).2 hX
  have hlayer := CFSG.layer_eq_bot_of_isCharacteristicP ↥X 2 hchar
  have hle0 : K.subgroupOf X ≤ CFSG.layer ↥X := le_sSup hK.2
  have hle : K.subgroupOf X ≤ ⊥ := by rw [← hlayer]; exact hle0
  have hKbot : K = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h3 : (⟨g, hK.1 hg⟩ : X) ∈ (⊥ : Subgroup X) := hle hg
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h3))
  have hq : CFSG.IsQuasisimple K := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact ((Subgroup.nontrivial_iff_ne_bot K).mp hnt) hKbot

theorem fit_le_pCoreOf_sup_oddCoreIn (X : Subgroup G) :
    sSup {N : Subgroup G | N ≤ X ∧ (N.subgroupOf X).Normal ∧ Group.IsNilpotent N} ≤
      pCoreOf 2 X ⊔ oddCoreIn X := by
  refine sSup_le fun N ⟨hNX, hNn, hNnil⟩ => ?_
  have hnil : Group.IsNilpotent (N.subgroupOf X) :=
    (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNX)).mpr hNnil
  have h1 : N.subgroupOf X ≤ CFSG.fittingSubgroup ↥X := le_sSup ⟨hNn, hnil⟩
  have h2 : CFSG.fittingSubgroup ↥X ≤ CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun p => ?_
    by_cases hp : p.1.1 = 2
    · rw [hp]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      have hq : Nat.Prime p.1.1 := Nat.prime_of_mem_primeFactors p.1.2
      have hqodd : Odd p.1.1 := hq.odd_of_ne_two hp
      refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p.1.1) (G := ↥X)).exists_card_eq
      rw [hn]
      exact hqodd.pow
  have hmap : (CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X).map X.subtype = pCoreOf 2 X ⊔ oddCoreIn X := by
    rw [Subgroup.map_sup, pCoreOf]
    rfl
  intro g hg
  have hgX : g ∈ X := hNX hg
  have : (⟨g, hgX⟩ : X) ∈ CFSG.pCore 2 ↥X ⊔ CFSG.oddCore ↥X := h2 (h1 hg)
  rw [← hmap]
  exact ⟨_, this, rfl⟩

end Components

section Config

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3K.z₁_mem_K (hK : A3A3K T M H S L s x z₁ z₂ K) : z₁ ∈ K :=
  hK.L_le_K (hK.isA4.le hK.z₁_mem.1)

theorem lemma2_4_33 (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) :
    ∀ (G : Type) [Group G] [Finite G] (T M H S L : Subgroup G) (s x z₁ z₂ : G) (K : Subgroup G),
      A3A3K T M H S L s x z₁ z₂ K →
        layerOf (centralizerElem z₂) = K ∧
          genFittingOf (centralizerElem z₂) = K ⊔ pCoreOf 2 (centralizerElem z₂) := by
  intro G _ _ T M H S L s x z₁ z₂ K hAK
  have hcs := hAK.cs
  have hB := basic31 hD h27_1 hAK.toA3A3
  obtain ⟨hΓ2, -, hS₁M⟩ := remark31_G₂ hD h27_1 hAK.toA3A3x
  have hz := z_central hB hAK.toA3A3x
  have hMz : centralizer ({z₁ * z₂} : Set G) ≤ M :=
    hcs.setting.centralizer_le_of_mem_center_isSylowTwoOf hcs.setting.isSylowTwoOf_M hz hAK.z_ne
  have hcharM : CharTwo (centralizerElem z₂ ⊓ M) :=
    IsGamma0.charTwo_inf hcs.setting (Or.inr hΓ2) hS₁M
  have hz₁K := hAK.z₁_mem_K
  have hC : centralizerElem z₂ ⊓ centralizer (K : Set G) ≤ centralizerElem z₂ ⊓ M := by
    rintro c ⟨hcG, hcK⟩
    refine ⟨hcG, hMz ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h1 : c * z₁ = z₁ * c := (Subgroup.mem_centralizer_iff.mp hcK z₁ hz₁K).symm
    have h2 : c * z₂ = z₂ * c := Subgroup.mem_centralizer_singleton_iff.mp hcG
    calc c * (z₁ * z₂) = (c * z₁) * z₂ := by group
      _ = (z₁ * c) * z₂ := by rw [h1]
      _ = z₁ * (c * z₂) := by group
      _ = z₁ * (z₂ * c) := by rw [h2]
      _ = (z₁ * z₂) * c := by group
  have hlayer : layerOf (centralizerElem z₂) = K := by
    refine le_antisymm (sSup_le fun K' hK' => ?_) (le_sSup hAK.K_comp)
    rcases BenderBranch.eq_or_commute_of_isComponentIn hAK.K_comp hK' with h | h
    · exact h.ge
    · exfalso
      have hle : K' ≤ centralizer (K : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer).mp (by
          rw [Subgroup.commutator_comm]; exact h)
      have hK'M : K' ≤ centralizerElem z₂ ⊓ M := fun k hk => hC ⟨hK'.1 hk, hle hk⟩
      exact not_isComponentIn_of_charTwo hcharM K'
        (BenderBranch.isComponentIn_of_le hK' hK'M inf_le_left)
  refine ⟨hlayer, ?_⟩
  have hodd := oddCoreIn_centralizer₂_eq_bot hD h27_1 hAK.toA3A3x
  have hfit : sSup {N : Subgroup G | N ≤ centralizerElem z₂ ∧
      ((N.subgroupOf (centralizerElem z₂)).Normal) ∧ Group.IsNilpotent N} =
        pCoreOf 2 (centralizerElem z₂) := by
    refine le_antisymm ?_ ?_
    · have := fit_le_pCoreOf_sup_oddCoreIn (centralizerElem z₂)
      rwa [hodd, sup_bot_eq] at this
    · refine le_sSup ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 _, ?_,
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).isNilpotent⟩
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (CFSG.LieType.BorelTits.pCoreOf_le 2 _)).mpr
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hlay2 : sSup {K' : Subgroup G | CFSG.Open.IsComponentOf K' (centralizerElem z₂)} = K := by
    have : {K' : Subgroup G | CFSG.Open.IsComponentOf K' (centralizerElem z₂)} =
        {K' : Subgroup G | IsComponentIn K' (centralizerElem z₂)} :=
      Set.ext fun K' => isComponentIn_iff_open.symm
    rw [this]
    exact hlayer
  unfold genFittingOf CFSG.Open.quasithinGenFitting
  rw [hfit, hlay2, sup_comm]

end Config

end CFSG.QuasithinUnique.DoubleA3
