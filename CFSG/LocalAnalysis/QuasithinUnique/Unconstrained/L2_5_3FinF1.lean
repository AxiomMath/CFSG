module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinL2p
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinBT
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinCore
public import CFSG.LieType.BorelTits.Classical
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Open CFSG.Quasithin

@[expose] def A6RadicalCharTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K R : Subgroup G),
    Nonempty (↥K ≃* alternatingGroup (Fin 6)) → R ≤ K → IsPGroup 2 ↥R → R ≠ ⊥ →
      pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R →
        CharTwo (K ⊓ Subgroup.normalizer (R : Set G))

@[expose] def L33M11RadicalCharTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K R : Subgroup G),
    (StatedClassicalModel ↥K .PSL 3 3 1 ∨
      Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)) → R ≤ K → IsPGroup 2 ↥R →
      R ≠ ⊥ → pCoreOf 2 (K ⊓ Subgroup.normalizer (R : Set G)) = R →
        CharTwo (K ⊓ Subgroup.normalizer (R : Set G))

@[expose] def NoCommutingConjugate : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H S : Subgroup G) (z : G),
    UnconstrainedSetting G T M → Tuple25 T M H S z →
      ∀ K : Subgroup G, IsComponentIn K H → ¬ fusionIsBenderGroup ↥K → ComponentList M S z K →
        (¬ IsL2pType ↥K ∨ InCase3 M z K) → ∀ g ∈ H, CFSG.conjugate K g = K

theorem radicalNormalizerCharTwo_of_facts
    (h252 : Lemma252) (hBT : RankTwoBorelFacts)
    (hA6 : A6RadicalCharTwo) (hL33 : L33M11RadicalCharTwo) (hNP : NoCommutingConjugate) :
    RadicalNormalizerCharTwo := by
  intro G _ _ T M H S z hs ht K hK hBe hcl R hRD hR2 hcomp hrad
  have hinn : ∀ L : Subgroup G, IsComponentIn L H → Ch1.InducesInner z L := fun L hL =>
    (h252 G T M H S z hs ht L hL).2.1
  by_cases hL2p : IsL2pType ↥K
  · exact charTwo_inf_normalizer_of_l2p hs ht hinn hK hL2p hRD hR2 hcomp hrad
  · have hall := hNP G T M H S z hs ht K hK hBe hcl (Or.inl hL2p)
    have hD : conjJoin H K = K := by
      refine le_antisymm (iSup_le fun g => ?_) (le_conjJoin_self H K)
      have := hall (g : G)⁻¹ (H.inv_mem g.2)
      simp only [CFSG.conjugate, inv_inv] at this
      exact this.le
    have hRC : ¬ R ≤ Subgroup.centralizer (K : Set G) := hcomp K hK (le_conjJoin_self H K)
    have hRne : R ≠ ⊥ := fun h => hRC (h ▸ bot_le)
    rw [hD] at hRD hrad ⊢
    have hq : CFSG.IsQuasisimple ↥K := BenderBranch.isQuasisimple_of_isComponentIn hK
    obtain ⟨-, -, -, -, hcase⟩ := hcl
    rcases hcase with h1 | h2 | h3 | h4
    · exact absurd h1.1 hBe
    · obtain ⟨hrt, -, -⟩ := h2
      rcases id hrt with ⟨n, -, hmod⟩ | ⟨n, -, hmod⟩ | hA6' | hcov
      · exact charTwo_inf_normalizer_of_holds hBT hq hrt
          (CFSG.LieType.BorelTits.holds_of_statedClassicalModel (G := ↥K) (t := .PSL) (n := 3)
            (p := 2) (f := n) hmod) hRD hR2 hRne hrad
      · exact charTwo_inf_normalizer_of_holds hBT hq hrt
          (CFSG.LieType.BorelTits.holds_of_statedClassicalModel (G := ↥K) (t := .PSp) (n := 2)
            (p := 2) (f := n) hmod) hRD hR2 hRne hrad
      · exact hA6 G K R hA6' hRD hR2 hRne hrad
      · exact charTwo_inf_normalizer_of_holds_quotient hBT hq hrt
          (CFSG.LieType.BorelTits.holds_of_statedClassicalModel (G := ↥K ⧸ CFSG.pCore 2 ↥K)
            (t := .PSL) (n := 3) (p := 2) (f := 2) hcov) hRD hR2 hRC hrad
    · exact hL33 G K R h3.1 hRD hR2 hRne hrad
    · exact absurd (Or.inl h4.1) hL2p

end CFSG.QuasithinUnique.Fin253
