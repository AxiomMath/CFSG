module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNTwoAZNAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoTheoremZAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataU.layer_le_sup_of_two (hd : D1CaseTwoDataU p P M H R Rbar)
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hne : L₁ ≠ L₂) :
    CFSG.layer (H ⧸ primeComplementCore (G := H) p) ≤ L₁ ⊔ L₂ := by
  refine sSup_le fun L hL => ?_
  rcases hd.cfg.red.eq_or_eq_of_isComponentOf h₁ h₂ hne ((CFSG.isComponent_iff_open L).mp hL)
    with rfl | rfl
  · exact le_sup_left
  · exact le_sup_right

theorem D1CaseTwoDataU.nineThree_of_mixed (hd : D1CaseTwoDataU p P M H R Rbar)
    {L₁ L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (hL₁ : ¬ L₁ ≤ d1X0 p M H) (hL₂ : L₂ ≤ d1X0 p M H) :
    Hyp111NineThree p M H L₁ := by
  have he := hd.cfg.ext.toD1Escape
  have hne : L₁ ≠ L₂ := fun heq => hL₁ (heq ▸ hL₂)
  have hn := (hd.cfg.red.normal_of_two_components hd.cyclic h₁ h₂ hL₁ hL₂).1
  refine ⟨hn, plusCore_le_of_centralizer_le he
    (hd.cfg.red.centralizer_le_of_not_le hd.cyclic h₁ h₂ hL₁ hL₂), factor_of_top_le he ?_⟩
  refine (hd.cfg.red.top_le_sup_layer hd.cyclic h₁ h₂ hne).trans (sup_le le_sup_left ?_)
  refine (hd.layer_le_sup_of_two h₁ h₂ hne).trans (sup_le le_sup_right ?_)
  exact hL₂.trans le_sup_left

theorem D1CaseTwoDataU.nineThree_of_unique (hd : D1CaseTwoDataU p P M H R Rbar)
    (hA : CycAutRankLeTwo p (H ⧸ primeComplementCore (G := H) p) Rbar)
    {L₁ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (h₁ : IsComponentOf L₁ ⊤)
    (huniq : ∀ L : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L ⊤ → L = L₁) :
    Hyp111NineThree p M H L₁ := by
  have he := hd.cfg.ext.toD1Escape
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hO := hd.cfg.red.pCore_ne_bot_of_unique_of_aut hA hd.cyclic hd.rank h₁ huniq
  obtain ⟨z, hz, hzp⟩ : ∃ z ∈ CFSG.pCore p (H ⧸ primeComplementCore (G := H) p),
      orderOf z = p := by
    obtain ⟨z, hz⟩ : ∃ x : CFSG.pCore p (H ⧸ primeComplementCore (G := H) p),
        orderOf x = p := by
      rcases (CFSG.pCore_isPGroup (p := p)
          (G := H ⧸ primeComplementCore (G := H) p)).card_eq_or_dvd with h1 | hdvd
      · exact absurd (Subgroup.card_eq_one.mp h1) hO
      · exact exists_prime_orderOf_dvd_card' p hdvd
    exact ⟨z, z.2, (Subgroup.orderOf_coe z).trans hz⟩
  have hn : L₁.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hL : IsComponentOf (L₁.map (MulAut.conj g).toMonoidHom) ⊤ :=
      (ComponentClassification.LocalComponents.equiv_iff (MulAut.conj g) L₁).mpr h₁
    rw [← huniq _ hL]
    exact ⟨n, hn, rfl⟩
  refine ⟨hn, plusCore_le_of_centralizer_le he
    (hd.cfg.red.centralizer_le_of_pCore h₁ (hd.cyclic L₁ h₁) hz hzp), factor_of_top_le he ?_⟩
  obtain ⟨T₁, hT₁⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Rbar
    (Subgroup.Normal.isSubnormal hn)
  have htop := Sylow.normalizer_sup_eq_top T₁
  rw [hT₁] at htop
  rw [← htop]
  exact sup_le_sup_right (hd.cfg.red.normalizer_inf_le_of_pCore h₁ (hd.cyclic L₁ h₁) hz hzp) _

theorem D1CaseTwoDataU.nineThree_of_forall_le (hd : D1CaseTwoDataU p P M H R Rbar)
    (hA : CycAutRankLeTwo p (H ⧸ primeComplementCore (G := H) p) Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H)
    (hle : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ →
      L ≠ L' → L' ≤ d1X0 p M H) :
    Hyp111NineThree p M H L := by
  by_cases huniq : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ →
      L' = L
  · exact hd.nineThree_of_unique hA hL huniq
  · push Not at huniq
    obtain ⟨L₂, h₂, hne⟩ := huniq
    exact hd.nineThree_of_mixed hL h₂ hLX (hle L₂ h₂ (Ne.symm hne))

end CFSG.LocalAnalysis.RankThreeTheoremC
