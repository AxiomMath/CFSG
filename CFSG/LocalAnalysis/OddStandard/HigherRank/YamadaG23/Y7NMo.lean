module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7NTw
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54Card
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7SFc

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem frameWith_Sσ_eq (s : Setting3 G L) (g : G) :
    (frameWith s g).Sσ = s.fr.S ⊔ Subgroup.zpowers g := by
  have hset : ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
      ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀} : Set G) ∪ {g} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_empty_iff_false]
    tauto
  change Subgroup.closure ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂, s.fr.h₀, g} : Set G) =
    s.fr.S ⊔ Subgroup.zpowers g
  rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
  rfl

theorem sgMore_of_setting {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {g : G}
    (hg2 : g ^ 2 = 1) (hgσ : ActsAs L g s.fr'.σ) : SgMore s.fr.S s.fr.F g := by
  obtain ⟨h13, h15, -⟩ := hH.hLF.sigma g hg2 hgσ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx f hf
    have hxN : x ∈ normalizer (s.fr.F : Set G) :=
      (Subgroup.mem_inf.mp (y54_S_le_N hH hx)).2
    exact (Subgroup.mem_set_normalizer_iff.mp hxN f).mp hf
  · intro f hf
    have hmemL : f * (frameWith s g).σ ∈
        {y : G | ∃ c ∈ centEl (frameWith s g).S (frameWith s g).σ,
          y = c * (frameWith s g).σ} :=
      ⟨f, h13.1.symm ▸ hf, rfl⟩
    have hmem : f * (frameWith s g).σ ∈
        conjClass (frameWith s g).S (frameWith s g).σ := h13.2.2.1 ▸ hmemL
    obtain ⟨s', hs', hs'eq⟩ := hmem
    exact ⟨s', hs', hs'eq.symm⟩
  · intro E hE hEcomm
    refine h15.2.2.2.2.1 E ?_ hEcomm
    rwa [frameWith_Sσ_eq s g]
  · intro E hE hEea hEcard
    have hEσ : E ≤ (frameWith s g).Sσ := by rwa [frameWith_Sσ_eq s g]
    have hmem : E ∈ maxElemAbelian (frameWith s g).Sσ := by
      refine ⟨hEσ, hEea, ?_⟩
      intro Y' hEY' hY'σ hY'ea
      have h16 : Nat.card Y' ≤ 16 := h15.2.2.2.2.1 Y' hY'σ hY'ea.1
      exact (Subgroup.eq_of_le_of_card_ge hEY' (by omega)).symm
    rw [h15.2.2.2.1.2.2, Set.mem_sdiff, Set.mem_insert_iff] at hmem
    rcases hmem with ⟨hcase, -⟩
    rcases hcase with hcase | hcase
    · simpa only [Subgroup.zpowers_eq_closure, frameWith] using hcase
    · exfalso
      have h8 : Nat.card E ≤ 8 :=
        (s3_rankFacts hH).bound E (show E ≤ s.fr.S from hcase.1) hcase.2.1
      omega

end CFSG.OddStandard.HigherRank.YamadaG23
