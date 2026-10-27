module

public import CFSG.CGT.PushingUpLit.BHS7.TwoThree

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

theorem cStarIn_eq_of_baum_eq_bot {G T : Subgroup Γ} (h : baum T = ⊥) : cStarIn G T = G := by
  have hZ : omegaOneCenterOf T = ⊥ :=
    le_bot_iff.1 (h ▸ C1GN.omegaOneCenterOf_le_baum T)
  refine le_antisymm (cStarIn_le G T) ?_
  have h1 : G ≤ G ⊓ Subgroup.centralizer (omegaOneCenterOf T : Set Γ) := by
    rw [hZ]
    refine le_inf le_rfl fun g _ => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    simp [this]
  exact h1.trans (centralizer_le_cStarIn G T)

theorem isBTBlock_of_sub {G L S T E : Subgroup Γ} (hE : IsBTBlock L S E) (hLG : L ≤ G)
    (hb : baum S = baum T) (hn : ¬ E ≤ cStarIn G T) : IsBTBlock G T E where
  le := hE.le.trans hLG
  residual := hE.residual
  commutator := by rw [← hb]; exact hE.commutator
  perfect := hE.perfect
  elemAbelian := hE.elemAbelian
  nonCentral := by
    intro h0
    apply hn
    refine le_trans (le_inf (hE.le.trans hLG) ?_) (centralizer_le_cStarIn G T)
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have h1 : ⁅e, z⁆ ∈ (⁅E, omegaOneCenterOf T⁆ : Subgroup Γ) :=
      Subgroup.commutator_mem_commutator he hz
    rw [h0, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  type := hE.type

section Finite

variable [Finite Γ]

theorem seven_three {G T : Subgroup Γ} (h : MinCex G T) {T' L S : Subgroup Γ}
    (hT' : IsSylowTwoOf T' G) (hL : L ∈ lSet G T') (hS : IsSylowTwoOf S L) :
    CharTwo L ∧ cStarIn L S ≠ L ∧ LocalCStarConcl L S := by
  obtain ⟨hLG, hBL, hLC⟩ := hL
  have hb0 : baum T' ≠ ⊥ := by
    intro h0
    apply hLC
    rw [cStarIn_eq_of_baum_eq_bot (G := G) h0]
    exact hLG.le
  obtain ⟨S₁, hS₁, hBS₁⟩ := B6.exists_isSylowTwoOf_ge (hT'.2.1.to_le inf_le_left) hBL
  have hcharL : CharTwo L := two_three_c h.charTwo hT' hLG.le hS₁ hBS₁
  have hne₁ : cStarIn L S₁ ≠ L := by
    intro heq
    apply hLC
    have := two_three_d hT' hb0 hLG.le hS₁ hBS₁
    rw [heq] at this
    exact this
  obtain ⟨l, hl, hlS⟩ := B6.isSylowTwoOf_exists_conj hS₁ hS
  have hne : cStarIn L S ≠ L := by
    intro heq
    apply hne₁
    have h1 : cStarIn L S = conjSub l (cStarIn L S₁) := by
      have := cStarIn_conjSub l L S₁
      rwa [conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hl), ← b6_conjSub_eq, ← hlS]
        at this
    have h2 : conjSub l (cStarIn L S₁) = conjSub l L := by
      rw [← h1, heq, conjSub_eq_of_mem_normalizer (Subgroup.le_normalizer hl)]
    exact (B6.conjSub l).injective h2
  exact ⟨hcharL, hne, h.ih L S (Nine.card_lt_of_lt hLG) hcharL (hS : IsSylowOf 2 S L) hne⟩

end Finite

end CFSG.CGT.PushingUpLit.BHS7
