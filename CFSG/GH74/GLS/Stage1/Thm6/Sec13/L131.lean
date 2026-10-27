module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.DMain
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Claim1b
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Setup4

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup
open scoped commutatorElement

theorem h0Type_of_sylow {G : Type*} [Group G] [Finite G] {x : G} {T V H : Subgroup G} {f : G}
    (d : D13 x T V H f) (hsyl : Sylow2In H (centralizer (V : Set G))) : H0Type (Hzero H f) := by
  rcases d.iv4 with h1 | h2 | h3 | ⟨n, hn, ⟨e⟩⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inl h2))
  · exact Or.inr (Or.inr (Or.inr h3))
  · by_cases hn2 : 2 ≤ n
    · exact Or.inr (Or.inl ⟨n, hn2, ⟨e⟩⟩)
    · exfalso
      have hn1 : n = 1 := by omega
      subst hn1
      have hcard : Nat.card (Hzero H f) = 4 := by
        rw [Nat.card_congr e.toEquiv, card_Z2n2]; norm_num
      have hVH0 : V ≤ Hzero H f := InH.V_le_Hzero d.out d.hI
      have hV : V = Hzero H f :=
        Subgroup.eq_of_le_of_card_ge hVH0 (by rw [hcard, d.out.V_four.2])
      have hH : H = EV x V := by
        rw [← d.iv2, ← hV]; rfl
      rw [hH] at hsyl
      exact d.out.not_sylow_E hsyl

theorem lemma13_1_d13 (h9 : IG_9_16) (h27 : IV2_2_7) {G : Type} [Group G] [Finite G] {x : G}
    {T V : Subgroup G} (h : Out12 G x T V) :
    ∃ (H : Subgroup G) (f : G), D13 x T V H f ∧ Lemma13_1Conc x V H f := by
  obtain ⟨H, f, hI, hmax⟩ := h.exists_maximal_InH
  have hCx : H ⊓ centralizer ({x} : Set G) = EV x V := InH.C_H_x h hI
  obtain ⟨iv1, iv2, iv3, iv4⟩ := h27 G H x f hI.H2 hI.x_mem h.x_ne h.x_sq
    (by rw [hCx]; exact h.EV_elemAb) (by rw [hCx]; exact h.card_EV) hI.f3 hI.f_H hI.f_comm_x
    (InH.exists_noncomm h hI)
  have d : D13 x T V H f :=
    ⟨h, hI, iv1, iv2, iv3, iv4, fun g hgN hgH => InH.claim1 h9 h hI iv1 iv2 iv3 iv4 hgN hgH⟩
  have hsyl := d.sylow_of_maximal hmax
  exact ⟨H, f, d, ⟨hsyl, hI.f3, hI.f_N, hI.f_C, hI.f_H, hI.C_H, iv2.symm, d.x_not_mem_H0,
    h0Type_of_sylow d hsyl⟩⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
