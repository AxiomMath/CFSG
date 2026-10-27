module

public import CFSG.CGT.PushingUpLit.BHS.HomTransfer
public import CFSG.CGT.PushingUpLit.BHS7.SevenSeven

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

theorem exists_minimal_overgroup (h : MinCex G T) (h5 : Seven5 G T) {H : Subgroup Γ}
    (hH : IsMaximalSubgroup G H) (hTH : T ≤ H)
    (hNH : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ H) :
    ∃ P : Subgroup Γ, T ≤ P ∧ P < G ∧ ¬ P ≤ H ∧ ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ H := by
  have hne : ∃ X : Subgroup Γ, T ≤ X ∧ X < G ∧ ¬ X ≤ H := by
    by_contra hcon
    have hall : ∀ X : Subgroup Γ, T ≤ X → X < G → X ≤ H := fun X hTX hXG => by
      by_contra hXH
      exact hcon ⟨X, hTX, hXG, hXH⟩
    refine h5 ⟨h.sylow, fun hGN => hH.1.not_ge (fun _ hg => hNH ⟨hg, hGN hg⟩), H, hTH, hH.1, hall⟩
  obtain ⟨P, ⟨hTP, hPG, hPH⟩, hmin⟩ := (wellFounded_lt (α := Subgroup Γ)).has_min
    {X : Subgroup Γ | T ≤ X ∧ X < G ∧ ¬ X ≤ H} hne
  refine ⟨P, hTP, hPG, hPH, fun X hTX hXP => ?_⟩
  by_contra hXH
  exact hmin X ⟨hTX, hXP.trans hPG, hXH⟩ hXP

theorem minPar_of_minimal (h : MinCex G T) {H P : Subgroup Γ} (hTH : T ≤ H)
    (hNH : G ⊓ Subgroup.normalizer (T : Set Γ) ≤ H) (hTP : T ≤ P) (hPG : P < G)
    (hPH : ¬ P ≤ H) (hmin : ∀ X : Subgroup Γ, T ≤ X → X < P → X ≤ H) :
    MinPar P T (P ⊓ H) where
  syl := isSylowOf_of_isSylowTwoOf
    (isSylowTwoOf_of_le_of_le (isSylowTwoOf_of_isSylowOf h.sylow) hTP hPG.le)
  not_normal := fun hPN => hPH (fun _ hg => hNH ⟨hPG.le hg, hPN hg⟩)
  le_M := le_inf hTP hTH
  lt_P := lt_of_le_of_ne inf_le_left fun heq => hPH (heq.symm ▸ inf_le_right)
  max := fun X hTX hXP => le_inf hXP.le (hmin X hTX hXP)

theorem sup_eq_top_of_not_le {E H P : Subgroup Γ}
    (huniq : ∀ H' : Subgroup Γ, IsMaximalSubgroup G H' → E ⊔ baum T ≤ H' → H' = H)
    (hPG : P ≤ G) (hEG : E ≤ G) (hTP : T ≤ P) (hPH : ¬ P ≤ H) : P ⊔ E = G := by
  by_contra hne
  have hlt : P ⊔ E < G := lt_of_le_of_ne (sup_le hPG hEG) hne
  obtain ⟨M, hM, hPEM⟩ := exists_maximalSubgroup_ge hlt
  have hMH : M = H := huniq M hM (sup_le (le_sup_right.trans hPEM)
    ((C1GN.baum_le T).trans (hTP.trans (le_sup_left.trans hPEM))))
  exact hPH (hMH ▸ le_sup_left.trans hPEM)

end CFSG.CGT.PushingUpLit.BHS7
