module

public import CFSG.CGT.PushingUpLit.BHS.ThreeSixC
public import CFSG.CGT.PushingUpLit.BHS.FourTwoC

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

section Five

variable {V : Type} [CommGroup V] [Finite V]

theorem exists_isAOff {P : Subgroup (MulAut V)} (h : ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A) :
    ∃ A : Subgroup (MulAut V), IsAOff P A := by
  obtain ⟨A₁, hA₁P, hA₁⟩ := h
  have hmem : offMax P ∈ {n | ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A ∧ wt A = n} :=
    Nat.sSup_mem ⟨wt A₁, A₁, hA₁P, hA₁, rfl⟩ (bddAbove_wt P)
  obtain ⟨A₀, hA₀P, hA₀, hA₀w⟩ := hmem
  obtain ⟨A, ⟨hAA₀, hA, hAw⟩, hAmin⟩ :
      ∃ A ∈ {B : Subgroup (MulAut V) | B ≤ A₀ ∧ IsOff B ∧ wt B = offMax P},
        ∀ B ∈ {B : Subgroup (MulAut V) | B ≤ A₀ ∧ IsOff B ∧ wt B = offMax P},
          Nat.card A ≤ Nat.card B := by
    refine Set.exists_min_image _ (fun B : Subgroup (MulAut V) => Nat.card B) (Set.toFinite _) ?_
    exact ⟨A₀, le_rfl, hA₀, hA₀w⟩
  refine ⟨A, hAA₀.trans hA₀P, hA, hAw, fun B hBA hB hBw => ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hBA (hAmin B ⟨hBA.trans hAA₀, hB, hBw⟩)

structure Hyp51 (P T M : Subgroup (MulAut V)) : Prop where
  minpar : MinPar P T M
  o2 : pCoreOf 2 P = ⊥
  off : ∃ A : Subgroup (MulAut V), A ≤ P ∧ IsOff A
  cen : cenIn P (fixV T) ≤ M

namespace Hyp51

variable {P T M : Subgroup (MulAut V)}

@[expose] def offSet (P : Subgroup (MulAut V)) : Set (Subgroup (MulAut V)) :=
  {A | IsAOff P A}

theorem exists_mem_dInter (h : Hyp51 P T M) :
    ∃ A : Subgroup (MulAut V), A ∈ dInter (offSet P) T := by
  obtain ⟨A, hA⟩ := exists_isAOff h.off
  obtain ⟨k, hkP, hk⟩ := Glauberman.exists_conj_le_of_isSylowOf h.minpar.syl
    (isPGroup_of_isElemAbelian2 hA.2.1.2.2.1) hA.1
  exact ⟨conjSub k A, hA.conj hkP, hk⟩

theorem hyp43 (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) :
    Hyp43 P (offSet P) T M := by
  have hnum : ∀ A, A ∈ offSet P → OffNumeric A := fun A hA =>
    three_six_numeric hV h.minpar h.o2 h.cen hA
  have h41 : Hyp41 P (offSet P) :=
    { le := fun A hA => hA.1
      ne_bot := fun A hA => hA.2.1.2.1
      elemAb := fun A hA => hA.2.1.2.2.1
      conj_mem := fun A hA g hg => hA.conj hg
      quad := fun A hA => (hnum A hA).quad
      card_eq := fun A hA => (hnum A hA).card
      fixV_eq := fun A hA => (hnum A hA).fixV_eq
      card_prod := fun A hA B hB hBA hc =>
        three_six_commuting hV h.minpar h.o2 h.cen hA hB hBA hc }
  have hTM : T ≤ M := h.minpar.le_M
  refine
  { toHyp42 :=
    { toHyp41 := h41
      syl := h.minpar.syl
      le_M := hTM
      M_le := h.minpar.M_le
      ne_core := ?_
      normSet_le := ?_
      cen_le := h.cen }
    max := fun A hA X hX hXP => hA.wt_le hXP hX }
  ·
    intro heq
    obtain ⟨A, hAD, hAT⟩ := h.exists_mem_dInter
    have hAcore : A ∈ dCore P (offSet P) M := heq ▸ hAD
    have hAK : A ≤ Glauberman.coreIn P M := fun y hy =>
      Glauberman.mem_coreIn.2 fun g hg => mem_conjSub_iff.1 (hAcore.2 g hg hy)
    have hnorm : P ≤ Subgroup.normalizer ((Glauberman.coreIn P M : Subgroup (MulAut V)) : Set _) :=
      Glauberman.le_normalizer_coreIn P M
    have hKM : Glauberman.coreIn P M ≤ M := Glauberman.coreIn_le
    have h33 := three_three_a h.minpar.syl h.minpar.lt_P h.minpar.max
      (Glauberman.coreIn_le.trans h.minpar.M_le) hnorm hKM
    have hle : Glauberman.coreIn P M ⊓ T ≤ pCoreOf 2 P :=
      le_pCoreOf_of_le_normalizer 2 (inf_le_right.trans h.minpar.T_le) h33
        (h.minpar.syl.2.1.to_le inf_le_right)
    have : A ≤ ⊥ := h.o2 ▸ (le_inf hAK hAT).trans hle
    exact hAD.2.1.2.1 (le_bot_iff.1 this)
  ·
    by_contra hnot
    set N' := setNormalizer P (dInter (offSet P) T) with hN'
    have hN'P : N' ≤ P := fun g hg => hg.1
    have hTN' : T ≤ N' := fun t ht => h41.mem_setNormalizer_dInter (h.minpar.T_le ht) ht
    have hN'eq : N' = P := by
      by_contra hne
      exact hnot (h.minpar.max N' hTN' (lt_of_le_of_ne hN'P hne))
    obtain ⟨A, hAD, hAT⟩ := h.exists_mem_dInter
    have hperm : ∀ B ∈ dInter (offSet P) T, ∀ g ∈ P, conjSub g B ∈ dInter (offSet P) T := by
      intro B hB g hg
      have hg' : g ∈ N' := hN'eq ▸ hg
      exact (hg'.2 B).1 hB
    have hnorm := FourTwoTools.le_normalizer_iSup hperm
    have hK2 : IsPGroup 2 (⨆ B ∈ dInter (offSet P) T, B : Subgroup (MulAut V)) :=
      h.minpar.syl.2.1.to_le (iSup₂_le fun B hB => hB.2)
    have hle : (⨆ B ∈ dInter (offSet P) T, B : Subgroup (MulAut V)) ≤ pCoreOf 2 P :=
      le_pCoreOf_of_le_normalizer 2
        (iSup₂_le fun B hB => hB.2.trans h.minpar.T_le) hnorm hK2
    have : A ≤ ⊥ := h.o2 ▸ (le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V))
      (_ : B ∈ dInter (offSet P) T) => B) A ⟨hAD, hAT⟩ le_rfl).trans hle
    exact hAD.2.1.2.1 (le_bot_iff.1 this)

end Hyp51

end Five

end CFSG.CGT.PushingUpLit.BHS
