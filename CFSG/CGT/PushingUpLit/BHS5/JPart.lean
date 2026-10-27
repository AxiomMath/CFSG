module

public import CFSG.CGT.PushingUpLit.BHS5.FiveFive
public import CFSG.CGT.PushingUpLit.BHS5.JStepSym

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS

variable {V : Type} [CommGroup V] [Finite V]
  {P T M : Subgroup (MulAut V)}

theorem offMax_eq_card (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) :
    offMax P = Nat.card V := by
  obtain ⟨A, hA⟩ := h.exists_mem_dInter
  have h43 := h.hyp43 hV
  have h1 : wt A = offMax P := hA.1.2.2.1
  rw [← h1]
  exact (h43.card_eq A hA.1).symm

theorem exists_offSet_le (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)}
    (hXP : X ≤ P) (hoff : IsOff X) (hw : wt X = Nat.card V) :
    ∃ B ∈ Hyp51.offSet P, B ≤ X := by
  have hm := offMax_eq_card h hV
  obtain ⟨B, ⟨hBX, hBoff, hBw⟩, hBmin⟩ : ∃ B ∈ {B' : Subgroup (MulAut V) |
      B' ≤ X ∧ IsOff B' ∧ wt B' = offMax P},
      ∀ B' ∈ {B' : Subgroup (MulAut V) | B' ≤ X ∧ IsOff B' ∧ wt B' = offMax P},
        Nat.card B ≤ Nat.card B' := by
    refine Set.exists_min_image _ (fun B : Subgroup (MulAut V) => Nat.card B) (Set.toFinite _) ?_
    exact ⟨X, le_rfl, hoff, by rw [hw, hm]⟩
  refine ⟨B, ⟨hBX.trans hXP, hBoff, hBw, fun B' hB'B hB' hB'w => ?_⟩, hBX⟩
  exact Subgroup.eq_of_le_of_card_ge hB'B (hBmin B' ⟨hB'B.trans hBX, hB', hB'w⟩)

theorem jPart (hsym : BHSSymType) (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1)
    (𝔄 : Subgroup (MulAut V) → Prop)
    (h𝔄₁ : ∀ X, 𝔄 X → X ≤ P)
    (h𝔄₂ : ∀ X, 𝔄 X → X ≠ ⊥ → IsOff X ∧ wt X = Nat.card V)
    (h𝔄₃ : ∀ X, 𝔄 X → ∀ Y, Y ≤ X → wt X ≤ wt Y → 𝔄 Y) :
    ∀ X, 𝔄 X → X ≤ genD P := by
  have hF := five_five hsym h hV
  have h43 := h.hyp43 hV
  intro X
  induction' hn : Nat.card X using Nat.strong_induction_on with n ih generalizing X
  intro hX
  by_cases hXbot : X = ⊥
  · rw [hXbot]
    exact bot_le
  obtain ⟨hoff, hw⟩ := h𝔄₂ X hX hXbot
  have hXP := h𝔄₁ X hX
  obtain ⟨B, hB, hBX⟩ := exists_offSet_le h hV hXP hoff hw
  have hBgen : B ≤ genD P := le_iSup₂_of_le (f := fun (A : Subgroup (MulAut V))
    (_ : A ∈ Hyp51.offSet P) => A) B hB le_rfl
  have hBne : B ≠ ⊥ := h43.ne_bot B hB
  obtain ⟨E, hE, hBE⟩ := hF.cover B hB
  have hEP : E ≤ P := hF.le_P h hV hE
  have hsub := hF.isSubnormal h hV hE
  have hsplit : JSplit X B := by
    rcases hF.type E hE with hSL | hSym
    · obtain ⟨n', hn2, hnat, htop, hsyl⟩ := hSL
      exact jSplit_sl hV hn2 hXP hoff hBX hEP hsub hnat htop ((hsyl B).1 ⟨hB, hBE⟩) hBne
    · obtain ⟨m, θ, β, hm, h3, hinv, hsurj, hker, hequiv, htop, hD, -⟩ := hSym
      let D : SymDat E m := ⟨θ, β, hm, h3, hinv, hsurj, hker, hequiv, htop⟩
      have hBt := hD B ⟨hB, hBE⟩
      by_cases hm3 : m = 3
      · subst hm3
        exact jSplit_sym_three hV D hXP hoff hBX hsub hBE hBne hBt
      · have h5 : 5 ≤ m := by
          obtain ⟨k, hk⟩ := hm
          omega
        exact jSplit_sym_alt hV D h5 hXP hoff hBX hEP hsub hBE hBne hBt
  obtain ⟨X₀, hX₀X, hX₀ne, hX₀w, hXle⟩ := hsplit
  have hX₀ : 𝔄 X₀ := h𝔄₃ X hX X₀ hX₀X hX₀w
  have hlt : Nat.card X₀ < n := by
    rw [← hn]
    exact lt_of_le_of_ne (Subgroup.card_le_of_le hX₀X) fun hc =>
      hX₀ne (Subgroup.eq_of_le_of_card_ge hX₀X hc.ge)
  exact hXle.trans (sup_le hBgen (ih _ hlt X₀ rfl hX₀))

end CFSG.CGT.PushingUpLit.BHS5
