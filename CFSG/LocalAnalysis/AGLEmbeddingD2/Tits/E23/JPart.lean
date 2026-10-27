module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.E23.Setup

public section

namespace CFSG.AGLEmbeddingD2.Tits.E23

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5

section Abstract

variable {V : Type} [CommGroup V] [Finite V]
  {P T M : Subgroup (MulAut V)}

theorem jPart' (hsym : BHSSymType) (h : Hyp51 P T M) (hV : ∀ v : V, v ^ 2 = 1)
    (𝔄 : Subgroup (MulAut V) → Prop)
    (h𝔄₁ : ∀ X, 𝔄 X → X ≤ P)
    (h𝔄₂ : ∀ X, 𝔄 X → X ≠ ⊥ → IsOff X ∧ wt X = Nat.card V)
    (h𝔄₃ : ∀ X, 𝔄 X → ∀ Y, Y ≤ X → wt X ≤ wt Y → 𝔄 Y) :
    ∀ X, 𝔄 X → X ≤ ⨆ B ∈ {B | B ∈ Hyp51.offSet P ∧ B ≤ X}, B := by
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
  have hBgen : B ≤ ⨆ B' ∈ {B' | B' ∈ Hyp51.offSet P ∧ B' ≤ X}, B' :=
    le_iSup₂_of_le (f := fun (A : Subgroup (MulAut V)) (_ : A ∈ {B' | B' ∈ Hyp51.offSet P ∧ B' ≤ X})
      => A) B ⟨hB, hBX⟩ le_rfl
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
  have hX₀gen : X₀ ≤ ⨆ B' ∈ {B' | B' ∈ Hyp51.offSet P ∧ B' ≤ X}, B' :=
    (ih _ hlt X₀ rfl hX₀).trans (biSup_mono fun B' hB' => ⟨hB'.1, hB'.2.trans hX₀X⟩)
  exact hXle.trans (sup_le hBgen hX₀gen)

end Abstract

section Ambient

variable {G : Type} [Group G] [Finite G] {H T M : Subgroup G}
  (hV : IsElemAbelian 2 (VZ T H)) (hmin : MinParabolic H T M) (hmp : MinPar H T M)
  (hF : CharTwo H) (hred : IsTwoReducedIn H (VZ T H))
  (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T H : Set G))

omit [Finite G] in
theorem autI_le_normalizer_autI_thompsonJ :
    autI hV T ≤ Subgroup.normalizer (autI hV (thompsonJ T) : Set (MulAut (IntMod (VZ T H) hV))) := by
  intro y hy
  obtain ⟨t, htT, rfl⟩ := (mem_autI hV).1 hy
  have htJ : conjSub (t : G) (thompsonJ T) = thompsonJ T :=
    conjSub_eq_of_mem_normalizer' ((Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_thompsonJ T)) htT)
  have e := autOn_conjSub (V := VZ T H) t.2 (X := thompsonJ T)
  rw [htJ] at e
  refine Subgroup.mem_normalizer_iff_map_conj_eq.2 ?_
  exact e.symm

include hmin hmp hF hred hJ

theorem autI_thompsonJ_le_iSup :
    autI hV (thompsonJ T) ≤ ⨆ B ∈ {B | B ∈ Hyp51.offSet (autI hV H) ∧
      B ≤ autI hV (thompsonJ T)}, B := by
  have hv := vHyp_of_e23 hV hmin hmp hF hred hJ
  have h51 := hyp51_of_e23 hV hmin hmp hF hred hJ
  have hV2 : ∀ v : IntMod (VZ T H) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hGN : H ≤ Subgroup.normalizer (VZ T H : Set G) := hv.normalized
  have hTH : T ≤ H := hmin.isSylow.1
  set Y : Subgroup (MulAut (IntMod (VZ T H) hV)) := ⨆ B ∈ {B | B ∈ Hyp51.offSet (autI hV H) ∧
      B ≤ autI hV (thompsonJ T)}, B with hYdef
  have hYP : Y ≤ autI hV H := iSup₂_le fun B hB => hB.1.1
  have hAY : ∀ A, IsMaxElemAbelian T A → autI hV A ≤ Y := by
    intro A hA
    have h1 := jPart' bhsSymType h51 hV2 (fun X => ∃ A, IsMaxElemAbelian T A ∧ X = autOn A (VZ T H))
      (by
        rintro X ⟨A', hA', rfl⟩
        exact autOn_le_autOn (VZ T H) (hA'.1.trans hTH))
      (by
        rintro X ⟨A', hA', rfl⟩ hne
        exact hv.family_off hA' hne)
      (by
        rintro X ⟨A', hA', rfl⟩ Y' hYX hw
        obtain ⟨A'', hA'', hA''Y⟩ := hv.family_sub hA' Y' hYX hw
        exact ⟨A'', hA'', hA''Y.symm⟩) _ ⟨A, hA, rfl⟩
    have hAJ : autI hV A ≤ autI hV (thompsonJ T) :=
      autOn_le_autOn (VZ T H) (le_iSup₂_of_le A hA le_rfl)
    exact h1.trans (biSup_mono fun B hB => ⟨hB.1, hB.2.trans hAJ⟩)
  have hlift : thompsonJ T ≤ liftSub (VZ T H) H Y := by
    refine iSup₂_le fun A hA x hx => ?_
    have hxN : x ∈ Subgroup.normalizer (VZ T H : Set G) := hGN (hTH (hA.1 hx))
    exact mem_liftSub_iff.2 ⟨hTH (hA.1 hx), hxN, hAY A hA (mem_autOn_iff.2 ⟨⟨x, hxN⟩, hx, rfl⟩)⟩
  have e := autOn_liftSub (V := VZ T H) (A := H) hYP
  exact (autOn_le_autOn (VZ T H) hlift).trans e.le

theorem exists_offSet_le_autI_thompsonJ :
    ∃ B ∈ Hyp51.offSet (autI hV H), B ≤ autI hV (thompsonJ T) := by
  have hv := vHyp_of_e23 hV hmin hmp hF hred hJ
  have h51 := hyp51_of_e23 hV hmin hmp hF hred hJ
  have hV2 : ∀ v : IntMod (VZ T H) hV, v ^ 2 = 1 := fun v => IntMod.sq_eq_one v
  have hTN : T ≤ Subgroup.normalizer (VZ T H : Set G) := hmin.isSylow.1.trans hv.normalized
  obtain ⟨A, hA, hne⟩ : ∃ A, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer (VZ T H : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hJ (iSup₂_le fun A hA => hcon A hA)
  have hAN : A ≤ Subgroup.normalizer (VZ T H : Set G) := hA.1.trans hTN
  obtain ⟨hoff, hw⟩ := hv.family_off hA (CFSG.CGT.PushingUpLit.BHS5.autOn_ne_bot_of_not_le_centralizer hAN hne)
  obtain ⟨B₀, hB₀, hB₀A⟩ := exists_offSet_le h51 hV2
    (autOn_le_autOn (VZ T H) (hA.1.trans hmin.isSylow.1)) hoff hw
  exact ⟨B₀, hB₀, hB₀A.trans (autOn_le_autOn (VZ T H) (le_iSup₂_of_le A hA le_rfl))⟩

end Ambient

end CFSG.AGLEmbeddingD2.Tits.E23
