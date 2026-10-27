module

public import CFSG.CGT.PushingUpLit.BHS7.FifteenMax
public import CFSG.CGT.PushingUpLit.BHS7.AltAssembly
public import CFSG.CGT.PushingUpLit.BHS7.FifteenBlock
public import CFSG.CGT.PushingUpLit.BHS7.FifteenDefs

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Prod

variable {V : Type} [CommGroup V] [Finite V]

theorem card_prod_of_max {D : Set (Subgroup (MulAut V))} {P : Subgroup (MulAut V)}
    (hgood : ∀ A ∈ D, Good41 A) (hDP : ∀ A ∈ D, A ≤ P)
    (hmax : ∀ X : Subgroup (MulAut V), IsElemAbelian2 X → X ≤ P →
      Nat.card X * Nat.card (fixV X) ≤ Nat.card V) :
    ∀ A ∈ D, ∀ B ∈ D, B ≠ A → (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) →
      Nat.card V = Nat.card A * Nat.card B * Nat.card (fixV (A ⊔ B)) := by
  intro A hA B hB hBA hcomm
  have hAg := hgood A hA
  have hBg := hgood B hB
  have hel : IsElemAbelian2 (A ⊔ B) := isElemAbelian2_sup hAg.elemAb hBg.elemAb hcomm
  have hwt : Nat.card ↥(A ⊔ B) * Nat.card (fixV (A ⊔ B)) ≤ Nat.card V :=
    hmax _ hel (sup_le (hDP A hA) (hDP B hB))
  have hfix : fixV (A ⊔ B) = fixV A ⊓ fixV B := CFSG.Quasithin.fixV_sup A B
  have hcardAB := card_sup_mul_card_inf' hcomm
  by_cases hfAB : fixV A = fixV B
  · exfalso
    have hf : fixV (A ⊔ B) = fixV A := by rw [hfix, ← hfAB, inf_idem]
    have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
    rw [hf] at hwt
    have h1 : Nat.card ↥(A ⊔ B) ≤ Nat.card A := by
      have := hAg.card_eq
      rw [this] at hwt
      exact Nat.le_of_mul_le_mul_right hwt hpos
    have h2 : Nat.card ↥(A ⊔ B) ≤ Nat.card B := by
      have := hBg.card_eq
      rw [← hfAB] at this
      rw [this] at hwt
      exact Nat.le_of_mul_le_mul_right hwt hpos
    have hBle : B ≤ A := by
      have := Subgroup.eq_of_le_of_card_ge (le_sup_left : A ≤ A ⊔ B) h1
      exact this ▸ le_sup_right
    have hAle : A ≤ B := by
      have := Subgroup.eq_of_le_of_card_ge (le_sup_right : B ≤ A ⊔ B) h2
      exact this ▸ le_sup_left
    exact hBA (le_antisymm hBle hAle)
  ·
    have hinf : A ⊓ B = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
      by_contra hx1
      exact hfAB ((hAg.fixV_eq x hx.1 hx1).symm.trans (hBg.fixV_eq x hx.2 hx1))
    rw [hinf, Subgroup.card_bot, mul_one] at hcardAB
    apply le_antisymm
    ·
      have hiA : (fixV A).index = Nat.card A := by
        have h := B1.card_eq_index_mul A
        have hpos : 0 < Nat.card (fixV A) := Nat.card_pos
        have h' : (fixV A).index * Nat.card (fixV A) = Nat.card A * Nat.card (fixV A) := by
          rw [← h, hAg.card_eq]
        exact Nat.eq_of_mul_eq_mul_right hpos h'
      have hiB : (fixV B).index = Nat.card B := by
        have h := B1.card_eq_index_mul B
        have hpos : 0 < Nat.card (fixV B) := Nat.card_pos
        have h' : (fixV B).index * Nat.card (fixV B) = Nat.card B * Nat.card (fixV B) := by
          rw [← h, hBg.card_eq]
        exact Nat.eq_of_mul_eq_mul_right hpos h'
      rw [hfix]
      calc Nat.card V = (fixV A ⊓ fixV B).index * Nat.card ↥(fixV A ⊓ fixV B) := by
            have := Subgroup.card_mul_index (fixV A ⊓ fixV B)
            rw [mul_comm]
            exact this.symm
        _ ≤ (Nat.card A * Nat.card B) * Nat.card ↥(fixV A ⊓ fixV B) := by
            refine Nat.mul_le_mul_right _ ?_
            calc (fixV A ⊓ fixV B).index ≤ (fixV A).index * (fixV B).index :=
                  Subgroup.index_inf_le
              _ = Nat.card A * Nat.card B := by rw [hiA, hiB]
    · calc Nat.card A * Nat.card B * Nat.card (fixV (A ⊔ B))
          = Nat.card ↥(A ⊔ B) * Nat.card (fixV (A ⊔ B)) := by rw [hcardAB]
        _ ≤ Nat.card V := hwt

end Prod

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {G T : Subgroup Γ}

omit [Finite Γ] in
theorem le_autOn_of_mem_dBar {B : Subgroup (MulAut ↥(vSub G T))} (hB : B ∈ dBar G T)
    (hTG : T ≤ G) : B ≤ autOn G (vSub G T) := by
  obtain ⟨g, hg, A, hA, rfl⟩ := hB
  have hAG : A ≤ G := (le_baum_of_mem_ySet hA).trans ((inf_le_left : baum T ≤ T).trans hTG)
  intro x hx
  have h1 : g⁻¹ * x * g ∈ autOn A (vSub G T) := A1b.mem_conjSub_iff.1 hx
  have h2 : g⁻¹ * x * g ∈ autOn G (vSub G T) := autOn_le_autOn (vSub G T) hAG h1
  have h3 := (autOn G (vSub G T)).mul_mem ((autOn G (vSub G T)).mul_mem hg h2)
    ((autOn G (vSub G T)).inv_mem hg)
  simpa [mul_assoc] using h3

omit [Finite Γ] in
theorem pBar_le_autOn (hTG : T ≤ G) : pBar G T ≤ autOn G (vSub G T) :=
  sup_le (iSup₂_le fun _ hB => le_autOn_of_mem_dBar hB hTG) (autOn_le_autOn _ hTG)

omit [Finite Γ] in
theorem autOn_mem_dBar {A : Subgroup Γ} (hA : A ∈ ySet G T) : autOn A (vSub G T) ∈ dBar G T :=
  ⟨1, (autOn G (vSub G T)).one_mem, A, hA, (A1b.conjSub_one _).symm⟩

omit [Finite Γ] in
theorem mem_iSup_dBar {B : Subgroup (MulAut ↥(vSub G T))} (hB : B ∈ dBar G T)
    {x : MulAut ↥(vSub G T)} (hx : x ∈ B) : x ∈ ⨆ B ∈ dBar G T, B :=
  (le_iSup₂ (f := fun (B : Subgroup (MulAut ↥(vSub G T))) (_ : B ∈ dBar G T) => B) B hB) hx

omit [Finite Γ] in
theorem autOn_le_iSup_dBar {E A : Subgroup Γ} (hTG : T ≤ G) (hEG : E ≤ G) (hAy : A ∈ ySet G T)
    (hEA : ⁅E, A⁆ = E) : autOn E (vSub G T) ≤ ⨆ B ∈ dBar G T, B := by
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hAG : A ≤ G := (le_baum_of_mem_ySet hAy).trans ((inf_le_left : baum T ≤ T).trans hTG)
  have h1 : autOn E (vSub G T) = ⁅autOn E (vSub G T), autOn A (vSub G T)⁆ := by
    rw [← autOn_commutator_eq (hEG.trans hGN) (hAG.trans hGN), hEA]
  rw [h1]
  refine Subgroup.commutator_le.2 fun e he a ha => ?_
  rw [commutatorElement_def]
  have heG : e ∈ autOn G (vSub G T) := autOn_le_autOn (vSub G T) hEG he
  have h2 : e * a * e⁻¹ ∈ ⨆ B ∈ dBar G T, B :=
    mem_iSup_dBar (⟨e, heG, A, hAy, rfl⟩ : A1b.conjSub e (autOn A (vSub G T)) ∈ dBar G T)
      (A1b.mem_conjSub_of_mem ha)
  have h3 : a⁻¹ ∈ ⨆ B ∈ dBar G T, B :=
    mem_iSup_dBar (autOn_mem_dBar hAy) ((autOn A (vSub G T)).inv_mem ha)
  exact Subgroup.mul_mem _ h2 h3

omit [Finite Γ] in
theorem mem_of_conjAct_mem_autOn {V G K : Subgroup Γ}
    (hGN : G ≤ Subgroup.normalizer (V : Set Γ)) (hKG : K ≤ G)
    (hcen : G ⊓ Subgroup.centralizer (V : Set Γ) ≤ K) {x : Γ} (hx : x ∈ G)
    (h : conjAct V ⟨x, hGN hx⟩ ∈ autOn K V) : x ∈ K := by
  obtain ⟨c, hcK, hc⟩ := mem_autOn_iff.1 h
  have h1 : conjAct V (c⁻¹ * ⟨x, hGN hx⟩) = 1 := by
    rw [map_mul, map_inv, hc, inv_mul_cancel]
  have h2 : (c : Γ)⁻¹ * x ∈ Subgroup.centralizer (V : Set Γ) := (conjAct_eq_one_iff V _).1 h1
  have h3 : (c : Γ)⁻¹ * x ∈ K :=
    hcen ⟨G.mul_mem (G.inv_mem (hKG hcK)) hx, h2⟩
  have := K.mul_mem hcK h3
  simpa using this

omit [Finite Γ] in
theorem not_mem_dCore_of_block (hV : IsElemAbelian 2 (vSub G T)) {E A : Subgroup Γ}
    (hTG : T ≤ G) (hEG : E ≤ G)
    (hAy : A ∈ ySet G T) (hEA : ⁅E, A⁆ = E) (hEC : ¬ E ≤ cStarIn G T)
    {Q M₀ : Subgroup (MulAut ↥(vSub G T))} (hQ : autOn E (vSub G T) ≤ Q)
    (hM₀ : M₀ ≤ autOn (cStarIn G T) (vSub G T)) :
    autOn A (vSub G T) ∉ @dCore ↥(vSub G T) (commGroupOfElemAbelian hV) Q (dBar G T) M₀ := by
  rintro ⟨-, hcore⟩
  apply hEC
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hAG : A ≤ G := (le_baum_of_mem_ySet hAy).trans ((inf_le_left : baum T ≤ T).trans hTG)
  have h1 : autOn E (vSub G T) = ⁅autOn E (vSub G T), autOn A (vSub G T)⁆ := by
    rw [← autOn_commutator_eq (hEG.trans hGN) (hAG.trans hGN), hEA]
  have h2 : autOn E (vSub G T) ≤ M₀ := by
    rw [h1]
    refine Subgroup.commutator_le.2 fun e he a ha => ?_
    rw [commutatorElement_def]
    have h3 : a ∈ M₀ := by
      have := hcore 1 Q.one_mem
      rw [A1b.conjSub_one] at this
      exact this ha
    have h4 : e * a * e⁻¹ ∈ M₀ := by
      have := A1b.mem_conjSub_iff.1 (hcore e⁻¹ (Q.inv_mem (hQ he)) ha)
      simpa using this
    exact M₀.mul_mem h4 (M₀.inv_mem h3)
  intro x hx
  exact mem_of_conjAct_mem_autOn hGN (cStarIn_le G T) (centralizer_vSub_le_cStarIn G T) (hEG hx)
    (hM₀ (h2 (mem_autOn_iff.2 ⟨⟨x, hGN (hEG hx)⟩, hx, rfl⟩)))

omit [Finite Γ] in
theorem conj_mem_dInter {B : Subgroup (MulAut ↥(vSub G T))} {t : MulAut ↥(vSub G T)}
    (hTG : T ≤ G) (ht : t ∈ autOn T (vSub G T)) (hB : B ∈ dBar G T) (hBT : B ≤ autOn T (vSub G T)) :
    A1b.conjSub t B ∈ dBar G T ∧ A1b.conjSub t B ≤ autOn T (vSub G T) :=
  ⟨conj_mem_dBar hB (autOn_le_autOn (vSub G T) hTG ht),
    (A1b.conjSub_mono t hBT).trans (conjSub_of_mem ht).le⟩

theorem hyp43_dBar (h : MinCex G T) (h5 : Seven5 G T) (h13 : Seven13 G T) (h14 : Seven14 G T) :
    @Hyp43 ↥(vSub G T) (commGroupOfElemAbelian (isElemAbelian_vSub h.charTwo h.sylow))
      (pBar G T) (dBar G T) (autOn T (vSub G T)) (mBar G T) := by
  classical
  have hG := h.charTwo
  have hT : IsSylowTwoOf T G := h.sylow
  have hV : IsElemAbelian 2 (vSub G T) := isElemAbelian_vSub hG hT
  let _ : CommGroup ↥(vSub G T) := commGroupOfElemAbelian hV
  have hTG : T ≤ G := hT.1
  have hGN : G ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := le_normalizer_vSub G T
  have hTN : T ≤ Subgroup.normalizer ((vSub G T : Subgroup Γ) : Set Γ) := hTG.trans hGN
  have hgood : ∀ B ∈ dBar G T, Good41 B := by
    rintro _ ⟨g, hg, A, ⟨E, hE, hEC, hpair⟩, rfl⟩
    obtain ⟨hAB, hEA, hq, hrel, hfix⟩ := hpair
    have hAG : A ≤ G := hAB.trans ((inf_le_left : baum T ≤ T).trans hTG)
    exact (good41_autOn hV (hAG.trans hGN)
      (not_le_centralizer_vSub_of_commutator hE.le hEA hEC) hq hrel hfix).conj g
  have hP_le : pBar G T ≤ autOn G (vSub G T) := pBar_le_autOn hTG
  have hD_le_P : ∀ B ∈ dBar G T, B ≤ pBar G T := fun B hB =>
    le_sup_of_le_left (fun x hx => mem_iSup_dBar hB hx)
  have hTP : autOn T (vSub G T) ≤ pBar G T := le_sup_right
  have hmaxP : ∀ X : Subgroup (MulAut ↥(vSub G T)), IsElemAbelian2 X → X ≤ pBar G T →
      Nat.card X * Nat.card (fixV X) ≤ Nat.card (vSub G T) := fun X hX hXP =>
    wt_le_card_vSub hG hT h13 hX (hXP.trans hP_le)
  have hsyl : IsSylowTwoOf (autOn T (vSub G T)) (autOn G (vSub G T)) :=
    CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hT hGN
  have hTC : T ≤ cStarIn G T := le_cStarIn_of_minCex h
  refine
    { toHyp42 :=
      { toHyp41 :=
        { le := hD_le_P
          ne_bot := fun B hB => (hgood B hB).ne_bot
          elemAb := fun B hB => (hgood B hB).elemAb
          conj_mem := fun B hB g hg => conj_mem_dBar hB (hP_le hg)
          quad := fun B hB => (hgood B hB).quad
          card_eq := fun B hB => (hgood B hB).card_eq
          fixV_eq := fun B hB => (hgood B hB).fixV_eq
          card_prod := card_prod_of_max hgood hD_le_P hmaxP }
        syl := isSylowOf_of_isSylowTwoOf (isSylowTwoOf_of_le_of_le hsyl hTP hP_le)
        le_M := le_inf hTP (autOn_le_autOn _ hTC)
        M_le := inf_le_left
        ne_core := ?_
        normSet_le := ?_
        cen_le := ?_ }
      max := fun A hA X hX hXP => (hmaxP X hX hXP).trans (hgood A hA).card_eq.le }
  ·
    obtain ⟨F, hF, hFC⟩ := exists_isBTBlock_not_le h h5
    obtain ⟨A, hpair⟩ := h14 F hF hFC
    have hAy : A ∈ ySet G T := ⟨F, hF, hFC, hpair⟩
    intro heq
    have hcore : autOn A (vSub G T) ∈ dCore (pBar G T) (dBar G T) (mBar G T) :=
      heq ▸ autOn_mem_dBar hAy
    exact not_mem_dCore_of_block hV hTG hF.le hAy hpair.2.1 hFC
      ((autOn_le_iSup_dBar hTG hF.le hAy hpair.2.1).trans le_sup_left) inf_le_right hcore
  ·
    intro g hg
    set N : Subgroup (MulAut ↥(vSub G T)) :=
      setNormalizer (pBar G T) (dInter (dBar G T) (autOn T (vSub G T))) with hN
    have hNP : N ≤ pBar G T := fun x hx => hx.1
    have hNG : N ≤ autOn G (vSub G T) := hNP.trans hP_le
    have hTN' : autOn T (vSub G T) ≤ N := by
      intro t ht
      refine ⟨hTP ht, fun B => ⟨fun hB => ?_, fun hB => ?_⟩⟩
      · exact conj_mem_dInter hTG ht hB.1 hB.2
      · have h1 := conj_mem_dInter hTG ((autOn T (vSub G T)).inv_mem ht) hB.1 hB.2
        have h2 : A1b.conjSub t⁻¹ (A1b.conjSub t B) = B := by
          rw [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one]
        rw [h2] at h1
        exact h1
    have hTL : T ≤ liftSub (vSub G T) G N := by
      intro t ht
      exact mem_liftSub_iff.2 ⟨hTG ht, hTN ht, hTN' (mem_autOn_iff.2 ⟨⟨t, hTN ht⟩, ht, rfl⟩)⟩
    have hLG : liftSub (vSub G T) G N ≤ G := liftSub_le G N
    have hLC : liftSub (vSub G T) G N ≤ cStarIn G T := by
      by_contra hLC
      obtain ⟨F, hF, hFL, hFC⟩ := exists_isBTBlock_le h h5 hTL hLG hLC
      obtain ⟨A, hpair⟩ := h14 F hF hFC
      have hAy : A ∈ ySet G T := ⟨F, hF, hFC, hpair⟩
      have hAT : autOn A (vSub G T) ∈ dInter (dBar G T) (autOn T (vSub G T)) :=
        ⟨autOn_mem_dBar hAy, autOn_le_autOn (vSub G T) (hpair.1.trans inf_le_left)⟩
      have key : ∀ e ∈ autOn F (vSub G T), ∀ a ∈ autOn A (vSub G T),
          e * a * e⁻¹ ∈ autOn T (vSub G T) := by
        intro e he a ha
        have heN : e ∈ N := by
          have := autOn_le_autOn (vSub G T) hFL he
          rwa [autOn_liftSub hNG] at this
        have h1 := ((heN.2 (autOn A (vSub G T))).1 hAT).2
        exact h1 (A1b.mem_conjSub_of_mem ha)
      have hFT : autOn F (vSub G T) ≤ autOn T (vSub G T) := by
        have h1 : autOn F (vSub G T) = ⁅autOn F (vSub G T), autOn A (vSub G T)⁆ := by
          rw [← autOn_commutator_eq (hF.le.trans hGN)
            ((hpair.1.trans ((inf_le_left : baum T ≤ T).trans hTG)).trans hGN), hpair.2.1]
        rw [h1]
        refine Subgroup.commutator_le.2 fun e he a ha => ?_
        rw [commutatorElement_def]
        exact (autOn T (vSub G T)).mul_mem (key e he a ha) ((autOn T (vSub G T)).inv_mem
          (autOn_le_autOn (vSub G T) (hpair.1.trans inf_le_left) ha))
      have h2 : IsPGroup 2 ↥(autOn F (vSub G T)) :=
        (CFSG.CGT.PushingUpLit.BHS6.isPGroup_autOn hT.2.1 hTN).to_le hFT
      have h3 := le_centralizer_of_isPGroup_autOn hF (hF.le.trans hGN) h2
      exact hFC (fun x hx => centralizer_vSub_le_cStarIn G T ⟨hF.le hx, h3 hx⟩)
    have hgN : g ∈ N := hg
    have hgL : g ∈ autOn (liftSub (vSub G T) G N) (vSub G T) := by
      rw [autOn_liftSub hNG]
      exact hgN
    exact ⟨hgN.1, autOn_le_autOn (vSub G T) hLC hgL⟩
  ·
    intro g hg
    obtain ⟨hgP, hgf⟩ := hg
    obtain ⟨g', hg'G, rfl⟩ := mem_autOn_iff.1 (hP_le hgP)
    refine ⟨hgP, mem_autOn_iff.2 ⟨g', ?_, rfl⟩⟩
    refine centralizer_le_cStarIn G T ⟨hg'G, Subgroup.mem_centralizer_iff.2 fun z hz => ?_⟩
    have hzV : z ∈ vSub G T := omegaOneCenterOf_le_vSub G T hz
    have hzT : z ∈ Subgroup.centralizer (T : Set Γ) := (C1GN.omegaOneCenterOf_le_centerOf T hz).2
    have hzf : (⟨z, hzV⟩ : ↥(vSub G T)) ∈ fixV (autOn T (vSub G T)) := by
      intro x hx
      obtain ⟨t, htT, rfl⟩ := mem_autOn_iff.1 hx
      apply Subtype.ext
      rw [conjAct_apply']
      have := Subgroup.mem_centralizer_iff.1 hzT t htT
      calc (t : Γ) * z * (t : Γ)⁻¹ = (z * t) * (t : Γ)⁻¹ := by rw [this]
        _ = z := by group
    have h1 := congrArg (fun w : ↥(vSub G T) => (w : Γ)) (hgf _ hzf)
    simp only [conjAct_apply'] at h1
    calc z * (g' : Γ) = (g' * z * (g' : Γ)⁻¹) * g' := by rw [h1]
      _ = g' * z := by group

end Main

end CFSG.CGT.PushingUpLit.BHS7
