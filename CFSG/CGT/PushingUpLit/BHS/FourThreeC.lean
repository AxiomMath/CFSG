module

public import CFSG.CGT.PushingUpLit.BHS.FourThreeB

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

variable {V : Type} [CommGroup V] [Finite V]

namespace LocMax

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))} {M : Subgroup (MulAut V)}

theorem caseI_false (h : LocMax P D M) {A B : Subgroup (MulAut V)}
    (hA : A ∈ D) (hAM : A ≤ M) (hB : B ∈ D) (hBM : ¬ B ≤ M)
    (hBx : ∃ x ∈ A ⊔ B, B = conjSub x A)
    (IH : ∀ A' B' : Subgroup (MulAut V), A' ∈ D → A' ≤ M → B' ∈ D → ¬ B' ≤ M →
      Nat.card ↥(A' ⊔ B') < Nat.card ↥(A ⊔ B) → A' ⊔ B' ∈ lamSet P D M)
    {l : MulAut V} (hl : l ∈ A ⊔ B) (hlt : A ⊔ conjSub l A < A ⊔ B)
    (hXM : ¬ conjSub l A ≤ M) : False := by
  set L : Subgroup (MulAut V) := A ⊔ B with hL
  obtain ⟨x, hxL, hBxe⟩ := hBx
  have hAL : A ≤ L := le_sup_left
  have hBL : B ≤ L := le_sup_right
  have hLP : L ≤ P := sup_le (h.hyp.le A hA) (h.hyp.le B hB)
  have hlP : l ∈ P := hLP hl
  set X : Subgroup (MulAut V) := conjSub l A with hX
  have hXD : X ∈ D := h.hyp.conj_mem A hA l hlP
  have hXL : X ≤ L := by
    have := conjSub_mono l hAL
    rwa [conjSub_self_of_mem hl] at this
  set L₀ : Subgroup (MulAut V) := A ⊔ X with hL₀
  have hL₀L : L₀ ≤ L := sup_le hAL hXL
  have hΛ : L₀ ∈ lamSet P D M :=
    IH A X hA hAM hXD hXM (FourOneTools.card_lt_of_le_of_ne hlt.le hlt.ne)
  obtain ⟨-, ⟨n, hn1, hSL⟩, hΛ2, -⟩ := hΛ
  have hAs : IsSylowOf 2 A L₀ := (hΛ2 A).1 ⟨hA, le_sup_left⟩
  have hG : SylowGood L₀ := fun S hS =>
    have hSD : S ∈ D := ((hΛ2 S).2 hS).1
    ⟨h.hyp.quad S hSD, h.hyp.card_eq S hSD⟩
  have hq : Nat.card A = 2 ^ n := hSL.sylow_card hn1 hAs
  have hBcard : Nat.card B = Nat.card A := by rw [hBxe, card_conjSub]
  have hidxA : (fixV A).index = 2 ^ n := by
    rw [index_fixV_eq (h.hyp.card_eq A hA), hq]
  have hidxB : (fixV B).index = 2 ^ n := by
    rw [index_fixV_eq (h.hyp.card_eq B hB), hBcard, hq]
  set V₀ : Subgroup V := fixV L₀ with hV₀
  have hcardV : Nat.card V = 4 ^ n * Nat.card V₀ := hSL.card_V hn1
  have h4pos : 0 < 4 ^ n := by positivity
  have hidxV₀ : V₀.index = 4 ^ n := by
    have h1 := Subgroup.card_mul_index V₀
    rw [hcardV, mul_comm (4 ^ n)] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hfL : fixV L = fixV A ⊓ fixV B := fixV_sup A B
  have hLle : fixV L ≤ V₀ := fixV_anti hL₀L
  have hidxL : (fixV L).index ≤ 4 ^ n := by
    rw [hfL]
    calc (fixV A ⊓ fixV B).index ≤ (fixV A).index * (fixV B).index := Subgroup.index_inf_le
      _ = 4 ^ n := by rw [hidxA, hidxB, ← mul_pow]; norm_num
  have hfLeq : fixV L = V₀ := by
    refine Subgroup.eq_of_le_of_card_ge hLle ?_
    have h1 := Subgroup.card_mul_index (fixV L)
    have h2 : Nat.card V₀ * 4 ^ n ≤ Nat.card (fixV L) * 4 ^ n := by
      calc Nat.card V₀ * 4 ^ n = Nat.card V := by rw [hcardV]; ring
        _ = Nat.card (fixV L) * (fixV L).index := h1.symm
        _ ≤ Nat.card (fixV L) * 4 ^ n := Nat.mul_le_mul_left _ hidxL
    exact Nat.le_of_mul_le_mul_right h2 h4pos
  have h2n : 2 ^ n < 4 ^ n := Nat.pow_lt_pow_left (by norm_num) (by omega)
  have hBV₀ : V₀ ≤ fixV B := hfLeq ▸ fixV_anti hBL
  have hne : ¬ fixV B ≤ V₀ := fun hle => by
    have : fixV B = V₀ := le_antisymm hle hBV₀
    rw [this, hidxV₀] at hidxB
    omega
  obtain ⟨v, hvB, hvV₀⟩ := IsConcreteLE.not_le_iff_exists.1 hne
  have hstar : ∀ w ∈ fixV B, w ∉ V₀ → ∀ S : Subgroup (MulAut V), IsSylowOf 2 S L₀ →
      w ∈ fixV S → S ≤ conjSub x M := by
    intro w hwB hwV₀ S hS hwS
    by_contra hSx
    have hSD : S ∈ D := ((hΛ2 S).2 hS).1
    obtain ⟨y, hyL₀, hSy⟩ := IsSLNatSection.sylow_conj hAs hS
    have hyP : y ∈ P := hLP (hL₀L hyL₀)
    have hxP : x ∈ P := hLP hxL
    have hB'M : ¬ conjSub y⁻¹ B ≤ M := by
      intro hB'
      have hBy : B ≤ conjSub y M := by
        have := conjSub_mono y hB'
        rwa [FourTwoTools.conjSub_conjSub_inv] at this
      have hAxy : A ≤ conjSub (x⁻¹ * y) M := by
        have := conjSub_mono x⁻¹ hBy
        rw [hBxe, FourTwoTools.conjSub_inv_conjSub, ← conjSub_mul] at this
        exact this
      have hxyM : conjSub (x⁻¹ * y) M = M :=
        h.uniq A hA hAM _ (P.mul_mem (P.inv_mem hxP) hyP) hAxy
      have hyx : conjSub y M = conjSub x M := by
        have := congrArg (conjSub x) hxyM
        rwa [← conjSub_mul, mul_inv_cancel_left] at this
      apply hSx
      rw [hSy, ← hyx]
      exact conjSub_mono y hAM
    have hB'D : conjSub y⁻¹ B ∈ D := h.hyp.conj_mem B hB y⁻¹ (P.inv_mem hyP)
    have hSL₀ : S ≤ L₀ := hS.1
    have hcardAB' : Nat.card ↥(A ⊔ conjSub y⁻¹ B) = Nat.card ↥(S ⊔ B) := by
      have : A ⊔ conjSub y⁻¹ B = conjSub y⁻¹ (S ⊔ B) := by
        rw [conjSub_sup, hSy, FourTwoTools.conjSub_inv_conjSub]
      rw [this, card_conjSub]
    have hw : w ∈ fixV (S ⊔ B) := by
      rw [fixV_sup]
      exact ⟨hwS, hwB⟩
    have hL₁lt : Nat.card ↥(S ⊔ B) < Nat.card ↥L := by
      refine FourOneTools.card_lt_of_le_of_ne (sup_le (hSL₀.trans hL₀L) hBL) fun heq => ?_
      rw [heq, hfLeq] at hw
      exact hwV₀ hw
    have hΛ' := IH A (conjSub y⁻¹ B) hA hAM hB'D hB'M (hcardAB' ▸ hL₁lt)
    obtain ⟨-, ⟨n', hn1', hSL'⟩, hΛ2', -⟩ := hΛ'
    have hAs' : IsSylowOf 2 A (A ⊔ conjSub y⁻¹ B) := (hΛ2' A).1 ⟨hA, le_sup_left⟩
    have hq' : Nat.card A = 2 ^ n' := hSL'.sylow_card hn1' hAs'
    have hn'n : n' = n :=
      Nat.pow_right_injective (le_refl 2) (show 2 ^ n' = 2 ^ n by rw [← hq', hq])
    subst hn'n
    have hcardV' := hSL'.card_V hn1'
    have hZ : Nat.card (fixV (S ⊔ B)) = Nat.card V₀ := by
      have h1 : S ⊔ B = conjSub y (A ⊔ conjSub y⁻¹ B) := by
        rw [conjSub_sup, ← hSy, FourTwoTools.conjSub_conjSub_inv]
      have h2 : Nat.card (fixV (S ⊔ B)) = Nat.card (fixV (A ⊔ conjSub y⁻¹ B)) := by
        rw [h1, conjSub, Glauberman.fixV_map_conj,
          Subgroup.card_map_of_injective y.injective]
      have h3 : Nat.card (fixV (A ⊔ conjSub y⁻¹ B)) = Nat.card V₀ :=
        Nat.eq_of_mul_eq_mul_left h4pos (by rw [← hcardV', hcardV])
      rw [h2, h3]
    have hle : fixV L ≤ fixV (S ⊔ B) := fixV_anti (sup_le (hSL₀.trans hL₀L) hBL)
    have heq : fixV L = fixV (S ⊔ B) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hZ, hfLeq])
    have hwL : w ∈ fixV L := by
      rw [heq]
      exact hw
    exact hwV₀ (hfLeq ▸ hwL)
  have huniqS : ∀ S₁ S₂ : Subgroup (MulAut V), IsSylowOf 2 S₁ L₀ → IsSylowOf 2 S₂ L₀ →
      S₁ ≤ conjSub x M → S₂ ≤ conjSub x M → S₁ = S₂ := by
    intro S₁ S₂ h₁ h₂ hS₁ hS₂
    by_contra hne
    have hL₀le : L₀ ≤ conjSub x M := by
      rw [← hSL.sylow_sup_eq hn1 h₁ h₂ hne]
      exact sup_le hS₁ hS₂
    have hxM : conjSub x M = M := h.uniq A hA hAM x (hLP hxL) (le_sup_left.trans hL₀le)
    apply hBM
    rw [hBxe]
    have := conjSub_mono x hAM
    rwa [hxM] at this
  obtain ⟨S₁, hS₁, hvS₁⟩ := hSL.exists_sylow_mem_fixV hn1 hG v
  have hS₁x : S₁ ≤ conjSub x M := hstar v hvB hvV₀ S₁ hS₁ hvS₁
  have hBS : fixV B ≤ fixV S₁ := by
    intro w hw
    by_cases hwV : w ∈ V₀
    · exact IsSLNatSection.fixV_le_fixV_sylow hS₁ hwV
    · obtain ⟨S₂, hS₂, hwS₂⟩ := hSL.exists_sylow_mem_fixV hn1 hG w
      have := huniqS S₂ S₁ hS₂ hS₁ (hstar w hw hwV S₂ hS₂ hwS₂) hS₁x
      rwa [this] at hwS₂
  have hS₁D : S₁ ∈ D := ((hΛ2 S₁).2 hS₁).1
  have hidxS₁ : (fixV S₁).index = 2 ^ n := by
    rw [index_fixV_eq (hG S₁ hS₁).2, hSL.sylow_card hn1 hS₁]
  have hfixeq : fixV B = fixV S₁ := by
    refine Subgroup.eq_of_le_of_card_ge hBS ?_
    have h1 := Subgroup.card_mul_index (fixV B)
    have h2 := Subgroup.card_mul_index (fixV S₁)
    rw [hidxB] at h1
    rw [hidxS₁] at h2
    have h3 : Nat.card (fixV B) * 2 ^ n = Nat.card (fixV S₁) * 2 ^ n := by rw [h1, h2]
    exact (Nat.eq_of_mul_eq_mul_right (by positivity) h3).ge
  have hcommS : ∀ s ∈ S₁, ∀ b ∈ B, s * b = b * s := by
    refine FourOneTools.commute_of_commV_le ?_ ?_
    · rw [hfixeq]
      exact (hG S₁ hS₁).1
    · rw [← hfixeq]
      exact h.hyp.quad B hB
  by_cases hSB : S₁ = B
  · have hBL₀ : B ≤ L₀ := hSB ▸ hS₁.1
    exact hlt.not_ge (sup_le le_sup_left hBL₀)
  · have hprod := h.hyp.card_prod S₁ hS₁D B hB (Ne.symm hSB) hcommS
    have hfSB : fixV (S₁ ⊔ B) = fixV B := by rw [fixV_sup, ← hfixeq, inf_idem]
    rw [hfSB, hSL.sylow_card hn1 hS₁, hBcard, hq] at hprod
    have h1 := h.hyp.card_eq B hB
    rw [hBcard, hq] at h1
    have hf : 0 < Nat.card (fixV B) := Nat.card_pos
    have h3 : 2 ^ n * Nat.card (fixV B) = (2 ^ n * 2 ^ n) * Nat.card (fixV B) := by
      rw [← h1, hprod]
    have h4 : 2 ^ n = 2 ^ n * 2 ^ n := Nat.eq_of_mul_eq_mul_right hf h3
    nlinarith [Nat.one_lt_two_pow (by omega : n ≠ 0)]


theorem sup_mem_lamSet (h : LocMax P D M)
    (hV : ∀ v : V, v ^ 2 = 1) {A B : Subgroup (MulAut V)} (hA : A ∈ D) (hAM : A ≤ M)
    (hB : B ∈ D) (hBM : ¬ B ≤ M) : A ⊔ B ∈ lamSet P D M := by
  suffices H : ∀ m : ℕ, ∀ A B : Subgroup (MulAut V), A ∈ D → A ≤ M → B ∈ D → ¬ B ≤ M →
      Nat.card ↥(A ⊔ B) = m → A ⊔ B ∈ lamSet P D M from H _ A B hA hAM hB hBM rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro A B hA hAM hB hBM hm
    have hnc : ¬ ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun hc => by
      refine hBM fun b hb => h.mem_of_le_conjSub hA hAM (h.hyp.le B hB hb) ?_
      have h1 : conjSub b A = A := FourOneTools.conjSub_eq_of_comm fun x hx => (hc x hx b hb).symm
      have := conjSub_mono b hAM
      rwa [h1] at this
    rcases h.hyp.four_eight_conj hA hB with hc | ⟨g, hg, hBg⟩
    · exact absurd hc hnc
    by_cases hI : ∃ l ∈ A ⊔ B, A ⊔ conjSub l A < A ⊔ B ∧ ¬ conjSub l A ≤ M
    · obtain ⟨l, hl, hlt, hXM⟩ := hI
      exact (h.caseI_false hA hAM hB hBM ⟨g, hg, hBg⟩
        (fun A' B' hA' hA'M hB' hB'M hlt' => ih _ (hm ▸ hlt') A' B' hA' hA'M hB' hB'M rfl)
        hl hlt hXM).elim
    · push Not at hI
      exact h.sup_mem_lamSet_of_caseII hV hA hAM hB hBM hnc fun l hl hlt => hI l hl hlt

end LocMax

end CFSG.CGT.PushingUpLit.BHS
