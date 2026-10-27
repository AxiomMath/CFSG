module

public import CFSG.LocalAnalysis.GH72.Sec5CKbar
public import CFSG.LocalAnalysis.GH72.A7Local
public import CFSG.LocalAnalysis.GH72.PGammaL2Field
public import CFSG.CGT.Foote81L6.Lemma1
public import CFSG.ClassicalInvolution.NormalQuaternion
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.GH72.Sec4Residual

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement MatrixGroups

namespace Sec5KConfig

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔨 : Sec5KConfig ρ p)

theorem isPGroup_two_bar_X : IsPGroup 2 (bar 𝔨.K₁ ρ.X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.of_card (n := 2) (by rw [𝔨.isKleinFour_bar_X.card_four]; norm_num)

theorem bar_A_eq : bar 𝔨.K₁ A = bar 𝔨.K₁ ρ.X ⊔ bar 𝔨.K₁ ρ.Y :=
  (congrArg (fun L => bar 𝔨.K₁ L) ρ.X_sup_Y.symm).trans (bar_sup 𝔨.X_le_K₁ 𝔨.Y_le_K₁)

end Sec5KConfig

namespace Sec5ConfigR

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {ρ : Sec5Roles G A} {p : ℕ}
  (𝔠 : Sec5ConfigR ρ p)

theorem commutator_P_X_eq : ⁅𝔠.P, ρ.X⁆ = ⁅𝔠.Q, ρ.X⁆ := by
  refine le_antisymm ?_ (commutator_mono 𝔠.Q_le_P le_rfl)
  rw [commutator_le]
  intro g hg x hx
  have hRQ : 𝔠.R ≤ normalizer (𝔠.Q : Set G) := inf_le_left.trans 𝔠.P_le_normalizer_Q
  have hg' : g ∈ ((𝔠.Q ⊔ 𝔠.R : Subgroup G) : Set G) := 𝔠.P_le_Q_sup_R hg
  rw [coe_mul_of_right_le_normalizer_left _ _ hRQ] at hg'
  obtain ⟨q, hq, r, hr, rfl⟩ := Set.mem_mul.mp hg'
  have hr' : r ∈ 𝔠.R := hr
  rw [commutatorElement_mul_of_commute (mem_centralizer_iff.mp hr'.2 x hx).symm]
  exact commutator_mem_commutator hq hx

theorem lemma_5_12_of_ne_bot
    (h58 : 𝔠.R = 𝔠.U)
    (h59E : ∃ E : Subgroup G, E ≤ 𝔠.R ⊓ 𝔠.Q ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (h59cyc : IsCyclic (⁅𝔠.Pstar, ρ.X⁆ : Subgroup G))
    (W : Subgroup G)
    (hW : 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W)
    (hW1 : W ≠ ⊥) (hQUV : ¬ 𝔠.Q ⊓ 𝔠.U ≤ 𝔠.V) : ∃ H, ρ.IsCovering p H := by
  have h48i := 𝔠.quotIs_N₀
  have hXN₀ := 𝔠.X_le_N₀
  have hp := 𝔠.hp
  have hp2 := 𝔠.hp2
  obtain ⟨hPP, hPUW⟩ := 𝔠.lemma_5_11_of h58 W hW
  have hPK : 𝔠.P ≤ 𝔠.K := hPP.le.trans inf_le_right
  have hPK₁ : 𝔠.P ≤ 𝔠.K₁ := hPP.le.trans 𝔠.Pstar_le_K₁
  have hQK : 𝔠.Q ≤ 𝔠.K := 𝔠.Q_le_P.trans hPK
  have hUP : 𝔠.U ≤ 𝔠.P := 𝔠.U_le_Pstar.trans inf_le_left
  obtain ⟨E, hEdef⟩ : ∃ E : Subgroup G, E = ⁅𝔠.P, ρ.X⁆ := ⟨_, rfl⟩
  have hEP : E ≤ 𝔠.P := by
    rw [hEdef, commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (ρ.X_le_A.trans 𝔠.A_le_normalizer_P)
  have hEQX : E = ⁅𝔠.Q, ρ.X⁆ := hEdef.trans 𝔠.commutator_P_X_eq
  have hWP : W ≤ 𝔠.P := (le_sup_right.trans hW.1.ge).trans 𝔠.Q_le_P
  have hWE : W ≤ E := by
    have h1 := commutator_mono (le_rfl : ρ.X ≤ ρ.X) hWP
    rw [hW.2.2.2.2, commutator_comm] at h1
    rwa [hEdef]
  have hEc : IsCyclic E := by
    rw [hEdef, hPP]
    exact h59cyc
  have hPUE : 𝔠.P = 𝔠.U ⊔ E :=
    le_antisymm (hPUW.le.trans (sup_le_sup_left hWE _)) (sup_le hUP hEP)
  have hPE : 𝔠.P ≤ normalizer (E : Set G) := by
    rw [hEdef]
    exact normalizer_commutator_ge_left _ _
  have hAE : A ≤ normalizer (E : Set G) := by
    rw [hEdef]
    exact le_normalizer_commutator 𝔠.A_le_normalizer_P (ρ.A_le_normalizer_of_le ρ.X_le_A)
  have hQU : 𝔠.Q ⊓ 𝔠.U = 𝔠.Q ⊓ centralizer (ρ.X : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans inf_le_right))
    · exact le_inf inf_le_left
        (le_inf (le_inf (inf_le_left.trans 𝔠.Q_le_P) inf_le_right) (inf_le_left.trans hQK))
  obtain ⟨Qs, hQsdef⟩ : ∃ Qs : Subgroup G, Qs = 𝔠.Q ⊓ 𝔠.U ⊓ centralizer (E : Set G) :=
    ⟨_, rfl⟩
  have hQs1 : Qs ≠ ⊥ := by
    obtain ⟨F, hF, hFel, hF3⟩ := h59E
    have hFQU : F ≤ 𝔠.Q ⊓ 𝔠.U := by
      rw [← h58, inf_comm]
      exact hF
    have hFE : F ≤ normalizer (E : Set G) := hFQU.trans (inf_le_left.trans (𝔠.Q_le_P.trans hPE))
    have h := inf_centralizer_ne_bot_of_isCyclic hp hp2 (𝔠.isPGroup_P.to_le hEP) hEc hFel hF3 hFE
    intro hbot
    apply h
    rw [eq_bot_iff, ← hbot, hQsdef]
    exact inf_le_inf_right _ hFQU
  have hUEV : 𝔠.U ⊓ centralizer (E : Set G) ≤ 𝔠.V := by
    obtain ⟨WK, hWK, hXWK, -, hK₁WK, hWKn, -, hL₀⟩ := 𝔠.exists_W
    have hWKK₁ : WK ≤ 𝔠.K₁ := hWK.trans inf_le_left
    have hJn : (bar 𝔠.K₁ WK).Normal := 𝔠.bar_W_normal hWKK₁ hWKn
    have hXJ : bar 𝔠.K₁ ρ.X ≤ bar 𝔠.K₁ WK := bar_mono hXWK
    have hXb := 𝔠.isKleinFour_bar_X
    have hEb : bar 𝔠.K₁ E = ⁅bar 𝔠.K₁ 𝔠.P, bar 𝔠.K₁ ρ.X⁆ := by
      rw [hEdef]
      exact bar_commutator hPK₁ 𝔠.X_le_K₁
    have hEJ : bar 𝔠.K₁ E ≤ bar 𝔠.K₁ WK :=
      hEb ▸ (commutator_mono le_rfl hXJ).trans (commutator_le_right _ _)
    have hPb : bar 𝔠.K₁ 𝔠.P = bar 𝔠.K₁ 𝔠.U ⊔ bar 𝔠.K₁ E := by
      conv_lhs => rw [hPUE]
      exact bar_sup 𝔠.U_le_K₁ (hEP.trans hPK₁)
    have hUbJ : bar 𝔠.K₁ 𝔠.U ≤ normalizer (bar 𝔠.K₁ WK : Set (Bar 𝔠.K₁)) := by
      rw [normalizer_eq_top_iff.mpr hJn]
      exact le_top
    have hUbX := 𝔠.bar_U_le_centralizer_bar_X
    have hUb : IsPGroup p (bar 𝔠.K₁ 𝔠.U) := isPGroup_bar_of_isPGroup (𝔠.isPGroup_P.to_le hUP)
    have hUbodd : Odd (Nat.card (bar 𝔠.K₁ 𝔠.U)) := CFSG.GH72.odd_card_of_isPGroup hp hp2 hUb
    have hUb1 : bar 𝔠.K₁ 𝔠.U ≠ ⊥ := 𝔠.bar_U_ne_bot hQUV
    have hJU : bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.U =
        bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.Pstar := by
      rw [← hPP, hPb]
      apply le_antisymm
      · exact sup_le le_sup_left (le_sup_left.trans le_sup_right)
      · exact sup_le le_sup_left (sup_le le_sup_right (hEJ.trans le_sup_left))
    have hJUn : (bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.U).Normal :=
      hJU ▸ 𝔠.bar_W_sup_Pstar_normal hWKK₁ hK₁WK
    have hWb1 : bar 𝔠.K₁ W ≠ ⊥ := fun h =>
      hW1 (𝔠.eq_bot_of_bar_eq_bot (hWP.trans hPP.le) hW.2.2.2.2 h)
    have hWEb : bar 𝔠.K₁ W ≤ bar 𝔠.K₁ E := bar_mono hWE
    have hEb1 : bar 𝔠.K₁ E ≠ ⊥ := fun h => hWb1 (eq_bot_iff.mpr (hWEb.trans h.le))
    have hEbp : IsPGroup p (bar 𝔠.K₁ E) := isPGroup_bar_of_isPGroup (𝔠.isPGroup_P.to_le hEP)
    rcases hL₀ with hL | ⟨-, hL⟩
    · have hZJ : center (bar 𝔠.K₁ WK) = ⊥ :=
        center_eq_bot_of_isL2OrA7 hL
      have hfaith : (bar 𝔠.K₁ WK ⊔ bar 𝔠.K₁ 𝔠.U) ⊓
          centralizer (bar 𝔠.K₁ WK : Set (Bar 𝔠.K₁)) = ⊥ :=
        sup_inf_centralizer_eq_bot hJn hJUn hZJ hUbJ hUbodd 𝔠.oddCore_bar_K₁
      rcases hL with ⟨⟨e⟩⟩ | ⟨r, k, hrF, hr2, hrk, ⟨e⟩⟩
      ·
        exfalso
        obtain ⟨hUbJ', -⟩ := le_and_card_dvd_three_of_aSeven e hXb hXJ hUbJ hUbodd hUbX hfaith
        obtain ⟨hU3, hUmax⟩ :=
          card_eq_three_and_isMaxInvIn_of_aSeven e hXb hXJ hUbJ' hUbodd hUbX hUb1
        have : Fact p.Prime := ⟨hp⟩
        have hp3 : p = 3 := by
          rcases hUb.card_eq_or_dvd with h1 | h1
          · rw [hU3] at h1
            norm_num at h1
          · rw [hU3] at h1
            exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h1
        have hEU3 : IsPGroup 3 (bar 𝔠.K₁ E ⊔ bar 𝔠.K₁ 𝔠.U : Subgroup (Bar 𝔠.K₁)) := by
          rw [← hp3]
          exact (isPGroup_bar_of_isPGroup 𝔠.isPGroup_P).to_le (hPb ▸ (sup_comm _ _).le)
        have hXEU : bar 𝔠.K₁ ρ.X ≤
            normalizer ((bar 𝔠.K₁ E ⊔ bar 𝔠.K₁ 𝔠.U : Subgroup (Bar 𝔠.K₁)) : Set (Bar 𝔠.K₁)) :=
          le_inf (hEb ▸ normalizer_commutator_ge_right _ _)
            (le_centralizer_iff.mp hUbX |>.trans (centralizer_le_normalizer _)) |>.trans
            (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)
        have hEU := hUmax.2.2.2 _ (sup_le hEJ hUbJ') hEU3 hXEU le_sup_right
        apply hWb1
        have hWX : bar 𝔠.K₁ W ≤ centralizer (bar 𝔠.K₁ ρ.X : Set (Bar 𝔠.K₁)) :=
          hWEb.trans ((le_sup_left.trans hEU.le).trans hUbX)
        have hWW : bar 𝔠.K₁ W = ⁅bar 𝔠.K₁ ρ.X, bar 𝔠.K₁ W⁆ := by
          rw [← bar_commutator 𝔠.X_le_K₁ (hW.2.2.2.1.trans inf_le_left), hW.2.2.2.2]
        rw [hWW, commutator_eq_bot_iff_le_centralizer]
        exact le_centralizer_iff.mp hWX
      ·
        have : Fact r.Prime := hrF
        have hJL : IsL2PGL2OrA7OrV4 (bar 𝔠.K₁ WK) :=
          Or.inl (Or.inr ⟨r, k, hrF, hr2, hrk, ⟨e⟩⟩)
        have hXE : bar 𝔠.K₁ ρ.X ≤ normalizer (bar 𝔠.K₁ E : Set (Bar 𝔠.K₁)) :=
          hEb ▸ normalizer_commutator_ge_right _ _
        obtain ⟨F, hF, hEF⟩ := G5d.exists_isMaxInvIn_ge hEJ hEbp hXE
        have hPbF : bar 𝔠.K₁ 𝔠.P ≤ normalizer (F : Set (Bar 𝔠.K₁)) := by
          rw [hPb]
          refine sup_le ?_ (hEF.trans le_normalizer)
          exact (le_inf hUbJ hUbX).trans
            (normalizer_inf_centralizer_le_normalizer_of_isMaxInvIn hJL hXb hXJ hp hp2 hF)
        have hmax := 𝔠.isMaxInvIn_bar_Pstar
        rw [← hPP] at hmax
        have hAFP : bar 𝔠.K₁ A ≤
            normalizer ((F ⊔ bar 𝔠.K₁ 𝔠.P : Subgroup (Bar 𝔠.K₁)) : Set (Bar 𝔠.K₁)) := by
          rw [𝔠.bar_A_eq]
          refine sup_le ?_ (𝔠.bar_Y_le_center.trans (center_le_normalizer _))
          exact (le_inf hF.2.2.1 (bar_le_normalizer
            (ρ.X_le_A.trans 𝔠.A_le_normalizer_P))).trans
            (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)
        have hFP : F ≤ bar 𝔠.K₁ 𝔠.P := by
          have h1 := hmax.2.2.2 (F ⊔ bar 𝔠.K₁ 𝔠.P) le_top
            (IsPGroup.to_sup_of_normal_left' hF.2.1 hmax.2.1 hPbF) hAFP le_sup_right
          rw [← h1]
          exact le_sup_left
        have hFC : F ⊓ centralizer (bar 𝔠.K₁ ρ.X : Set (Bar 𝔠.K₁)) = ⊥ := by
          have h1 := inf_eq_bot_of_odd_of_le_centralizer_kleinFour hr2 hrk e hXb hXJ
            (U := F ⊓ centralizer (bar 𝔠.K₁ ρ.X : Set (Bar 𝔠.K₁)))
            ((CFSG.GH72.odd_card_of_isPGroup hp hp2 hF.2.1).of_dvd_nat (card_dvd_of_le inf_le_left))
            inf_le_right
          rwa [inf_eq_left.mpr (inf_le_left.trans hF.1)] at h1
        have hFE : F ≤ bar 𝔠.K₁ E := by
          have h1 := le_commutator_sup_inf_centralizer_of_coprime_pGroup hp hp2 hF.2.1
            𝔠.isPGroup_two_bar_X hF.2.2.1
          rw [hFC, sup_bot_eq] at h1
          exact h1.trans (hEb ▸ commutator_mono hFP le_rfl)
        have hEmax : IsMaxInvIn p (bar 𝔠.K₁ ρ.X) (bar 𝔠.K₁ WK) (bar 𝔠.K₁ E) :=
          (le_antisymm hFE hEF) ▸ hF
        have h21 := inf_centralizer_eq_bot_of_isMaxInvIn hr2 hrk e hXb hXJ hp hp2 hUb hUbJ hUbX
          hfaith hEmax hEb1
        intro u hu
        have huK₁ : u ∈ 𝔠.K₁ := 𝔠.U_le_K₁ hu.1
        have hub : (QuotientGroup.mk (⟨u, huK₁⟩ : 𝔠.K₁) : Bar 𝔠.K₁) ∈
            bar 𝔠.K₁ 𝔠.U ⊓ centralizer (bar 𝔠.K₁ E : Set (Bar 𝔠.K₁)) :=
          ⟨mk_mem_bar huK₁ hu.1, bar_le_centralizer (P := E) (Q := 𝔠.U ⊓ centralizer (E : Set G))
            inf_le_right (mk_mem_bar huK₁ hu)⟩
        rw [h21, mem_bot, mk_eq_one_iff] at hub
        rw [← 𝔠.V_eq]
        exact ⟨𝔠.U_le_Pstar hu.1, hub⟩
    ·
      exfalso
      exact hEb1 (eq_bot_of_le_of_isKleinFour hL hEJ
        (CFSG.GH72.odd_card_of_isPGroup hp hp2 hEbp))
  have hQsV : Qs ≤ 𝔠.V := hQsdef ▸ (inf_le_inf_right _ inf_le_right).trans hUEV
  have hQsp : IsPGroup p Qs :=
    𝔠.isPGroup_P.to_le (hQsdef ▸ inf_le_left.trans (inf_le_left.trans 𝔠.Q_le_P))
  have hAU : A ≤ normalizer (𝔠.U : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨𝔠.A_le_normalizer_P ha,
        le_normalizer (ρ.A_le_centralizer_of_le ρ.X_le_A ha)⟩, le_normalizer (𝔠.A_le_K ha)⟩
  have hAQs : A ≤ normalizer (Qs : Set G) := fun a ha => by
    rw [hQsdef]
    exact inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨𝔠.A_le_normalizer_Q ha, hAU ha⟩,
        normalizer_le_normalizer_centralizer _ (hAE ha)⟩
  have hPQs : 𝔠.P ≤ normalizer (Qs : Set G) := by
    rw [hPUE]
    refine sup_le ?_ ?_
    · intro u hu
      rw [hQsdef]
      exact inf_normalizer_le_normalizer_inf
        ⟨inf_normalizer_le_normalizer_inf ⟨𝔠.P_le_normalizer_Q (hUP hu), le_normalizer hu⟩,
          normalizer_le_normalizer_centralizer _ (hPE (hUP hu))⟩
    · intro w hw
      apply centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro q hq
      rw [hQsdef] at hq
      exact (mem_centralizer_iff.mp hq.2 w hw).symm
  refine ⟨normalizer (Qs : Set G), ⟨⟨Qs, hQs1, hQsp, rfl⟩, hAQs, 𝔠.P, 𝔠.hP, hPQs⟩, ?_, ?_⟩
  · refine 𝔠.covers_H₁.mono ?_
    rintro g ⟨⟨-, hgQ⟩, hgM₀⟩
    have hgX : g ∈ centralizer (ρ.X : Set G) := (ρ.M₀_le) hgM₀
    have hgE : g ∈ normalizer (E : Set G) := by
      rw [hEQX]
      exact le_normalizer_commutator (L := normalizer (𝔠.Q : Set G) ⊓ centralizer (ρ.X : Set G))
        inf_le_left (inf_le_right.trans (centralizer_le_normalizer _)) ⟨hgQ, hgX⟩
    rw [hQsdef, hQU]
    exact inf_normalizer_le_normalizer_inf
      ⟨inf_normalizer_le_normalizer_inf ⟨hgQ, le_normalizer hgX⟩,
        normalizer_le_normalizer_centralizer _ hgE⟩
  · refine (𝔠.covers_centralizer_V h48i hXN₀).mono fun g hg => ?_
    apply centralizer_le_normalizer
    exact centralizer_le (fun x hx => hQsV hx) hg.1

theorem lemma_5_12_of
    (h58 : 𝔠.R = 𝔠.U)
    (h59E : ∃ E : Subgroup G, E ≤ 𝔠.R ⊓ 𝔠.Q ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3)
    (h59cyc : IsCyclic (⁅𝔠.Pstar, ρ.X⁆ : Subgroup G))
    (W : Subgroup G)
    (hW : 𝔠.Q = (𝔠.R ⊓ 𝔠.Q) ⊔ W ∧ IsCyclic W ∧
      A ≤ normalizer (W : Set G) ∧ W ≤ 𝔠.K₁ ⊓ centralizer (𝔠.V : Set G) ∧ ⁅ρ.X, W⁆ = W) :
    (𝔠.Q ⊓ 𝔠.U ≤ 𝔠.V ∨ W ≠ ⊥) → ∃ H, ρ.IsCovering p H := by
  intro h
  by_cases hQUV : 𝔠.Q ⊓ 𝔠.U ≤ 𝔠.V
  · exact 𝔠.lemma_5_12_of_inf_le h58 𝔠.quotIs_M₀ 𝔠.Y_le_M₀ 𝔠.quotIs_N₀ 𝔠.X_le_N₀ W hW hQUV
  · exact 𝔠.lemma_5_12_of_ne_bot h58 h59E h59cyc W hW (h.resolve_left hQUV) hQUV

end Sec5ConfigR

end CFSG.GH72
