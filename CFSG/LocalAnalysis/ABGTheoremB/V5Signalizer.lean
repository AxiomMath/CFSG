module

public import CFSG.LocalAnalysis.ABGTheoremB.V5Tools
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
public import CFSG.LocalAnalysis.ABGTheoremB.Statements
public import CFSG.LocalAnalysis.ABGTheoremB.V56Inputs

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

section FamilyW

variable {σ : Setting G} {J W : Subgroup G}

theorem sup_inf_C_le (hσ : σ.IsValid) (hJ : σ.IsV21Layer J) (hW : W ∈ σ.familyW J)
    {P U : Subgroup G} (hP : IsSylowOf σ.p P σ.C) (hU : U ∈ signalizersPerm ⊤ σ.D W σ.p)
    (hPU : P ≤ U) : (U ⊔ W) ⊓ σ.C ≤ P ⊔ W := by
  have : Fact σ.p.Prime := ⟨hσ.p_prime⟩
  have hWC := le_C_of_mem_familyW hσ hJ hW
  intro x hx
  obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
  have hx' : x ∈ (U : Set G) * W := by
    rw [← coe_sup_of_permutable hU.2]
    exact hxX
  obtain ⟨u, hu, w, hw, rfl⟩ := hx'
  have huC : u ∈ σ.C := by
    have := σ.C.mul_mem hxC (σ.C.inv_mem (hWC hw))
    simpa using this
  have hUC : U ⊓ σ.C = P :=
    hP.eq_of_le (le_inf hPU hP.le) inf_le_right hU.1.2.1.to_inf_left
  have huP : u ∈ P := by
    rw [← hUC]
    exact ⟨hu, huC⟩
  exact Subgroup.mul_mem_sup huP hw

end FamilyW

theorem lemmaV51 {σ : Setting G} (hσ : σ.IsValid) {J : Subgroup G} (hJ : σ.IsV21Layer J)
    (h45 : σ.LemmaV45 J) (hV31 : LemmaV31 σ J) (hV33 : LemmaV33 σ J) {W : Subgroup G}
    (hW : W ∈ σ.familyW J) {P U : Subgroup G} (hP : IsSylowOf σ.p P σ.C)
    (hU : U ∈ signalizersPerm ⊤ σ.D W σ.p) (hPU : P ≤ U) :
    U = pCoreIn σ.p (U ⊔ W) ⊔ P := by
  have hp := hσ.p_prime
  have : Fact σ.p.Prime := ⟨hp⟩
  have hUp : IsPGroup σ.p U := hU.1.2.1
  have hUW : (U : Set G) * W = W * U := hU.2
  have hWp : ¬ σ.p ∣ Nat.card W := hV31.coprime W hW
  set X := U ⊔ W with hX
  set A := pCoreIn σ.p X
  have hDX : σ.D ≤ Subgroup.normalizer (X : Set G) :=
    (le_inf hU.1.2.2.1 hW.2.1).trans (normalizer_inf_normalizer_le_normalizer_sup U W)
  have hWX : W ≤ Subgroup.normalizer (X : Set G) := le_sup_right.trans Subgroup.le_normalizer
  have hprimes : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card X → ℓ = σ.p ∨ ℓ ∣ Nat.card W := by
    intro ℓ hℓ hdvd
    rw [card_sup_pPrime hp hUp hWp hUW] at hdvd
    rcases (Nat.Prime.dvd_mul hℓ).mp hdvd with h | h
    · left
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hUp
      rw [hk] at h
      exact (Nat.prime_dvd_prime_iff_eq hℓ hp).mp (hℓ.dvd_of_dvd_pow h)
    · exact Or.inr h
  obtain ⟨-, P', hP'syl, hP'le⟩ := h45 W hW X hDX hWX hprimes
  have hXA : X ≤ Subgroup.normalizer (A : Set G) := le_normalizer_pCoreIn σ.p X
  have hAU : A ≤ U := by
    have hUA : IsPGroup σ.p (U ⊔ A : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hUp (isPGroup_pCoreIn σ.p X) (le_sup_left.trans hXA)
    have h := eq_of_le_sup_pPrime hp hUp hWp hUW hUA le_sup_left
      (sup_le le_sup_left (pCoreIn_le σ.p X))
    rw [← h]
    exact le_sup_right
  have hPA : P ≤ Subgroup.normalizer (A : Set G) := (hPU.trans le_sup_left).trans hXA
  have hMp : IsPGroup σ.p (A ⊔ P : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (isPGroup_pCoreIn σ.p X) hP.isPGroup hPA
  have hMU : A ⊔ P ≤ U := sup_le hAU hPU
  have hP'M : P' ≤ (A ⊔ P) ⊔ W := by
    refine hP'le.trans (sup_le (le_sup_left.trans le_sup_left) ?_)
    refine (sup_inf_C_le hσ hJ hW hP hU hPU).trans ?_
    exact sup_le_sup_right le_sup_right W
  have hMW : ((A ⊔ P : Subgroup G) : Set G) * W = W * ((A ⊔ P : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact permutable_sup_of_le_normalizer hPA (le_sup_right.trans hXA)
      (hV33.permutable W hW P hP)
  have hcard : Nat.card P' ∣ Nat.card (A ⊔ P : Subgroup G) :=
    card_dvd_of_le_sup_pPrime hp hMp hWp hMW hP'syl.isPGroup hP'M
  have hUsyl := isSylowOf_sup_pPrime hp hUp hWp hUW
  have hcardU : Nat.card U = Nat.card P' := by
    rw [hUsyl.card_eq, hP'syl.card_eq]
  exact (Subgroup.eq_of_le_of_card_ge hMU
    (by rw [hcardU]; exact Nat.le_of_dvd Nat.card_pos hcard)).symm

theorem propV51 {σ : Setting G} (hσ : σ.IsValid) (hII : σ.ChapterIIFacts) {J : Subgroup G}
    (hJ : σ.IsV21Layer J) (h41 : σ.PropV41 J) (hV31 : LemmaV31 σ J) (hV33 : LemmaV33 σ J)
    (h32 : σ.LemmaIV32) (h71 : σ.PropIV71) (h81 : σ.LemmaIV81) :
    σ.HypIV7 σ.p → ∀ W ∈ σ.familyW J, ∀ P : Subgroup G, IsSylowOf σ.p P σ.C →
      σ.D ≤ Subgroup.normalizer (P : Set G) →
      ∃ V ∈ signalizersPerm ⊤ σ.D W σ.p, P ≤ V ∧ pPrimeCoreIn σ.p (V ⊔ W) = ⊥ ∧
        (∃ K ∈ σ.familyL σ.p, V ⊔ W ⊔ σ.D ≤ K) ∧
        ∃ d : σ.IV7Data σ.p, d.P = P ∧ ∃ K ∈ d.familyM, V ⊔ W ⊔ σ.D ≤ K := by
  intro hHyp W hW P hP hDP
  have hp := hσ.p_prime
  have hp2 := hσ.p_ne_two
  have : Fact σ.p.Prime := ⟨hp⟩
  have hD2 : IsPGroup 2 σ.D := σ.S.isPGroup'.to_le σ.D_le_S
  have hPp : IsPGroup σ.p P := hP.isPGroup
  have hPN : P ≤ σ.N := hP.le.trans σ.C_le_N
  have hPD : P ⊓ σ.D = ⊥ := inf_eq_bot_of_isPGroup_of_two hp hp2 hPp hD2
  have hPW : (P : Set G) * W = W * P := hV33.permutable W hW P hP
  have hWN : W ≤ σ.N := le_N_of_mem_familyW hσ hJ hW
  have hWp : ¬ σ.p ∣ Nat.card W := hV31.coprime W hW
  have hWodd : Odd (Nat.card W) := odd_card_of_mem_familyW hσ hJ hW
  have hWON : W ⊓ σ.ON = ⊥ := hV33.inf_ON W hW
  have hON : σ.ON ≠ ⊥ := ne_bot_of_prime_dvd_card hp hHyp.dvd_ON
  have hPsigN : P ∈ signalizersPerm σ.N σ.D W σ.p := ⟨⟨hPN, hPp, hDP, hPD⟩, hPW⟩
  obtain ⟨U, hU, hPU, -, hRsyl⟩ :=
    (h41 σ.N (σ.D_le_N hσ) hON P hP hDP hPN W hW hWN P hPsigN le_rfl).1
  set R := U ⊓ σ.ON with hR
  have hUp : IsPGroup σ.p U := hU.1.2.1
  have hDR : σ.D ≤ Subgroup.normalizer (R : Set G) :=
    (le_inf hU.1.2.2.1 ((σ.D_le_N hσ).trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPR : P ≤ Subgroup.normalizer (R : Set G) :=
    (le_inf (hPU.trans Subgroup.le_normalizer) (hPN.trans σ.N_le_normalizer_ON)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hWR : W ≤ Subgroup.normalizer (R : Set G) :=
    le_normalizer_inf_of_permutable hU.2.symm (coprime_card_of_isPGroup hp hUp hWp).symm
      (hWN.trans σ.N_le_normalizer_ON) hWON
  obtain ⟨hK, hcon⟩ := h32 σ.p hp hHyp.dvd_ON hHyp.exceptional R hRsyl hDR
  set K := Subgroup.normalizer (R : Set G) with hKdef
  obtain ⟨-, -, -, -, ⟨hOKN, -⟩, -⟩ := σ.familyL_properties hσ hII hp hHyp.dvd_ON hK
  have hOK : oddCoreIn K ≠ ⊥ := oddCoreIn_ne_bot_of_isPLocal hp hp2 hK.1
  have hS : solvRadIn K = oddCoreIn K ⊔ centerOf σ.D :=
    hII.qgroup_solvRad K hDR hOK hK.2.1
  have hZ2 : IsPGroup 2 (centerOf σ.D) := hD2.to_le inf_le_left
  have hZK : centerOf σ.D ≤ K := inf_le_left.trans hDR
  have hWOK : W ⊓ oddCoreIn K = ⊥ := by
    rw [eq_bot_iff, ← hWON]
    intro x hx
    exact ⟨hx.1, hOKN ⟨hx.2, hWN hx.1⟩⟩
  have hPsigK : P ∈ signalizersPerm K σ.D W σ.p := ⟨⟨hPR, hPp, hDP, hPD⟩, hPW⟩
  obtain ⟨U₁, hU₁, hPU₁, -, hFsyl⟩ :=
    (h41 K hDR hOK P hP hDP hPR W hW hWR P hPsigK le_rfl).1
  set F := U₁ ⊓ oddCoreIn K with hF
  have hU₁p : IsPGroup σ.p U₁ := hU₁.1.2.1
  have hKO : K ≤ Subgroup.normalizer (oddCoreIn K : Set G) := le_normalizer_oddCoreIn K
  have hFp : IsPGroup σ.p F := hFsyl.isPGroup
  have hDF : σ.D ≤ Subgroup.normalizer (F : Set G) :=
    (le_inf hU₁.1.2.2.1 (hDR.trans hKO)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hPF : P ≤ Subgroup.normalizer (F : Set G) :=
    (le_inf (hPU₁.trans Subgroup.le_normalizer) (hPR.trans hKO)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hWF : W ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_inf_of_permutable hU₁.2.symm (coprime_card_of_isPGroup hp hU₁p hWp).symm
      (hWR.trans hKO) hWOK
  obtain ⟨d, hdP, hdR⟩ := h71 σ.p hHyp P R hP hDP hRsyl hDR hPR
  set Q := d.Q with hQ
  have hQP : Q ≤ P := hdP ▸ d.Q_le
  have hQchar : (Q.subgroupOf P).Characteristic := hdP ▸ d.Q_characteristic
  have hNPQ := normalizer_le_normalizer_of_characteristic hQP hQchar
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := Subgroup.le_normalizer.trans hNPQ
  have hDQ : σ.D ≤ Subgroup.normalizer (Q : Set G) := hDP.trans hNPQ
  have hWQ : W ≤ Subgroup.normalizer (Q : Set G) := hV33.normalizes_Q hHyp W hW d
  set M := F ⊓ Subgroup.normalizer (Q : Set G) with hM
  have hnormM : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (F : Set G) →
      A ≤ Subgroup.normalizer (Q : Set G) → A ≤ Subgroup.normalizer (M : Set G) := by
    intro A hAF hAQ
    exact (le_inf hAF (hAQ.trans Subgroup.le_normalizer)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hPM := hnormM P hPF hPQ
  have hWM := hnormM W hWF hWQ
  have hDM := hnormM σ.D hDF hDQ
  set V := P ⊔ M with hV
  have hVp : IsPGroup σ.p V := IsPGroup.to_sup_of_normal_right' hPp hFp.to_inf_left hPM
  have hDV : σ.D ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf hDP hDM).trans (normalizer_inf_normalizer_le_normalizer_sup P M)
  have hVW : (V : Set G) * W = W * V := permutable_sup_of_le_normalizer hPM hWM hPW
  have hVsig : V ∈ signalizersPerm ⊤ σ.D W σ.p :=
    ⟨⟨le_top, hVp, hDV, inf_eq_bot_of_isPGroup_of_two hp hp2 hVp hD2⟩, hVW⟩
  have hMK : M ≤ K := inf_le_left.trans (inf_le_right.trans (oddCoreIn_le K))
  refine ⟨V, hVsig, le_sup_left, ?_, ⟨K, hK, sup_le (sup_le (sup_le hPR hMK) hWR) hDR⟩,
    d, hdP, Subgroup.normalizer (Q : Set G), h81 σ.p hHyp d,
    sup_le (sup_le (sup_le hPQ inf_le_right) hWQ) hDQ⟩
  set Y := pPrimeCoreIn σ.p (V ⊔ W) with hY
  have hYW : Y ≤ W := pPrimeCoreIn_sup_le hp hVp hWp hVW
  have hYp : ¬ σ.p ∣ Nat.card Y := fun h =>
    hWp (h.trans (Subgroup.card_dvd_of_le hYW))
  set V₀ := Q ⊔ M with hV₀
  have hV₀V : V₀ ≤ V := sup_le_sup_right hQP M
  have hV₀p : IsPGroup σ.p V₀ := hVp.to_le hV₀V
  have hYV₀ : Y ≤ Subgroup.centralizer (V₀ : Set G) := by
    apply le_centralizer_of_le_normalizer
    · exact hYW.trans ((le_inf hWQ hWM).trans (normalizer_inf_normalizer_le_normalizer_sup Q M))
    · exact (hV₀V.trans le_sup_left).trans (le_normalizer_pPrimeCoreIn σ.p _)
    · rw [inf_comm]
      exact inf_eq_bot_of_coprime (coprime_card_of_isPGroup hp hV₀p hYp)
  have hYQ : Y ≤ Subgroup.centralizer (Q : Set G) :=
    hYV₀.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hYFQ : Y ≤ Subgroup.centralizer
      ((F ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
    refine hYV₀.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr ?_))
    exact (inf_le_inf_left F (Subgroup.centralizer_le_normalizer _)).trans le_sup_right
  have hYF : Y ≤ Subgroup.centralizer (F : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.ambient_subgroup_axb_centralizer_le σ.p hp Q Y F
      (hPp.to_le hQP) hFp (coprime_card_of_isPGroup hp hFp hYp) (hQP.trans hPF)
      (hYW.trans hWF) hYQ hYFQ
  have hYS : Y ≤ solvRadIn K :=
    (le_inf (hYW.trans hWR) hYF).trans
      (inf_centralizer_le_solvRadIn hp hp2 hcon hS hZ2 hZK hFsyl)
  rw [eq_bot_iff, ← inf_solvRadIn_eq_bot hS hZ2 hZK hWodd hWOK]
  exact le_inf hYW hYS

end CFSG.ABGTheoremB.V56
