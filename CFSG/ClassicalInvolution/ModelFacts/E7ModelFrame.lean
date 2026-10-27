module

public import CFSG.ClassicalInvolution.ModelFacts.E7ModelFrameStep
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdMain
public import CFSG.ClassicalInvolution.RouteD.TypeE8Block
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

section Frame

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)
local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)

theorem transport_rel {c : M₇} {A B A' B' : Subgroup M₇} (hA : conjSub c A = A')
    (hB : conjSub c B = B') :
    (A ≠ B → A' ≠ B') ∧ (¬ Commutes A B → ¬ Commutes A' B') ∧
      (Commutes A B → Commutes A' B') := by
  subst hA hB
  refine ⟨fun h heq => h ?_, fun h hc => h ?_, fun h => h.conjSub c⟩
  · have := congrArg (conjSub c⁻¹) heq
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this
  · have := hc.conjSub c⁻¹
    rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem exists_conj_pin {ω : List ℕ} {γ g : V7} (hγ : IsRoot .E7 γ)
    (h : wordAct ω γ = g ∨ wordAct ω γ = -g) (Zs : List V7)
    (hZ : ∀ z ∈ Zs, IsRoot .E7 z ∧ wordAct ω z = z) :
    ∃ k : M₇, conjSub k (stdRankOne D₇ γ) = stdRankOne D₇ g ∧
      ∀ z ∈ Zs, conjSub k (stdRankOne D₇ z) = stdRankOne D₇ z := by
  obtain ⟨k, hk⟩ := exists_conj_stdRankOne_wordAct (GaloisField p f) ω
  refine ⟨k, ?_, fun z hz => ?_⟩
  · rw [hk γ hγ]
    rcases h with h | h
    · rw [h]
    · rw [h, stdRankOne_neg]
  · rw [hk z (hZ z hz).1, (hZ z hz).2]

theorem frame_round_one (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (C : Fin 4 → Subgroup M₇)
    (hC : ∀ i, C i ∈ fundamentalSubgroups .E7 D₇)
    (hadj : ∀ i j : Fin 4, i.val + 1 = j.val →
      Gaps.ModelAdj (Subgroup.center M₇) (C i) (C j) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (C i) (C j))
    (hnadj : ∀ i j : Fin 4, i.val + 2 ≤ j.val → Commutes (C i) (C j)) :
    ∃ c : M₇, conjSub c (C 0) = stdRankOne D₇ e0V ∧ conjSub c (C 1) = stdRankOne D₇ thetaE7 ∧
      conjSub c (C 2) = stdRankOne D₇ gA := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  have he2 : IsRoot .E7 (Pi.single (e7Idx 2) 1 : V7) := isRoot_single .E7 (e7Idx 2)
  obtain ⟨g, hg1, hg2⟩ := e7PairFrame_sc hp2 hq (C 0) (hC 0) (C 1) (hC 1) (hadj 0 1 rfl).1
    (hadj 0 1 rfl).2 0 2 (by decide)
  have hpair : iform (Pi.single (e7Idx 2) 1 : V7) e0V = 1 ∨
      iform (Pi.single (e7Idx 2) 1 : V7) e0V = -1 := by decide +kernel
  obtain ⟨k, hk2, hk0⟩ := exists_conj_theta_e0 (GaloisField p f) he2 he0 hpair
  rw [e7Idx_zero] at hk0
  have hx₀0 : conjSub (k * g⁻¹) (C 0) = stdRankOne D₇ e0V := by
    rw [conjSub_mul, hg1, conjSub_inv_conjSub]
    exact hk0
  have hx₀1 : conjSub (k * g⁻¹) (C 1) = stdRankOne D₇ thetaE7 := by
    rw [conjSub_mul, hg2, conjSub_inv_conjSub]
    exact hk2
  set x₀ : M₇ := k * g⁻¹ with hx₀
  have hX₂ : conjSub x₀ (C 2) ∈ fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups (hC 2) x₀
  have hθX : InvComm (stdRankOne D₇ thetaE7) (conjSub x₀ (C 2)) := by
    have := (invComm_of_modelAdj hp2 hq (hC 1) (hC 2) (hadj 1 2 rfl).1).conjSub x₀
    rwa [hx₀1] at this
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub x₀ (C 2)) := by
    have := (hnadj 0 2 (by decide)).conjSub x₀
    rwa [hx₀0] at this
  obtain ⟨x₁, hx₁θ, hx₁e, -, γ₂, hγ₂, hx₁⟩ := stage_step hp2 hq hX₂ hθX hcomm
    (J := Jsign) subset_rfl lamSign_J lamSign_B lamSign_ker [] (by simp) (by simp) (by simp)
    (fun y hyG hyd hye _ => levi_prefix hp2 hq hyG hyd hye)
  have hc0 : conjSub (x₁ * x₀) (C 0) = stdRankOne D₇ e0V := by
    rw [conjSub_mul, hx₀0, hx₁e]
  have hc1 : conjSub (x₁ * x₀) (C 1) = stdRankOne D₇ thetaE7 := by
    rw [conjSub_mul, hx₀1, hx₁θ]
  have hc2 : conjSub (x₁ * x₀) (C 2) = stdRankOne D₇ γ₂ := by
    rw [conjSub_mul, hx₁]
  have hne := (transport_rel hc1 hc2).1 (hadj 1 2 rfl).1.1
  have hnc := (transport_rel hc1 hc2).2.1 (hadj 1 2 rfl).1.2.1
  have hcm := (transport_rel hc0 hc2).2.2 (hnadj 0 2 (by decide))
  have hθγ := iform_odd_of_rel hp2 hq isRoot_thetaE7 hγ₂ hne hnc
  have h0γ := iform_eq_zero_of_commutes hp2 hq he0 hγ₂ hcm
  rw [thetaE7_eq] at hθγ
  obtain ⟨ω, hω, hωγ⟩ := pin_A γ₂ (mem_rootFinset.2 hγ₂) hθγ h0γ
  have hfix := pinWordsA_fix ω hω
  obtain ⟨k₂, hk₂γ, hk₂Z⟩ := exists_conj_pin (p := p) (f := f) hγ₂ hωγ [thetaE7, e0V] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact ⟨isRoot_thetaE7, by rw [thetaE7_eq]; exact hfix.1⟩
    · exact ⟨he0, hfix.2⟩)
  refine ⟨k₂ * (x₁ * x₀), ?_, ?_, ?_⟩
  · rw [conjSub_mul, hc0]
    exact hk₂Z e0V (by simp)
  · rw [conjSub_mul, hc1]
    exact hk₂Z thetaE7 (by simp)
  · rw [conjSub_mul, hc2]
    exact hk₂γ

theorem frame_round_two (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (C : Fin 4 → Subgroup M₇)
    (hC : ∀ i, C i ∈ fundamentalSubgroups .E7 D₇)
    (hadj : ∀ i j : Fin 4, i.val + 1 = j.val →
      Gaps.ModelAdj (Subgroup.center M₇) (C i) (C j) ∧
        ∃ W, LinearBlockStandardPair (GaloisField p f) W (C i) (C j))
    (hnadj : ∀ i j : Fin 4, i.val + 2 ≤ j.val → Commutes (C i) (C j)) {c : M₇}
    (hc0 : conjSub c (C 0) = stdRankOne D₇ e0V) (hc1 : conjSub c (C 1) = stdRankOne D₇ thetaE7)
    (hc2 : conjSub c (C 2) = stdRankOne D₇ gA) :
    ∃ c' : M₇, conjSub c' (C 0) = stdRankOne D₇ e0V ∧ conjSub c' (C 1) = stdRankOne D₇ thetaE7 ∧
      conjSub c' (C 2) = stdRankOne D₇ gA ∧ conjSub c' (C 3) = stdRankOne D₇ gB := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  have hX₃ : conjSub c (C 3) ∈ fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups (hC 3) c
  have hθX : InvComm (stdRankOne D₇ thetaE7) (conjSub c (C 3)) := by
    have := (invComm_of_commutes (hnadj 1 3 (by decide))).conjSub c
    rwa [hc1] at this
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c (C 3)) := by
    have := (hnadj 0 3 (by decide)).conjSub c
    rwa [hc0] at this
  have hZX : ∀ z ∈ [gA], InvComm (stdRankOne D₇ z) (conjSub c (C 3)) := by
    intro z hz
    rw [List.mem_singleton.1 hz]
    have := (invComm_of_modelAdj hp2 hq (hC 2) (hC 3) (hadj 2 3 rfl).1).conjSub c
    rwa [hc2] at this
  obtain ⟨x₂, hx₂θ, hx₂e, hx₂Z, γ₃, hγ₃, hx₂⟩ := stage_step hp2 hq hX₃ hθX hcomm
    (J := JofL [0, 2, 5]) (JofL_le_Jsign (by simp) (by simp)) lamB_J lamB_B lamB_ker [gA]
    (fun z hz => by rw [List.mem_singleton.1 hz]; exact isRoot_gA)
    (fun z hz j hj => by rw [List.mem_singleton.1 hz]; exact gA_even_JB j hj) hZX
    (fun y hyG hyd hye hyz => levi_cut hp2 lamSign_J lamSign_B isRoot_gA cut_B hyG
      (levi_prefix hp2 hq hyG hyd hye) (hyz gA (by simp)))
  have hd0 : conjSub (x₂ * c) (C 0) = stdRankOne D₇ e0V := by
    rw [conjSub_mul, hc0, hx₂e]
  have hd1 : conjSub (x₂ * c) (C 1) = stdRankOne D₇ thetaE7 := by
    rw [conjSub_mul, hc1, hx₂θ]
  have hd2 : conjSub (x₂ * c) (C 2) = stdRankOne D₇ gA := by
    rw [conjSub_mul, hc2]
    exact hx₂Z gA (by simp)
  have hd3 : conjSub (x₂ * c) (C 3) = stdRankOne D₇ γ₃ := by
    rw [conjSub_mul, hx₂]
  have hne := (transport_rel hd2 hd3).1 (hadj 2 3 rfl).1.1
  have hnc := (transport_rel hd2 hd3).2.1 (hadj 2 3 rfl).1.2.1
  have hcθ := (transport_rel hd1 hd3).2.2 (hnadj 1 3 (by decide))
  have hce := (transport_rel hd0 hd3).2.2 (hnadj 0 3 (by decide))
  have hgγ := iform_odd_of_rel hp2 hq isRoot_gA hγ₃ hne hnc
  have hθγ := iform_eq_zero_of_commutes hp2 hq isRoot_thetaE7 hγ₃ hcθ
  have heγ := iform_eq_zero_of_commutes hp2 hq he0 hγ₃ hce
  rw [thetaE7_eq] at hθγ
  obtain ⟨ω, hω, hωγ⟩ := pin_B γ₃ (mem_rootFinset.2 hγ₃) hgγ hθγ heγ
  have hfix := pinWordsB_fix ω hω
  obtain ⟨k₃, hk₃γ, hk₃Z⟩ := exists_conj_pin (p := p) (f := f) hγ₃ hωγ [thetaE7, e0V, gA] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨isRoot_thetaE7, by rw [thetaE7_eq]; exact hfix.1⟩
    · exact ⟨he0, hfix.2.1⟩
    · exact ⟨isRoot_gA, hfix.2.2⟩)
  refine ⟨k₃ * (x₂ * c), ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hd0]
    exact hk₃Z e0V (by simp)
  · rw [conjSub_mul, hd1]
    exact hk₃Z thetaE7 (by simp)
  · rw [conjSub_mul, hd2]
    exact hk₃Z gA (by simp)
  · rw [conjSub_mul, hd3]
    exact hk₃γ

theorem frame_round_three (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (C : Fin 4 → Subgroup M₇)
    (RM : Subgroup M₇) (hRM : RM ∈ fundamentalSubgroups .E7 D₇)
    (hRMC : ∀ i, Commutes RM (C i)) {c : M₇}
    (hc0 : conjSub c (C 0) = stdRankOne D₇ e0V) (hc1 : conjSub c (C 1) = stdRankOne D₇ thetaE7)
    (hc2 : conjSub c (C 2) = stdRankOne D₇ gA) (hc3 : conjSub c (C 3) = stdRankOne D₇ gB) :
    ∃ c' : M₇, conjSub c' (C 0) = stdRankOne D₇ e0V ∧ conjSub c' (C 1) = stdRankOne D₇ thetaE7 ∧
      conjSub c' (C 2) = stdRankOne D₇ gA ∧ conjSub c' (C 3) = stdRankOne D₇ gB ∧
      conjSub c' RM = stdRankOne D₇ muV := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  have hXM : conjSub c RM ∈ fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hRM c
  have hcom : ∀ (i : Fin 4) (r : V7), conjSub c (C i) = stdRankOne D₇ r →
      Commutes (stdRankOne D₇ r) (conjSub c RM) := fun i r h => by
    have := (hRMC i).symm.conjSub c
    rwa [h] at this
  have hθX : InvComm (stdRankOne D₇ thetaE7) (conjSub c RM) := invComm_of_commutes (hcom 1 _ hc1)
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c RM) := hcom 0 _ hc0
  have hZX : ∀ z ∈ [gA, gB], InvComm (stdRankOne D₇ z) (conjSub c RM) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact invComm_of_commutes (hcom 2 _ hc2)
    · exact invComm_of_commutes (hcom 3 _ hc3)
  obtain ⟨x₃, hx₃θ, hx₃e, hx₃Z, γ, hγ, hx₃⟩ := stage_step hp2 hq hXM hθX hcomm
    (J := JofL [0, 2, 4, 5, 6]) (JofL_le_Jsign (by simp) (by simp)) lamC_J lamC_B lamC_ker
    [gA, gB]
    (fun z hz => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact isRoot_gA
      · exact isRoot_gB)
    (fun z hz j hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · exact gA_even_JC j hj
      · exact gB_even_JC j hj) hZX
    (fun y hyG hyd hye hyz => levi_cut hp2 lamB_J lamB_B isRoot_gB cut_C hyG
      (levi_cut hp2 lamSign_J lamSign_B isRoot_gA cut_B hyG (levi_prefix hp2 hq hyG hyd hye)
        (hyz gA (by simp))) (hyz gB (by simp)))
  have hd0 : conjSub (x₃ * c) (C 0) = stdRankOne D₇ e0V := by
    rw [conjSub_mul, hc0, hx₃e]
  have hd1 : conjSub (x₃ * c) (C 1) = stdRankOne D₇ thetaE7 := by
    rw [conjSub_mul, hc1, hx₃θ]
  have hd2 : conjSub (x₃ * c) (C 2) = stdRankOne D₇ gA := by
    rw [conjSub_mul, hc2]
    exact hx₃Z gA (by simp)
  have hd3 : conjSub (x₃ * c) (C 3) = stdRankOne D₇ gB := by
    rw [conjSub_mul, hc3]
    exact hx₃Z gB (by simp)
  have hdM : conjSub (x₃ * c) RM = stdRankOne D₇ γ := by
    rw [conjSub_mul, hx₃]
  have hθγ := iform_eq_zero_of_commutes hp2 hq isRoot_thetaE7 hγ
    ((transport_rel hd1 hdM).2.2 (hRMC 1).symm)
  have heγ := iform_eq_zero_of_commutes hp2 hq he0 hγ ((transport_rel hd0 hdM).2.2 (hRMC 0).symm)
  have hAγ := iform_eq_zero_of_commutes hp2 hq isRoot_gA hγ
    ((transport_rel hd2 hdM).2.2 (hRMC 2).symm)
  have hBγ := iform_eq_zero_of_commutes hp2 hq isRoot_gB hγ
    ((transport_rel hd3 hdM).2.2 (hRMC 3).symm)
  rw [thetaE7_eq] at hθγ
  obtain ⟨ω, hω, hωγ⟩ := pin_C γ (mem_rootFinset.2 hγ) hθγ heγ hAγ hBγ
  have hfix := pinWordsC_fix ω hω
  obtain ⟨k₄, hk₄γ, hk₄Z⟩ := exists_conj_pin (p := p) (f := f) hγ hωγ [thetaE7, e0V, gA, gB] (by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨isRoot_thetaE7, by rw [thetaE7_eq]; exact hfix.1⟩
    · exact ⟨he0, hfix.2.1⟩
    · exact ⟨isRoot_gA, hfix.2.2.1⟩
    · exact ⟨isRoot_gB, hfix.2.2.2⟩)
  refine ⟨k₄ * (x₃ * c), ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hd0]
    exact hk₄Z e0V (by simp)
  · rw [conjSub_mul, hd1]
    exact hk₄Z thetaE7 (by simp)
  · rw [conjSub_mul, hd2]
    exact hk₄Z gA (by simp)
  · rw [conjSub_mul, hd3]
    exact hk₄Z gB (by simp)
  · rw [conjSub_mul, hdM]
    exact hk₄γ

theorem e7A1A4Frame_sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ (C : Fin 4 → Subgroup M₇) (RM : Subgroup M₇),
      (∀ i, C i ∈ fundamentalSubgroups .E7 D₇) → RM ∈ fundamentalSubgroups .E7 D₇ →
      (∀ i j : Fin 4, i.val + 1 = j.val →
        Gaps.ModelAdj (Subgroup.center M₇) (C i) (C j) ∧
          ∃ W, LinearBlockStandardPair (GaloisField p f) W (C i) (C j)) →
      (∀ i j : Fin 4, i.val + 2 ≤ j.val → Commutes (C i) (C j)) →
      (∀ i, Commutes RM (C i)) →
      ∃ g : M₇, RM = conjSub g ((D₇).rootGroup CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7 ⊔
          (D₇).rootGroup (-CFSG.ClassicalInvolution.ModelFacts.ChevAut.θE7)) ∧
        ∀ i, C i = conjSub g (rankOne (D₇).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) i)) := by
  intro C RM hC hRM hadj hnadj hRMC
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨c₁, h10, h11, h12⟩ := frame_round_one hp2 hq C hC hadj hnadj
  obtain ⟨c₂, h20, h21, h22, h23⟩ := frame_round_two hp2 hq C hC hadj hnadj h10 h11 h12
  obtain ⟨c₃, h30, h31, h32, h33, h3M⟩ :=
    frame_round_three hp2 hq C RM hRM hRMC h20 h21 h22 h23
  obtain ⟨kf, hkf⟩ := exists_conj_stdRankOne_wordAct (GaloisField p f) finalWord
  have key : ∀ (A B : Subgroup M₇), conjSub (kf * c₃) A = B → A = conjSub (kf * c₃)⁻¹ B :=
    fun A B h => by rw [← h, conjSub_inv_conjSub]
  have hRMt : conjSub (kf * c₃) RM = stdRankOne D₇ thetaLit := by
    rw [conjSub_mul, h3M, hkf muV isRoot_muV]
    have : wordAct finalWord muV = thetaLit := finalWord_RM
    rw [this]
  have h0 : wordAct finalWord e0V = -(simpleV 6) := finalWord_C0
  have h1 : wordAct finalWord thetaE7 = simpleV 5 := by rw [thetaE7_eq]; exact finalWord_C1
  have h2 : wordAct finalWord gA = -(simpleV 4) := finalWord_C2
  have h3 : wordAct finalWord gB = -(simpleV 3) := finalWord_C3
  have e0' : C 0 = conjSub (kf * c₃)⁻¹
      (rankOne (D₇).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) 0)) := by
    refine key _ _ ?_
    rw [conjSub_mul, h30, hkf e0V he0, h0, stdRankOne_neg]
    rfl
  have e1' : C 1 = conjSub (kf * c₃)⁻¹
      (rankOne (D₇).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) 1)) := by
    refine key _ _ ?_
    rw [conjSub_mul, h31, hkf thetaE7 isRoot_thetaE7, h1]
    rfl
  have e2' : C 2 = conjSub (kf * c₃)⁻¹
      (rankOne (D₇).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) 2)) := by
    refine key _ _ ?_
    rw [conjSub_mul, h32, hkf gA isRoot_gA, h2, stdRankOne_neg]
    rfl
  have e3' : C 3 = conjSub (kf * c₃)⁻¹
      (rankOne (D₇).rootGroup ((![6, 5, 4, 3] : Fin 4 → Fin 7) 3)) := by
    refine key _ _ ?_
    rw [conjSub_mul, h33, hkf gB isRoot_gB, h3, stdRankOne_neg]
    rfl
  refine ⟨(kf * c₃)⁻¹, key _ _ hRMt, fun i => ?_⟩
  fin_cases i
  exacts [e0', e1', e2', e3']

end Frame

theorem e7A1A4Frame {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    CFSG.ClassicalInvolution.RouteD.TypeE8.E7A1A4Frame p f :=
  e7A1A4Frame_sc hp2 hq

end CFSG.ClassicalInvolution.ModelFacts.E7Model
