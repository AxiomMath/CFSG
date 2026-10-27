module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclRound
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclStarData
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclFrame
public import CFSG.ClassicalInvolution.RouteD.TypeE8Excl
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

section Star

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)
local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)

theorem fix_theta_conv {ω : List ℕ}
    (h : wordAct ω thetaLit = thetaLit ∨ wordAct ω thetaLit = -thetaLit) :
    wordAct ω thetaE7 = thetaE7 ∨ wordAct ω thetaE7 = -thetaE7 := by
  rw [thetaE7_eq]
  exact h

theorem invComm_of_linearPair (hp2 : p ≠ 2) {U V : Subgroup M₇}
    (h : ∃ W, LinearBlockStandardPair (GaloisField p f) W U V) : InvComm U V := by
  obtain ⟨W, hW⟩ := h
  intro s hs hs2 t ht ht2
  exact Gaps.standardPair_involutions_commute (two_ne_zero_galoisField f hp2) hW hs ht hs2 ht2

theorem e7PerpA2StarFree_sc (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∀ A ∈ fundamentalSubgroups .E7 D₇, ∀ B ∈ fundamentalSubgroups .E7 D₇,
      Gaps.ModelAdj (Subgroup.center M₇) A B →
      (∃ W, LinearBlockStandardPair (GaloisField p f) W A B) →
      ∀ C ∈ fundamentalSubgroups .E7 D₇, ∀ L₁ ∈ fundamentalSubgroups .E7 D₇,
        ∀ L₂ ∈ fundamentalSubgroups .E7 D₇, ∀ L₃ ∈ fundamentalSubgroups .E7 D₇,
        Commutes C A → Commutes C B → Commutes L₁ A → Commutes L₁ B → Commutes L₂ A →
        Commutes L₂ B → Commutes L₃ A → Commutes L₃ B →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W C L₁) →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W C L₂) →
        (∃ W, LinearBlockStandardPair (GaloisField p f) W C L₃) →
        Commutes L₁ L₂ → Commutes L₁ L₃ → Commutes L₂ L₃ → False := by
  intro A hA B hB hadj hlin C hC L₁ hL₁ L₂ hL₂ L₃ hL₃ hCA hCB h1A h1B h2A h2B h3A h3B hl1 hl2 hl3
    h12 h13 h23
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨x₀, hxA, hxB⟩ := pair_normal hp2 hq hA hB hadj hlin
  have hcommθ : ∀ (X : Subgroup M₇) (c : M₇), Commutes X B →
      Commutes (stdRankOne D₇ thetaE7) (conjSub c X) → True := fun _ _ _ _ => trivial
  clear hcommθ
  obtain ⟨c₁, hc₁C, hc₁θ, hc₁e⟩ : ∃ c : M₇, conjSub c C = stdRankOne D₇ starC ∧
      conjSub c B = stdRankOne D₇ thetaE7 ∧ conjSub c A = stdRankOne D₇ e0V := by
    have hX : conjSub x₀ C ∈ fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hC x₀
    have hθG : GRel thetaE7 false (conjSub x₀ C) := by
      have := hCB.symm.conjSub x₀
      rwa [hxB] at this
    have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub x₀ C) := by
      have := hCA.symm.conjSub x₀
      rwa [hxA] at this
    obtain ⟨k, hkX, hkθ, hke, -⟩ := round_pin hp2 hq hX false hθG (invComm_of_commutes hθG) hcomm
      (J := Jsign) subset_rfl lamSign_J lamSign_B lamSign_ker [] (by simp) (by simp) (by simp)
      (by simp) (fun y hyG hyd hye _ => levi_prefix hp2 hq hyG hyd hye) starC starPinC
      (fun γ hγ hrθ hre _ => by
        have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
        obtain ⟨ω, hω, hωγ⟩ := star_pinC γ (mem_rootFinset.2 hγ) h1 hre
        obtain ⟨hf1, hf2⟩ := starPinC_fix ω hω
        exact ⟨ω, hω, hωγ, fix_theta_conv hf1, hf2, by simp⟩)
    refine ⟨k * x₀, ?_, ?_, ?_⟩
    · rw [conjSub_mul]
      exact hkX
    · rw [conjSub_mul, hxB]
      exact hkθ
    · rw [conjSub_mul, hxA]
      exact hke
  obtain ⟨c₂, hc₂C, hc₂L, hc₂θ, hc₂e⟩ : ∃ c : M₇, conjSub c C = stdRankOne D₇ starC ∧
      conjSub c L₁ = stdRankOne D₇ star1 ∧ conjSub c B = stdRankOne D₇ thetaE7 ∧
      conjSub c A = stdRankOne D₇ e0V := by
    have hX : conjSub c₁ L₁ ∈ fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hL₁ c₁
    have hθG : GRel thetaE7 false (conjSub c₁ L₁) := by
      have := h1B.symm.conjSub c₁
      rwa [hc₁θ] at this
    have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c₁ L₁) := by
      have := h1A.symm.conjSub c₁
      rwa [hc₁e] at this
    have hCG : GRel starC true (conjSub c₁ L₁) := by
      obtain ⟨W, hW⟩ := hl1
      refine ⟨?_, ?_⟩
      · have := (transport_rel (c := c₁) (A := C) (B := L₁) rfl rfl).1
          (ne_of_linearBlockStandardPair hW)
        rwa [hc₁C] at this
      · have := (transport_rel (c := c₁) (A := C) (B := L₁) rfl rfl).2.1
          (not_commutes_of_linearBlockStandardPair hW)
        rwa [hc₁C] at this
    have hCX : InvComm (stdRankOne D₇ starC) (conjSub c₁ L₁) := by
      have := (invComm_of_linearPair hp2 hl1).conjSub c₁
      rwa [hc₁C] at this
    obtain ⟨k, hkX, hkθ, hke, hkZ⟩ := round_pin hp2 hq hX false hθG (invComm_of_commutes hθG)
      hcomm (J := JofL [0, 2, 3]) (JofL_le_Jsign (by simp) (by simp)) starLam1_J starLam1_B
      starLam1_ker [(starC, true)] (by simp [isRoot_starC]) (by
        intro zb hzb j hj
        rw [List.mem_singleton.1 hzb]
        exact starC_even_J1 j hj) (by
        intro zb hzb
        rw [List.mem_singleton.1 hzb]
        exact hCX) (by
        intro zb hzb
        rw [List.mem_singleton.1 hzb]
        exact hCG)
      (fun y hyG hyd hye hyz => levi_cut hp2 lamSign_J lamSign_B isRoot_starC star_cut1 hyG
        (levi_prefix hp2 hq hyG hyd hye) (hyz (starC, true) (by simp))) star1 starPin1
      (fun γ hγ hrθ hre hrZ => by
        have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
        have h2 : iform starC γ = 1 ∨ iform starC γ = -1 := hrZ (starC, true) (by simp)
        obtain ⟨ω, hω, hωγ⟩ := star_pin1 γ (mem_rootFinset.2 hγ) h1 hre h2
        obtain ⟨hf1, hf2, hf3⟩ := starPin1_fix ω hω
        refine ⟨ω, hω, hωγ, fix_theta_conv hf1, hf2, ?_⟩
        intro zb hzb
        rw [List.mem_singleton.1 hzb]
        exact hf3)
    have hkC := hkZ (starC, true) (by simp)
    refine ⟨k * c₁, ?_, ?_, ?_, ?_⟩
    · rw [conjSub_mul, hc₁C]
      exact hkC
    · rw [conjSub_mul]
      exact hkX
    · rw [conjSub_mul, hc₁θ]
      exact hkθ
    · rw [conjSub_mul, hc₁e]
      exact hke
  obtain ⟨c₃, hc₃C, hc₃L, hc₃L₂, hc₃θ, hc₃e⟩ : ∃ c : M₇, conjSub c C = stdRankOne D₇ starC ∧
      conjSub c L₁ = stdRankOne D₇ star1 ∧ conjSub c L₂ = stdRankOne D₇ star2 ∧
      conjSub c B = stdRankOne D₇ thetaE7 ∧ conjSub c A = stdRankOne D₇ e0V := by
    have hX : conjSub c₂ L₂ ∈ fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hL₂ c₂
    have hθG : GRel thetaE7 false (conjSub c₂ L₂) := by
      have := h2B.symm.conjSub c₂
      rwa [hc₂θ] at this
    have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c₂ L₂) := by
      have := h2A.symm.conjSub c₂
      rwa [hc₂e] at this
    have hCG : GRel starC true (conjSub c₂ L₂) := by
      obtain ⟨W, hW⟩ := hl2
      refine ⟨?_, ?_⟩
      · have := (transport_rel (c := c₂) (A := C) (B := L₂) rfl rfl).1
          (ne_of_linearBlockStandardPair hW)
        rwa [hc₂C] at this
      · have := (transport_rel (c := c₂) (A := C) (B := L₂) rfl rfl).2.1
          (not_commutes_of_linearBlockStandardPair hW)
        rwa [hc₂C] at this
    have hCX : InvComm (stdRankOne D₇ starC) (conjSub c₂ L₂) := by
      have := (invComm_of_linearPair hp2 hl2).conjSub c₂
      rwa [hc₂C] at this
    have h1G : GRel star1 false (conjSub c₂ L₂) := by
      have := h12.conjSub c₂
      rwa [hc₂L] at this
    obtain ⟨k, hkX, hkθ, hke, hkZ⟩ := round_pin hp2 hq hX false hθG (invComm_of_commutes hθG)
      hcomm (J := JofL [0, 1, 2, 3, 4]) (JofL_le_Jsign (by simp) (by simp)) starLam2_J starLam2_B
      starLam2_ker [(starC, true), (star1, false)] (by
        intro zb hzb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
        rcases hzb with rfl | rfl
        · exact isRoot_starC
        · exact isRoot_star1) (by
        intro zb hzb j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
        rcases hzb with rfl | rfl
        · exact starC_even_J2 j hj
        · exact star1_even_J2 j hj) (by
        intro zb hzb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
        rcases hzb with rfl | rfl
        · exact hCX
        · exact invComm_of_commutes h1G) (by
        intro zb hzb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
        rcases hzb with rfl | rfl
        · exact hCG
        · exact h1G)
      (fun y hyG hyd hye hyz => levi_cut hp2 starLam1_J starLam1_B isRoot_star1 star_cut2 hyG
        (levi_cut hp2 lamSign_J lamSign_B isRoot_starC star_cut1 hyG
          (levi_prefix hp2 hq hyG hyd hye) (hyz (starC, true) (by simp)))
        (hyz (star1, false) (by simp))) star2 starPin2
      (fun γ hγ hrθ hre hrZ => by
        have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
        have h2 : iform starC γ = 1 ∨ iform starC γ = -1 := hrZ (starC, true) (by simp)
        have h3 : iform star1 γ = 0 := hrZ (star1, false) (by simp)
        obtain ⟨ω, hω, hωγ⟩ := star_pin2 γ (mem_rootFinset.2 hγ) h1 hre h2 h3
        obtain ⟨hf1, hf2, hf3, hf4⟩ := starPin2_fix ω hω
        refine ⟨ω, hω, hωγ, fix_theta_conv hf1, hf2, ?_⟩
        intro zb hzb
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
        rcases hzb with rfl | rfl
        · exact hf3
        · exact hf4)
    have hkC := hkZ (starC, true) (by simp)
    have hkL := hkZ (star1, false) (by simp)
    refine ⟨k * c₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [conjSub_mul, hc₂C]
      exact hkC
    · rw [conjSub_mul, hc₂L]
      exact hkL
    · rw [conjSub_mul]
      exact hkX
    · rw [conjSub_mul, hc₂θ]
      exact hkθ
    · rw [conjSub_mul, hc₂e]
      exact hke
  have hX : conjSub c₃ L₃ ∈ fundamentalSubgroups .E7 D₇ := conjSub_mem_fundamentalSubgroups hL₃ c₃
  have hθG : GRel thetaE7 false (conjSub c₃ L₃) := by
    have := h3B.symm.conjSub c₃
    rwa [hc₃θ] at this
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c₃ L₃) := by
    have := h3A.symm.conjSub c₃
    rwa [hc₃e] at this
  have hCG : GRel starC true (conjSub c₃ L₃) := by
    obtain ⟨W, hW⟩ := hl3
    refine ⟨?_, ?_⟩
    · have := (transport_rel (c := c₃) (A := C) (B := L₃) rfl rfl).1
        (ne_of_linearBlockStandardPair hW)
      rwa [hc₃C] at this
    · have := (transport_rel (c := c₃) (A := C) (B := L₃) rfl rfl).2.1
        (not_commutes_of_linearBlockStandardPair hW)
      rwa [hc₃C] at this
  have hCX : InvComm (stdRankOne D₇ starC) (conjSub c₃ L₃) := by
    have := (invComm_of_linearPair hp2 hl3).conjSub c₃
    rwa [hc₃C] at this
  have h1G : GRel star1 false (conjSub c₃ L₃) := by
    have := h13.conjSub c₃
    rwa [hc₃L] at this
  have h2G : GRel star2 false (conjSub c₃ L₃) := by
    have := h23.conjSub c₃
    rwa [hc₃L₂] at this
  obtain ⟨x, -, -, -, γ, hγ, -, hrθ, hre, hrZ⟩ := round_root hp2 hq hX false hθG
    (invComm_of_commutes hθG) hcomm (J := JofL [0, 1, 2, 3, 4, 5])
    (JofL_le_Jsign (by simp) (by simp)) starLam3_J starLam3_B starLam3_ker
    [(starC, true), (star1, false), (star2, false)] (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact isRoot_starC
      · exact isRoot_star1
      · exact isRoot_star2) (by
      intro zb hzb j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact starC_even_J3 j hj
      · exact star1_even_J3 j hj
      · exact star2_even_J3 j hj) (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact hCX
      · exact invComm_of_commutes h1G
      · exact invComm_of_commutes h2G) (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact hCG
      · exact h1G
      · exact h2G)
    (fun y hyG hyd hye hyz => levi_cut hp2 starLam2_J starLam2_B isRoot_star2 star_cut3 hyG
      (levi_cut hp2 starLam1_J starLam1_B isRoot_star1 star_cut2 hyG
        (levi_cut hp2 lamSign_J lamSign_B isRoot_starC star_cut1 hyG
          (levi_prefix hp2 hq hyG hyd hye) (hyz (starC, true) (by simp)))
        (hyz (star1, false) (by simp))) (hyz (star2, false) (by simp)))
  have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
  exact star_no_root γ (mem_rootFinset.2 hγ) (hrZ (starC, true) (by simp)) h1 hre
    (hrZ (star1, false) (by simp)) (hrZ (star2, false) (by simp))

end Star

section Wrapper

variable {p f : ℕ} [Fact p.Prime]

theorem e7PerpA2StarFree (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : TypeE8.E7PerpA2StarFree p f :=
  e7PerpA2StarFree_sc hp2 hq

end Wrapper

end CFSG.ClassicalInvolution.ModelFacts.E7Model
