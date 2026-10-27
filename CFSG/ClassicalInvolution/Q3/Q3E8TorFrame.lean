module

public import CFSG.ClassicalInvolution.Q3.Q3E8TorData
public import CFSG.ClassicalInvolution.Q3.Q3E7MStar

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)
local notation "e0V" => (Pi.single (e7Idx 0) 1 : V7)



section Chain

theorem gRel_true_conj {c : M₇} {A X : Subgroup M₇} {z : V7} (hA : conjSub c A = stdRankOne D₇ z)
    (hne : A ≠ X) (hnc : ¬ Commutes A X) : GRel z true (conjSub c X) :=
  ⟨(transport_rel hA rfl).1 hne, (transport_rel hA rfl).2.1 hnc⟩

theorem gRel_false_conj {c : M₇} {A X : Subgroup M₇} {z : V7}
    (hA : conjSub c A = stdRankOne D₇ z) (h : Commutes A X) : GRel z false (conjSub c X) :=
  (transport_rel hA rfl).2.2 h

theorem invComm_conj {c : M₇} {A X : Subgroup M₇} {z : V7}
    (hA : conjSub c A = stdRankOne D₇ z) (h : InvComm A X) :
    InvComm (stdRankOne D₇ z) (conjSub c X) := by
  have := h.conjSub c
  rwa [hA] at this

theorem chain_step3 {c : M₇} {T₁ T₂ T₃ : Subgroup M₇}
    (h₃ : T₃ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hT₁ : conjSub c T₁ = stdRankOne D₇ e0V) (hT₂ : conjSub c T₂ = stdRankOne D₇ thetaE7)
    (hne : T₂ ≠ T₃) (hnc : ¬ Commutes T₂ T₃)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₂ T₃) (hc13 : Commutes T₁ T₃) :
    ∃ c' : M₇, conjSub c' T₁ = stdRankOne D₇ e0V ∧ conjSub c' T₂ = stdRankOne D₇ thetaE7 ∧
      conjSub c' T₃ = stdRankOne D₇ chG3 := by
  have hX : conjSub c T₃ ∈ Generic.fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups h₃ c
  have hθG : GRel thetaE7 true (conjSub c T₃) := gRel_true_conj hT₂ hne hnc
  have hθX : InvComm (stdRankOne D₇ thetaE7) (conjSub c T₃) :=
    invComm_conj hT₂ (invComm_of_linearPair3 hlin)
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c T₃) := (transport_rel hT₁ rfl).2.2 hc13
  obtain ⟨k, hkX, hkθ, hke, -⟩ := round_pin3 hX true hθG hθX hcomm (J := Jsign) subset_rfl
    lamSign_J lamSign_B lamSign_ker [] (by simp) (by simp) (by simp) (by simp)
    (fun y hyG hyd hye _ => levi_prefix3 hyG hyd hye) chG3 chPin3
    (fun γ hγ hrθ hre _ => by
      have h1 : iform thetaLit γ = 1 ∨ iform thetaLit γ = -1 := by
        rw [← thetaE7_eq]; exact hrθ
      obtain ⟨ω, hω, hωγ⟩ := ch_pin3 γ (mem_rootFinset.2 hγ) h1 hre
      obtain ⟨hf1, hf2⟩ := chPin3_fix ω hω
      exact ⟨ω, hω, hωγ, fix_theta_conv hf1, hf2, by simp⟩)
  refine ⟨k * c, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hT₁]
    exact hke
  · rw [conjSub_mul, hT₂]
    exact hkθ
  · rw [conjSub_mul]
    exact hkX

theorem chain_step4 {c : M₇} {T₁ T₂ T₃ T₄ : Subgroup M₇}
    (h₄ : T₄ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hT₁ : conjSub c T₁ = stdRankOne D₇ e0V) (hT₂ : conjSub c T₂ = stdRankOne D₇ thetaE7)
    (hT₃ : conjSub c T₃ = stdRankOne D₇ chG3)
    (hc14 : Commutes T₁ T₄) (hc24 : Commutes T₂ T₄) (hne : T₃ ≠ T₄) (hnc : ¬ Commutes T₃ T₄)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₃ T₄) :
    ∃ c' : M₇, conjSub c' T₁ = stdRankOne D₇ e0V ∧ conjSub c' T₂ = stdRankOne D₇ thetaE7 ∧
      conjSub c' T₃ = stdRankOne D₇ chG3 ∧ conjSub c' T₄ = stdRankOne D₇ chG4 := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hX : conjSub c T₄ ∈ Generic.fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups h₄ c
  have hθG : GRel thetaE7 false (conjSub c T₄) := gRel_false_conj hT₂ hc24
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c T₄) := (transport_rel hT₁ rfl).2.2 hc14
  have h3G : GRel chG3 true (conjSub c T₄) := gRel_true_conj hT₃ hne hnc
  have h3X : InvComm (stdRankOne D₇ chG3) (conjSub c T₄) :=
    invComm_conj hT₃ (invComm_of_linearPair3 hlin)
  obtain ⟨k, hkX, hkθ, hke, hkZ⟩ := round_pin3 hX false hθG (invComm_of_commutes hθG) hcomm
    (J := JofL [0, 2, 5]) (JofL_le_Jsign (by simp) (by simp)) chLam1_J chLam1_B chLam1_ker
    [(chG3, true)] (by simp [isRoot_chG3]) (by
      intro zb hzb j hj
      rw [List.mem_singleton.1 hzb]
      exact chG3_even_J1 j hj) (by
      intro zb hzb
      rw [List.mem_singleton.1 hzb]
      exact h3X) (by
      intro zb hzb
      rw [List.mem_singleton.1 hzb]
      exact h3G)
    (fun y hyG hyd hye hyz => levi_cut hp2 lamSign_J lamSign_B isRoot_chG3 ch_cut1 hyG
      (levi_prefix3 hyG hyd hye) (hyz (chG3, true) (by simp))) chG4 chPin4
    (fun γ hγ hrθ hre hrZ => by
      have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
      have h2 : iform chG3 γ = 1 ∨ iform chG3 γ = -1 := hrZ (chG3, true) (by simp)
      obtain ⟨ω, hω, hωγ⟩ := ch_pin4 γ (mem_rootFinset.2 hγ) h1 hre h2
      obtain ⟨hf1, hf2, hf3⟩ := chPin4_fix ω hω
      refine ⟨ω, hω, hωγ, fix_theta_conv hf1, hf2, ?_⟩
      intro zb hzb
      rw [List.mem_singleton.1 hzb]
      exact hf3)
  have hkC := hkZ (chG3, true) (by simp)
  refine ⟨k * c, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, hT₁]
    exact hke
  · rw [conjSub_mul, hT₂]
    exact hkθ
  · rw [conjSub_mul, hT₃]
    exact hkC
  · rw [conjSub_mul]
    exact hkX

theorem chain_step5 {c : M₇} {T₁ T₂ T₃ T₄ T₅ : Subgroup M₇}
    (h₅ : T₅ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hT₁ : conjSub c T₁ = stdRankOne D₇ e0V) (hT₂ : conjSub c T₂ = stdRankOne D₇ thetaE7)
    (hT₃ : conjSub c T₃ = stdRankOne D₇ chG3) (hT₄ : conjSub c T₄ = stdRankOne D₇ chG4)
    (hc15 : Commutes T₁ T₅) (hc25 : Commutes T₂ T₅) (hc35 : Commutes T₃ T₅)
    (hne : T₄ ≠ T₅) (hnc : ¬ Commutes T₄ T₅)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₄ T₅) :
    ∃ (c' : M₇) (g₅ : V7), (g₅ = chG5a ∨ g₅ = chG5b) ∧
      conjSub c' T₁ = stdRankOne D₇ e0V ∧ conjSub c' T₂ = stdRankOne D₇ thetaE7 ∧
      conjSub c' T₃ = stdRankOne D₇ chG3 ∧ conjSub c' T₄ = stdRankOne D₇ chG4 ∧
      conjSub c' T₅ = stdRankOne D₇ g₅ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hX : conjSub c T₅ ∈ Generic.fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups h₅ c
  have hθG : GRel thetaE7 false (conjSub c T₅) := gRel_false_conj hT₂ hc25
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c T₅) := (transport_rel hT₁ rfl).2.2 hc15
  have h3G : GRel chG3 false (conjSub c T₅) := gRel_false_conj hT₃ hc35
  have h4G : GRel chG4 true (conjSub c T₅) := gRel_true_conj hT₄ hne hnc
  have h3X : InvComm (stdRankOne D₇ chG3) (conjSub c T₅) := invComm_of_commutes h3G
  have h4X : InvComm (stdRankOne D₇ chG4) (conjSub c T₅) :=
    invComm_conj hT₄ (invComm_of_linearPair3 hlin)
  obtain ⟨k, hkθ, hke, hkZ, γ, hγ, hkX, hrθ, hre, hrZ⟩ := round_root3 hX false hθG
    (invComm_of_commutes hθG) hcomm (J := JofL [0, 2, 4, 5, 6])
    (JofL_le_Jsign (by simp) (by simp)) chLam2_J chLam2_B chLam2_ker
    [(chG3, false), (chG4, true)] (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl
      · exact isRoot_chG3
      · exact isRoot_chG4) (by
      intro zb hzb j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl
      · exact chG3_even_J2 j hj
      · exact chG4_even_J2 j hj) (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl
      · exact h3X
      · exact h4X) (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl
      · exact h3G
      · exact h4G)
    (fun y hyG hyd hye hyz => levi_cut hp2 chLam1_J chLam1_B isRoot_chG4 ch_cut2 hyG
      (levi_cut hp2 lamSign_J lamSign_B isRoot_chG3 ch_cut1 hyG (levi_prefix3 hyG hyd hye)
        (hyz (chG3, false) (by simp))) (hyz (chG4, true) (by simp)))
  have hk3 := hkZ (chG3, false) (by simp)
  have hk4 := hkZ (chG4, true) (by simp)
  have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
  have h2 : iform chG3 γ = 0 := hrZ (chG3, false) (by simp)
  have h3 : iform chG4 γ = 1 ∨ iform chG4 γ = -1 := hrZ (chG4, true) (by simp)
  obtain ⟨ω, hω, hωγ⟩ := ch_pin5 γ (mem_rootFinset.2 hγ) h1 hre h2 h3
  obtain ⟨hf1, hf2, hf3, hf4⟩ := chPin5_fix ω hω
  have hZ : ∀ z ∈ [thetaE7, e0V, chG3, chG4], IsRoot .E7 z ∧
      (wordAct ω z = z ∨ wordAct ω z = -z) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨isRoot_thetaE7, fix_theta_conv hf1⟩
    · exact ⟨isRoot_single .E7 (e7Idx 0), hf2⟩
    · exact ⟨isRoot_chG3, hf3⟩
    · exact ⟨isRoot_chG4, hf4⟩
  have hfin : ∀ g : V7, (wordAct ω γ = g ∨ wordAct ω γ = -g) →
      ∃ c' : M₇, conjSub c' T₁ = stdRankOne D₇ e0V ∧ conjSub c' T₂ = stdRankOne D₇ thetaE7 ∧
        conjSub c' T₃ = stdRankOne D₇ chG3 ∧ conjSub c' T₄ = stdRankOne D₇ chG4 ∧
        conjSub c' T₅ = stdRankOne D₇ g := by
    intro g hg
    obtain ⟨k', hk'γ, hk'Z⟩ := exists_conj_pin' (p := 3) (f := 1) hγ hg
      [thetaE7, e0V, chG3, chG4] hZ
    have hk'θ := hk'Z thetaE7 (by simp)
    have hk'e := hk'Z e0V (by simp)
    have hk'3 := hk'Z chG3 (by simp)
    have hk'4 := hk'Z chG4 (by simp)
    refine ⟨k' * (k * c), ?_, ?_, ?_, ?_, ?_⟩
    · rw [conjSub_mul, conjSub_mul, hT₁, hke]
      exact hk'e
    · rw [conjSub_mul, conjSub_mul, hT₂, hkθ]
      exact hk'θ
    · rw [conjSub_mul, conjSub_mul, hT₃, hk3]
      exact hk'3
    · rw [conjSub_mul, conjSub_mul, hT₄, hk4]
      exact hk'4
    · rw [conjSub_mul, conjSub_mul, hkX]
      exact hk'γ
  rcases hωγ with (h | h) | (h | h)
  · obtain ⟨c', hc'⟩ := hfin chG5a (Or.inl h)
    exact ⟨c', chG5a, Or.inl rfl, hc'⟩
  · obtain ⟨c', hc'⟩ := hfin chG5a (Or.inr h)
    exact ⟨c', chG5a, Or.inl rfl, hc'⟩
  · obtain ⟨c', hc'⟩ := hfin chG5b (Or.inl h)
    exact ⟨c', chG5b, Or.inr rfl, hc'⟩
  · obtain ⟨c', hc'⟩ := hfin chG5b (Or.inr h)
    exact ⟨c', chG5b, Or.inr rfl, hc'⟩

theorem mem_span_six (c : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ) (a b d e f g : V7) :
    c.1 • a + c.2.1 • b + c.2.2.1 • d + c.2.2.2.1 • e + c.2.2.2.2.1 • f + c.2.2.2.2.2 • g ∈
      Submodule.span ℤ ({a, b, d, e, f, g} : Set V7) := by
  have hs : ∀ v ∈ ({a, b, d, e, f, g} : Set V7),
      v ∈ Submodule.span ℤ ({a, b, d, e, f, g} : Set V7) := fun v hv => Submodule.subset_span hv
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (hs a (by simp)))
      (Submodule.smul_mem _ _ (hs b (by simp)))) (Submodule.smul_mem _ _ (hs d (by simp))))
    (Submodule.smul_mem _ _ (hs e (by simp)))) (Submodule.smul_mem _ _ (hs f (by simp))))
    (Submodule.smul_mem _ _ (hs g (by simp)))

theorem chain_last3 {c : M₇} {T₁ T₂ T₃ T₄ T₅ RM : Subgroup M₇} {g₅ : V7}
    (hRM : RM ∈ Generic.fundamentalSubgroups .E7 D₇) (hg₅ : IsRoot .E7 g₅)
    (hT₁ : conjSub c T₁ = stdRankOne D₇ e0V) (hT₂ : conjSub c T₂ = stdRankOne D₇ thetaE7)
    (hT₃ : conjSub c T₃ = stdRankOne D₇ chG3) (hT₄ : conjSub c T₄ = stdRankOne D₇ chG4)
    (hT₅ : conjSub c T₅ = stdRankOne D₇ g₅)
    (hM1 : Commutes T₁ RM) (hM2 : Commutes T₂ RM) (hM3 : Commutes T₃ RM) (hM4 : Commutes T₄ RM)
    (hM5 : Commutes T₅ RM) {L : List ℕ} (h0 : 0 ∈ L) (h2 : 2 ∈ L) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ JofL L, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 (JofL L))
    (hcut : ∀ σ ∈ rootFinset .E7, iform chLam2 σ = 0 → Even (iform g₅ σ) →
      σ ∈ parabolicRoots .E7 (JofL L))
    (he3 : ∀ j ∈ JofL L, Even (iform chG3 (Pi.single j 1)))
    (he4 : ∀ j ∈ JofL L, Even (iform chG4 (Pi.single j 1)))
    (he5 : ∀ j ∈ JofL L, Even (iform g₅ (Pi.single j 1)))
    (hreg : ∀ δ ∈ rootFinset .E7, iform e0V δ = 0 → iform thetaLit δ = 0 → iform chG3 δ = 0 →
      iform chG4 δ = 0 → iform g₅ δ = 0 → ∃ c : ℤ × ℤ × ℤ × ℤ × ℤ × ℤ, ∀ σ ∈ rootFinset .E7,
        iform (c.1 • e0V + c.2.1 • thetaLit + c.2.2.1 • chG3 + c.2.2.2.1 • chG4 +
          c.2.2.2.2.1 • g₅ + c.2.2.2.2.2 • δ) σ ≠ 0) :
    ∃ (x : M₇) (Γ : Set V7) (l' : V7), (∀ γ ∈ Γ, IsRoot .E7 γ) ∧ l' ∈ Submodule.span ℤ Γ ∧
      (∀ σ ∈ rootFinset .E7, iform l' σ ≠ 0) ∧
      ∀ γ ∈ Γ, conjSub x T₁ = stdRankOne D₇ γ ∨ conjSub x T₂ = stdRankOne D₇ γ ∨
        conjSub x T₃ = stdRankOne D₇ γ ∨ conjSub x T₄ = stdRankOne D₇ γ ∨
        conjSub x T₅ = stdRankOne D₇ γ ∨ conjSub x RM = stdRankOne D₇ γ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hX : conjSub c RM ∈ Generic.fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups hRM c
  have hθG : GRel thetaE7 false (conjSub c RM) := gRel_false_conj hT₂ hM2
  have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub c RM) := (transport_rel hT₁ rfl).2.2 hM1
  have h3G : GRel chG3 false (conjSub c RM) := gRel_false_conj hT₃ hM3
  have h4G : GRel chG4 false (conjSub c RM) := gRel_false_conj hT₄ hM4
  have h5G : GRel g₅ false (conjSub c RM) := gRel_false_conj hT₅ hM5
  obtain ⟨k, hkθ, hke, hkZ, δ, hδ, hkX, hrθ, hre, hrZ⟩ := round_root3 hX false hθG
    (invComm_of_commutes hθG) hcomm (J := JofL L) (JofL_le_Jsign h0 h2) hlJ hB hker
    [(chG3, false), (chG4, false), (g₅, false)] (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact isRoot_chG3
      · exact isRoot_chG4
      · exact hg₅) (by
      intro zb hzb j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact he3 j hj
      · exact he4 j hj
      · exact he5 j hj) (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact invComm_of_commutes h3G
      · exact invComm_of_commutes h4G
      · exact invComm_of_commutes h5G) (by
      intro zb hzb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hzb
      rcases hzb with rfl | rfl | rfl
      · exact h3G
      · exact h4G
      · exact h5G)
    (fun y hyG hyd hye hyz => levi_cut hp2 chLam2_J chLam2_B hg₅ hcut hyG
      (levi_cut hp2 chLam1_J chLam1_B isRoot_chG4 ch_cut2 hyG
        (levi_cut hp2 lamSign_J lamSign_B isRoot_chG3 ch_cut1 hyG (levi_prefix3 hyG hyd hye)
          (hyz (chG3, false) (by simp))) (hyz (chG4, false) (by simp)))
      (hyz (g₅, false) (by simp)))
  have hk3 := hkZ (chG3, false) (by simp)
  have hk4 := hkZ (chG4, false) (by simp)
  have hk5 := hkZ (g₅, false) (by simp)
  have h1 : iform thetaLit δ = 0 := by rw [← thetaE7_eq]; exact hrθ
  have h3 : iform chG3 δ = 0 := hrZ (chG3, false) (by simp)
  have h4 : iform chG4 δ = 0 := hrZ (chG4, false) (by simp)
  have h5 : iform g₅ δ = 0 := hrZ (g₅, false) (by simp)
  obtain ⟨cc, hcc⟩ := hreg δ (mem_rootFinset.2 hδ) hre h1 h3 h4 h5
  rw [← thetaE7_eq] at hcc
  refine ⟨k * c, {e0V, thetaE7, chG3, chG4, g₅, δ},
    cc.1 • e0V + cc.2.1 • thetaE7 + cc.2.2.1 • chG3 + cc.2.2.2.1 • chG4 + cc.2.2.2.2.1 • g₅ +
      cc.2.2.2.2.2 • δ, ?_, mem_span_six cc _ _ _ _ _ _, hcc, ?_⟩
  · intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact isRoot_single .E7 (e7Idx 0)
    · exact isRoot_thetaE7
    · exact isRoot_chG3
    · exact isRoot_chG4
    · exact hg₅
    · exact hδ
  · intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · refine Or.inl ?_
      rw [conjSub_mul, hT₁]
      exact hke
    · refine Or.inr (Or.inl ?_)
      rw [conjSub_mul, hT₂]
      exact hkθ
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [conjSub_mul, hT₃]
      exact hk3
    · refine Or.inr (Or.inr (Or.inr (Or.inl ?_)))
      rw [conjSub_mul, hT₄]
      exact hk4
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
      rw [conjSub_mul, hT₅]
      exact hk5
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [conjSub_mul]
      exact hkX

theorem chain_frame_E7_3 {T₁ T₂ T₃ T₄ T₅ RM : Subgroup M₇}
    (h₁ : T₁ ∈ Generic.fundamentalSubgroups .E7 D₇) (h₂ : T₂ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (h₃ : T₃ ∈ Generic.fundamentalSubgroups .E7 D₇) (h₄ : T₄ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (h₅ : T₅ ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hRM : RM ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hadj12 : Gaps.ModelAdj (Subgroup.center M₇) T₁ T₂)
    (hlin12 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₁ T₂)
    (hadj23 : Gaps.ModelAdj (Subgroup.center M₇) T₂ T₃)
    (hlin23 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₂ T₃)
    (hadj34 : Gaps.ModelAdj (Subgroup.center M₇) T₃ T₄)
    (hlin34 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₃ T₄)
    (hadj45 : Gaps.ModelAdj (Subgroup.center M₇) T₄ T₅)
    (hlin45 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T₄ T₅)
    (hc13 : Commutes T₁ T₃) (hc14 : Commutes T₁ T₄) (hc24 : Commutes T₂ T₄)
    (hc15 : Commutes T₁ T₅) (hc25 : Commutes T₂ T₅) (hc35 : Commutes T₃ T₅)
    (hM1 : Commutes T₁ RM) (hM2 : Commutes T₂ RM) (hM3 : Commutes T₃ RM)
    (hM4 : Commutes T₄ RM) (hM5 : Commutes T₅ RM) :
    ∃ (x : M₇) (Γ : Set V7) (l : V7), (∀ γ ∈ Γ, IsRoot .E7 γ) ∧ l ∈ Submodule.span ℤ Γ ∧
      (∀ σ ∈ rootFinset .E7, iform l σ ≠ 0) ∧
      ∀ γ ∈ Γ, conjSub x T₁ = stdRankOne D₇ γ ∨ conjSub x T₂ = stdRankOne D₇ γ ∨
        conjSub x T₃ = stdRankOne D₇ γ ∨ conjSub x T₄ = stdRankOne D₇ γ ∨
        conjSub x T₅ = stdRankOne D₇ γ ∨ conjSub x RM = stdRankOne D₇ γ := by
  obtain ⟨x₀, hxA, hxB⟩ := pair_normal3 h₁ h₂ hadj12 hlin12
  obtain ⟨c₃, hc₃1, hc₃2, hc₃3⟩ := chain_step3 h₃ hxA hxB hadj23.1 hadj23.2.1 hlin23 hc13
  obtain ⟨c₄, hc₄1, hc₄2, hc₄3, hc₄4⟩ := chain_step4 h₄ hc₃1 hc₃2 hc₃3 hc14 hc24 hadj34.1
    hadj34.2.1 hlin34
  obtain ⟨c₅, g₅, hg₅, hc₅1, hc₅2, hc₅3, hc₅4, hc₅5⟩ := chain_step5 h₅ hc₄1 hc₄2 hc₄3 hc₄4 hc15
    hc25 hc35 hadj45.1 hadj45.2.1 hlin45
  rcases hg₅ with rfl | rfl
  · exact chain_last3 hRM isRoot_chG5a hc₅1 hc₅2 hc₅3 hc₅4 hc₅5 hM1 hM2 hM3 hM4 hM5
      (L := [0, 2, 3, 4, 5, 6]) (by simp) (by simp) chLam3a_J chLam3a_B chLam3a_ker ch_cut3a
      chG3_even_J3a chG4_even_J3a chG5a_even_J3a
      (fun δ hδ h1 h2 h3 h4 h5 => by
        obtain ⟨cc, -, hcc⟩ := ch_regular_a δ hδ h1 h2 h3 h4 h5
        exact ⟨cc, hcc⟩)
  · exact chain_last3 hRM isRoot_chG5b hc₅1 hc₅2 hc₅3 hc₅4 hc₅5 hM1 hM2 hM3 hM4 hM5
      (L := [0, 2, 4, 5, 6]) (by simp) (by simp) chLam3b_J chLam3b_B chLam3b_ker ch_cut3b
      chG3_even_J3b chG4_even_J3b chG5b_even_J3b
      (fun δ hδ h1 h2 h3 h4 h5 => by
        obtain ⟨cc, -, hcc⟩ := ch_regular_b δ hδ h1 h2 h3 h4 h5
        exact ⟨cc, hcc⟩)

end Chain

end CFSG.ClassicalInvolution.Q3.Q3W
