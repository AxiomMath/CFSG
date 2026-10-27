module

public import CFSG.ClassicalInvolution.Q3.Q3E7MStep
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclStar

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


section Star

theorem rRel_of_conj3 {z γ : V7} (hz : IsRoot .E7 z)
    (hγ : IsRoot .E7 γ) {X : Subgroup M₇} {k : M₇} (hkX : conjSub k X = stdRankOne D₇ γ)
    (hkz : conjSub k (stdRankOne D₇ z) = stdRankOne D₇ z) (b : Bool) (h : GRel z b X) :
    RRel z b γ := by
  cases b
  · exact iform_eq_zero_of_commutes3 hz hγ ((transport_rel hkz hkX).2.2 h)
  · obtain ⟨hne, hnc⟩ := h
    exact iform_odd_of_rel3 hz hγ ((transport_rel hkz hkX).1 hne)
      ((transport_rel hkz hkX).2.1 hnc)


theorem round_root3 {X : Subgroup M₇}
    (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇) (bθ : Bool) (hθG : GRel thetaE7 bθ X)
    (hθX : InvComm (stdRankOne D₇ thetaE7) X) (hcomm : Commutes (stdRankOne D₇ e0V) X)
    {J : Set (Fin (Tag.rank .E7))} (hJ : J ⊆ Jsign) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    (Zs : List (V7 × Bool)) (hZr : ∀ zb ∈ Zs, IsRoot .E7 zb.1)
    (hZJ : ∀ zb ∈ Zs, ∀ j ∈ J, Even (iform zb.1 (Pi.single j 1)))
    (hZX : ∀ zb ∈ Zs, InvComm (stdRankOne D₇ zb.1) X) (hZG : ∀ zb ∈ Zs, GRel zb.1 zb.2 X)
    (hLevi : ∀ y : ModGL .E7 (GaloisField 3 1), y ∈ adjointGroup .E7 (GaloisField 3 1) →
      y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y →
      (∀ A : SL2 (GaloisField 3 1),
        y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
          rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y) →
      (∀ zb ∈ Zs, y * rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField 3 1)ˣ)) * y) →
      baseChangeGL (algebraMap (GaloisField 3 1) (AlgebraicClosure (GaloisField 3 1))) y ∈
        parabolicLevi .E7 (AlgebraicClosure (GaloisField 3 1)) J) :
    ∃ x : M₇, conjSub x (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub x (stdRankOne D₇ e0V) = stdRankOne D₇ e0V ∧
      (∀ zb ∈ Zs, conjSub x (stdRankOne D₇ zb.1) = stdRankOne D₇ zb.1) ∧
      ∃ γ : V7, IsRoot .E7 γ ∧ conjSub x X = stdRankOne D₇ γ ∧ RRel thetaE7 bθ γ ∧
        iform e0V γ = 0 ∧ ∀ zb ∈ Zs, RRel zb.1 zb.2 γ := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨x, hxθ, hxe, hxZ, γ, hγ, hxγ⟩ := stage_step3 hX hθX hcomm hJ hlJ hB hker
    (Zs.map Prod.fst) (fun z hz => by
      obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hz
      exact hZr zb hzb)
    (fun z hz j hj => by
      obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hz
      exact hZJ zb hzb j hj)
    (fun z hz => by
      obtain ⟨zb, hzb, rfl⟩ := List.mem_map.1 hz
      exact hZX zb hzb)
    (fun y hyG hyd hye hyz => hLevi y hyG hyd hye fun zb hzb =>
      hyz zb.1 (List.mem_map.2 ⟨zb, hzb, rfl⟩))
  refine ⟨x, hxθ, hxe, fun zb hzb => hxZ zb.1 (List.mem_map.2 ⟨zb, hzb, rfl⟩), γ, hγ, hxγ,
    rRel_of_conj3 isRoot_thetaE7 hγ hxγ hxθ bθ hθG, ?_, fun zb hzb => ?_⟩
  · exact rRel_of_conj3 he0 hγ hxγ hxe false hcomm
  · exact rRel_of_conj3 (hZr zb hzb) hγ hxγ
      (hxZ zb.1 (List.mem_map.2 ⟨zb, hzb, rfl⟩)) zb.2 (hZG zb hzb)

theorem round_pin3 {X : Subgroup M₇}
    (hX : X ∈ Generic.fundamentalSubgroups .E7 D₇) (bθ : Bool) (hθG : GRel thetaE7 bθ X)
    (hθX : InvComm (stdRankOne D₇ thetaE7) X) (hcomm : Commutes (stdRankOne D₇ e0V) X)
    {J : Set (Fin (Tag.rank .E7))} (hJ : J ⊆ Jsign) {l : V7} {B : ℕ}
    (hlJ : ∀ j ∈ J, iform l (Pi.single j 1) = 0) (hB : ∀ σ ∈ rootFinset .E7, |iform l σ| ≤ B)
    (hker : ∀ σ ∈ rootFinset .E7, iform l σ = 0 → σ ∈ parabolicRoots .E7 J)
    (Zs : List (V7 × Bool)) (hZr : ∀ zb ∈ Zs, IsRoot .E7 zb.1)
    (hZJ : ∀ zb ∈ Zs, ∀ j ∈ J, Even (iform zb.1 (Pi.single j 1)))
    (hZX : ∀ zb ∈ Zs, InvComm (stdRankOne D₇ zb.1) X) (hZG : ∀ zb ∈ Zs, GRel zb.1 zb.2 X)
    (hLevi : ∀ y : ModGL .E7 (GaloisField 3 1), y ∈ adjointGroup .E7 (GaloisField 3 1) →
      y * rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag thetaE7 (-1 : (GaloisField 3 1)ˣ)) * y →
      (∀ A : SL2 (GaloisField 3 1),
        y * rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A =
          rootSL2 .E7 (GaloisField 3 1) (Pi.single (e7Idx 0) 1) A * y) →
      (∀ zb ∈ Zs, y * rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField 3 1)ˣ)) =
        rootDiagUnit .E7 (thetaDiag zb.1 (-1 : (GaloisField 3 1)ˣ)) * y) →
      baseChangeGL (algebraMap (GaloisField 3 1) (AlgebraicClosure (GaloisField 3 1))) y ∈
        parabolicLevi .E7 (AlgebraicClosure (GaloisField 3 1)) J)
    (g : V7) (words : List (List ℕ))
    (hpin : ∀ γ : V7, IsRoot .E7 γ → RRel thetaE7 bθ γ → iform e0V γ = 0 →
      (∀ zb ∈ Zs, RRel zb.1 zb.2 γ) → ∃ ω ∈ words, (wordAct ω γ = g ∨ wordAct ω γ = -g) ∧
        (wordAct ω thetaE7 = thetaE7 ∨ wordAct ω thetaE7 = -thetaE7) ∧
        (wordAct ω e0V = e0V ∨ wordAct ω e0V = -e0V) ∧
        ∀ zb ∈ Zs, wordAct ω zb.1 = zb.1 ∨ wordAct ω zb.1 = -zb.1) :
    ∃ k : M₇, conjSub k X = stdRankOne D₇ g ∧
      conjSub k (stdRankOne D₇ thetaE7) = stdRankOne D₇ thetaE7 ∧
      conjSub k (stdRankOne D₇ e0V) = stdRankOne D₇ e0V ∧
      ∀ zb ∈ Zs, conjSub k (stdRankOne D₇ zb.1) = stdRankOne D₇ zb.1 := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨x, hxθ, hxe, hxZ, γ, hγ, hxγ, hrθ, hre, hrZ⟩ := round_root3 hX bθ hθG hθX hcomm
    hJ hlJ hB hker Zs hZr hZJ hZX hZG hLevi
  obtain ⟨ω, -, hωγ, hωθ, hωe, hωZ⟩ := hpin γ hγ hrθ hre hrZ
  obtain ⟨k, hkγ, hkZ⟩ := exists_conj_pin' (p := 3) (f := 1) hγ hωγ
    (thetaE7 :: e0V :: Zs.map Prod.fst) (by
      intro z hz
      simp only [List.mem_cons, List.mem_map] at hz
      rcases hz with rfl | rfl | ⟨zb, hzb, rfl⟩
      · exact ⟨isRoot_thetaE7, hωθ⟩
      · exact ⟨he0, hωe⟩
      · exact ⟨hZr zb hzb, hωZ zb hzb⟩)
  refine ⟨k * x, ?_, ?_, ?_, fun zb hzb => ?_⟩
  · rw [conjSub_mul, hxγ]
    exact hkγ
  · rw [conjSub_mul, hxθ]
    exact hkZ thetaE7 (by simp)
  · rw [conjSub_mul, hxe]
    exact hkZ e0V (by simp)
  · rw [conjSub_mul, hxZ zb hzb]
    exact hkZ zb.1 (by
      simp only [List.mem_cons, List.mem_map]
      exact Or.inr (Or.inr ⟨zb, hzb, rfl⟩))


theorem pair_normal3 {A B : Subgroup M₇}
    (hA : A ∈ Generic.fundamentalSubgroups .E7 D₇) (hB : B ∈ Generic.fundamentalSubgroups .E7 D₇)
    (hadj : Gaps.ModelAdj (Subgroup.center M₇) A B)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W A B) :
    ∃ x : M₇, conjSub x A = stdRankOne D₇ e0V ∧ conjSub x B = stdRankOne D₇ thetaE7 := by
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  have he2 : IsRoot .E7 (Pi.single (e7Idx 2) 1 : V7) := isRoot_single .E7 (e7Idx 2)
  obtain ⟨g, hg1, hg2⟩ := e7PairFrame_sc_3 A hA B hB hadj hlin 0 2 (by decide)
  have hpair : iform (Pi.single (e7Idx 2) 1 : V7) e0V = 1 ∨
      iform (Pi.single (e7Idx 2) 1 : V7) e0V = -1 := by decide +kernel
  obtain ⟨k, hk2, hk0⟩ := exists_conj_theta_e0 (GaloisField 3 1) he2 he0 hpair
  rw [e7Idx_zero] at hk0
  refine ⟨k * g⁻¹, ?_, ?_⟩
  · rw [conjSub_mul, hg1, Generic.conjSub_inv_conjSub]
    exact hk0
  · rw [conjSub_mul, hg2, Generic.conjSub_inv_conjSub]
    exact hk2


theorem invComm_of_linearPair3 {U V : Subgroup M₇}
    (h : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W U V) : InvComm U V := by
  obtain ⟨W, hW⟩ := h
  intro s hs hs2 t ht ht2
  exact Gaps.standardPair_involutions_commute (two_ne_zero_gf3) hW hs ht hs2 ht2


theorem e7PerpA2StarFree_sc_3 :
    ∀ A ∈ Generic.fundamentalSubgroups .E7 D₇, ∀ B ∈ Generic.fundamentalSubgroups .E7 D₇,
      Gaps.ModelAdj (Subgroup.center M₇) A B →
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W A B) →
      ∀ C ∈ Generic.fundamentalSubgroups .E7 D₇, ∀ L₁ ∈ Generic.fundamentalSubgroups .E7 D₇,
        ∀ L₂ ∈ Generic.fundamentalSubgroups .E7 D₇, ∀ L₃ ∈ Generic.fundamentalSubgroups .E7 D₇,
        Commutes C A → Commutes C B → Commutes L₁ A → Commutes L₁ B → Commutes L₂ A →
        Commutes L₂ B → Commutes L₃ A → Commutes L₃ B →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W C L₁) →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W C L₂) →
        (∃ W, LinearBlockStandardPair (GaloisField 3 1) W C L₃) →
        Commutes L₁ L₂ → Commutes L₁ L₃ → Commutes L₂ L₃ → False := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  intro A hA B hB hadj hlin C hC L₁ hL₁ L₂ hL₂ L₃ hL₃ hCA hCB h1A h1B h2A h2B h3A h3B hl1 hl2 hl3
    h12 h13 h23
  have he0 : IsRoot .E7 e0V := isRoot_single .E7 (e7Idx 0)
  obtain ⟨x₀, hxA, hxB⟩ := pair_normal3 hA hB hadj hlin
  have hcommθ : ∀ (X : Subgroup M₇) (c : M₇), Commutes X B →
      Commutes (stdRankOne D₇ thetaE7) (conjSub c X) → True := fun _ _ _ _ => trivial
  clear hcommθ
  obtain ⟨c₁, hc₁C, hc₁θ, hc₁e⟩ : ∃ c : M₇, conjSub c C = stdRankOne D₇ starC ∧
      conjSub c B = stdRankOne D₇ thetaE7 ∧ conjSub c A = stdRankOne D₇ e0V := by
    have hX : conjSub x₀ C ∈ Generic.fundamentalSubgroups .E7 D₇ :=
      conjSub_mem_fundamentalSubgroups hC x₀
    have hθG : GRel thetaE7 false (conjSub x₀ C) := by
      have := hCB.symm.conjSub x₀
      rwa [hxB] at this
    have hcomm : Commutes (stdRankOne D₇ e0V) (conjSub x₀ C) := by
      have := hCA.symm.conjSub x₀
      rwa [hxA] at this
    obtain ⟨k, hkX, hkθ, hke, -⟩ := round_pin3 hX false hθG (invComm_of_commutes hθG) hcomm
      (J := Jsign) subset_rfl lamSign_J lamSign_B lamSign_ker [] (by simp) (by simp) (by simp)
      (by simp) (fun y hyG hyd hye _ => levi_prefix3 hyG hyd hye) starC starPinC
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
    have hX : conjSub c₁ L₁ ∈ Generic.fundamentalSubgroups .E7 D₇ :=
      conjSub_mem_fundamentalSubgroups hL₁ c₁
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
      have := (invComm_of_linearPair3 hl1).conjSub c₁
      rwa [hc₁C] at this
    obtain ⟨k, hkX, hkθ, hke, hkZ⟩ := round_pin3 hX false hθG (invComm_of_commutes hθG)
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
        (levi_prefix3 hyG hyd hye) (hyz (starC, true) (by simp))) star1 starPin1
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
    have hX : conjSub c₂ L₂ ∈ Generic.fundamentalSubgroups .E7 D₇ :=
      conjSub_mem_fundamentalSubgroups hL₂ c₂
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
      have := (invComm_of_linearPair3 hl2).conjSub c₂
      rwa [hc₂C] at this
    have h1G : GRel star1 false (conjSub c₂ L₂) := by
      have := h12.conjSub c₂
      rwa [hc₂L] at this
    obtain ⟨k, hkX, hkθ, hke, hkZ⟩ := round_pin3 hX false hθG (invComm_of_commutes hθG)
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
          (levi_prefix3 hyG hyd hye) (hyz (starC, true) (by simp)))
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
  have hX : conjSub c₃ L₃ ∈ Generic.fundamentalSubgroups .E7 D₇ :=
    conjSub_mem_fundamentalSubgroups hL₃ c₃
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
    have := (invComm_of_linearPair3 hl3).conjSub c₃
    rwa [hc₃C] at this
  have h1G : GRel star1 false (conjSub c₃ L₃) := by
    have := h13.conjSub c₃
    rwa [hc₃L] at this
  have h2G : GRel star2 false (conjSub c₃ L₃) := by
    have := h23.conjSub c₃
    rwa [hc₃L₂] at this
  obtain ⟨x, -, -, -, γ, hγ, -, hrθ, hre, hrZ⟩ := round_root3 hX false hθG
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
          (levi_prefix3 hyG hyd hye) (hyz (starC, true) (by simp)))
        (hyz (star1, false) (by simp))) (hyz (star2, false) (by simp)))
  have h1 : iform thetaLit γ = 0 := by rw [← thetaE7_eq]; exact hrθ
  exact star_no_root γ (mem_rootFinset.2 hγ) (hrZ (starC, true) (by simp)) h1 hre
    (hrZ (star1, false) (by simp)) (hrZ (star2, false) (by simp))


theorem e7PerpA2StarFree3 : TypeE8.E7PerpA2StarFree 3 1 := e7PerpA2StarFree_sc_3

end Star

end CFSG.ClassicalInvolution.Q3.Q3W
