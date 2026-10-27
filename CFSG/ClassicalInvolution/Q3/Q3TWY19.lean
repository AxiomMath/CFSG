module

public import CFSG.ClassicalInvolution.Q3.Q3TWY18
public import CFSG.ClassicalInvolution.Q3.Q3TWY11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TY CFSG.ClassicalInvolution.Q3.Q3TWC CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Timmesfeld
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

local macro "b4_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.DAdj, edgeD]; done)
    | (simp [DNodes3.DAdj, edgeD]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Leaf

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem exists_layer_leaf3 (c : TCtx3 .POmegaOdd 4 Ω K z) {M : Subgroup G}
    (nd : DNodes3 4 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) :
    ∃ b : Fin 4, 2 ≤ b.val ∧ nd.J b ∈ centralizingMembers Ω {z} ∧ nd.J b ≠ K ∧
      ¬ locImg Ω z (nd.J b) ≤ c.d.Q₁ := by
  have hKJ : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Fin.ne_of_val_ne (by b4_idx)) (by b4_idx)
  have hJz : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hJK : ∀ a : ℕ, ∀ h : a < 4, 2 ≤ a → nd.J ⟨a, h⟩ ≠ K := fun a h ha => by
    rw [← h0]
    exact (nd.ne_J (Fin.ne_of_val_ne (by b4_idx))).symm
  by_cases hQ2 : locImg Ω z (nd.J ⟨2, by omega⟩) ≤ c.d.Q₁
  · refine ⟨⟨3, by omega⟩, by norm_num, hJz 3 (by omega) (by omega), hJK 3 (by omega) (by omega),
      fun hQ3 => ?_⟩
    have := c.eq_of_locImg_le_Q₁ (hJz 2 (by omega) (by omega)) (hJz 3 (by omega) (by omega))
      hQ2 hQ3
    exact nd.ne_J (Fin.ne_of_val_ne (by b4_idx)) this
  · exact ⟨⟨2, by omega⟩, by norm_num, hJz 2 (by omega) (by omega), hJK 2 (by omega) (by omega),
      hQ2⟩

end Leaf

section Main

theorem twinYPatternAtL3_b4 (h3 : OddThreeFreeInput) :
    TwinYPatternAtL3 .POmegaOdd 4 (fun Ω K β t => PartnerPatternBPair3 4 Ω K β t) := by
  intro G _ _ _ hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'
  classical
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hm4 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaOdd 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by norm_num⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_odd hm4 hadm) h3 hR hshape
  have hex : ExactMembers3 (conjClass3 K) := c.hex
  have cq := centralQuot3_odd (m := 4) hm4
  have hT := hcfg.twin
  have hTz : T ∈ centralizingMembers (conjClass3 K) {z} := hT.mem
  have hTQ := twin_locImg_le3 c hT
  have hJz := hcfg.mem_J
  have hJ'z := hcfg.mem_J'
  have hJΩ : J ∈ conjClass3 K := hJz.1
  have hJQ : ¬ locImg (conjClass3 K) z J ≤ c.d.Q₁ := fun hle =>
    hcfg.J_ne_T (c.eq_of_locImg_le_Q₁ hJz hTz hle hTQ)
  have hJ'Q : ¬ locImg (conjClass3 K) z J' ≤ c.d.Q₁ := fun hle =>
    hcfg.J'_ne_T (c.eq_of_locImg_le_Q₁ hJ'z hTz hle hTQ)
  obtain ⟨RzM, hRzM, hMR⟩ := c.exists_fund_of_ne hJz hcfg.J_ne_K hJQ
  obtain ⟨RJ', hRJ', hJ'R⟩ := c.exists_fund_of_ne hJ'z hcfg.J'_ne_K hJ'Q
  have ht := hcfg.clsβ
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have htz : s * z * s⁻¹ = z := fix_of_stdpair3 hR.cls ht hcfg.linear
  have h2t : s * s = 1 := ht.isCentralInvolution.sq
  have hKt : conjSub s K = K := conjSub_eq_of_standardPair h2 hW₀ ht.mem ht.orderOf_eq_two
  have hKJ : Commutes K J := hT.comm_K J hJz hcfg.J_ne_K
  have hKJ' : Commutes K J' := hT.comm_K J' hJ'z hcfg.J'_ne_K
  have hKu : K ∈ centralizingMembers (conjClass3 K) {e'.u} :=
    e'.mem_centralizingMembers_u hKΩ hKJ hKJ'
  have hβu : β ∈ centralizingMembers (conjClass3 K) {e'.u} := hcfg.memβ
  have hβΩ : β ∈ conjClass3 K := hβu.1
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_odd3_ge4 (le_refl 4) c hsingle hβΩ ht hcfg.linear
    hJΩ hKJ hcfg.comm_J
  have hnodeW : ∀ a : Fin 4, nd.J a ∈ centralizingMembers (conjClass3 K) {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hcfg.clsJ.mem (commutes_symm (nd.commK a))
  have hneJ' : ∀ a : Fin 4, nd.J a ≠ J' := by
    intro a h
    obtain ⟨b, hab⟩ : ∃ b : Fin 4, DNodes3.DAdj a b := by
      by_cases h1 : a.val = 1
      · exact ⟨⟨0, by norm_num⟩, by simp [DNodes3.DAdj, edgeD]; omega⟩
      · exact ⟨⟨1, by norm_num⟩, by simp [DNodes3.DAdj, edgeD]; omega⟩
    have hbJ' : nd.J b ≠ J' := fun hb => nd.ne_J hab.ne (h.trans hb.symm)
    have := hcfg.twinJ.comm_T (nd.J b) (hnodeW b) hbJ'
    rw [← h] at this
    exact nd.not_commutes_of_adj hab this
  obtain ⟨N₁, hN₁, N₂, hN₂, hKN₁, hβN₁, hKN₂, hβN₂, hnc, hne₁₂⟩ := exists_noncommuting_members3
    hΩ hex hP1u' hO3u' hty' hKu hβu hR.cls ht hcfg.linear
  have hN₁z : N₁ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hN₁.1 hR.cls.mem (commutes_symm hKN₁)
  have hN₂z : N₂ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hN₂.1 hR.cls.mem (commutes_symm hKN₂)
  obtain ⟨hN₁K, hN₁Q⟩ := c.ne_and_not_le_Q₁3 hN₁z hN₂z hne₁₂ hnc
  obtain ⟨hN₂K, hN₂Q⟩ := c.ne_and_not_le_Q₁3 hN₂z hN₁z (fun h => hne₁₂ h.symm)
    (fun h => hnc (commutes_symm h))
  obtain ⟨RN₁, hRN₁, hN₁R⟩ := c.exists_fund_of_ne hN₁z hN₁K hN₁Q
  obtain ⟨RN₂, hRN₂, hN₂R⟩ := c.exists_fund_of_ne hN₂z hN₂K hN₂Q
  obtain ⟨b, hb2, hJbz, hJbK, hJbQ⟩ := exists_layer_leaf3 c nd h0
  obtain ⟨RJ, hRJ, hJR⟩ := c.exists_fund_of_ne hJbz hJbK hJbQ
  obtain ⟨FM, g', J₁, hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hJ₁O, hJ₁span, hJ₁sq, hJ₁comm,
    hg'comm⟩ := twin_datum_odd3 hm4 c hJz hJ'z hcfg.clsJ hcfg.clsJ' e' hcfg.twinJ.ne.symm hRzM
    hMR hRJ' hJ'R
  have htwin : ∀ i j, IsFundamental (quadOdd 4 𝔽₃) (RzM.map (spinAction (quadOdd 4 𝔽₃))) i →
      IsFundamental (quadOdd 4 𝔽₃) (RJ'.map (spinAction (quadOdd 4 𝔽₃))) j → i = j := by
    intro i j hi hj
    rw [hFM] at hi
    rw [hFM'] at hj
    rw [IsFundamental.involution_unique hodd hi (IsFundamental.of_frame FM),
      IsFundamental.involution_unique hodd hj (IsFundamental.of_frame_swap FM)]
  have hne : RJ' ≠ RzM := fun h =>
    hcfg.twinJ.ne (c.eq_of_locImg_eq hJ'z hJz (by rw [hJ'R, hMR, h]))
  let θ : spinGroup (quadOdd 4 𝔽₃) →* locQuot (conjClass3 K) z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range3 c htz h2t hKt (range_le_iSup_fund_odd (by norm_num) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd 4 𝔽₃))},
      L ∈ centralizingMembers (conjClass3 K) {z} → locImg (conjClass3 K) z L = R.map θ →
      Commutes β L → ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hL).mp
      (fun n hn => Subgroup.mem_centralizer_singleton_iff.mpr (hβL s ht.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_b4_3 θ c.d.ker_le c.ker_cop σ hσ2 hσr
    hRzM hRJ' hne htwin (hfixσ hJz hMR hcfg.comm_J) (hfixσ hJ'z hJ'R hcfg.comm_J')
  have hcommg : ∀ {R : Subgroup (spinGroup (quadOdd 4 𝔽₃))},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 4 𝔽₃) → (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadOdd 4 𝔽₃)), g₀ * l = l * g₀ :=
    fun hR' hfix => commute_of_fixed3 θ c.d.ker_le c.ker_cop σ α hαθ (cq.pow3 _ hR') hfix hconj
  have hadjb : DNodes3.DAdj b (⟨1, by omega⟩ : Fin 4) := by
    have := b.isLt
    simp [DNodes3.DAdj, edgeD]
    omega
  obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hadjb
  rw [h1] at hW₁
  have hJt : conjSub s (nd.J b) = nd.J b :=
    conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := 3) h2 hW₁ ht.mem ht.orderOf_eq_two
  obtain ⟨hαJ, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_odd3 c htz hJbz hRJ hJR hJt hx₁J hx₁1 hx₁p hx₁inv hαθ
  have hnormJ : ∀ l ∈ RJ.map (spinAction (quadOdd 4 𝔽₃)),
      g₀ * l * g₀ ∈ RJ.map (spinAction (quadOdd 4 𝔽₃)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨α y, hαJ y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
    have := hconj y (g₀ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, g₀ (spinAction (quadOdd 4 𝔽₃) x₀ v) =
      (spinAction (quadOdd 4 𝔽₃) x₀).symm (g₀ v) := by
    intro v
    have h1' := hconj x₀ v
    rw [hx₀α, map_inv] at h1'
    exact h1'.symm
  have hJM : nd.J b ≠ J := fun h => not_commutes_self3 hcfg.clsJ (by
    have := nd.commK b
    rw [h] at this
    exact this)
  have hRJM : RJ ≠ RzM := fun h => hJM (c.eq_of_locImg_eq hJbz hJz (by rw [hJR, hMR, h]))
  have hRJM' : RJ ≠ RJ' := fun h =>
    hneJ' b (c.eq_of_locImg_eq hJbz hJ'z (by rw [hJR, hJ'R, h]))
  have hcomm : Commutes (RzM.map (spinAction (quadOdd 4 𝔽₃)))
      (RJ.map (spinAction (quadOdd 4 𝔽₃))) :=
    (cq.commutes_iff hRzM).mpr ((c.commutes_iff_fund hJz hJbz hRzM hMR hJR).mp (nd.commK b))
  have hSne : RN₁.map (spinAction (quadOdd 4 𝔽₃)) ≠ RN₂.map (spinAction (quadOdd 4 𝔽₃)) :=
    fun e => hne₁₂ (c.eq_of_locImg_eq hN₁z hN₂z (by rw [hN₁R, hN₂R, cq.map_inj hRN₁ hRN₂ e]))
  have hSnc : ¬ Commutes (RN₁.map (spinAction (quadOdd 4 𝔽₃)))
      (RN₂.map (spinAction (quadOdd 4 𝔽₃))) := fun h =>
    hnc ((c.commutes_iff_fund hN₁z hN₂z hRN₁ hN₁R hN₂R).mpr ((cq.commutes_iff hRN₁).mp h))
  obtain ⟨x', ε, hε, hRJeq, hscal⟩ := class_spin_b4_3 cq hg₀O hg₀2 hg'O hg'2 hRzM hRJ' hRJ hRN₁
    hRN₂ FM hFM hFM' hRJM hRJM' hcomm (hcommg hRzM (hfixσ hJz hMR hcfg.comm_J))
    (hcommg hRN₁ (hfixσ hN₁z hN₁R hβN₁)) (hcommg hRN₂ (hfixσ hN₂z hN₂R hβN₂)) hnormJ hx₀J hx₀1
    hx₀p hx₀inv hg'le hg'dim hg'fix
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₁.2 hn)) hN₁R
      (c.hY.pow3 _ hRN₁))
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn)) hN₂R
      (c.hY.pow3 _ hRN₂)) hSnc hSne
  have hn2 : locImg (conjClass3 K) z (nd.J b) =
      ((rootSL2 (oddFrame 4 𝔽₃).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x').toMonoidHom).map c.d.ψ := by
    rw [hJR, hRJeq]
  have hKJb : Commutes K (nd.J b) := by
    have hb4 := b.isLt
    have := nd.commutes_of_not_adj (a := ⟨0, by omega⟩) (b := b) (Fin.ne_of_val_ne (by b4_idx))
      (by b4_idx)
    rwa [h0] at this
  exact pattern_odd3 hm4 c htz (nd.mem b) hKJb ⟨W₁, linearBlockStandardPair_symm hW₁⟩ hn2 hαθ hg₀O
    hconj
    (by rcases hε with rfl | rfl <;> norm_num) hscal

end Main

end CFSG.ClassicalInvolution.Q3.Q3TWY
