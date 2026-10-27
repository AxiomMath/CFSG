module

public import CFSG.ClassicalInvolution.Q3.Q3TWY10
public import CFSG.ClassicalInvolution.Q3.Q3TWC2
public import CFSG.ClassicalInvolution.Q3.Q3TY12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TWY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible StatedSp
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TY CFSG.ClassicalInvolution.Q3.Q3TWC CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

section Main

theorem twinYPatternAtL3_b3 (h3 : OddThreeFreeInput) :
    TwinYPatternAtL3 .POmegaOdd 3 (fun Ω K β t => PartnerPatternBPair3 3 Ω K β t) := by
  intro G _ _ _ hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'
  classical
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card 𝔽₃) := odd_gf3
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_odd (le_refl 3) hadm) h3 hR hshape
  have hex : ExactMembers3 (conjClass3 K) := c.hex
  have cq := centralQuot3_odd (m := 3) (le_refl 3)
  have hT := hcfg.twin
  have hTz : T ∈ centralizingMembers (conjClass3 K) {z} := hT.mem
  have hTQ := twin_locImg_le3 c hT
  have hJz := hcfg.mem_J
  have hJ'z := hcfg.mem_J'
  have hJQ : ¬ locImg (conjClass3 K) z J ≤ c.d.Q₁ := fun hle =>
    hcfg.J_ne_T (c.eq_of_locImg_le_Q₁ hJz hTz hle hTQ)
  have hJ'Q : ¬ locImg (conjClass3 K) z J' ≤ c.d.Q₁ := fun hle =>
    hcfg.J'_ne_T (c.eq_of_locImg_le_Q₁ hJ'z hTz hle hTQ)
  obtain ⟨RM, hRM, hJR⟩ := c.exists_fund_of_ne hJz hcfg.J_ne_K hJQ
  obtain ⟨RM', hRM', hJ'R⟩ := c.exists_fund_of_ne hJ'z hcfg.J'_ne_K hJ'Q
  have ht := hcfg.clsβ
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have htz : s * z * s⁻¹ = z := fix_of_stdpair3 hR.cls ht hcfg.linear
  have h2t : s * s = 1 := ht.isCentralInvolution.sq
  have hKt : conjSub s K = K := conjSub_eq_of_standardPair h2 hW₀ ht.mem ht.orderOf_eq_two
  obtain ⟨FM, g', J₁, hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hJ₁O, hJ₁span, hJ₁sq, hJ₁comm,
    hg'comm⟩ := twin_datum_b3_3 c hJz hJ'z hcfg.clsJ hcfg.clsJ' e' hcfg.twinJ.ne.symm hRM hJR hRM'
    hJ'R
  have htwin : ∀ i j, IsFundamental (quadOdd 3 𝔽₃) (RM.map (spinAction (quadOdd 3 𝔽₃))) i →
      IsFundamental (quadOdd 3 𝔽₃) (RM'.map (spinAction (quadOdd 3 𝔽₃))) j → i = j := by
    intro i j hi hj
    rw [hFM] at hi
    rw [hFM'] at hj
    rw [IsFundamental.involution_unique hodd hi (IsFundamental.of_frame FM),
      IsFundamental.involution_unique hodd hj (IsFundamental.of_frame_swap FM)]
  have hne : RM' ≠ RM := fun h =>
    hcfg.twinJ.ne (c.eq_of_locImg_eq hJ'z hJz (by rw [hJ'R, hJR, h]))
  let θ : spinGroup (quadOdd 3 𝔽₃) →* locQuot (conjClass3 K) z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    locAut_mem_range3 c htz h2t hKt (range_le_iSup_fund_odd (by norm_num) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadOdd 3 𝔽₃))},
      L ∈ centralizingMembers (conjClass3 K) {z} → locImg (conjClass3 K) z L = R.map θ →
      Commutes β L → ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hL).mp
      (fun n hn => Subgroup.mem_centralizer_singleton_iff.mpr (hβL s ht.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_b3_3 θ c.d.ker_le c.ker_cop σ hσ2
    hσr hRM hRM' hne htwin (hfixσ hJz hJR hcfg.comm_J) (hfixσ hJ'z hJ'R hcfg.comm_J')
  have hcommg : ∀ {R : Subgroup (spinGroup (quadOdd 3 𝔽₃))},
      R ∈ fundamentalSubgroups .POmegaOdd (oddDatum 3 𝔽₃) → (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadOdd 3 𝔽₃)), g₀ * l = l * g₀ :=
    fun hR' hfix => commute_of_fixed3 θ c.d.ker_le c.ker_cop σ α hαθ (cq.pow3 _ hR') hfix hconj
  have hKJ : Commutes K J := hT.comm_K J hJz hcfg.J_ne_K
  have hKJ' : Commutes K J' := hT.comm_K J' hJ'z hcfg.J'_ne_K
  have hKu : K ∈ centralizingMembers (conjClass3 K) {e'.u} :=
    e'.mem_centralizingMembers_u hKΩ hKJ hKJ'
  obtain ⟨N₁, hN₁, N₂, hN₂, hKN₁, hKN₂, hβN₁, hβN₂, hne₁₂⟩ := exists_leaf_b3_3 hΩ hex hP1u' hO3u'
    hty' hKu hcfg.memβ hR.cls ht hcfg.linear
  obtain ⟨N₀, hN₀u, hKN₀, hβN₀, hN₀T⟩ : ∃ N ∈ centralizingMembers (conjClass3 K) {e'.u},
      Commutes K N ∧ (∃ W, LinearBlockStandardPair 𝔽₃ W β N) ∧ N ≠ T := by
    by_cases h : N₁ = T
    · exact ⟨N₂, hN₂, hKN₂, hβN₂, fun h' => hne₁₂ (h.trans h'.symm)⟩
    · exact ⟨N₁, hN₁, hKN₁, hβN₁, h⟩
  have hN₀z : N₀ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hN₀u.1 hR.cls.mem (commutes_symm hKN₀)
  have hN₀K : N₀ ≠ K := fun h => not_commutes_self3 hR.cls (by rw [h] at hKN₀; exact hKN₀)
  have hN₀Q : ¬ locImg (conjClass3 K) z N₀ ≤ c.d.Q₁ := fun hle =>
    hN₀T (c.eq_of_locImg_le_Q₁ hN₀z hTz hle hTQ)
  obtain ⟨RN, hRN, hN₀R⟩ := c.exists_fund_of_ne hN₀z hN₀K hN₀Q
  obtain ⟨W₁, hW₁⟩ := hβN₀
  obtain ⟨W₂, hW₂⟩ : ∃ W, LinearBlockStandardPair 𝔽₃ W N₀ β :=
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩
  have hN₀t : conjSub s N₀ = N₀ :=
    conjSub_eq_of_standardPair h2 hW₂ ht.mem ht.orderOf_eq_two
  obtain ⟨x₁, hx₁N, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := 3) h2 hW₂ ht.mem ht.orderOf_eq_two
  obtain ⟨hαN, x₀, hx₀N, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_b3_3 c htz hN₀z hRN hN₀R hN₀t hx₁N hx₁1 hx₁p hx₁inv hαθ
  have hnormN : ∀ l ∈ RN.map (spinAction (quadOdd 3 𝔽₃)),
      g₀ * l * g₀ ∈ RN.map (spinAction (quadOdd 3 𝔽₃)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨α y, hαN y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
    have := hconj y (g₀ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, g₀ (spinAction (quadOdd 3 𝔽₃) x₀ v) =
      (spinAction (quadOdd 3 𝔽₃) x₀).symm (g₀ v) := by
    intro v
    have h1 := hconj x₀ v
    rw [hx₀α, map_inv] at h1
    exact h1.symm
  obtain ⟨x', ε, hε, hRNeq, hscal⟩ := class_spin_b3_3 cq hg₀O hg₀2 hg'O hg'2 hJ₁O hRN FM hFM
    (hcommg hRM (hfixσ hJz hJR hcfg.comm_J)) hnormN hx₀N hx₀1 hx₀p hx₀inv hg'le hg'dim
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₀u.2 hn)) hN₀R
      (c.hY.pow3 _ hRN)) hJ₁span hJ₁sq hJ₁comm
  have hn2 : locImg (conjClass3 K) z N₀ =
      ((rootSL2 (oddFrame 3 𝔽₃).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x').toMonoidHom).map c.d.ψ := by
    rw [hN₀R, hRNeq]
  exact pattern_b3_3 c htz hN₀u.1 hKN₀ ⟨W₁, hW₁⟩ hn2 hαθ hg₀O hconj
    (by rcases hε with rfl | rfl <;> norm_num) hscal

end Main

end CFSG.ClassicalInvolution.Q3.Q3TWY
