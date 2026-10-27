module

public import CFSG.ClassicalInvolution.Q3.Q3TWY32
public import CFSG.ClassicalInvolution.Q3.Q3TWY19
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

local macro "nd_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.DAdj, edgeD]; done)
    | (simp [DNodes3.DAdj, edgeD]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem exists_adj_node3 {m : ℕ} (hm : 4 ≤ m) (a : Fin m) : ∃ b : Fin m, DNodes3.DAdj a b := by
  by_cases h : a.val + 2 < m
  · exact ⟨⟨a.val + 1, by omega⟩, by simp [DNodes3.DAdj, edgeD]; omega⟩
  · exact ⟨⟨m - 3, by omega⟩, by simp [DNodes3.DAdj, edgeD]; omega⟩


section Main

theorem twinYPatternAtL3_b_ge5 (u : ℕ) (h3 : OddThreeFreeInput) :
    TwinYPatternAtL3 .POmegaOdd (u + 5) (fun Ω K β t => PartnerPatternBPair3 (u + 5) Ω K β t) := by
  intro G _ _ _ hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'
  classical
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_gf3
  have hm3 : 3 ≤ u + 5 := by omega
  have hadm : StatedLieAdmissible .POmegaOdd (u + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by omega, by norm_num⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_odd hm3 hadm) h3 hR hshape
  have hex : ExactMembers3 (conjClass3 K) := c.hex
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
  have ht := hcfg.clsβ
  have htz : s * z * s⁻¹ = z := fix_of_stdpair3 hR.cls ht hcfg.linear
  have hKJ : Commutes K J := hT.comm_K J hJz hcfg.J_ne_K
  have hKJ' : Commutes K J' := hT.comm_K J' hJ'z hcfg.J'_ne_K
  have hβu : β ∈ centralizingMembers (conjClass3 K) {e'.u} := hcfg.memβ
  have hβΩ : β ∈ conjClass3 K := hβu.1
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_odd3_ge4 (by omega : 4 ≤ u + 5) c hsingle hβΩ ht
    hcfg.linear hJΩ hKJ hcfg.comm_J
  have hnodeW : ∀ a : Fin (u + 5), nd.J a ∈ centralizingMembers (conjClass3 K) {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hcfg.clsJ.mem (commutes_symm (nd.commK a))
  have hneJ' : ∀ a : Fin (u + 5), nd.J a ≠ J' := by
    intro a h
    obtain ⟨b, hab⟩ := exists_adj_node3 (by omega : 4 ≤ u + 5) a
    have hbJ' : nd.J b ≠ J' := fun hb => nd.ne_J hab.ne (h.trans hb.symm)
    have := hcfg.twinJ.comm_T (nd.J b) (hnodeW b) hbJ'
    rw [← h] at this
    exact nd.not_commutes_of_adj hab this
  have hnodeu : ∀ a : Fin (u + 5), nd.J a ∈ centralizingMembers (conjClass3 K) {e'.u} := fun a =>
    e'.mem_centralizingMembers_u (nd.mem a) (commutes_symm (nd.commK a))
      (commutes_symm (hcfg.twinJ.comm_T (nd.J a) (hnodeW a) (hneJ' a)))
  obtain ⟨N₁, hN₁, N₂, hN₂, hNc, hN₁4, hN₁5, hN₂4, hN₂5, hN₁₂, hne₁₂⟩ := exists_bridges_group3
    hΩ hex hP1u' hO3u' hty' nd hnodeu
  obtain ⟨Rz, RzM, hch⟩ := exists_layerChain3 c nd h0 hJz hcfg.J_ne_K hJQ
  have hdt := hdt_odd3 c nd h0 hJz hch hN₁.1 (fun a ha => (hNc a ha).1) hN₁4 hN₁5
  obtain ⟨x, tM, α, g₀, hxR, hxM, hαθ, hg₀O, hg₀2, hconj⟩ := recognition_odd3 c ht htz
    hcfg.linear hJz nd h0 h1 hch hdt
  obtain ⟨ε, hε, hscal⟩ := scalar_odd3 c ht htz hJz nd h0 h1 hch hxR hxM hαθ hg₀O hg₀2 hconj
    hN₁.1 hN₂.1 (fun a ha => (hNc a ha).1) (fun a ha => (hNc a ha).2) hN₁4 hN₂4 hN₁₂ hne₁₂ e'
    hcfg.clsJ hcfg.clsJ' hJ'z hcfg.twinJ.ne.symm hcfg.J'_ne_K hJ'Q
    (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₁.2 hn))
    (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn))
  obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by nd_idx)
  rw [h1] at hW₁
  have hn2 : locImg (conjClass3 K) z (nd.J ⟨2, by omega⟩) =
      ((rootSL2 (oddFrame (u + 5) 𝔽₃).toHypFrame 0 1 (by omega) (by omega) (by omega)
        true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [hch.img 2 (by omega) (by omega)]
    exact congrArg (fun S => S.map c.d.ψ) (hxR 0 (by omega))
  exact pattern_odd3 hm3 c htz (nd.mem ⟨2, by omega⟩)
    (node_commutes_K3 nd h0 (a := 2) (by omega) (by omega))
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩ hn2 hαθ hg₀O hconj hε hscal

theorem twinYPatternAtL3_b_all (h3 : OddThreeFreeInput) :
    ∀ m, 3 ≤ m → TwinYPatternAtL3 .POmegaOdd m
      (fun Ω K β t => PartnerPatternBPair3 m Ω K β t) := by
  intro m hm
  by_cases h5 : 5 ≤ m
  · obtain ⟨u, rfl⟩ : ∃ u, m = u + 5 := ⟨m - 5, by omega⟩
    exact twinYPatternAtL3_b_ge5 u h3
  · obtain rfl | rfl : m = 3 ∨ m = 4 := by omega
    · exact twinYPatternAtL3_b3 h3
    · exact twinYPatternAtL3_b4 h3

end Main

end CFSG.ClassicalInvolution.Q3.Q3TWY
