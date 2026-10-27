module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R6Fix
public import CFSG.ClassicalInvolution.Q3.Q3TD3R6Br
public import CFSG.ClassicalInvolution.Q3.Q3TD3Y
public import CFSG.ClassicalInvolution.Q3.Q3TY24

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


theorem twinYPatternAtL3_plus6 (h3 : OddThreeFreeInput) (hcls : TwinInvolution3) :
    TwinYPatternAtL3 .POmegaPlus 6 (fun Ω K β t => PartnerPatternPlus3 6 Ω K β t) := by
  intro G _ _ _ hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'
  classical
  have hrow : TwinRow .POmegaPlus 6 := Or.inl ⟨rfl, rfl, by norm_num⟩
  obtain ⟨hex, -⟩ := hR.setup
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_plus (by norm_num) hadm) h3 hR hshape
  have hβΩ : β ∈ conjClass3 K := hcfg.memβ.1
  have hJΩ : J ∈ conjClass3 K := hcfg.mem_J.1
  have hJz : J ∈ centralizingMembers (conjClass3 K) {z} := hcfg.mem_J
  have hKJ : Commutes K J := hcfg.twin.comm_K J hcfg.mem_J hcfg.J_ne_K
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW₀
  obtain ⟨T₀, hT₀z, hT₀Q⟩ := c.exists_twin
  have hT₀ : IsTwinAt (conjClass3 K) K T₀ z := c.isTwinAt3 hT₀z hT₀Q.le
  have clsT₀ : IsClassicalMember3 T₀ z := hcls G hnab K z hR .POmegaPlus 6 hrow hshape T₀ hT₀
  have hlayer : ∀ L : Subgroup G, L ∈ centralizingMembers (conjClass3 K) {z} → L ≠ K →
      Commutes β L → ¬ locImg (conjClass3 K) z L ≤ c.d.Q₁ := by
    intro L hLz hLK hβL hle
    have hLT₀ : L = T₀ := c.eq_of_locImg_le_Q₁ hLz hT₀z hle hT₀Q.le
    have hzL : z ∈ L := hLT₀ ▸ clsT₀.mem
    have hβz : β ∈ centralizingMembers (conjClass3 K) {z} :=
      mem_centralizingMembers_of_commutes hβΩ hzL hβL
    rcases cp_at_member3 h3 hnab hR hKΩ hR.cls hβz with h | h
    · exact hnKβ h
    · exact hKβne h.symm
  have hJlayer : IsLayerMember3 c J :=
    ⟨hJz, hcfg.J_ne_K, hlayer J hJz hcfg.J_ne_K hcfg.comm_J⟩
  have hzt : Commute z s := standardPair_involutions_commute h2 hW₀ hR.cls.mem hcfg.clsβ.mem
    hR.cls.orderOf_eq_two hcfg.clsβ.orderOf_eq_two
  have htz : s * z * s⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm.eq
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_plus3 (by norm_num : 5 ≤ 6) c hsingle hβΩ
    hcfg.clsβ hcfg.linear hJΩ hKJ hcfg.comm_J
  have hnodeW : ∀ a : Fin 6, nd.J a ∈ centralizingMembers (conjClass3 K) {w} := fun a =>
    mem_centralizingMembers_of_commutes (nd.mem a) hcfg.clsJ.mem (commutes_symm (nd.commK a))
  have hneJ' : ∀ a : Fin 6, nd.J a ≠ J' := by
    intro a h
    obtain ⟨b, hab⟩ : ∃ b : Fin 6, DNodes3.Adj a b := by
      by_cases h4 : a.val ≤ 3
      · exact ⟨⟨a.val + 1, by omega⟩, by simp [DNodes3.adj_def]; omega⟩
      · exact ⟨⟨3, by norm_num⟩, by simp [DNodes3.adj_def]; omega⟩
    have hbJ' : nd.J b ≠ J' := fun hb => nd.ne_J hab.ne (h.trans hb.symm)
    have := hcfg.twinJ.comm_T (nd.J b) (hnodeW b) hbJ'
    rw [← h] at this
    exact nd.not_commutes_of_adj hab this
  have hnodeu : ∀ a : Fin 6, nd.J a ∈ centralizingMembers (conjClass3 K) {e'.u} := fun a =>
    e'.mem_centralizingMembers_u (nd.mem a) (commutes_symm (nd.commK a))
      (commutes_symm (hcfg.twinJ.comm_T (nd.J a) (hnodeW a) (hneJ' a)))
  obtain ⟨N, hN, hNc, hN4, hN5⟩ := exists_tilted_bridge_d6_3 hΩ hex hP1u' hO3u' hty' nd hnodeu
  have hNΩ : N ∈ conjClass3 K := hN.1
  obtain ⟨Rz, RzM, RN, x, tM, α, g₀, hRz, hRzM, hRN, hxR, hxM, hαθ, hg₀O, hg₀2, hconj, hfixv⟩ :=
    recognition_plus_six3 c hcfg.clsβ htz hcfg.linear hJΩ hJlayer nd h0 h1 hNΩ hNc hN4 hN5
  have hNK : Commutes N K := by
    have := hNc ⟨0, by omega⟩ (by norm_num)
    rw [h0] at this
    exact this
  have hNz : N ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hNΩ hR.cls.mem hNK
  have hscal := scalar_plus_six3 c hcfg.clsβ htz hJz nd h0 h1 hRz hRzM hNz hRN hxR hxM hαθ hg₀O
    hg₀2 hconj hfixv hNc hN4 hN5
  have hn2 : locImg (conjClass3 K) z (nd.J ⟨2, by omega⟩) =
      ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [(hRz 2 (by omega) (by omega)).2]
    exact congrArg (fun S => S.map c.d.ψ) (hxR 0 (by norm_num))
  exact pattern_plus_six3 c htz nd h0 h1 hn2 hαθ hg₀O hconj hscal

end CFSG.ClassicalInvolution.Q3.Q3TD
