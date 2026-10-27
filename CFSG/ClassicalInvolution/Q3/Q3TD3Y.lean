module

public import CFSG.ClassicalInvolution.Q3.Q3TY12

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.ClassicalInvolution.Q3.Q3TY
open CFSG.ClassicalInvolution.RouteD.TWD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

section Config

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem twinYConfigL3_of_partner_gen {tY : StatedLieTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hadm : StatedLieAdmissible tY nY 3 1)
    (hsign : tY = .PSL ∨ tY = .PSU ∨ tY = .PSp ∨ tY = .POmegaOdd ∨ tY = .POmegaPlus ∨
      tY = .POmegaMinus)
    (hcls : TwinInvolution3)
    (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x) (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 K) z)
    (c : TCtx3 tY nY (conjClass3 K) K z) {β : Subgroup G} (hβ : β ∈ conjClass3 K)
    {t : G} (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfix : HasFixedMember (conjClass3 K) K β z) :
    ∃ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w)
      (s : G), TwinYConfigL3 (conjClass3 K) K T z e J J' w e' β s := by
  classical
  obtain ⟨hex, hP1⟩ := hR.setup
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (conjClass3 K) K T z := c.isTwinAt3 hTz hTQ.le
  have clsT : IsClassicalMember3 T z := hcls G hnab K z hR tY nY hrow hshape T hT
  have hKT : Commutes K T := hT.comm_K T hT.mem hT.ne
  obtain ⟨M, hMΩ, hKM, hβM, hMnon⟩ := hfix
  obtain ⟨W₀, hW₀⟩ := id hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW₀
  have hzt : Commute z t := standardPair_involutions_commute h2 hW₀ hR.cls.mem ht.mem
    hR.cls.orderOf_eq_two ht.orderOf_eq_two
  have hMz : M ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hMΩ hR.cls.mem (commutes_symm hKM)
  have hMK : M ≠ K := fun h => not_commutes_self3 hR.cls (by rw [h] at hKM; exact hKM)
  have hMT : M ≠ T := fun h => hMnon (fun N hN hNM => by
    rw [h]; exact hT.comm_T N hN (by rw [← h]; exact hNM))
  obtain ⟨w, hw⟩ := hΩ.classical M hMΩ
  have hwz : w ≠ z := by
    intro hwz
    apply hMnon
    intro N hN hNM
    have hN' : N ∈ centralizingMembers (conjClass3 K) {w} := by rw [hwz]; exact hN
    exact (cp_at_member3 h3 hnab hR hMΩ hw hN').resolve_right hNM
  obtain ⟨cx⟩ := c.exists_ctx_member hsingle hMΩ hw
  obtain ⟨J', hJ'⟩ := cx.exists_isTwinAt3
  have hSM : RouteD3Setup M w := RouteD3Setup.of_mem_conjClass3 hR hMΩ hw
  have hclsM : conjClass3 M = conjClass3 K := conjClass3_eq_of_mem hMΩ
  have hshapeM : LocalShapeC3 2 (CompData.model tY nY) (conjClass3 M) w :=
    localShapeC3_at_member hR hshape hMΩ hw
  have hJ'M : IsTwinAt (conjClass3 M) M J' w := by rw [hclsM]; exact hJ'
  have clsJ' : IsClassicalMember3 J' w :=
    hcls G hnab M w hSM tY nY hrow hshapeM J' hJ'M
  have hJ'Ω : J' ∈ conjClass3 K := hJ'.mem.1
  have hKw : K ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hKΩ hw.mem hKM
  have hTM : Commutes T M := hT.comm_T M hMz hMT
  have hTΩ : T ∈ conjClass3 K := hTz.1
  have hTw : T ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hTΩ hw.mem hTM
  have hβw : β ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hβ hw.mem hβM
  have hJ'K : J' ≠ K := fun h => hwz (involution_unique3 (h ▸ clsJ') hR.cls)
  have hJ'T : J' ≠ T := fun h => hwz (involution_unique3 (h ▸ clsJ') clsT)
  have hJ'Kc : Commutes J' K := hJ'.comm_T K hKw hJ'K.symm
  have hJ'Tc : Commutes J' T := hJ'.comm_T T hTw hJ'T.symm
  have hJ'z : J' ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hJ'Ω hR.cls.mem hJ'Kc
  have hβJ' : β ≠ J' := fun h => hnKβ (by rw [h]; exact commutes_symm hJ'Kc)
  have hJ'βc : Commutes J' β := hJ'.comm_T β hβw hβJ'
  obtain ⟨e'⟩ := exists_twinElt3 hw clsJ' (hex M hMΩ) (hex J' hJ'Ω)
  have hβT : β ≠ T := fun h => hnKβ (by rw [h]; exact hKT)
  have hnβT : ¬ Commutes β T := by
    intro h
    have hβz : β ∈ centralizingMembers (conjClass3 K) {z} :=
      mem_centralizingMembers_of_commutes hβ clsT.mem h
    rcases cp_at_member3 h3 hnab hR hKΩ hR.cls hβz with h' | h'
    · exact hnKβ h'
    · exact hKβne h'.symm
  have htz : t * z * t⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]; exact hzt.symm.eq
  have htt : t * t = 1 := ht.isCentralInvolution.sq
  have hna : conjSub t K = K := conjSub_eq_of_standardPair h2 hW₀ ht.mem ht.orderOf_eq_two
  have hnd : conjSub t T = T := c.conjSub_twin_eq3 htz htt hna hTz hTQ.le
  obtain ⟨W₁, hW₁⟩ := cx.sign_config3 hsign hadm
    hKw hβw hTw hR.cls ht clsT hKβne hβT hKβ hnβT hKT hna
  have hTβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T β :=
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩
  obtain ⟨e, he⟩ := exists_twinElt_comm3 hR.cls clsT ht hKβ hTβ
  exact ⟨T, e, M, J', w, e', t, ⟨hT, clsT, hMz, hJ'z, hMK, hMT, hJ'K, hJ'T, hJ', hw, clsJ',
    e'.mem_centralizingMembers_u hβ hβM (commutes_symm hJ'βc), ht, hKβ, he, hβM,
    commutes_symm hJ'βc⟩⟩

end Config

end CFSG.ClassicalInvolution.Q3.Q3TD
