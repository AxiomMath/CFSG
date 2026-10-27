module

public import CFSG.ClassicalInvolution.Q3.Q3TY11
public import CFSG.ClassicalInvolution.Q3.Q3TY9
public import CFSG.ClassicalInvolution.Q3.Q3WASTInner
public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.RouteD.TWD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

structure TwinYConfigL3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K T : Subgroup G) (z : G)
    (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w) (β : Subgroup G)
    (s : G) : Prop where
  twin : IsTwinAt Ω K T z
  clsT : IsClassicalMember3 T z
  mem_J : J ∈ centralizingMembers Ω {z}
  mem_J' : J' ∈ centralizingMembers Ω {z}
  J_ne_K : J ≠ K
  J_ne_T : J ≠ T
  J'_ne_K : J' ≠ K
  J'_ne_T : J' ≠ T
  twinJ : IsTwinAt Ω J J' w
  clsJ : IsClassicalMember3 J w
  clsJ' : IsClassicalMember3 J' w
  memβ : β ∈ centralizingMembers Ω {e'.u}
  clsβ : IsClassicalMember3 β s
  linear : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β
  comm_u : s * e.u = e.u * s
  comm_J : Commutes β J
  comm_J' : Commutes β J'

section Config

variable {G : Type} [Group G] [Finite G]


theorem localShapeC3_at_member {a : ℕ} {c : CompData} {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 a c (conjClass3 K) z) {M : Subgroup G}
    {w : G} (hM : M ∈ conjClass3 K) (hw : IsClassicalMember3 M w) :
    LocalShapeC3 a c (conjClass3 M) w := by
  obtain ⟨g, hg⟩ := hM
  have hMg : M = conjSub g K := hg.symm
  have hw' : w = g * z * g⁻¹ := involution_unique3 hw (hMg ▸ hR.cls.conj g)
  rw [conjClass3_eq_of_mem ⟨g, hg⟩, hw']
  exact hshape.conjShape3 hR.inClass.conjInvariant g

variable [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem twinYConfigL3_of_partner {m : ℕ} (hm : 4 ≤ m) (hcls : TwinInvolution3)
    (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x) (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .POmegaMinus m) (conjClass3 K) z)
    (c : TCtx3 .POmegaMinus m (conjClass3 K) K z) {β : Subgroup G} (hβ : β ∈ conjClass3 K)
    {t : G} (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfix : HasFixedMember (conjClass3 K) K β z) :
    ∃ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w)
      (s : G), TwinYConfigL3 (conjClass3 K) K T z e J J' w e' β s := by
  classical
  have hrow : TwinRow .POmegaMinus m :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))))
  have hadm : StatedLieAdmissible .POmegaMinus m 3 1 := ⟨Nat.prime_three, le_rfl, hm⟩
  obtain ⟨hex, hP1⟩ := hR.setup
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨T, hTz, hTQ⟩ := c.exists_twin
  have hT : IsTwinAt (conjClass3 K) K T z := c.isTwinAt3 hTz hTQ.le
  have clsT : IsClassicalMember3 T z := hcls G hnab K z hR .POmegaMinus m hrow hshape T hT
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
  have hshapeM : LocalShapeC3 2 (CompData.model .POmegaMinus m) (conjClass3 M) w :=
    localShapeC3_at_member hR hshape hMΩ hw
  have hJ'M : IsTwinAt (conjClass3 M) M J' w := by rw [hclsM]; exact hJ'
  have clsJ' : IsClassicalMember3 J' w :=
    hcls G hnab M w hSM .POmegaMinus m hrow hshapeM J' hJ'M
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
  obtain ⟨W₁, hW₁⟩ := cx.sign_config3 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hadm
    hKw hβw hTw hR.cls ht clsT hKβne hβT hKβ hnβT hKT hna
  have hTβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W T β :=
    ⟨W₁, linearBlockStandardPair_symm hW₁⟩
  obtain ⟨e, he⟩ := exists_twinElt_comm3 hR.cls clsT ht hKβ hTβ
  exact ⟨T, e, M, J', w, e', t, ⟨hT, clsT, hMz, hJ'z, hMK, hMT, hJ'K, hJ'T, hJ', hw, clsJ',
    e'.mem_centralizingMembers_u hβ hβM (commutes_symm hJ'βc), ht, hKβ, he, hβM,
    commutes_symm hJ'βc⟩⟩

end Config

section Y4


@[expose] def TwinYPatternAtL3 (t : StatedLieTag) (n : ℕ)
    (Pat : ∀ {G : Type} [Group G], Set (Subgroup G) → Subgroup G → Subgroup G → G → Prop) :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G)
          (e' : TwinElt J J' w) (β : Subgroup G) (s : G),
          TwinYConfigL3 (conjClass3 K) K T z e J J' w e' β s →
          LocalOddCentral (conjClass3 K) {e.u} → LocalOddThreeFree3 (conjClass3 K) e.u →
          LocalOddCentral (conjClass3 K) {e'.u} → LocalOddThreeFree3 (conjClass3 K) e'.u →
          LocalShapeC3 0 (CompData.model (twinYModel 3 t n).1 (twinYModel 3 t n).2)
            (conjClass3 K) e.u →
          LocalShapeC3 0 (CompData.model (twinYModel 3 t n).1 (twinYModel 3 t n).2)
            (conjClass3 K) e'.u → Pat (conjClass3 K) K β s

theorem partnerPatternStmt3_of_y4 {m : ℕ} (hm : 4 ≤ m) (h3 : OddThreeFreeInput)
    (hcls : TwinInvolution3) (hP : CommutingProductP1Input3) (hY2 : TwinYType3)
    (hY4 : TwinYPatternAtL3 .POmegaMinus m
      (fun Ω K β t => PartnerPatternMinus3 m Ω K β t)) : PartnerPatternStmt3 m := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hrow : TwinRow .POmegaMinus m :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, hm⟩))))
  have hadm : StatedLieAdmissible .POmegaMinus m 3 1 := ⟨Nat.prime_three, le_rfl, hm⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_minus hm hadm) h3 hR hshape
  obtain ⟨T, e, J, J', w, e', s, hcfg⟩ :=
    twinYConfigL3_of_partner hm hcls h3 hnab hR hshape c hβ ht hKβ hfix
  have hst : s = t := involution_unique3 hcfg.clsβ ht
  subst hst
  obtain ⟨hex, -⟩ := hR.setup
  have hKT : Commutes K T := hcfg.twin.comm_K T hcfg.twin.mem hcfg.twin.ne
  have hJΩ : J ∈ conjClass3 K := hcfg.mem_J.1
  have hJ'Ω : J' ∈ conjClass3 K := hcfg.mem_J'.1
  have hTΩ : T ∈ conjClass3 K := hcfg.twin.mem.1
  have hclsJ : conjClass3 J = conjClass3 K := conjClass3_eq_of_mem hJΩ
  have hSJ : RouteD3Setup J w := RouteD3Setup.of_mem_conjClass3 hR hJΩ hcfg.clsJ
  have hshapeJ : LocalShapeC3 2 (CompData.model .POmegaMinus m) (conjClass3 J) w :=
    localShapeC3_at_member hR hshape hJΩ hcfg.clsJ
  have hJJ' : Commutes J J' :=
    hcfg.twinJ.comm_K J' hcfg.twinJ.mem hcfg.twinJ.ne
  obtain ⟨hP1u, hO3u⟩ := hP G K z hR T hTΩ hKT e.u e.u_mem_sup
    (twinElt_orderOf_u3 e hR.cls (hex K ⟨1, conjSub_one K⟩) hKT)
    (twinElt_u_not_mem_left3 e hR.cls (hex K ⟨1, conjSub_one K⟩) hKT)
    (twinElt_u_not_mem_right3 e hcfg.clsT (hex T hTΩ) hKT)
  obtain ⟨hP1u', hO3u'⟩ := hP G J w hSJ J' (by rw [hclsJ]; exact hJ'Ω) hJJ' e'.u e'.u_mem_sup
    (twinElt_orderOf_u3 e' hcfg.clsJ (hex J hJΩ) hJJ')
    (twinElt_u_not_mem_left3 e' hcfg.clsJ (hex J hJΩ) hJJ')
    (twinElt_u_not_mem_right3 e' hcfg.clsJ' (hex J' hJ'Ω) hJJ')
  rw [hclsJ] at hP1u' hO3u'
  have hty := hY2 G hnab K z hR .POmegaMinus m hrow hshape T hcfg.twin hcfg.clsT e hP1u hO3u
  have hty' := hY2 G hnab J w hSJ .POmegaMinus m hrow hshapeJ J' (by rw [hclsJ]; exact hcfg.twinJ)
    hcfg.clsJ' e' (by rw [hclsJ]; exact hP1u') (by rw [hclsJ]; exact hO3u')
  rw [hclsJ] at hty'
  exact hY4 G hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'

theorem chainPiece3TwinTD_of_pattern (h3 : OddThreeFreeInput)
    (hpat : ∀ m, 4 ≤ m → PartnerPatternStmt3 m) : Q3TW.ChainPiece3TwinTD :=
  chainPiece3TwinTD_of_on (P := fun _ => True)
    (chainPiece3TwinTDOn_of_pattern h3 (Gaps.fundNoncentral 3)
      (fun N hN _ => hpat (N - 2) (by omega)))
    (chainPiece3TwinTDOn_of_pattern h3 (Gaps.fundNoncentral 3) (fun _ _ h => absurd trivial h))

theorem chainPiece3TwinTD_of_y4 (h3 : OddThreeFreeInput) (hcls : TwinInvolution3)
    (hP : CommutingProductP1Input3) (hY2 : TwinYType3)
    (hY4 : ∀ m, 4 ≤ m → TwinYPatternAtL3 .POmegaMinus m
      (fun Ω K β t => PartnerPatternMinus3 m Ω K β t)) : Q3TW.ChainPiece3TwinTD :=
  chainPiece3TwinTD_of_pattern h3 fun m hm => partnerPatternStmt3_of_y4 hm h3 hcls hP hY2 (hY4 m hm)

end Y4

end CFSG.ClassicalInvolution.Q3.Q3TY
