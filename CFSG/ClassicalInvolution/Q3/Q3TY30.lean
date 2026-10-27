module

public import CFSG.ClassicalInvolution.Q3.Q3TY29
public import CFSG.ClassicalInvolution.Q3.Q3TY26
public import CFSG.ClassicalInvolution.Q3.Q3TY25
public import CFSG.ClassicalInvolution.Q3.Q3TY24
public import CFSG.ClassicalInvolution.Q3.Q3TY22

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWT8
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


theorem twinYPatternAtL3_td5 (h3 : OddThreeFreeInput) (hcls : TwinInvolution3) :
    TwinYPatternAtL3 .POmegaMinus 5 (fun Ω K β t => PartnerPatternMinus3 5 Ω K β t) := by
  intro G _ _ _ hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'
  classical
  have hrow : TwinRow .POmegaMinus 5 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))))
  obtain ⟨hex, -⟩ := hR.setup
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hadm : StatedLieAdmissible .POmegaMinus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_minus (by norm_num) hadm) h3 hR hshape
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have cq := centralQuot3_minus hadm
  have hKJ : Commutes K J := hcfg.twin.comm_K J hcfg.mem_J hcfg.J_ne_K
  have hKJ' : Commutes K J' := hcfg.twin.comm_K J' hcfg.mem_J' hcfg.J'_ne_K
  have hKu : K ∈ centralizingMembers (conjClass3 K) {e'.u} :=
    e'.mem_centralizingMembers_u hKΩ hKJ hKJ'
  obtain ⟨W₀, hW₀⟩ := id hcfg.linear
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW₀
  have hKβne : K ≠ β := ne_of_linearBlockStandardPair hW₀
  obtain ⟨T₀, hT₀z, hT₀Q⟩ := c.exists_twin
  have hT₀ : IsTwinAt (conjClass3 K) K T₀ z := c.isTwinAt3 hT₀z hT₀Q.le
  have clsT₀ : IsClassicalMember3 T₀ z := hcls G hnab K z hR .POmegaMinus 5 hrow hshape T₀ hT₀
  have hlayer : ∀ L : Subgroup G, L ∈ centralizingMembers (conjClass3 K) {z} → L ≠ K →
      Commutes β L → ¬ locImg (conjClass3 K) z L ≤ c.d.Q₁ := by
    intro L hLz hLK hβL hle
    have hLT₀ : L = T₀ := c.eq_of_locImg_le_Q₁ hLz hT₀z hle hT₀Q.le
    have hzL : z ∈ L := hLT₀ ▸ clsT₀.mem
    have hβz : β ∈ centralizingMembers (conjClass3 K) {z} :=
      mem_centralizingMembers_of_commutes hcfg.memβ.1 hzL hβL
    rcases cp_at_member3 h3 hnab hR hKΩ hR.cls hβz with h | h
    · exact hnKβ h
    · exact hKβne h.symm
  have hMz : J ∈ centralizingMembers (conjClass3 K) {z} := hcfg.mem_J
  have hJ'z : J' ∈ centralizingMembers (conjClass3 K) {z} := hcfg.mem_J'
  obtain ⟨RM, hRM, hMR⟩ := c.exists_fund_of_ne hMz hcfg.J_ne_K
    (hlayer J hMz hcfg.J_ne_K hcfg.comm_J)
  obtain ⟨RJ', hRJ', hJ'R⟩ := c.exists_fund_of_ne hJ'z hcfg.J'_ne_K
    (hlayer J' hJ'z hcfg.J'_ne_K hcfg.comm_J')
  have hne : RJ' ≠ RM := fun h => hcfg.twinJ.ne
    (c.eq_of_locImg_eq hJ'z hMz (by rw [hJ'R, hMR, h]))
  obtain ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'comm⟩ :=
    twin_datum_td5_3 c hMz hJ'z hcfg.clsJ hcfg.clsJ' e' hcfg.twinJ.ne.symm hRM hMR hRJ' hJ'R
  have htwin : ∀ i j, IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (RM.map (spinAction (quadMinus 5 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) i →
      IsFundamental (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (RJ'.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) j → i = j := by
    intro i j hi hj
    rw [hFM] at hi
    rw [hFM'] at hj
    rw [IsFundamental.involution_unique hodd hi (IsFundamental.of_frame FM),
      IsFundamental.involution_unique hodd hj (IsFundamental.of_frame_swap FM)]
  have hzs : Commute z s := standardPair_involutions_commute h2 hW₀ hR.cls.mem hcfg.clsβ.mem
    hR.cls.orderOf_eq_two hcfg.clsβ.orderOf_eq_two
  have htz : s * z * s⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzs.symm.eq
  have h2t : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hcfg.clsβ.orderOf_eq_two, pow_two] at this
  have hKt : conjSub s K = K :=
    conjSub_eq_of_standardPair h2 hW₀ hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  let θ : spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →*
    locQuot (conjClass3 K) z := c.d.ψ
  let σ := locAut c.hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    c.locAut_mem_range htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (p := 3) (f := 1) (by norm_num) hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadMinus 5 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))},
      L ∈ centralizingMembers (conjClass3 K) {z} → locImg (conjClass3 K) z L = R.map θ →
      Commutes β L → ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hL).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hβL s hcfg.clsβ.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_td5_3 θ c.d.ker_le σ hσ2 hσr
    hRM hRJ' hne htwin (hfixσ hMz hMR hcfg.comm_J) (hfixσ hJ'z hJ'R hcfg.comm_J')
  have hcommg : ∀ {R : Subgroup (spinGroup (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))},
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 5 (minusCoeffs_irr 3 1)) →
      (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)), g₀ * l = l * g₀ := by
    intro R hR hfix
    rintro _ ⟨r, hr, rfl⟩
    have hαr : α r = r :=
      eq_of_fixed_of_pow3 θ c.d.ker_le c.ker_cop α σ hαθ (cq.pow3 _ hR) hfix r hr
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hconj r v, hαr]
  obtain ⟨N₁, hN₁, N₂, hN₂, hKN₁, hβN₁, hKN₂, hβN₂, hnc, hne₁₂, n₂, hn₂, hn₂N₁⟩ :=
    exists_bridge_members_td5_3 hΩ hex hP1u' hO3u' hty' hKu hcfg.memβ hR.cls hcfg.clsβ hcfg.linear
  have hN₁z : N₁ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hN₁.1 hR.cls.mem (commutes_symm hKN₁)
  have hN₂z : N₂ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hN₂.1 hR.cls.mem (commutes_symm hKN₂)
  obtain ⟨hN₁K, hN₁Q⟩ := c.ne_and_not_le_Q₁3 hN₁z hN₂z hne₁₂ hnc
  obtain ⟨hN₂K, hN₂Q⟩ := c.ne_and_not_le_Q₁3 hN₂z hN₁z hne₁₂.symm
    (fun h => hnc (commutes_symm h))
  obtain ⟨RN₁, hRN₁, hN₁R⟩ := c.exists_fund_of_ne hN₁z hN₁K hN₁Q
  obtain ⟨RN₂, hRN₂, hN₂R⟩ := c.exists_fund_of_ne hN₂z hN₂K hN₂Q
  have hbr := bridgeOmega_of_members3 cq c hN₁z hN₂z hRN₁ hRN₂ hRN₁ hRN₂ hN₁R hN₂R hnc hne₁₂
    hn₂ hn₂N₁
  have hβw : β ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hcfg.memβ.1 hcfg.clsJ.mem hcfg.comm_J
  have hβJ'ne : β ≠ J' := fun h => not_commutes_self3 hcfg.clsβ (by
    have := hcfg.comm_J'
    rw [← h] at this
    exact this)
  have hJ'β : Commutes J' β := hcfg.twinJ.comm_T β hβw hβJ'ne
  obtain ⟨J₂, hJ₂Ω, J₃, hJ₃Ω, hne23, -, hMJ₂, hMJ₃, hKJ₂, hKJ₃, hW₂, hW₃⟩ :=
    exists_leaves_td5_3 c hsingle hcfg.memβ.1 hcfg.clsβ hcfg.linear hcfg.mem_J.1 hKJ
    hcfg.comm_J
  have key : ∀ J₁ ∈ conjClass3 K, Commutes J J₁ → Commutes K J₁ →
      (∃ W, LinearBlockStandardPair (GaloisField 3 1) W β J₁) →
      (J₁ ∈ centralizingMembers (conjClass3 K) {z} →
        ¬ locImg (conjClass3 K) z J₁ ≤ c.d.Q₁) →
      PartnerPatternMinus3 5 (conjClass3 K) K β s := by
    intro J₁ hJ₁Ω hMJ₁ hKJ₁ hβJ₁ hQ
    have hJ₁z : J₁ ∈ centralizingMembers (conjClass3 K) {z} :=
      mem_centralizingMembers_of_commutes hJ₁Ω hR.cls.mem (commutes_symm hKJ₁)
    have hJ₁K : J₁ ≠ K := fun h => not_commutes_self3 hR.cls (by rw [h] at hKJ₁; exact hKJ₁)
    obtain ⟨RJ₁, hRJ₁, hJ₁R⟩ := c.exists_fund_of_ne hJ₁z hJ₁K (hQ hJ₁z)
    obtain ⟨W₁, hW₁⟩ := id hβJ₁
    have hW₁' := linearBlockStandardPair_symm hW₁
    have hJ₁t : conjSub s J₁ = J₁ :=
      conjSub_eq_of_standardPair h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
    obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
      TWS7.exists_inverted_unipotent (p := 3) h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
    obtain ⟨hαJ, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ :=
      unip_data_td5_3 c htz hJ₁z hRJ₁ hJ₁R hJ₁t hx₁J hx₁1 hx₁p hx₁inv hαθ
    have hnormJ : ∀ l ∈ RJ₁.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)), g₀ * l * g₀ ∈ RJ₁.map (spinAction (quadMinus 5 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨α y, hαJ y hy, ?_⟩
      refine LinearEquiv.ext fun v => ?_
      have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
      have := hconj y (g₀ v)
      rw [e1] at this
      exact this
    have hx₀inv : ∀ v, g₀ (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2) x₀ v) = (spinAction (quadMinus 5 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x₀).symm (g₀ v) := by
      intro v
      have h1 := hconj x₀ v
      rw [hx₀α, map_inv] at h1
      exact h1.symm
    have hJM : J₁ ≠ J := fun h => not_commutes_self3 hcfg.clsJ (by rw [h] at hMJ₁; exact hMJ₁)
    have hRJM : RJ₁ ≠ RM := fun h => hJM (c.eq_of_locImg_eq hJ₁z hMz (by rw [hJ₁R, hMR, h]))
    have hnβJ₁ : ¬ Commutes β J₁ := not_commutes_of_linearBlockStandardPair hW₁
    have hJ₁J' : J₁ ≠ J' := fun h => hnβJ₁ (by rw [h]; exact commutes_symm hJ'β)
    have hRJM' : RJ₁ ≠ RJ' := fun h =>
      hJ₁J' (c.eq_of_locImg_eq hJ₁z hJ'z (by rw [hJ₁R, hJ'R, h]))
    have hcomm : Commutes (RM.map (spinAction (quadMinus 5 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2))) (RJ₁.map (spinAction (quadMinus 5 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) :=
      (cq.commutes_iff hRM).mpr ((c.commutes_iff_fund hMz hJ₁z hRM hMR hJ₁R).mp hMJ₁)
    obtain ⟨x', ε, hε, hRJeq, hscal⟩ := class_spin_td5_3 cq hg₀O hg₀2 hg'O hg'2 hRM hRJ' hRJ₁
      hRN₁ hRN₂ FM hFM hFM' hRJM hRJM' hcomm (hcommg hRM (hfixσ hMz hMR hcfg.comm_J))
      (hcommg hRN₁ (hfixσ hN₁z hN₁R hβN₁)) (hcommg hRN₂ (hfixσ hN₂z hN₂R hβN₂)) hnormJ hx₀J
      hx₀1 hx₀p hx₀inv hg'le hg'dim
      (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₁.2 hn)) hN₁R
        (c.hY.pow3 _ hRN₁))
      (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN₂.2 hn)) hN₂R
        (c.hY.pow3 _ hRN₂)) hbr
    have hn2 : locImg (conjClass3 K) z J₁ =
        ((rootSL2 (minusFrame 5 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1
          (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom).map
          c.d.ψ := by
      rw [hJ₁R, hRJeq]
    exact pattern_td5_3 c htz hJ₁Ω hKJ₁ hβJ₁ hn2 hαθ hg₀O hconj
      (by rcases hε with rfl | rfl <;> norm_num) hscal
  have hJ₂z : J₂ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hJ₂Ω hR.cls.mem (commutes_symm hKJ₂)
  have hJ₃z : J₃ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hJ₃Ω hR.cls.mem (commutes_symm hKJ₃)
  by_cases hQ2 : locImg (conjClass3 K) z J₂ ≤ c.d.Q₁
  · exact key J₃ hJ₃Ω hMJ₃ hKJ₃ hW₃ fun hz3 hQ3 =>
      hne23 (c.eq_of_locImg_le_Q₁ hJ₂z hz3 hQ2 hQ3)
  · exact key J₂ hJ₂Ω hMJ₂ hKJ₂ hW₂ fun _ => hQ2

end Main

end CFSG.ClassicalInvolution.Q3.Q3TY
