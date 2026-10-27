module

public import CFSG.ClassicalInvolution.Q3.Q3TY21
public import CFSG.ClassicalInvolution.Q3.Q3TY18
public import CFSG.ClassicalInvolution.Q3.Q3TY12
public import CFSG.ClassicalInvolution.RouteD.TWS7Grp
public import CFSG.ClassicalInvolution.RouteD.ExoticSingleMinus
public import CFSG.ClassicalInvolution.Q3.Q3TY17

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.RouteD.TWT9
  CFSG.ClassicalInvolution.WeakCT CFSG.LieType.Universal.Spin.Twisted
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]


theorem twinYPatternAtL3_td4 (h3 : OddThreeFreeInput) (hcls : TwinInvolution3) :
    TwinYPatternAtL3 .POmegaMinus 4 (fun Ω K β t => PartnerPatternMinus3 4 Ω K β t) := by
  intro G _ _ _ hnab K z hR hshape T e J J' w e' β s hcfg hP1u hO3u hP1u' hO3u' hty hty'
  classical
  have hrow : TwinRow .POmegaMinus 4 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, by norm_num⟩))))
  obtain ⟨hex, -⟩ := hR.setup
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hadm : StatedLieAdmissible .POmegaMinus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_minus le_rfl hadm) h3 hR hshape
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
  have clsT₀ : IsClassicalMember3 T₀ z := hcls G hnab K z hR .POmegaMinus 4 hrow hshape T₀ hT₀
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
  obtain ⟨RJ, hRJ, hJR⟩ := c.exists_fund_of_ne hcfg.mem_J hcfg.J_ne_K
    (hlayer J hcfg.mem_J hcfg.J_ne_K hcfg.comm_J)
  obtain ⟨RJ', hRJ', hJ'R⟩ := c.exists_fund_of_ne hcfg.mem_J' hcfg.J'_ne_K
    (hlayer J' hcfg.mem_J' hcfg.J'_ne_K hcfg.comm_J')
  have hne : RJ' ≠ RJ := fun h => hcfg.twinJ.ne
    (c.eq_of_locImg_eq hcfg.mem_J' hcfg.mem_J (by rw [hJ'R, hJR, h]))
  obtain ⟨FM, g', hFM, hFM', hg'O, hg'2, hg'fix, hg'dim, hg'le, hg'an, hg'comm⟩ :=
    twin_datum_td4_3 c hcfg.mem_J hcfg.mem_J' hcfg.clsJ hcfg.clsJ' e' hcfg.twinJ.ne.symm hRJ hJR
      hRJ' hJ'R
  have htwin : ∀ i j, IsFundamental (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (RJ.map (spinAction (quadMinus 4 (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))) i →
      IsFundamental (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (RJ'.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
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
  let θ : spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) →*
    locQuot (conjClass3 K) z := c.d.ψ
  let σ := locAut c.hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut c.hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    c.locAut_mem_range htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (p := 3) (f := 1) le_rfl hadm c.hY.std c.d.ψ) k'
  have hfixσ : ∀ {L : Subgroup G} {R : Subgroup (spinGroup (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))},
      L ∈ centralizingMembers (conjClass3 K) {z} → locImg (conjClass3 K) z L = R.map θ →
      Commutes β L → ∀ r ∈ R, σ (θ r) = θ r := fun hL hLR hβL r hr =>
    (locAut_fixed_iff3 c.hΩ c.hex c.hP1 c.hO3 htz hL).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hβL s hcfg.clsβ.mem n hn).symm) _
      (by rw [hLR]; exact ⟨r, hr, rfl⟩)
  obtain ⟨x, α, g₀, -, -, hαθ, hg₀O, hg₀2, hconj, -⟩ := lift_td4_3 θ c.d.ker_le σ hσ2 hσr
    hRJ hRJ' hne htwin (hfixσ hcfg.mem_J hJR hcfg.comm_J)
    (hfixσ hcfg.mem_J' hJ'R hcfg.comm_J')
  have hcommg : ∀ {R : Subgroup (spinGroup (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))},
      R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 4 (minusCoeffs_irr 3 1)) →
      (∀ r ∈ R, σ (θ r) = θ r) →
      ∀ l ∈ R.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)), g₀ * l = l * g₀ := by
    intro R hR hfix
    rintro _ ⟨r, hr, rfl⟩
    have hαr : α r = r :=
      eq_of_fixed_of_pow3 θ c.d.ker_le c.ker_cop α σ hαθ (cq.pow3 _ hR) hfix r hr
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hconj r v, hαr]
  obtain ⟨J₁, hJ₁, N, hN, hKJ₁, hβJ₁, hKN, hβN, hJ₁N⟩ := exists_chain_members_td4_3 hΩ hex
    hP1u' hO3u' hty' hKu hcfg.memβ hR.cls hcfg.clsβ hcfg.linear
  have hJ₁z : J₁ ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hJ₁.1 hR.cls.mem (commutes_symm hKJ₁)
  have hNz : N ∈ centralizingMembers (conjClass3 K) {z} :=
    mem_centralizingMembers_of_commutes hN.1 hR.cls.mem (commutes_symm hKN)
  obtain ⟨W₂, hW₂⟩ := id hJ₁N
  have hJ₁Nne : J₁ ≠ N := ne_of_linearBlockStandardPair hW₂
  have hJ₁Nnc : ¬ Commutes J₁ N := not_commutes_of_linearBlockStandardPair hW₂
  obtain ⟨hJ₁K, hJ₁Q⟩ := c.ne_and_not_le_Q₁3 hJ₁z hNz hJ₁Nne hJ₁Nnc
  obtain ⟨hNK, hNQ⟩ := c.ne_and_not_le_Q₁3 hNz hJ₁z hJ₁Nne.symm
    (fun h => hJ₁Nnc (commutes_symm h))
  obtain ⟨RJ₁, hRJ₁, hJ₁R⟩ := c.exists_fund_of_ne hJ₁z hJ₁K hJ₁Q
  obtain ⟨RN, hRN, hNR⟩ := c.exists_fund_of_ne hNz hNK hNQ
  obtain ⟨W₁, hW₁⟩ := id hβJ₁
  have hW₁' := linearBlockStandardPair_symm hW₁
  have hJ₁t : conjSub s J₁ = J₁ :=
    conjSub_eq_of_standardPair h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  obtain ⟨x₁, hx₁J, hx₁1, hx₁p, hx₁inv⟩ :=
    TWS7.exists_inverted_unipotent (p := 3) h2 hW₁' hcfg.clsβ.mem hcfg.clsβ.orderOf_eq_two
  obtain ⟨hαJ, x₀, hx₀J, hx₀1, hx₀p, hx₀α⟩ :=
    unip_data_td4_3 c htz hJ₁z hRJ₁ hJ₁R hJ₁t hx₁J hx₁1 hx₁p hx₁inv hαθ
  have hnormJ : ∀ l ∈ RJ₁.map (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)), g₀ * l * g₀ ∈ RJ₁.map (spinAction (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)) := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨α y, hαJ y hy, ?_⟩
    refine LinearEquiv.ext fun v => ?_
    have e1 : g₀ (g₀ v) = v := by simpa using LinearEquiv.congr_fun hg₀2 v
    have := hconj y (g₀ v)
    rw [e1] at this
    exact this
  have hx₀inv : ∀ v, g₀ (spinAction (quadMinus 4 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) x₀ v) = (spinAction (quadMinus 4 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) x₀).symm (g₀ v) := by
    intro v
    have h1 := hconj x₀ v
    rw [hx₀α, map_inv] at h1
    exact h1.symm
  have hnsq : ¬ IsSquare (-1 : GaloisField 3 1) :=
    CFSG.ClassicalInvolution.Q3.not_isSquare_neg_one_of_card_eq_three card_gf3
  obtain ⟨x', ε, hε, hRJ₁eq, hscal⟩ := class_spin_td4a_3 cq hg₀O hg₀2 hg'O hg'2 hRJ₁ hRN
    FM hFM (hcommg hRJ (hfixσ hcfg.mem_J hJR hcfg.comm_J))
    (hcommg hRN (hfixσ hNz hNR hβN)) hnormJ hx₀J hx₀1 hx₀p hx₀inv hg'le hg'dim
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hJ₁.2 hn)) hJ₁R
      (c.hY.pow3 _ hRJ₁))
    (hg'comm (fun n hn => Subgroup.mem_centralizer_singleton_iff.mp (hN.2 hn)) hNR
      (c.hY.pow3 _ hRN))
    (hg'an hnsq)
  have hn2 : locImg (conjClass3 K) z J₁ =
      ((rootSL2 (minusFrame 4 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame 0 1
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x').toMonoidHom).map
        c.d.ψ := by
    rw [hJ₁R, hRJ₁eq]
  exact pattern_td4_3 c htz hJ₁.1 hKJ₁ hβJ₁ hn2 hαθ hg₀O hconj
    (by rcases hε with rfl | rfl <;> norm_num) hscal

end Main

end CFSG.ClassicalInvolution.Q3.Q3TY
