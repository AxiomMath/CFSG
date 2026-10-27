module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PFact
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PNoThird
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCaseA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PCaseC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTrans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec63_om6p_false (h33 : Asc82Lemma33) (h35 : Asc82Lemma35) (h36 : Asc82Lemma36)
    (hsh : Asc82Shapes) (hM : Asc82Tab6M) (hF : Asc82AutFacts) (hA6 : Asc82FactOm6PA6)
    {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G} (hS : Sec3SettingLB G t L)
    (hHyp : Asc82Hyp62 G) {v x y : G} {V W Y : Subgroup G} (hVbad : Bad63 V v)
    (hWc : IsComponentIn W (centralizer ({v} : Set G))) (hWF : InFStar W) (hWne : W ≠ V)
    (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x)
    (hVc : IsComponentIn V (centralizer ({x} : Set G)))
    (hYc : IsComponentIn Y (centralizer ({y} : Set G))) (hVY : V ≤ Y) (hcomm : ⁅Y, zpowers x⁆ = Y)
    (hVF : InFStar V) (hYF : InFStar Y) (hYC : InCStar Y) (hV29 : IsL29 V)
    (hY6 : IsOmega6Plus Y) : False := by
  obtain ⟨hv, hVcv, -, -⟩ := hVbad
  have hxN : x ∈ normalizer (Y : Set G) := sec63_mem_normalizer_of_comm hcomm
  have hxC : x ∉ centralizer (Y : Set G) := by
    intro hxc
    have hYx : Y ≤ centralizer ({x} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hxc a ha)
    have hbot := commutator_zpowers_eq_bot_of_le_centralizer hYx
    rw [hcomm] at hbot
    exact hYc.ne_bot hbot
  have hVx : IsComponentIn V (Y ⊓ centralizer ({x} : Set G)) :=
    hVc.mono (le_inf hVY hVc.le) inf_le_right
  have hYom : IsOm6P Y := ⟨hYc.isQuasisimple, hY6⟩
  obtain ⟨b, hbV, hb⟩ := exists_involution_of_isComponentIn hVc
  have hbY : b ∈ Y := hVY hbV
  have hVy : V ≤ centralizer ({y} : Set G) := hVY.trans hYc.le
  have hvb : v * b = b * v :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hVcv.le hbV)).symm
  have hyb : y * b = b * y := (Subgroup.mem_centralizer_singleton_iff.mp (hVy hbV)).symm
  have hyne : y ≠ b := fun h =>
    sec63_involution_not_mem hy hVy hVc.isQuasisimple (Or.inl hV29) (h ▸ hbV)
  rcases hA6 G Y x V hYom hx hxN hxC hVx hV29 b hbV hb with
    hpocket | ⟨Vb, hVbc, hVb29, hVbF, huniq, hbound, R, hR2, hRle, hR8, hRgen⟩
  · exact sec63P_not_pocket h35 hS hv hVcv hWc hWF hWne hy hYc hYF hbV hVY hpocket
  have hrk : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E →
      E ≤ centralizer (Vb : Set G) ⊓ centralizer ({y} : Set G) → CFSG.Open.pRank 2 E ≤ 2 :=
    fun E hE hEle =>
      sec63_om6p_rank_cent h33 hF hS hHyp hy hYc hYF hYC hY6 hb hbY hVbc hVbF hVb29 hE hEle
  have hWb : W ≤ centralizer ({b} : Set G) := by
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hVcv.commute_of_ne hWc hWne.symm b hbV c hc).symm)
  have hWc2 : IsComponentIn W (centralizer ({v, b} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact hWc.mono (le_inf hWc.1 hWb) inf_le_left
  obtain ⟨J, hJc, hWJ⟩ := hS.lBalance v b hv hb hvb W hWc2
  have hJF : InFStar J := hS.a2 v b hv hb hvb W J hWc2 hJc hWJ hWF
  have hVbc2 : IsComponentIn Vb (centralizer ({y, b} : Set G)) := by
    rw [centralizer_pair_eq_inf]
    exact sec63P_isComponentIn_of_subnormal hYc.le hYc.2.2 hVbc
  obtain ⟨I, hIc, hVbI⟩ := hS.lBalance y b hy hb hyb Vb hVbc2
  have hIF : InFStar I := hS.a2 y b hy hb hyb Vb I hVbc2 hIc hVbI hVbF
  have hVbY : Vb ≤ Y := hVbc.le.trans inf_le_left
  have hthird : ∀ K : Subgroup G, IsComponentIn K (centralizer ({b} : Set G)) → InFStar K →
      K = I ∨ K = CFSG.conjugate I y := fun K hKc hKF =>
    sec63_om6p_no_third h36 hS hy hb hyb hyne (hVbY.trans hYc.le)
      (hVbc.le.trans inf_le_right) hIc hIF hVbI hrk hKc hKF
  have c : Sec63PCtx v y b V W Y Vb R I J :=
    { hv := hv, hy := hy, hb := hb, hvb := hvb, hyb := hyb, hVc := hVcv, hWc := hWc,
      hWne := hWne, hVF := hVF, hWF := hWF, hVY := hVY, hYc := hYc, hVbc := hVbc,
      huniq := huniq, hbound := hbound, hR2 := hR2, hRle := hRle, hR8 := hR8, hRgen := hRgen,
      hJc := hJc, hJF := hJF, hWJ := hWJ, hIc := hIc, hIF := hIF, hVbI := hVbI,
      hthird := hthird }
  by_cases hJv : CFSG.conjugate J v = J
  · by_cases hWJ' : W = J
    · exact sec63P_caseB c hWJ'
    · exact sec63P_caseC h35 h36 hsh hM hF hS hHyp c hJv hWJ'
  · exact sec63P_caseA c hJv

end CFSG.OddStandard.SmallF3.Omega
