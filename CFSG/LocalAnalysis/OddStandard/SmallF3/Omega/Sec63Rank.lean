module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6L65
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Walter.TwoRank
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem simple_oddCore_of_l29 [Finite G] {X : Subgroup G} (h : IsL29 X) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) := by
  unfold IsL29 at h
  exact (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ CFSG.oddCore X)
    ⟨.PSL, 2, 3, 2, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2

private theorem simple_oddCore_of_l281 [Finite G] {X : Subgroup G} (h : IsL281 X) :
    IsSimpleGroup (X ⧸ CFSG.oddCore X) := by
  unfold IsL281 at h
  exact (CFSG.LieType.Simplicity.fam_classical_converse (X ⧸ CFSG.oddCore X)
    ⟨.PSL, 2, 3, 4, h.statedClassicalModel_of_ne_zero (by norm_num)⟩).2.2

private theorem odd_card_oddCore {H : Type*} [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.oddCore H ≤ CFSG.pPrimeCore 2 H :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  exact Nat.coprime_two_left.mp
    (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hle)
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := H)))

private theorem odd_orderOf_of_mem_oddCore {H : Type*} [Group H] [Finite H] {m : H}
    (hm : m ∈ CFSG.oddCore H) : Odd (orderOf m) := by
  have hdvd : orderOf m ∣ Nat.card (CFSG.oddCore H) := by
    have := orderOf_dvd_natCard (⟨m, hm⟩ : CFSG.oddCore H)
    rwa [Subgroup.orderOf_mk] at this
  exact (odd_card_oddCore (H := H)).of_dvd_nat hdvd

theorem sec63_two_le_pRank [Finite G] {X : Subgroup G} (hq : IsQuasisimple ↥X)
    (h : IsL29 X ∨ IsL281 X) : 2 ≤ CFSG.Open.pRank 2 X := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : IsSimpleGroup (X ⧸ CFSG.oddCore X) := by
    rcases h with h | h
    · exact simple_oddCore_of_l29 h
    · exact simple_oddCore_of_l281 h
  have hcard : Nat.card (X ⧸ CFSG.oddCore X) = 360 ∨
      Nat.card (X ⧸ CFSG.oddCore X) = 265680 := by
    rcases h with h | h
    · left
      rw [← ctrQ_eq_card_of_simple hq hs]
      exact ctrQ_of_l29 hq h
    · right
      rw [← ctrQ_eq_card_of_simple hq hs]
      exact ctrQ_of_l281 hq h
  have heven : Even (Nat.card (X ⧸ CFSG.oddCore X)) := by
    rcases hcard with h | h <;> rw [h] <;> norm_num
  haveI : Group.IsPerfect ↥X := hq.1
  haveI : IsSimpleGroup (X ⧸ CFSG.oddCore X) := hs
  have hnc : ¬ IsMulCommutative (X ⧸ CFSG.oddCore X) :=
    Group.IsPerfect.not_isMulCommutative (X ⧸ CFSG.oddCore X)
  have hnonab : ∃ a b : (X ⧸ CFSG.oddCore X), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    exact hnc (IsMulCommutative.of_comm fun a b => hc a b)
  have h2 : 2 ≤ CFSG.Open.twoRank (X ⧸ CFSG.oddCore X) :=
    CFSG.Walter.two_le_twoRank (X ⧸ CFSG.oddCore X) hnonab heven
  have h2' : 2 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (X ⧸ CFSG.oddCore X)) := h2
  have hquot : CFSG.Open.pRank 2 (⊤ : Subgroup (X ⧸ CFSG.oddCore X)) =
      CFSG.Open.pRank 2 (⊤ : Subgroup ↥X) :=
    CFSG.SectionRank.pRank_quotient_eq (p := 2) (CFSG.oddCore ↥X)
      (odd_card_oddCore (H := ↥X)).not_two_dvd_nat
  rw [hquot, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 2) (H := X)] at h2'
  exact h2'

theorem sec63_involution_not_mem [Finite G] {v : G} {W : Subgroup G} (hv : orderOf v = 2)
    (hW : W ≤ centralizer ({v} : Set G)) (hq : IsQuasisimple ↥W) (h : IsL29 W ∨ IsL281 W) :
    v ∉ W := by
  intro hvW
  have hs : IsSimpleGroup (W ⧸ CFSG.oddCore W) := by
    rcases h with h | h
    · exact simple_oddCore_of_l29 h
    · exact simple_oddCore_of_l281 h
  have hvcenter : (⟨v, hvW⟩ : ↥W) ∈ Subgroup.center ↥W := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    show (g : G) * v = v * (g : G)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hW g.2)
  have hmem : (⟨v, hvW⟩ : ↥W) ∈ CFSG.oddCore ↥W := by
    rw [← center_eq_oddCore_of_simple hq hs]
    exact hvcenter
  have hodd : Odd (orderOf (⟨v, hvW⟩ : ↥W)) := odd_orderOf_of_mem_oddCore hmem
  have h2 : orderOf (⟨v, hvW⟩ : ↥W) = 2 := (Subgroup.orderOf_mk v hvW).trans hv
  rw [h2] at hodd
  exact (Nat.not_odd_iff_even.mpr even_two) hodd

theorem sec63_false_of_rank [Finite G] {v : G} {V W T : Subgroup G} (hv : orderOf v = 2)
    (hVc : IsComponentIn V (centralizer ({v} : Set G)))
    (hWc : IsComponentIn W (centralizer ({v} : Set G))) (hne : W ≠ V) (hW : IsL29 W ∨ IsL281 W)
    (hT : IsSylow2Of T (centralizer (V : Set G))) (hr : CFSG.Open.pRank 2 T ≤ 2) : False := by
  classical
  have hq : IsQuasisimple ↥W := hWc.isQuasisimple
  obtain ⟨E₄, hE₄W, hE₄, hE₄card⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 2) Nat.prime_two
      (H := W) (k := 2) (sec63_two_le_pRank hq hW)
  have hvW : v ∉ W := sec63_involution_not_mem hv hWc.le hq hW
  have hvE₄ : v ∉ E₄ := fun h => hvW (hE₄W h)
  have hcomm : ∀ e ∈ E₄, e * v = v * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hWc.le (hE₄W he))
  have hv2 : v ^ 2 = 1 := by simpa [hv] using pow_orderOf_eq_one v
  have hzv : Subgroup.zpowers v ≤ Subgroup.centralizer (E₄ : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr (fun e he => hcomm e he)
  have hAB : ∀ a ∈ E₄, ∀ b ∈ Subgroup.zpowers v, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hzv hb) a ha
  have hEsup : CFSG.Open.IsElemAbelian 2 (E₄ ⊔ Subgroup.zpowers v) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE₄ (CFSG.Open.isElemAbelian_zpowers hv2) hAB
  have hlt : E₄ < E₄ ⊔ Subgroup.zpowers v := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro hEq
    have hmem : v ∈ E₄ := by
      rw [hEq]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    exact hvE₄ hmem
  obtain ⟨k, hk⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card Nat.prime_two hEsup
  have hk3 : 3 ≤ k := by
    have hcl := CFSG.GH74.Uniqueness.SU.SU1.card_lt_of_lt hlt
    rw [hE₄card, hk] at hcl
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcl
  have h3 : 3 ≤ CFSG.Open.pRank 2 (E₄ ⊔ Subgroup.zpowers v) :=
    hk3.trans (CFSG.SectionRank.le_pRank (p := 2) (by norm_num) le_rfl hEsup hk)
  have hWV : W ≤ centralizer (V : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr
      (fun b hb => (hWc.commute_of_ne hVc hne a ha b hb).symm)
  have hzvV : Subgroup.zpowers v ≤ centralizer (V : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.mpr
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hVc.le ha))
  have hHC : E₄ ⊔ Subgroup.zpowers v ≤ centralizer (V : Set G) :=
    sup_le (hE₄W.trans hWV) hzvV
  have hH2 : IsPGroup 2 ↥(E₄ ⊔ Subgroup.zpowers v) := hEsup.isPGroup
  have hle2 : CFSG.Open.pRank 2 (E₄ ⊔ Subgroup.zpowers v) ≤ 2 :=
    sec65_pRank_le_of_sylow hT hHC hH2 hr
  omega

end CFSG.OddStandard.SmallF3.Omega
