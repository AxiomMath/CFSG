module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PThird
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63_om6p_no_third [Finite G] (h36 : Asc82Lemma36) {t : G} {L : Subgroup G}
    (hS : Sec3SettingLB G t L) {y b : G} {Vb I K : Subgroup G} (hy : orderOf y = 2)
    (hb : orderOf b = 2) (hyb : y * b = b * y) (hne : y ≠ b)
    (hVby : Vb ≤ centralizer ({y} : Set G)) (hVbb : Vb ≤ centralizer ({b} : Set G))
    (hIc : IsComponentIn I (centralizer ({b} : Set G))) (hIF : InFStar I)
    (hVbI : Vb ≤ I ⊔ CFSG.conjugate I y)
    (hrk : ∀ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E →
      E ≤ centralizer (Vb : Set G) ⊓ centralizer ({y} : Set G) → CFSG.Open.pRank 2 E ≤ 2)
    (hKc : IsComponentIn K (centralizer ({b} : Set G))) (hKF : InFStar K) :
    K = I ∨ K = CFSG.conjugate I y := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hK1, hK2⟩ := hcon
  have hyb_mem : y ∈ centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyb
  have hI'c : IsComponentIn (CFSG.conjugate I y) (centralizer ({b} : Set G)) :=
    hIc.conjugate hyb_mem
  have hK'c : IsComponentIn (CFSG.conjugate K y) (centralizer ({b} : Set G)) :=
    hKc.conjugate hyb_mem
  have hK'F : InFStar (CFSG.conjugate K y) := hKF.conjugate y
  have hK'I : CFSG.conjugate K y ≠ I := by
    intro h
    apply hK2
    have hc := congrArg (fun H : Subgroup G => CFSG.conjugate H y) h
    rwa [conjugate_conjugate_of_orderOf_eq_two hy] at hc
  have hK'I' : CFSG.conjugate K y ≠ CFSG.conjugate I y := by
    intro h
    apply hK1
    have hc := congrArg (fun H : Subgroup G => CFSG.conjugate H y) h
    rwa [conjugate_conjugate_of_orderOf_eq_two hy,
      conjugate_conjugate_of_orderOf_eq_two hy] at hc
  have hbadK : Bad63 K b := ⟨hb, hKc, hKF, I, fun h => hK1 h.symm, hIc, hIF⟩
  have hKs : IsL29 K ∨ IsL281 K := sec63_bad_shape h36 hS hbadK
  have hcommKI : ∀ a ∈ K, ∀ c ∈ I, a * c = c * a := hKc.commute_of_ne hIc hK1
  have hcommKI' : ∀ a ∈ K, ∀ c ∈ CFSG.conjugate I y, a * c = c * a :=
    hKc.commute_of_ne hI'c hK2
  have hIcentK : I ≤ centralizer (K : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommKI a ha c hc
  have hI'centK : CFSG.conjugate I y ≤ centralizer (K : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommKI' a ha c hc
  have hVbcentK : Vb ≤ centralizer (K : Set G) :=
    hVbI.trans (sup_le hIcentK hI'centK)
  have hKcentVb : K ≤ centralizer (Vb : Set G) :=
    Subgroup.le_centralizer_iff.mp hVbcentK
  have hcommK'I : ∀ a ∈ CFSG.conjugate K y, ∀ c ∈ I, a * c = c * a :=
    hK'c.commute_of_ne hIc hK'I
  have hcommK'I' : ∀ a ∈ CFSG.conjugate K y, ∀ c ∈ CFSG.conjugate I y,
      a * c = c * a :=
    hK'c.commute_of_ne hI'c hK'I'
  have hIcentK' : I ≤ centralizer (CFSG.conjugate K y : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommK'I a ha c hc
  have hI'centK' : CFSG.conjugate I y ≤ centralizer (CFSG.conjugate K y : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact hcommK'I' a ha c hc
  have hVbcentK' : Vb ≤ centralizer (CFSG.conjugate K y : Set G) :=
    hVbI.trans (sup_le hIcentK' hI'centK')
  have hK'centVb : CFSG.conjugate K y ≤ centralizer (Vb : Set G) :=
    Subgroup.le_centralizer_iff.mp hVbcentK'
  obtain ⟨E, hEea, hEcard, hEcentVb, hEcenty, hEcentb, hbE⟩ : ∃ E : Subgroup G,
      CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E ∧
      E ≤ centralizer (Vb : Set G) ∧ E ≤ centralizer ({y} : Set G) ∧
      E ≤ centralizer ({b} : Set G) ∧ b ∉ E := by
    by_cases hK'ne : CFSG.conjugate K y ≠ K
    · obtain ⟨E, hea, hcard, hle, hcent, hbE⟩ :=
        sec63P_third_swap hy hb hyb hKc hKs hK'ne
      exact ⟨E, hea, hcard, hle.trans (sup_le hKcentVb hK'centVb), hcent,
        hle.trans (sup_le hKc.le hK'c.le), hbE⟩
    · push Not at hK'ne
      have hzy_b : zpowers y ≤ centralizer ({b} : Set G) :=
        Subgroup.zpowers_le.mpr hyb_mem
      by_cases hyK : y ∈ zpowers b ⊔ K
      · obtain ⟨E, hea, hcard, hle, hcent, hbE⟩ :=
          sec63P_third_in hy hb hyb hne hKc hKs hyK
        exact ⟨E, hea, hcard, hle.trans hKcentVb, hcent, hle.trans hKc.le, hbE⟩
      · obtain ⟨E, hea, hcard, hle, hcent, hbE⟩ :=
          sec63P_third_out hy hb hyb hKc hKs hK'ne hyK
        have hycentVb : y ∈ centralizer (Vb : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          exact Subgroup.mem_centralizer_singleton_iff.mp (hVby hv)
        have hzy : zpowers y ≤ centralizer (Vb : Set G) := Subgroup.zpowers_le.mpr hycentVb
        exact ⟨E, hea, hcard, hle.trans (sup_le hKcentVb hzy), hcent,
          hle.trans (sup_le hKc.le hzy_b), hbE⟩
  have hEcentb_comm : ∀ e ∈ E, e * b = b * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hEcentb he)
  obtain ⟨hE'ea, hE'rank⟩ := sec63P_rank_ge_three hEea hEcard hb hEcentb_comm hbE
  have hbcentVb : b ∈ centralizer (Vb : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_singleton_iff.mp (hVbb hv)
  have hzybVb : zpowers b ≤ centralizer (Vb : Set G) := Subgroup.zpowers_le.mpr hbcentVb
  have hbcenty : b ∈ centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyb.symm
  have hzyb : zpowers b ≤ centralizer ({y} : Set G) := Subgroup.zpowers_le.mpr hbcenty
  have hE'le : E ⊔ zpowers b ≤ centralizer (Vb : Set G) ⊓ centralizer ({y} : Set G) :=
    le_inf (sup_le hEcentVb hzybVb) (sup_le hEcenty hzyb)
  have hcontr := hrk (E ⊔ zpowers b) hE'ea hE'le
  omega

end CFSG.OddStandard.SmallF3.Omega
