module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.AltDownPerm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS05I1416Arith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FPBasic
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltCenter

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)

open Equiv Equiv.Perm CFSG.LocalAnalysis.GLTheoremA.AltDown

theorem up1415_altExactRoot {n p : ℕ} (hn : 5 ≤ n) (hp : p.Prime) (hp2 : p ≠ 2)
    {α : MulAut (alternatingGroup (Fin n))} (hα : α ^ p = 1) (hα1 : α ≠ 1)
    {I : Subgroup (alternatingGroup (Fin n))} (hI : GLAPComponent p (fixSubgroup α) I) :
    ∃ m k : ℕ, 5 ≤ m ∧ 0 < k ∧ n = m + k * p ∧
      Nonempty (PSimple p I ≃* alternatingGroup (Fin m)) := by
  obtain ⟨x, hx1, hxp, rfl⟩ := exists_conj_of_alt hn hp hp2 hα hα1
  have hσp : (x : Perm (Fin n)) ^ p = 1 := by simpa using congrArg Subtype.val hxp
  have hσ1 : (x : Perm (Fin n)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hIF := le_range_ofSubtype_of_glaPComponent hp hp2 hxp hI
  obtain ⟨m, hm⟩ : ∃ m, ((x : Perm (Fin n)).support)ᶜ.card = m := ⟨_, rfl⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : ((x : Perm (Fin n)).support).card + m = n := by
    have h := Finset.card_compl ((x : Perm (Fin n)).support)
    rw [Fintype.card_fin, hm] at h
    have h2 : ((x : Perm (Fin n)).support).card ≤ n := by
      simpa using Finset.card_le_univ ((x : Perm (Fin n)).support)
    omega
  have hmn : m ≤ n := by omega
  have hmod : m ≡ n [MOD p] := by
    have h := Equiv.Perm.card_compl_support_modEq (n := 1) (σ := (x : Perm (Fin n)))
      (by rw [pow_one]; exact hσp)
    rw [Fintype.card_fin, hm] at h
    exact h
  obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hmn).1 hmod
  have hpos : p ≤ ((x : Perm (Fin n)).support).card := le_card_support_of_pow_eq_one hp hσp hσ1
  have hkpos : 0 < k := by
    have hp_two := hp.two_le
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; omega
    · exact h0
  have hnk : n = m + k * p := by rw [Nat.mul_comm]; omega
  obtain ⟨e⟩ := nonempty_range_ofSubtype_equiv ((x : Perm (Fin n)).support)ᶜ m hm
  have hIdvd : Nat.card I ∣ m.factorial := by
    have h1 := Subgroup.card_dvd_of_le hIF
    rw [Nat.card_congr e.toEquiv] at h1
    exact h1.trans (by simpa using natCard_alternatingGroup_dvd_factorial (Fin m))
  haveI : Nontrivial ↥I := nontrivial_of_glaPComponent hp hI
  have hm5 : 5 ≤ m := by
    by_contra hlt
    haveI : Group.IsPerfect ↥I := Subgroup.isPerfect_iff.2 (glaPComponent_perfect hI)
    exact false_of_isPerfect_of_card_dvd_twentyFour
      (hIdvd.trans (factorial_dvd_twentyFour (not_le.1 hlt)))
  have hm5' : 5 ≤ Nat.card (Fin m) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hm5
  haveI : IsSimpleGroup (alternatingGroup (Fin m)) := alternatingGroup.isSimpleGroup hm5'
  haveI : IsSimpleGroup ↥(alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range :=
    e.isSimpleGroup
  have hFC : (alternatingGroup.ofSubtype ((x : Perm (Fin n)).support)ᶜ).range ≤
      fixSubgroup (MulAut.conj x) := fun k hk => mem_fixSubgroup_conj.2
        (Subtype.ext (commute_of_mem_range_ofSubtype_compl hk).eq)
  have hIeq := eq_of_isSubnormal_of_isSimpleGroup (glaPComponent_of_le hp hI hIF hFC).2.1
    ((Subgroup.nontrivial_iff_ne_bot I).1 inferInstance)
  exact ⟨m, k, hm5, hkpos, hnk, nonempty_pSimple_equiv hp hI
    (alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega))
    ((MulEquiv.subgroupCongr hIeq).trans e)⟩

theorem up1415_alt_index_eq {m m' : ℕ} (hm : 5 ≤ m) (hm' : 5 ≤ m')
    (e : alternatingGroup (Fin m) ≃* alternatingGroup (Fin m')) : m = m' := by
  have hc : Nat.card (alternatingGroup (Fin m)) = Nat.card (alternatingGroup (Fin m')) :=
    Nat.card_congr e.toEquiv
  rw [natCard_alt_fin m (by omega), natCard_alt_fin m' (by omega)] at hc
  have h2 : ∀ k : ℕ, 2 ≤ k → k.factorial = 2 * (k.factorial / 2) := fun k hk =>
    (Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) hk)).symm
  have hfac : m.factorial = m'.factorial := by
    rw [h2 m (by omega), h2 m' (by omega), hc]
  exact (Nat.factorial_inj (by omega : 1 < m)).1 hfac

theorem up1415_pSimple_alt {G : Type} [Group G] [Finite G] {p m : ℕ} {J : Subgroup G} (hm : 5 ≤ m)
    (h : IsAltPType p J m) : Nonempty (PSimple p J ≃* alternatingGroup (Fin m)) := by
  obtain ⟨e⟩ := h
  have hZ : Subgroup.center (alternatingGroup (Fin m)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  exact ⟨(QuotientGroup.congr (Subgroup.center (PQuot p J)) (Subgroup.center (alternatingGroup (Fin m)))
    e (Subgroup.map_center_eq e)).trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot)⟩

theorem up1415_isAltPType_of_pSimple {G : Type} [Group G] [Finite G] {p n : ℕ} {X K : Subgroup G}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : GLAPComponent p X K) (hn : 8 ≤ n)
    (e : PSimple p K ≃* alternatingGroup (Fin n)) : IsAltPType p K n := by
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hcen : Subgroup.center (PQuot p K) = ⊥ :=
    CFSG.ComponentClassification.RankTwoAlt.center_eq_bot_of_odd hq.1 hn e
      (FP.odd_card_center_pQuot hp hp2 K)
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm.trans e⟩

section AltCerts


theorem up1415_alt_not_chev {S : Type} [Group S] {m : ℕ} (hm : 9 ≤ m)
    (e : S ≃* alternatingGroup (Fin m)) {r : ℕ} (hr : r.Prime) : ¬ IsChevSimple r S := by
  intro hC
  by_cases hr2 : r = 2
  · subst hr2
    exact not_chev2_alt (by omega) ⟨by omega, by omega, by omega⟩ e hC
  · rcases hC with ⟨i, hi, ⟨f⟩⟩ | h
    · cases i with
      | cyclic _ _ => exact hi.elim
      | alternating _ _ => exact hi.elim
      | sporadic _ => exact hi.elim
      | lie d =>
        obtain ⟨t, n, p', f', -, -, hadm, hY⟩ := small_odd_lie hr hr2 (d := d) hi f
        exact CFSG.OddStandard.AltStdSec.false_of_lieModel_alt
          CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hm e hadm hY
    · exact not_chev2_alt (by omega) ⟨by omega, by omega, by omega⟩ e (i1416_amb_chev2 hr2 h)

end AltCerts

end CFSG.LocalAnalysis.GLTheoremA
