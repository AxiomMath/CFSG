module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore
public import Certificates.Certificate10135
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Base
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Gen
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporR3E

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.KDSpor.Fi24Seven

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (J)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem card_alt7 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem alt7_noncomm : ∃ a c : ↥(alternatingGroup (Fin 7)), a * c ≠ c * a := by
  by_contra hcon
  push Not at hcon
  have hx : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 7) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hy : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 7) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have h2 := congrArg Subtype.val (hcon ⟨_, hx⟩ ⟨_, hy⟩)
  have h3 : (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) *
        (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) ≠
      (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3) *
        (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 1 2) := by decide
  exact h3 h2

theorem alt7_subgroup_data {G : Type} [Group G] {L : Subgroup G}
    (e : ↥(alternatingGroup (Fin 7)) ≃* ↥L) :
    IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧ Nat.card ↥L = 2520 := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.symm.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a, c, hac⟩ := alt7_noncomm
    exact ⟨e a, e c, fun h => hac (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [← Nat.card_congr e.toEquiv, card_alt7]

@[expose] def GoodA7 (T : Type) [Group T] : Prop := Nonempty (T ≃* ↥(alternatingGroup (Fin 7)))

@[expose] def NoRk (T : Type) [Group T] : Prop := True

theorem goodA7_of_equiv (T T' : Type) [Group T] [Group T'] (e : T ≃* T') (h : GoodA7 T) :
    GoodA7 T' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem kLevel_le_two_of_goodA7 {T : Type} [Group T] (h : GoodA7 T) : kLevel 7 T ≤ 2 := by
  obtain ⟨f⟩ := h
  exact kLevel_le_two ⟨TauCeti.CFSGIndex.alternating 7 (by norm_num), Or.inr ⟨rfl, rfl⟩,
    ⟨f.trans (MulEquiv.refl _)⟩⟩

section Row

theorem fi24Seven_parts : ∃ y ∈ CFSG.Sporadic.Fi24.J, ∃ e ∈ CFSG.Sporadic.Fi24.J, y ^ 7 = 1 ∧ y ≠ 1 ∧ e ^ 5 = 1 ∧ e ≠ 1 ∧
    e * y = y * e ∧ ∀ w : CFSG.Sporadic.Fi24.J, (w : GL (Fin 781) (ZMod 3)) = y →
      ∃ m : ℕ → CFSG.Sporadic.Fi24.J, CFSG.Sporadic.SchreierLemmas.IsMooreFamily 5 m ∧ m 1 ≠ 1 ∧
        ∀ j, 1 ≤ j → j < 6 → m j * w = w * m j := by
  obtain ⟨y, hy, e, he, h7, hy1, h5, he1, hey, P, hP, h1, h2⟩ := Certificates.certificate10135
  rw [CFSG.Sporadic.Fi24.mem_seedGrp_iff] at hy he
  refine ⟨y, hy, e, he, h7, hy1, h5, he1, hey, fun w hw => ?_⟩
  rw [← hw] at hP
  obtain ⟨s, hs, hnc, hcs⟩ := CFSG.Sporadic.Fi24.chain_D24 w P hP h1 h2
  exact moore_of_chainD24 (by norm_num) s hs hnc hcs

theorem levelOK_C7 :
    LevelOK 7 (CFSG.HardMathSupport.Dickson.I271.Fi7.C7) := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  intro I hI
  refine (false_of_glaPComponent_of_solvable (by norm_num) ?_ hI).elim
  exact isSolvable_of_card_two_mul (p := 3) (q := 7) (a := 1) (b := 3) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_C7]; norm_num)

theorem exists_levelOK_conj_Y7 :
    ∃ y : CFSG.Sporadic.Fi24.J, (∃ g : CFSG.Sporadic.Fi24.J, g * y * g⁻¹ = CFSG.HardMathSupport.Dickson.I271.Fi7.Y7) ∧
      LevelOK 7 y := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨y0, hy0, e0, he0, hy7, hy1, he5, he1, hey, hM⟩ := fi24Seven_parts
  obtain ⟨y, hyv⟩ : ∃ y : J, (y : GL (Fin 781) (ZMod 3)) = y0 := ⟨⟨y0, hy0⟩, rfl⟩
  obtain ⟨e, hev⟩ : ∃ e : J, (e : GL (Fin 781) (ZMod 3)) = e0 := ⟨⟨e0, he0⟩, rfl⟩
  have hy7' : y ^ 7 = 1 := Subtype.ext (by simp [hyv, hy7])
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [← hyv, h]; rfl)
  have he5' : e ^ 5 = 1 := Subtype.ext (by simp [hev, he5])
  have he1' : e ≠ 1 := fun h => he1 (by rw [← hev, h]; rfl)
  have hey' : e * y = y * e := Subtype.ext (by simp [hev, hyv, hey])
  have hyo : orderOf y = 7 := orderOf_eq_prime hy7' hy1'
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have heo : orderOf e = 5 := orderOf_eq_prime he5' he1'
  have h5 : 5 ∣ Nat.card (Subgroup.centralizer ({y} : Set J)) := by
    have hmem : e ∈ Subgroup.centralizer ({y} : Set J) :=
      Subgroup.mem_centralizer_singleton_iff.2 hey'
    rw [← heo, ← Subgroup.orderOf_mk e hmem]
    exact orderOf_dvd_natCard _
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Dickson.I271.Fi7.fi7_conj_class y hyo
  have hconj : IsConj y (g * y * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩
  have hgY : g * y * g⁻¹ = CFSG.HardMathSupport.Dickson.I271.Fi7.Y7 := by
    rcases hg with hg | hg
    · exact hg
    · exfalso
      rw [CFSG.Sporadic.HNOddCore.card_centralizer_of_isConj hconj, hg,
        CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_C7] at h5
      norm_num at h5
  have hcard : Nat.card (Subgroup.centralizer ({y} : Set J)) = 7 * 2520 := by
    rw [CFSG.Sporadic.HNOddCore.card_centralizer_of_isConj hconj, hgY,
      CFSG.HardMathSupport.Dickson.I271.Fi7.card_centralizer_Y7]
    norm_num
  refine ⟨y, ⟨g, hgY⟩, ?_⟩
  obtain ⟨m, hmoore, hm1, hmc⟩ := hM y hyv
  obtain ⟨-, ⟨eL⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 7)
    (by norm_num) m hmoore).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hm1⟩
  set L : Subgroup J := Subgroup.closure (m '' Set.Icc 1 (7 - 2)) with hL
  obtain ⟨hs, hnab, hcardL⟩ := alt7_subgroup_data eL
  haveI : Finite ↥(⊤ : Subgroup J) := inferInstance
  have hLC : L ≤ Subgroup.centralizer ({((⟨y, Subgroup.mem_top y⟩ : ↥(⊤ : Subgroup J)) : J)} :
      Set J) ⊓ ⊤ := by
    refine le_inf ((Subgroup.closure_le _).2 ?_) le_top
    rintro _ ⟨j, ⟨hj1, hj5⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hmc j hj1 (by omega))
  have hshape := CFSG.HardMathSupport.Dickson.I271.shapeRkAt_of_bound (Good := GoodA7)
    (Rk := NoRk) (by norm_num) goodA7_of_equiv (fun _ _ _ _ _ _ => trivial) ⊤
    ⟨y, Subgroup.mem_top y⟩ L hLC hs hnab (by rw [hcardL]; norm_num) hy1' hy7'
    (by rw [inf_top_eq, hcard, hcardL]) ⟨eL.symm⟩ trivial
  have hlev := levelOK_of_shapeRkAt (by norm_num) hshape fun _ _ h => kLevel_le_two_of_goodA7 h
  exact LevelOK.of_mulEquiv (by norm_num) Subgroup.topEquiv hlev

theorem levelOK_seven (k : CFSG.Sporadic.Fi24.J) (hk : orderOf k = 7) : LevelOK 7 k := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨y, ⟨g, hgy⟩, hy⟩ := exists_levelOK_conj_Y7
  have hY : LevelOK 7 CFSG.HardMathSupport.Dickson.I271.Fi7.Y7 := by
    have h := LevelOK.of_mulEquiv (by norm_num) (MulAut.conj g) hy
    rwa [MulAut.conj_apply, hgy] at h
  obtain ⟨c, hc⟩ := CFSG.HardMathSupport.Dickson.I271.Fi7.fi7_conj_class k hk
  have hck : LevelOK 7 (c * k * c⁻¹) := by
    rcases hc with hc | hc
    · rw [hc]; exact hY
    · rw [hc]; exact levelOK_C7
  have h := LevelOK.of_mulEquiv (by norm_num) (MulAut.conj c⁻¹) hck
  rwa [MulAut.conj_apply, inv_inv, show c⁻¹ * (c * k * c⁻¹) * c = k by group] at h

theorem kdSporRow_Fi24_seven
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    KDSporRow .Fi24Prime 7 := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  have hnc : ∃ a c : ↥J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr
  have b : ↥J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group :=
    CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some
  exact @kdSporRow_of_levelOK .Fi24Prime 7 ↥J _ hfin hs hOut b hnc (by norm_num) (by norm_num)
    levelOK_seven

end Row

end CFSG.LocalAnalysis.GLTheoremA.KDSpor.Fi24Seven

