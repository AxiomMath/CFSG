module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi24FiveBound
public import Certificates.Certificate10136
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelSporFi24Seven
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416QSporRowsA
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder181440

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 M)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [local instance] CFSG.Sporadic.Fi24.rAction

@[expose] def GoodA9 (T : Type) [Group T] : Prop := Nonempty (T ≃* ↥(alternatingGroup (Fin 9)))

theorem goodA9_of_equiv (T T' : Type) [Group T] [Group T'] (e : T ≃* T') (h : GoodA9 T) :
    GoodA9 T' := by
  obtain ⟨f⟩ := h
  exact ⟨e.symm.trans f⟩

theorem not_isChevSimple_of_card_181440
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (q : ℕ) {T : Type} [Group T]
    [Finite T] (hc : Nat.card T = 181440) : ¬ IsChevSimple q T := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d => exact I1416Rows.Order181440.lieOrderFormula_ne_181440 d.2 ((hb d T ⟨e⟩).symm.trans hc)
    | _ => exact hi.elim
  · cases i with
    | lie d => exact I1416Rows.Order181440.lieOrderFormula_ne_181440 d.2 ((hb d T ⟨e⟩).symm.trans hc)
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hc] at hcn
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num [Nat.factorial] at hcn
    | _ => exact hi.elim

theorem card_alt9 : Nat.card ↥(alternatingGroup (Fin 9)) = 181440 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.card_eq_fintype_card, Nat.factorial]

theorem alt9_noncomm : ∃ a c : ↥(alternatingGroup (Fin 9)), a * c ≠ c * a := by
  by_contra hcon
  push Not at hcon
  have hx : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have hy : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) ∈ alternatingGroup (Fin 9) :=
    Equiv.Perm.mem_alternatingGroup.2 (by decide)
  have h2 := congrArg Subtype.val (hcon ⟨_, hx⟩ ⟨_, hy⟩)
  have h3 : (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) *
        (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) ≠
      (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 2 3) *
        (Equiv.swap (0 : Fin 9) 1 * Equiv.swap 1 2) := by decide
  exact h3 h2

theorem card_of_goodA9 {T : Type} [Group T] (h : GoodA9 T) : Nat.card T = 181440 := by
  obtain ⟨f⟩ := h
  exact (Nat.card_congr f.toEquiv).trans card_alt9

theorem not_isChevSimple_of_goodA9 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    (q : ℕ) {T : Type} [Group T] (h : GoodA9 T) : ¬ IsChevSimple q T := by
  haveI : Finite T := Nat.finite_of_card_ne_zero (by rw [card_of_goodA9 h]; norm_num)
  exact not_isChevSimple_of_card_181440 hb q (card_of_goodA9 h)

theorem alt9_data {G : Type} [Group G] {L : Subgroup G}
    (e : ↥(alternatingGroup (Fin 9)) ≃* ↥L) :
    IsSimpleGroup ↥L ∧ (∃ a b : ↥L, a * b ≠ b * a) ∧ Nat.card ↥L = 181440 := by
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  refine ⟨e.symm.isSimpleGroup, ?_, ?_⟩
  · obtain ⟨a, c, hac⟩ := alt9_noncomm
    exact ⟨e a, e c, fun h => hac (e.injective (by rw [map_mul, map_mul]; exact h))⟩
  · rw [← Nat.card_congr e.toEquiv, card_alt9]

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi24.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24FiveNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24MooreNative
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Five
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Moore
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Sporadic.Fi24 (R J JR jR tR cls D24 M)

attribute [local instance] CFSG.Sporadic.Fi24.rAction


theorem crow_of_centShape {name : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → Chev2Rows.CTypeOK p T) : Chev2Rows.CRow name p :=
  Chev2Rows.crow_of_model hOut b hnc fun _ hk => Chev2Rows.ccompOK_of_centShape hp h hG hk

section Shape


theorem shapeRkAt_of_le {w : CFSG.Sporadic.Fi24.J} (hw1 : w ≠ 1) (hw5 : w ^ 5 = 1) {L : Subgroup CFSG.Sporadic.Fi24.J}
    (hLC : L ≤ Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi24.J)) (e : ↥(alternatingGroup (Fin 9)) ≃* ↥L)
    (hbound : Nat.card ↥(Subgroup.centralizer ({w} : Set CFSG.Sporadic.Fi24.J)) ≤ 5 * 181440) :
    CFSG.HardMathSupport.Dickson.I271.ShapeRkAt 5 GoodA9 KDSpor.Fi24Seven.NoRk w := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨hs, hnab, hcardL⟩ := alt9_data e
  have hLC' : L ≤ Subgroup.centralizer ({((⟨w, Subgroup.mem_top w⟩ : ↥(⊤ : Subgroup J)) : J)} :
      Set J) ⊓ ⊤ := le_inf hLC le_top
  have hshape := CFSG.HardMathSupport.Dickson.I271.shapeRkAt_of_bound (Good := GoodA9)
    (Rk := KDSpor.Fi24Seven.NoRk) Nat.prime_five goodA9_of_equiv (fun _ _ _ _ _ _ => trivial) ⊤
    ⟨w, Subgroup.mem_top w⟩ L hLC' hs hnab (by rw [hcardL]; norm_num) hw1 hw5
    (by rw [inf_top_eq, hcardL]; exact hbound) ⟨e.symm⟩ trivial
  exact CFSG.HardMathSupport.Dickson.I271.ShapeRkAt.of_equiv Nat.prime_five goodA9_of_equiv
    (fun _ _ _ _ _ _ => trivial) Subgroup.topEquiv hshape

theorem fi24FiveMoore_parts : ∃ e ∈ CFSG.Sporadic.Fi24.J, ∃ f ∈ CFSG.Sporadic.Fi24.J, e ^ 5 = 1 ∧ e ≠ 1 ∧ f ^ 5 = 1 ∧ e * f = f * e ∧
    (∀ k < 5, f ≠ e ^ k) ∧ ∀ a < 5, ∀ b < 5, a + b ≠ 0 → ∀ w : CFSG.Sporadic.Fi24.J,
      (w : GL (Fin 781) (ZMod 3)) = e ^ a * f ^ b →
      Nat.card (CFSG.Sporadic.Fi24.ptFix (w : GL (Fin 781) (ZMod 3))) = 36 ∧
      ∃ m : ℕ → CFSG.Sporadic.Fi24.J, CFSG.Sporadic.SchreierLemmas.IsMooreFamily 7 m ∧ m 1 ≠ 1 ∧
        ∀ j, 1 ≤ j → j < 8 → m j * w = w * m j := by
  obtain ⟨e, he, f, hf, h5e, he1, h5f, hc, hp, hg⟩ := Certificates.certificate10136
  rw [CFSG.Sporadic.Fi24.mem_seedGrp_iff] at he hf
  refine ⟨e, he, f, hf, h5e, he1, h5f, hc, hp, fun a ha b hb hab w hw => ?_⟩
  obtain ⟨h36, P, hP, h1, h2⟩ := hg a ha b hb hab
  rw [← hw] at h36 hP
  refine ⟨h36, ?_⟩
  obtain ⟨s, hs, hnc, hcs⟩ := CFSG.Sporadic.Fi24.chain_D24 w P hP h1 h2
  exact moore_of_chainD24 (by norm_num) s hs hnc hcs

theorem centShapeRk_five :
    CFSG.HardMathSupport.Dickson.I271.CentShapeRk 5 GoodA9 KDSpor.Fi24Seven.NoRk CFSG.Sporadic.Fi24.J := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨e, he, f, hf, h5e, he1, h5f, hcomm, hpow, hcM⟩ := fi24FiveMoore_parts
  intro s hs1 hs5
  have hs : orderOf s = 5 := orderOf_eq_prime hs5 hs1
  obtain ⟨g, a, ha, b, hb, hab, hw⟩ := exists_conj_sylow5 J he hf h5e he1 h5f hcomm hpow
    (m := 50208228367626468851712) (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num) (by norm_num) hs
  have hwo : orderOf (g⁻¹ * s * g) = 5 := by rw [CommutingPair.orderOf_inv_mul_mul, hs]
  obtain ⟨h36, m, hmoore, hm1, hmc⟩ := hcM a ha b hb hab _ hw
  set w := g⁻¹ * s * g with hwdef
  have hw1 : w ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hwo; exact absurd hwo (by norm_num)
  have hw5 : w ^ 5 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one w
  obtain ⟨-, ⟨eL⟩⟩ := (CFSG.Sporadic.SchreierLemmas.moore_alternating_presentation (n := 9)
    (by norm_num) m hmoore).2.2.2.2.2 (by norm_num) ⟨1, ⟨le_rfl, by norm_num⟩, hm1⟩
  have hLC : Subgroup.closure (m '' Set.Icc 1 (9 - 2)) ≤ Subgroup.centralizer ({w} : Set J) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨j, ⟨hj1, hj7⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hmc j hj1 (by omega))
  have hshape := shapeRkAt_of_le hw1 hw5 hLC eL
    ((Fi24FiveBound.card_centralizer_le_of_ncard w hwo
      ((Fi24FiveBound.ncard_fixD24_jR w).trans h36)).trans (by norm_num))
  have h := CFSG.HardMathSupport.Dickson.I271.ShapeRkAt.of_equiv Nat.prime_five goodA9_of_equiv
    (fun _ _ _ _ _ _ => trivial) (MulAut.conj g) hshape
  rwa [MulAut.conj_apply, hwdef, show g * (g⁻¹ * s * g) * g⁻¹ = s by group] at h

end Shape

section Rows


theorem fi24_model (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    Finite ↥CFSG.Sporadic.Fi24.J ∧ IsSimpleGroup ↥CFSG.Sporadic.Fi24.J ∧ (∃ a c : ↥CFSG.Sporadic.Fi24.J, a * c ≠ c * a) ∧
      Nonempty (↥CFSG.Sporadic.Fi24.J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) := by
  have hfin : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup ↥J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card ↥J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  exact ⟨hfin, hs, @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple ↥J _ hfin hs hpr,
    ⟨CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some⟩⟩

theorem row_Fi24_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416Rows.I1416SporRow .Fi24Prime 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  exact @I1416Rows.row_of_centShape .Fi24Prime 5 ↥J _ hfin hs hOut b hnc Nat.prime_five
    (by norm_num) _ (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk centShapeRk_five)
    fun _ _ h => I1416Rows.typeOK_of_not_chev (not_isChevSimple_of_goodA9 hb 2 h)

theorem qrow_Fi24_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416QRows.I1416QRow .Fi24Prime 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  exact @I1416QRows.qrow_of_centShape .Fi24Prime 5 ↥J _ hfin hs hOut b hnc Nat.prime_five
    (by norm_num) _ (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk centShapeRk_five)
    fun _ _ h => I1416QRows.qtypeOK_of_not_chev fun q _ _ _ => not_isChevSimple_of_goodA9 hb q h

theorem crow_Fi24_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    Chev2Rows.CRow .Fi24Prime 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  exact @crow_of_centShape .Fi24Prime 5 ↥J _ hfin hs hOut b hnc Nat.prime_five _
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk centShapeRk_five)
    fun _ _ h hc => (not_isChevSimple_of_goodA9 hb 2 h hc).elim

end Rows

end CFSG.LocalAnalysis.GLTheoremA.Fi24FiveRows
