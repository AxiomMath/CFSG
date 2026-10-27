module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRows
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.McLThree
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.ONThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.McL
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporAutSylow

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

theorem srow_three_of_perm {name : TauCeti.SporadicName} {n : ℕ}
    {P : Subgroup (Equiv.Perm (Fin n))}
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : ↥P ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hs : IsSimpleGroup ↥P)
    (hcard : ¬ (Nat.card ↥P).Prime)
    (hsmall : ∀ x ∈ P, orderOf x = 3 →
      Nat.card ↥(Subgroup.centralizer ({x} : Set (Equiv.Perm (Fin n))) ⊓ P) < 60) :
    SRow name 3 := by
  set G := (TauCeti.CFSGIndex.sporadic name).Group
  haveI : IsSimpleGroup G := (MulEquiv.isSimpleGroup_congr b).1 hs
  haveI : Finite G := Finite.of_equiv _ b.toEquiv
  have hcG : Nat.card G = Nat.card ↥P := (Nat.card_congr b.toEquiv).symm
  have hnc : ∃ a c : G, a * c ≠ c * a :=
    CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hcG]; exact hcard)
  refine srow_of_model hOut (MulEquiv.refl _) hnc fun x hx => scompOK_of_solvable Nat.prime_three
    (CFSG.GroupTheory.groups_order_below_sixty_solvable ?_)
  rw [KDSpor.card_centralizer_of_model b x]
  refine hsmall _ (b.symm x).2 ?_
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_M11_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    SRow .M11 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  exact srow_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M11]; norm_num) fun x hx h3 =>
    KDSpor.check_card_lt m11S3Data rep_m11A rep_m11B Certificates.certificate13511.1
      (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_M12_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    SRow .M12 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  exact srow_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M12]; norm_num) fun x hx h3 =>
    KDSpor.check_card_lt m12S3Data rep_m12A rep_m12B Certificates.certificate13511.2.1
      (by decide) x hx h3

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem srow_M22_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) :
    SRow .M22 3 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  exact srow_three_of_perm hOut b CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    (by rw [CFSG.Sporadic.Mathieu.card_M22]; norm_num) fun x hx h3 =>
    KDSpor.check_card_lt m22S3Data rep_m22A rep_m22B Certificates.certificate13511.2.2.1
      (by decide) x hx h3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

variable {n p : ℕ} {P R : Subgroup (Equiv.Perm (Fin n))}

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

theorem srow_of_centShape {name : TauCeti.SporadicName} {p : ℕ} {Q : Type} [Group Q]
    [Finite Q] [IsSimpleGroup Q]
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic name).Group) (hnc : ∃ a c : Q, a * c ≠ c * a)
    (hp : p.Prime) (_hp2 : p ≠ 2) {Good : ∀ (T : Type) [Group T], Prop}
    (h : CFSG.HardMathSupport.Dickson.I271.CentShape p Good Q)
    (hG : ∀ (T : Type) [Group T], Good T → STypeOK p T) : SRow name p :=
  srow_of_model hOut b hnc fun _ hk => scompOK_of_centShape hp h hG hk

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor
open scoped commutatorElement

set_option maxRecDepth 100000 in
theorem srow_ON_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .ONan 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .ONan) = 460815505920 :=
    CFSG.Sporadic.ON.card_ON
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    Finite.of_equiv _ CFSG.ONSchreier.onEquivPv.symm.toEquiv
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .ONan) :=
    CFSG.Sporadic.ON.isSimpleGroup_ON
  exact srow_of_centShape hOut (hbr .ONan).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num)
    (CFSG.HardMathSupport.Dickson.I271.CentShape.of_centShapeRk
      CFSG.HardMathSupport.Dickson.I271.onThree_centShapeRk)
    fun _ _ h => stypeOK_A6 hb h.2.some

theorem srow_McL_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    SRow .McL 3 := by
  have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .McL) = 898128000 :=
    CFSG.Sporadic.McL.card_McL
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    Nat.finite_of_card_ne_zero (by rw [hc]; norm_num)
  haveI : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .McL) :=
    CFSG.Sporadic.McL.isSimpleGroup_McL
  have hsh := CFSG.HardMathSupport.Dickson.I271.mcl_constrainedShape_three
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.oPrimeCoreTrivialAt_McL
  exact srow_of_centShape (Good := fun _ _ => False) hOut (hbr .McL).some
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple (by rw [hc]; norm_num))
    Nat.prime_three (by norm_num) (fun k hk1 hk3 => Or.inl (hsh k hk1 hk3))
    fun _ _ h => h.elim

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
