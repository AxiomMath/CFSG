module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporTables
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1116d
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenFinal
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporOrder181440
public import CFSG.HardMathSupport.Dickson.BMRows.M13B
import Mathlib.Tactic.Simproc.Factors
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables2

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1116c
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables (CentTypes SporTypes typeInv_card sporTypes_of_model)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple PSimple ambiguousChev)

set_option linter.unusedSectionVars false

section Bridge

theorem sporDownRow_of_sporTypes {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    {Good : ∀ (T : Type) [Group T], Prop} (h : SporTypes p Good s)
    (hG : ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
      p ∣ Nat.card T → Good T → DownTypeOK s p T) :
    SporDownRow s p := by
  intro S _ _ _ e x hx I hI
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab hp hI
  exact hG _ hsI hnab (Claims1116d.prime_dvd_card_pSimple hp hI) (h S e x hx I hI)

theorem not_isChevSimple_of_card_181440 (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {T : Type} [Group T] [Finite T] (hc : Nat.card T = 181440) (q : ℕ) : ¬ IsChevSimple q T := by
  rintro (⟨i, hi, ⟨e⟩⟩ | ⟨i, hi, ⟨e⟩⟩)
  · cases i with
    | lie d =>
      exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order181440.lieOrderFormula_ne_181440 d.2
        ((hb d T ⟨e⟩).symm.trans hc)
    | _ => exact hi.elim
  · cases i with
    | lie d =>
      exact CFSG.LocalAnalysis.GLTheoremA.I1416Rows.Order181440.lieOrderFormula_ne_181440 d.2
        ((hb d T ⟨e⟩).symm.trans hc)
    | alternating n hn5 =>
      simp only [ambiguousChev] at hi
      have hcn : Nat.card T = n.factorial / 2 :=
        (Nat.card_congr e.toEquiv).trans
          (CFSG.HardMathSupport.Solomon.Coordinator.YS08.L3Char.card_alt n (by omega))
      rw [hc] at hcn
      rcases hi with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num [Nat.factorial] at hcn
    | _ => exact hi.elim

theorem le_of_prime_dvd {r N b : ℕ} (hr : r.Prime) (hd : r ∣ N) (hN : N ≠ 0)
    (h : ∀ q ∈ N.primeFactorsList, q ≤ b) : r ≤ b :=
  h r ((Nat.mem_primeFactorsList hN).2 ⟨hr, hd⟩)

theorem downCompOK_of_conj_pow {s : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime) {Q : Type} [Group Q]
    [Finite Q] {t x m : Q} {k : ℕ} (ht : orderOf t = p) (hk : t ^ k ≠ 1) (hm : m * x * m⁻¹ = t ^ k)
    (h : DownCompOK s p t) : DownCompOK s p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : DownCompOK s p (t ^ k) := downCompOK_of_centralizer_eq
    (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.centralizer_pow_eq_of_prime ht hk).symm h
  have h2 := downCompOK_of_mulEquiv hp (MulAut.conj m⁻¹) h1
  have hx : (MulAut.conj m⁻¹) (t ^ k) = x := by
    rw [MulAut.conj_apply, ← hm]
    group
  rwa [hx] at h2

theorem pow_ne_one_of_mod {Q : Type} [Group Q] {p : ℕ} {t : Q} (ht : orderOf t = p) {k : ℕ} (hk : k % p ≠ 0) :
    t ^ k ≠ 1 := fun h1 => hk (Nat.mod_eq_zero_of_dvd (ht ▸ orderOf_dvd_of_pow_eq_one h1))

end Bridge

section ResidualsFi23

@[expose] def Fi23FiveNoA6 : Prop :=
  ∀ x : CFSG.Blueprint.NativeSporadic.Carrier .Fi23, orderOf x = 5 →
    ∀ I : Subgroup (CFSG.Blueprint.NativeSporadic.Carrier .Fi23),
      GLAPComponent 5 (Subgroup.centralizer
        ({x} : Set (CFSG.Blueprint.NativeSporadic.Carrier .Fi23))) I →
      Nat.card (PSimple 5 I) ≠ 360

end ResidualsFi23

section ResidualsB


@[expose] def BSevenNoL28 : Prop :=
  ∀ I : Subgroup CFSG.Blueprint.NativeSporadic.B,
    GLAPComponent 7 (Subgroup.centralizer
      ({CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven} : Set CFSG.Blueprint.NativeSporadic.B)) I →
      Nat.card (PSimple 7 I) ≠ 504

end ResidualsB

section ResidualsM

open CFSG.AGLEmbedding.Norton.MON5_7 (gw)

@[expose] def MElevenDown : Prop :=
  DownCompOK .M 11 (gw CFSG.AGLEmbedding.Norton.Gen11.gen11W0)

@[expose] def MThirteenADown : Prop :=
  DownCompOK .M 13 (gw CFSG.AGLEmbedding.Norton.MON11_13.thirteenX)

@[expose] def MThirteenBDown : Prop :=
  DownCompOK .M 13 (gw CFSG.AGLEmbedding.Norton.GenD13.genD13W1)

end ResidualsM

section S_sporDownRow_B_three_of_types


theorem sporDownRow_B_three_of_types (h : SporTypes 3 (fun T _ => Nat.card T = 64561751654400) .B) :
    SporDownRow .B 3 :=
  sporDownRow_of_sporTypes Nat.prime_three h fun _ _ _ _ _ _ hT =>
    downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hT (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))

end S_sporDownRow_B_three_of_types

section S_sporDownRow_M_three_of_types


theorem sporDownRow_M_three_of_types
    (h : SporTypes 3 (fun T _ => Nat.card T = 1255205709190661721292800 ∨ Nat.card T = 90745943887872000) .M) :
    SporDownRow .M 3 := by
  refine sporDownRow_of_sporTypes Nat.prime_three h fun T _ _ _ _ _ hT => ?_
  rcases hT with hT | hT
  · exact downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hT (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))
  · exact downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hT (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))

end S_sporDownRow_M_three_of_types

section S_sporDownRow_B_five_of_types


theorem sporDownRow_B_five_of_types (h : SporTypes 5 (fun T _ => Nat.card T = 44352000) .B) :
    SporDownRow .B 5 :=
  sporDownRow_of_sporTypes Nat.prime_five h fun _ _ _ _ _ _ hT =>
    downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hT (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))


theorem sporDownRow_M_five_of_types (h : SporTypes 5 (fun T _ => Nat.card T = 273030912000000) .M) :
    SporDownRow .M 5 :=
  sporDownRow_of_sporTypes Nat.prime_five h fun _ _ _ _ _ _ hT =>
    downTypeOK_of_not_chev (not_isChevSimple_of_card_bound hT (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))

end S_sporDownRow_B_five_of_types

section S_sporDownRow_B_three


theorem sporDownRow_B_three (hB3 : CFSG.HardMathSupport.Dickson.I271.TabBThreeBNoComp) : SporDownRow .B 3 :=
  sporDownRow_B_three_of_types (SporTables.sporTypes_B_three CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hB3)

end S_sporDownRow_B_three

section S_sporDownRow_M_three


theorem sporDownRow_M_three (hB : CFSG.HardMathSupport.Dickson.I271.M3ResBNoComp) : SporDownRow .M 3 :=
  sporDownRow_M_three_of_types (SporTables.sporTypes_M_three CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hB)

end S_sporDownRow_M_three

section S_sporDownRow_B_five


theorem sporDownRow_B_five
    (hB : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp) : SporDownRow .B 5 :=
  sporDownRow_B_five_of_types (SporTables.sporTypes_B_five_of_noComp
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hB)

end S_sporDownRow_B_five

section S_sporDownRow_M_five


theorem sporDownRow_M_five
    (hB : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)) :
    SporDownRow .M 5 :=
  sporDownRow_M_five_of_types (SporTables.sporTypes_M_five CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hB)

end S_sporDownRow_M_five

section S_sporDownRow_Fi24_five


theorem sporDownRow_Fi24_five (h : SporTables.Fi24FiveA9) : SporDownRow .Fi24Prime 5 := by
  have hS := SporTables.sporTypes_Fi24_five CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group h
  refine sporDownRow_of_sporTypes Nat.prime_five hS fun T _ _ _ _ _ hT => ?_
  exact downTypeOK_of_not_chev fun q _ _ _ =>
    not_isChevSimple_of_card_181440 CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hT q

end S_sporDownRow_Fi24_five

section S_sporDownRow_Fi23_five


set_option maxRecDepth 100000 in
theorem sporDownRow_Fi23_five (h : Fi23FiveNoA6) : SporDownRow .Fi23 5 := by
  haveI hJ : Finite CFSG.Sporadic.Fi23.J :=
    Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi23.card_J]; norm_num)
  haveI hf : Finite CFSG.Blueprint.NativeSporadic.Fi23 :=
    Finite.of_equiv CFSG.Sporadic.Fi23.J
      (CFSG.Sporadic.Fi23.fi23EquivJ :
        CFSG.Blueprint.NativeSporadic.Fi23 ≃* CFSG.Sporadic.Fi23.J).symm.toEquiv
  have hC1 : CentTypes 5 (fun T _ => Nat.card T ∣ 241920 ∧ Nat.card T ≤ 5040)
      CFSG.Blueprint.NativeSporadic.Fi23 :=
    @SporTables.CentTypes.of_equiv 5 Nat.prime_five (fun T _ => Nat.card T ∣ 241920 ∧ Nat.card T ≤ 5040)
      (typeInv_card fun N => N ∣ 241920 ∧ N ≤ 5040)
      CFSG.Sporadic.Fi23.J CFSG.Blueprint.NativeSporadic.Fi23 (inferInstance : Group CFSG.Sporadic.Fi23.J)
      (inferInstance : Group CFSG.Blueprint.NativeSporadic.Fi23) hf CFSG.Sporadic.Fi23.fi23EquivJ
      (fun s hs _ hI => CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five.card_pSimple_five s hs hI)
  have hC : CentTypes 5 (fun T _ => (Nat.card T ∣ 241920 ∧ Nat.card T ≤ 5040) ∧ Nat.card T ≠ 360)
      CFSG.Blueprint.NativeSporadic.Fi23 := hC1.and h
  have hS : SporTypes 5 (fun T _ => (Nat.card T ∣ 241920 ∧ Nat.card T ≤ 5040) ∧ Nat.card T ≠ 360) .Fi23 :=
    sporTypes_of_model Nat.prime_five (typeInv_card fun N => (N ∣ 241920 ∧ N ≤ 5040) ∧ N ≠ 360)
      (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi23).some hC
  refine sporDownRow_of_sporTypes Nat.prime_five hS fun T _ _ _ hnab h5 hT => ?_
  obtain ⟨⟨hd, hle⟩, h360⟩ := hT
  refine downTypeOK_of_not_chev fun q hq hq2 hq5 hC => ?_
  rcases CFSG.LocalAnalysis.GLTheoremA.I1416Rows.chev_card_dvd_241920_cases
      CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hnab hC hd hle with
    h60 | h168 | ⟨h360', -⟩ | ⟨h504, -⟩
  · exact not_isChevSimple_of_card_bound (p := 5) h60 (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide) (by decide) (by decide) q hq hq2 hq5 hC
  · rw [h168] at h5
    norm_num at h5
  · exact h360 h360'
  · rw [h504] at h5
    norm_num at h5

end S_sporDownRow_Fi23_five

section S_not_isChevSimple_seven


theorem not_isChevSimple_seven (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {T : Type}
    [Group T] [Finite T] [IsSimpleGroup T] (hnab : ∃ a b : T, a * b ≠ b * a) (h7 : 7 ∣ Nat.card T)
    (hd : Nat.card T ∣ 80640) (h504 : Nat.card T ≠ 504)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq7 : q ≠ 7) : ¬ IsChevSimple q T := by
  have h27 : ¬ 27 ∣ Nat.card T := fun h' => absurd (h'.trans hd) (by norm_num)
  have h25 : ¬ 25 ∣ Nat.card T := fun h' => absurd (h'.trans hd) (by norm_num)
  have h49 : ¬ 49 ∣ Nat.card T := fun h' => absurd (h'.trans hd) (by norm_num)
  have hbig : ∀ r : ℕ, r.Prime → 7 < r → ¬ r ∣ Nat.card T := fun r hr hr7 h' =>
    absurd (le_of_prime_dvd (b := 7) hr (h'.trans hd) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide)) (by omega)
  intro hC
  have hN0 : 0 < Nat.card T := Nat.card_pos
  have h60 : 60 ≤ Nat.card T := by
    by_contra hlt
    push Not at hlt
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2
      (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt)) a b)
  have hsmall : Nat.card T ∣ 2520 → False := fun hd => by
    rcases CFSG.LocalAnalysis.GLTheoremA.I1416Rows.chev_card_dvd_2520_cases hb hnab hC hd with
      h | h | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h] at h7
      norm_num at h7
    · exact not_isChevSimple_of_card_bound (p := 7) h (by norm_num) (by norm_num)
        (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide) q hq hq2 hq7 hC
    · rw [h] at h7
      norm_num at h7
    · exact h504 h
  by_cases hq3 : q = 3
  · subst hq3
    obtain ⟨a, m, hNam, hm3⟩ : ∃ a m : ℕ, Nat.card T = 3 ^ a * m ∧ ¬ 3 ∣ m :=
      ⟨_, _, (Nat.ordProj_mul_ordCompl_eq_self _ 3).symm, Nat.not_dvd_ordCompl Nat.prime_three hN0.ne'⟩
    have ha2 : a ≤ 2 := by
      by_contra hc
      exact h27 (hNam ▸ Dvd.dvd.mul_right (pow_dvd_pow 3 (by omega : 3 ≤ a)) m)
    by_cases h4 : 3 ^ (2 * a) ≤ m
    · refine CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb Nat.prime_three
        (by norm_num) hNam hm3 h4 (fun _ => ⟨?_, ?_, ?_⟩) (fun h => absurd h (by norm_num)) hC
      · rw [← hNam]
        rintro h360
        rw [h360] at h7
        norm_num at h7
      · rw [← hNam]
        exact h504
      · rw [← hNam]
        rintro h25920
        rw [h25920] at h7
        norm_num at h7
    · push Not at h4
      interval_cases a
      · norm_num at h4
        subst h4
        rw [mul_zero] at hNam
        omega
      · norm_num at h4 hNam
        omega
      · norm_num at h4 hNam
        have h7m : 7 ∣ m := by
          rw [hNam] at h7
          exact (Nat.Coprime.dvd_mul_left (by norm_num)).1 h7
        obtain ⟨j, rfl⟩ := h7m
        have hj : j < 12 := by omega
        interval_cases j
        · omega
        · exact hsmall (by rw [hNam]; norm_num)
        · exact hsmall (by rw [hNam]; norm_num)
        · exact hm3 (by norm_num)
        · exact hsmall (by rw [hNam]; norm_num)
        · exact hsmall (by rw [hNam]; norm_num)
        · exact hm3 (by norm_num)
        · exact h49 (by rw [hNam]; norm_num)
        · exact h504 (by omega)
        · exact hm3 (by norm_num)
        · exact hsmall (by rw [hNam]; norm_num)
        · exact hbig 11 (by norm_num) (by norm_num) (by rw [hNam]; norm_num)
  by_cases hq5 : q = 5
  · subst hq5
    obtain ⟨a, m, hNam, hm5⟩ : ∃ a m : ℕ, Nat.card T = 5 ^ a * m ∧ ¬ 5 ∣ m :=
      ⟨_, _, (Nat.ordProj_mul_ordCompl_eq_self _ 5).symm, Nat.not_dvd_ordCompl Nat.prime_five hN0.ne'⟩
    have ha1 : a ≤ 1 := by
      by_contra hc
      exact h25 (hNam ▸ Dvd.dvd.mul_right (pow_dvd_pow 5 (by omega : 2 ≤ a)) m)
    by_cases h4 : 5 ^ (2 * a) ≤ m
    · refine CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb Nat.prime_five
        (by norm_num) hNam hm5 h4 (fun h => absurd h (by norm_num)) (fun _ => ?_) hC
      rw [← hNam]
      rintro h60'
      rw [h60'] at h7
      norm_num at h7
    · push Not at h4
      interval_cases a
      · norm_num at h4
        subst h4
        rw [mul_zero] at hNam
        omega
      · norm_num at h4 hNam
        have h7m : 7 ∣ m := by
          rw [hNam] at h7
          exact (Nat.Coprime.dvd_mul_left (by norm_num)).1 h7
        obtain ⟨j, rfl⟩ := h7m
        have hj : j < 4 := by omega
        interval_cases j
        · omega
        · omega
        · exact hsmall (by rw [hNam]; norm_num)
        · exact hsmall (by rw [hNam]; norm_num)
  have h7q : 7 < q := by
    have h2 := hq.two_le
    have hq4 : q ≠ 4 := by
      rintro rfl
      norm_num at hq
    have hq6 : q ≠ 6 := by
      rintro rfl
      norm_num at hq
    omega
  exact CFSG.LocalAnalysis.GLTheoremA.I1416QRows.not_isChevSimple_of_card hb hq hq2 (a := 0) (m := Nat.card T)
    (by rw [pow_zero, one_mul]) (hbig q hq h7q) (by rw [mul_zero, pow_zero]; exact hN0)
    (fun h => absurd h hq3) (fun h => absurd h hq5) hC

end S_not_isChevSimple_seven

section S_downCompOK_B_xSeven


open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven (xSeven) in
theorem downCompOK_B_xSeven
    (h : BSevenNoL28) : DownCompOK .B 7 xSeven := by
  haveI : Finite CFSG.Blueprint.NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have P := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.bSevenElem_parts
  have hxS : orderOf xSeven = 7 := orderOf_eq_prime P.x_pow P.x_ne
  intro I hI q hq hq2 hq7 hC
  exfalso
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num : Nat.Prime 7) hI
  exact not_isChevSimple_seven CFSG.HardMathSupport.Solomon.Coordinator.lieOrderBridge_holds hnab
    (Claims1116d.prime_dvd_card_pSimple (by norm_num : Nat.Prime 7) hI)
    (CFSG.HardMathSupport.Dickson.BMRows.census_B_seven xSeven hxS I hI) (h I hI) hq hq2 hq7 hC

end S_downCompOK_B_xSeven

section S_sporDownRow_B_seven


theorem sporDownRow_B_seven
    (h : BSevenNoL28) : SporDownRow .B 7 := by
  haveI : Finite (CFSG.Blueprint.NativeSporadic.Carrier .B) := CFSG.Monster.B.Pinned.finite_B
  have P := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.bSevenElem_parts
  have hxS : orderOf CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSeven.xSeven = 7 :=
    orderOf_eq_prime P.x_pow P.x_ne
  refine sporDownRow_of_model' (by norm_num)
    (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .B).some fun k hk => ?_
  obtain ⟨c, hc⟩ := isConj_iff.1 (CFSG.HardMathSupport.Timmesfeld.SporadicBalance.bSeven_isConj hxS hk)
  have h2 := downCompOK_of_mulEquiv (by norm_num) (MulAut.conj c) (downCompOK_B_xSeven h)
  rwa [MulAut.conj_apply, hc] at h2

end S_sporDownRow_B_seven

section S_sporDownRow_M_eleven


open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.AGLEmbedding.Norton.Gen11 (gen11W0 gen11W1 gen11W2 gen11W3) in
open CFSG.Monster.Generated (Gmat) in
theorem sporDownRow_M_eleven (h : MElevenDown) : SporDownRow .M 11 := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨e1⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  refine sporDownRow_of_model' (by norm_num) e1 fun s hs => ?_
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hx, hy, hxy, hx1, h3, h4, -, -⟩ := CFSG.AGLEmbedding.Norton.MON11_13.eleven_gw_facts
  have hy3 := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterEleven.eleven_data_facts.1
  have hrot := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.eleven_rot_fact
    Certificates.certificate41508
  have hc : Commute (gw gen11W0) (gw gen11W1) := hxy
  obtain ⟨g, k, hgk⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.exists_conj_pow_of_eleven_lines
    (x₃ := gw gen11W2) (x₄ := gw gen11W3) hx hy hxy
    (by rw [h3, mul_inv_cancel_right, ((hc.pow_pow 6 3).symm).eq])
    (by rw [hy3, mul_inv_cancel_right]) (by rw [h4, mul_inv_cancel_right])
    (by rw [hrot, mul_inv_cancel_right]) hx1
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenFinal.factorization_Gmat_eleven hs
  have hk1 : gw gen11W0 ^ k ≠ 1 := by
    intro h1
    rw [h1, mul_one, mul_inv_cancel] at hgk
    rw [hgk, orderOf_one] at hs
    norm_num at hs
  exact downCompOK_of_conj_pow (m := g⁻¹) (by norm_num)
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterElevenLocal.orderOf_x11 hk1
    (by rw [hgk]; group) h

end S_sporDownRow_M_eleven

section S_sporDownRow_M_thirteen


open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.Monster.Generated (Gmat) in
theorem sporDownRow_M_thirteen (hA : MThirteenADown) (hB : MThirteenBDown) : SporDownRow .M 13 := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  obtain ⟨e1⟩ : Nonempty (Gmat ≃* (TauCeti.CFSGIndex.sporadic .M).Group) :=
    CFSG.Blueprint.NativeSporadic.MonsterModel.iso_gmat_tauCeti
  refine sporDownRow_of_model' (by norm_num) e1 fun s hs => ?_
  obtain ⟨m, k, hk, hmk | hmk⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen.census_thirteen s hs
  · have ht := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteenLocal.orderOf_c13
    exact downCompOK_of_conj_pow (by norm_num) ht (pow_ne_one_of_mod ht hk) hmk hB
  · have ht := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterThirteen.orderOf_xE
    exact downCompOK_of_conj_pow (by norm_num) ht (pow_ne_one_of_mod ht hk) hmk hA

end S_sporDownRow_M_thirteen

section S_mElevenDown_of_card


open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.Monster.Generated (Gmat) in
theorem mElevenDown_of_card (h : ∀ I : Subgroup Gmat, GLAPComponent 11 (Subgroup.centralizer
      ({gw CFSG.AGLEmbedding.Norton.Gen11.gen11W0} : Set Gmat)) I → Nat.card (PSimple 11 I) = 95040) :
    MElevenDown := by
  haveI : Finite Gmat := CFSG.Monster.Generated.finite_Gmat
  intro I hI
  exact downTypeOK_of_not_chev (not_isChevSimple_of_card_bound (h I hI) (by norm_num) (by norm_num)
    (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))

end S_mElevenDown_of_card

section Natural

open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.Monster.Generated (Gmat) in
theorem mThirteenADown_of_L33 (h : ∀ I : Subgroup Gmat, GLAPComponent 13 (Subgroup.centralizer
      ({gw CFSG.AGLEmbedding.Norton.MON11_13.thirteenX} : Set Gmat)) I → IsLpType 3 3 (PSimple 13 I)) :
    MThirteenADown :=
  fun I hI _ _ _ _ _ => Or.inr (Or.inr (Or.inr ⟨rfl, rfl, h I hI⟩))

open CFSG.AGLEmbedding.Norton.MON5_7 (gw) in
open CFSG.Monster.Generated (Gmat) in
theorem mThirteenBDown_of_noComp (h : ∀ I : Subgroup Gmat, ¬ GLAPComponent 13 (Subgroup.centralizer
      ({gw CFSG.AGLEmbedding.Norton.GenD13.genD13W1} : Set Gmat)) I) :
    MThirteenBDown :=
  downCompOK_of_no_comp h

end Natural

section S_mThirteenBDown_holds


theorem mThirteenBDown_holds : MThirteenBDown :=
  mThirteenBDown_of_noComp CFSG.HardMathSupport.Dickson.BMRows.noComp_c13

end S_mThirteenBDown_holds

section S_sporDownRow_M_thirteen_of


theorem sporDownRow_M_thirteen_of
    (hA : MThirteenADown) : SporDownRow .M 13 :=
  sporDownRow_M_thirteen hA mThirteenBDown_holds

end S_sporDownRow_M_thirteen_of

section Structure


structure SporDownResidual'' : Prop where
  B_three : CFSG.HardMathSupport.Dickson.I271.TabBThreeBNoComp
  M_three : CFSG.HardMathSupport.Dickson.I271.M3ResBNoComp
  Fi23_five : Fi23FiveNoA6
  Fi24Prime_five : SporTables.Fi24FiveA9
  B_five : CFSG.HardMathSupport.Dickson.I271.TabBFiveBNoComp
  M_five : CFSG.HardMathSupport.Dickson.I271.CentFiveBNoComp (CFSG.Blueprint.NativeSporadic.Carrier .M)
  B_seven : BSevenNoL28
  M_eleven : MElevenDown
  M_thirteen_A : MThirteenADown

end Structure

section S_sporDownResidualP_of_residualPP


theorem sporDownResidual'_of_residual''
    (h : SporDownResidual'') : Claims1116d.SporDownResidual' where
  B_three := sporDownRow_B_three h.B_three
  M_three := sporDownRow_M_three h.M_three
  Fi23_five := sporDownRow_Fi23_five h.Fi23_five
  Fi24Prime_five := sporDownRow_Fi24_five h.Fi24Prime_five
  B_five := sporDownRow_B_five h.B_five
  M_five := sporDownRow_M_five h.M_five
  B_seven := sporDownRow_B_seven h.B_seven
  M_eleven := sporDownRow_M_eleven h.M_eleven
  M_thirteen := sporDownRow_M_thirteen_of h.M_thirteen_A

end S_sporDownResidualP_of_residualPP

section S_inputSporDownChev_of_residualPP


theorem inputSporDownChev_of_residual''
    (h : SporDownResidual'') : Claims1116b.InputSporDownChev :=
  Claims1116d.inputSporDownChev_of_residual' (sporDownResidual'_of_residual'' h)

end S_inputSporDownChev_of_residualPP

section S_sporDownRow_B_three_of_kGroup


theorem sporDownRow_B_three_of_kGroup
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    SporDownRow .B 3 :=
  sporDownRow_B_three_of_types (SporTables.sporTypes_B_three_of_kGroup
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hK)

end S_sporDownRow_B_three_of_kGroup

section S_sporDownRow_M_three_of_kGroup


theorem sporDownRow_M_three_of_kGroup (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    SporDownRow .M 3 :=
  sporDownRow_M_three_of_types (SporTables.sporTypes_M_three_of_kGroup
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hK)

end S_sporDownRow_M_three_of_kGroup

section S_sporDownRow_B_five_of_kGroup


theorem sporDownRow_B_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group) :
    SporDownRow .B 5 :=
  sporDownRow_B_five_of_types (SporTables.sporTypes_B_five_of_kGroup
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hK)

end S_sporDownRow_B_five_of_kGroup

section S_sporDownRow_M_five_of_kGroup


theorem sporDownRow_M_five_of_kGroup
    (hK : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) :
    SporDownRow .M 5 :=
  sporDownRow_M_five_of_types (SporTables.sporTypes_M_five_of_kGroup
    CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds hK)

end S_sporDownRow_M_five_of_kGroup

section StructureK


structure SporDownResidualK : Prop where
  Fi23_five : Fi23FiveNoA6
  Fi24Prime_five : SporTables.Fi24FiveA9
  B_seven : BSevenNoL28
  M_eleven : MElevenDown
  M_thirteen_A : MThirteenADown

end StructureK

section S_sporDownResidualP_of_residualK


theorem sporDownResidual'_of_residualK
    (hB : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .B).Group)
    (hM : CFSG.Open.IsKGroup (TauCeti.CFSGIndex.sporadic .M).Group) (h : SporDownResidualK) :
    Claims1116d.SporDownResidual' where
  B_three := sporDownRow_B_three_of_kGroup hB
  M_three := sporDownRow_M_three_of_kGroup hM
  Fi23_five := sporDownRow_Fi23_five h.Fi23_five
  Fi24Prime_five := sporDownRow_Fi24_five h.Fi24Prime_five
  B_five := sporDownRow_B_five_of_kGroup hB
  M_five := sporDownRow_M_five_of_kGroup hM
  B_seven := sporDownRow_B_seven h.B_seven
  M_eleven := sporDownRow_M_eleven h.M_eleven
  M_thirteen := sporDownRow_M_thirteen_of h.M_thirteen_A

end S_sporDownResidualP_of_residualK

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.SporTables2

end
