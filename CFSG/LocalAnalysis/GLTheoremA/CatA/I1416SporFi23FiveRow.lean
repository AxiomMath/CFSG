module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFi23Five
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416CentOrbit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporFiveType
public import Certificates.Certificate10129
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving CFSG.Blueprint
  CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.I1416Rows

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


@[expose] def fixD (w : CFSG.Sporadic.Fi23.J) : Set CFSG.Sporadic.Fi23.J := {x | x ∈ D23 ∧ x * w = w * x}

set_option maxRecDepth 100000 in
theorem card_fix {a b : ℕ} (ha : a < 5) (hb : b < 5) (hab : a + b ≠ 0) :
    (fixD (eFive ^ a * fFive ^ b)).ncard = 21 := by
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  have hc := Certificates.certificate10129
  unfold fi23FiveFixOK at hc
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at hc
  have hlen := (hc a ha b hb).resolve_left hab
  have hW : Rep 31671 (fiveTab (eTab orb)
      (starWordTab orb (dTable orb) (genTables orb (-2)) (fivePathOf orb)) a b)
      (eFive ^ a * fFive ^ b) := (rep_eFive.powT hn a).compT (rep_fFive.powT hn b)
  set L := fixList (fiveTab (eTab orb)
      (starWordTab orb (dTable orb) (genTables orb (-2)) (fivePathOf orb)) a b)
  have hL : fixD (eFive ^ a * fFive ^ b) = (fun i => conjPt i) '' {i | i ∈ L} := by
    ext x
    constructor
    · rintro ⟨hx, hxw⟩
      obtain ⟨⟨i, hi⟩, rfl⟩ := (isConj_d_iff x).1 hx
      exact ⟨i, (mem_fixList_iff hW hi).2 hxw, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hilt := lt_of_mem_fixList hi
      exact ⟨conjPt_mem_D23 hilt, (mem_fixList_iff hW hilt).1 hi⟩
  have hnd : L.Nodup := List.Nodup.filter _ List.nodup_range
  have hinj : Set.InjOn (fun i => conjPt i) {i | i ∈ L} := fun i hi j hj h =>
    conjPt_injOn (lt_of_mem_fixList (show i ∈ L from hi)) (lt_of_mem_fixList (show j ∈ L from hj)) h
  rw [hL, hinj.ncard_image]
  have : {i | i ∈ L} = (L.toFinset : Set ℕ) := by ext; simp
  rw [this, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  exact hlen

set_option maxRecDepth 100000 in
theorem card_centralizer_five (s : CFSG.Sporadic.Fi23.J) (hs : orderOf s = 5) :
    ∃ m, Nat.card (Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi23.J)) = 1200 * m ∧ m ≤ 21 ∧ m ∣ 1008 := by
  have hn : (31671 : ℕ) < 2 ^ 32 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  obtain ⟨-, hc⟩ := fi23Five_parts
  unfold fi23FiveCore at hc
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true, List.mem_range,
    Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h5e', he1'⟩, h5f'⟩, hcomm'⟩, hpow'⟩, -⟩ := hc
  have h5e := eq_of_eqTab (rep_eFive.powT hn 5) (Rep.idT hn) h5e'
  have h5f := eq_of_eqTab (rep_fFive.powT hn 5) (Rep.idT hn) h5f'
  have hcomm := eq_of_eqTab (rep_eFive.compT rep_fFive) (rep_fFive.compT rep_eFive) hcomm'
  have he1 := ne_one_of_rep rep_eFive he1'
  have hpow : ∀ k < 5, fFive ≠ eFive ^ k := fun k hk =>
    ne_pow_of_rep rep_fFive rep_eFive k (hpow' k hk)
  have hQ := card_closure_pair_eq_sq hcomm h5e h5f he1 hpow (by rw [card_J]; norm_num)
  have hQfull : Nat.card (Subgroup.closure ({eFive, fFive} : Set J)) =
      5 ^ (Nat.card (⊤ : Subgroup J)).factorization 5 := by
    rw [hQ, Subgroup.card_top, card_J,
      show (4089470473293004800 : ℕ) = 5 ^ 2 * 163578818931720192 by norm_num,
      factorization_pow_mul Nat.prime_five 2 _ (by norm_num)]
  obtain ⟨g, -, hgQ⟩ := CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3T.exists_conj_mem_of_full
    le_top hQfull (Subgroup.mem_top s) hs
  obtain ⟨a, ha, b, hb, hw⟩ := exists_pow_mul_pow_of_mem (by norm_num) hcomm h5e h5f hgQ
  have hwo : orderOf (g⁻¹ * s * g) = 5 := by rw [orderOf_inv_mul_mul, hs]
  have hab : a + b ≠ 0 := by
    intro h0
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    rw [ha0, hb0, pow_zero, pow_zero, mul_one] at hw
    rw [hw, orderOf_one] at hwo
    exact absurd hwo (by norm_num)
  set w := eFive ^ a * fFive ^ b with hwdef
  have hwo' : orderOf w = 5 := hw ▸ hwo
  have hsw : Nat.card (Subgroup.centralizer ({s} : Set J)) =
      Nat.card (Subgroup.centralizer ({w} : Set J)) := by
    have h := card_centralizer_conj' g⁻¹ s
    rw [inv_inv, hw] at h
    exact h.symm
  have hF : ∀ c ∈ Subgroup.centralizer ({w} : Set J), ∀ x ∈ fixD w, c * x * c⁻¹ ∈ fixD w := by
    rintro c hc x ⟨hx, hxw⟩
    refine ⟨CFSG.HardMathSupport.Timmesfeld.SporadicBalance.D23_conj hx c, ?_⟩
    have hcw : c * w = w * c := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      exact hc
    calc c * x * c⁻¹ * w = c * x * (c⁻¹ * w) := by group
      _ = c * x * (w * c⁻¹) := by
          rw [show c⁻¹ * w = w * c⁻¹ by
            calc c⁻¹ * w = c⁻¹ * (w * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * w) * c⁻¹ := by rw [hcw]
              _ = w * c⁻¹ := by group]
      _ = c * (x * w) * c⁻¹ := by group
      _ = c * (w * x) * c⁻¹ := by rw [hxw]
      _ = (c * w) * x * c⁻¹ := by group
      _ = w * (c * x * c⁻¹) := by rw [hcw]; group
  have hN : ∀ x ∈ fixD w, Nat.card ↥(Subgroup.centralizer ({w} : Set J) ⊓
      Subgroup.centralizer ({x} : Set J)) = 1200 := fun x ⟨hx, hxw⟩ =>
    card_centralizer_inf_D23 w hwo' hx hxw.symm
  have h21 : (fixD w).ncard = 21 := card_fix ha hb hab
  obtain ⟨x₀, hx₀⟩ : (fixD w).Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [h21]; norm_num)
  obtain ⟨m, hm, hm21⟩ := CentOrbit.card_centralizer_eq_mul_orbit hF hx₀ (hN x₀ hx₀)
  rw [h21] at hm21
  refine ⟨m, hsw.trans hm, hm21, ?_⟩
  have hCJ : Nat.card (Subgroup.centralizer ({w} : Set J)) ∣ 4089470473293004800 :=
    card_J ▸ Subgroup.card_subgroup_dvd_card _
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (Nat.card_pos (α := ↥(Subgroup.centralizer ({w} : Set J)))).ne' hm
  have hprime : ∀ r : ℕ, r.Prime → ¬ r ∣ 1200 → r ∣ m → r ∣ 21 := fun r hr hr1 hrm =>
    h21 ▸ CentOrbit.prime_dvd_card_of_dvd_centralizer hF hN hr
      (hm ▸ Dvd.dvd.mul_left hrm 1200) hr1
  have h5 : ¬ 5 ∣ m := by
    intro h5
    have : 5 ^ 3 ∣ 4089470473293004800 :=
      (show 5 ^ 3 ∣ 1200 * m from by
        obtain ⟨k, rfl⟩ := h5
        exact ⟨k * 48, by ring⟩).trans (hm ▸ hCJ)
    norm_num at this
  have h11 : ¬ 11 ∣ m := fun h => absurd (hprime 11 (by norm_num) (by norm_num) h) (by norm_num)
  have h13 : ¬ 13 ∣ m := fun h => absurd (hprime 13 (by norm_num) (by norm_num) h) (by norm_num)
  have h17 : ¬ 17 ∣ m := fun h => absurd (hprime 17 (by norm_num) (by norm_num) h) (by norm_num)
  have h19 : ¬ 19 ∣ m := fun h => absurd (hprime 19 (by norm_num) (by norm_num) h) (by norm_num)
  interval_cases m <;> first | decide | (exfalso; omega)

theorem card_pSimple_five (s : CFSG.Sporadic.Fi23.J) (hs : orderOf s = 5) {I : Subgroup CFSG.Sporadic.Fi23.J}
    (hI : GLAPComponent 5 (Subgroup.centralizer ({s} : Set CFSG.Sporadic.Fi23.J)) I) :
    Nat.card (PSimple 5 I) ∣ 241920 ∧ Nat.card (PSimple 5 I) ≤ 5040 := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  obtain ⟨m, hm, hm21, hmd⟩ := card_centralizer_five s hs
  have hd := prime_mul_card_pSimple_dvd_cent Nat.prime_five hs hI.1
  rw [hm] at hd
  have hT : Nat.card (PSimple 5 I) ∣ 240 * m :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 5) (by rw [← mul_assoc]; exact hd)
  refine ⟨hT.trans (by rw [show (241920 : ℕ) = 240 * 1008 by norm_num]; exact Nat.mul_dvd_mul_left _ hmd), ?_⟩
  have hpos : 0 < 240 * m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm
      exact absurd hm (Nat.card_pos (α := ↥(Subgroup.centralizer ({s} : Set J)))).ne'
    · omega
  calc Nat.card (PSimple 5 I) ≤ 240 * m := Nat.le_of_dvd hpos hT
    _ ≤ 5040 := by omega

set_option maxRecDepth 100000 in
theorem fi23_model (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    Finite CFSG.Sporadic.Fi23.J ∧ IsSimpleGroup CFSG.Sporadic.Fi23.J ∧ (∃ a c : CFSG.Sporadic.Fi23.J, a * c ≠ c * a) ∧
      Nonempty (CFSG.Sporadic.Fi23.J ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group) := by
  have hfin : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J]; norm_num)
  have hs : IsSimpleGroup J := isSimpleGroup_J
  have hpr : ¬ (Nat.card J).Prime := by rw [card_J]; norm_num
  exact ⟨hfin, hs, @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple J _ hfin hs hpr,
    ⟨fi23EquivJ.symm.trans (hbr .Fi23).some⟩⟩

theorem row_Fi23_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : I1416SporRow .Fi23 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi23_model hbr
  refine @row_of_model .Fi23 5 J _ hfin hs hOut b hnc fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hsI
  obtain ⟨hd, hle⟩ := card_pSimple_five x hx hI
  exact fun hC h25 _ => absurd h25 (not_sq_five_dvd_card_mulAut_of_chev_241920 hb hnab hC hd hle)

theorem qrow_Fi23_five (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .Fi23 5 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi23_model hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_model .Fi23 5 J _ hfin hs hOut b hnc
    fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab Nat.prime_five hI
  haveI := hsI
  obtain ⟨hd, hle⟩ := card_pSimple_five x hx hI
  exact fun _ _ _ _ hC hA => not_sq_five_dvd_card_mulAut_of_chev_241920 hb hnab hC hd hle
    (CFSG.LocalAnalysis.GLTheoremA.I1416QRows.sq_dvd_card_mulAut_of_elemAb Nat.prime_five hA)

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five
