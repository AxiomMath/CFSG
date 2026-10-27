module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeA
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabFi23ThreeC
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporRowsA

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabFi23.SporAlt

open CFSG.HardMathSupport.Dickson.I271 CFSG.HardMathSupport.Dickson.I271.TabFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Five CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native CFSG.HardMathSupport.Solomon.Coordinator.YS08 CFSG.HardMathSupport.Dickson.I271.TabFi23Y CFSG.YGroups
open CFSG.Sporadic.Th hiding J a b closure_ab gA gB rows_B_cube
open CFSG.Certificates.CosetEnumeration (evalWord)
open CFSG.RankThree.PartOne.N143.O7 (Om)

section Top'

theorem shapeRkAt_of_om' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge)
    {G : Type} [Group G] [Finite G] (x : G)
    (hcore : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set G)) = ⊥) (L : Subgroup G)
    (e : ↥L ≃* ↥Om) (hLC : L ≤ Subgroup.centralizer ({x} : Set G))
    (hLn : ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hk : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) = Nat.card ↥L * 3) :
    ShapeRkAt 3 CFSG.LocalAnalysis.GLTheoremA.SporAltRows.STypeThree (fun _ _ => True) x := by
  have hGood := CFSG.LocalAnalysis.GLTheoremA.SporAltRows.stypeThree_of_equiv
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True :=
    fun _ _ _ _ _ h => h
  have hs : IsSimpleGroup ↥L := tabFi23_isSimpleGroup_of_equiv_om e
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := tabFi23_nonabelian_of_equiv_om e
  have hpL : 3 ∣ Nat.card ↥L := by
    rw [tabFi23_card_of_equiv_om e]
    norm_num
  exact shapeRkAt_of_data_solvable Nat.prime_three hGood hRk x L hLC hLn hs hnab hpL hcore
    (m := 3) hk (by norm_num)
    (CFSG.LocalAnalysis.GLTheoremA.SporAltRows.stypeOK_of_card hb (N := 4585351680) (by rw [tabFi23_card_of_equiv_om e] <;> norm_num) (by norm_num) (by norm_num)
      (by simp only [Nat.primeFactorsList_ofNat]; decide +kernel) (by decide) (by decide))
    trivial

end Top'

section ThreeA'

theorem shapeRkAt_t3_zero' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    ShapeRkAt 3 CFSG.LocalAnalysis.GLTheoremA.SporAltRows.STypeThree (fun _ _ => True) (t3 0) := by
  haveI := finite_J23
  have hcl := t3_classData.1
  have hz : orderOf (t3 0) = 3 := hcl.1
  have hcardC := card_cent_t3_zero
  have h17339 : yCheck orb (dTable orb) (genTables orb (-2)) (t3Tabs orb letters)[0]! y322Ks =
      true := Certificates.certificate17339
  obtain ⟨s, hrel, hnc, hzc⟩ := y322_of_check (rep_t3Tabs 0) h17339
  have hcl' : Subgroup.closure (Set.range s ∪ {t3 0}) ≤
      Subgroup.centralizer ({t3 0} : Set J) := by
    rw [Subgroup.closure_le]
    rintro g (⟨i, rfl⟩ | hg)
    · exact cen_iff' (hzc i)
    · rw [Set.mem_singleton_iff.1 hg]
      exact cen_iff' rfl
  have hcard : Nat.card ↥(Subgroup.closure (Set.range s ∪ {t3 0})) ≤ 3 * 4585351680 := by
    have h1 := Subgroup.card_le_of_le hcl'
    rw [hcardC] at h1
    omega
  obtain ⟨⟨e⟩, hLcard, hzL⟩ := tabFi23_y322_recognition s hrel hnc (t3 0) hz hzc hcard
  set L : Subgroup J := Subgroup.closure (Set.range s) with hL
  set N : Subgroup J := Subgroup.closure (Set.range s ∪ {t3 0}) with hN
  set C : Subgroup J := Subgroup.centralizer ({t3 0} : Set J) with hC
  have hLN : L ≤ N := Subgroup.closure_mono Set.subset_union_left
  have hLC : L ≤ C := hLN.trans hcl'
  have hCL : Nat.card C = Nat.card L * 3 := by
    rw [hC, hcardC, hLcard]
  have hLpos : 0 < Nat.card L := Nat.card_pos
  have hNC : N = C := by
    obtain ⟨c, hc⟩ := Subgroup.card_dvd_of_le hLN
    have hNd : Nat.card N ∣ Nat.card C := Subgroup.card_dvd_of_le hcl'
    rw [hc, hCL] at hNd
    have hc3 : c ∣ 3 := Nat.dvd_of_mul_dvd_mul_left hLpos hNd
    rcases (Nat.dvd_prime Nat.prime_three).1 hc3 with h1 | h3
    · exfalso
      have hEq : L = N := Subgroup.eq_of_le_of_card_ge hLN (by rw [hc, h1, mul_one])
      apply hzL
      rw [hEq]
      exact Subgroup.subset_closure (Set.mem_union_right _ rfl)
    · exact Subgroup.eq_of_le_of_card_ge hcl' (by rw [hCL, hc, h3])
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    have hNn : N ≤ Subgroup.normalizer L := by
      rw [hN, Subgroup.closure_le]
      rintro g (⟨i, rfl⟩ | hg)
      · exact Subgroup.le_normalizer (Subgroup.subset_closure ⟨i, rfl⟩)
      · rw [Set.mem_singleton_iff.1 hg]
        refine Subgroup.mem_normalizer_iff.2 fun h => ?_
        have hcomm : ∀ l ∈ L, t3 0 * l * (t3 0)⁻¹ = l := fun l hl => by
          have h1 := cen_iff (hLC hl)
          calc t3 0 * l * (t3 0)⁻¹ = (l * t3 0) * (t3 0)⁻¹ := by rw [h1]
            _ = l := by group
        constructor
        · intro hh
          rw [hcomm h hh]
          exact hh
        · intro hh
          have hh' := hcomm _ hh
          have h3 : t3 0 * h * (t3 0)⁻¹ = h := by
            calc t3 0 * h * (t3 0)⁻¹
                = (t3 0)⁻¹ * (t3 0 * (t3 0 * h * (t3 0)⁻¹) * (t3 0)⁻¹) * t3 0 := by group
              _ = (t3 0)⁻¹ * (t3 0 * h * (t3 0)⁻¹) * t3 0 := by rw [hh']
              _ = h := by group
          rw [h3] at hh
          exact hh
    intro g hg l hl
    rw [← hNC] at hg
    exact (Subgroup.mem_normalizer_iff.1 (hNn hg) l).1 hl
  exact shapeRkAt_of_om' hb (t3 0) (classData_core t3_classData.1) L e hLC hLn hCL

end ThreeA'

end CFSG.HardMathSupport.Dickson.I271.TabFi23.SporAlt

namespace CFSG.HardMathSupport.Dickson.I271.SporAltFi23

open CFSG.Open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.TabFi23 CFSG.LocalAnalysis.GLTheoremA.I1416Rows CFSG.LocalAnalysis.GLTheoremA.SporAltRows CFSG.HardMathSupport.Dickson.I271.TabFi23.SporAlt
  CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.KDSpor

theorem shapeRkAt_t3' (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) (i : Fin 4) : ShapeRkAt 3 STypeThree (fun _ _ => True) (t3 i) := by
  haveI := finite_J23
  have h0 : ShapeRkAt 3 STypeThree (fun _ _ => True) (t3 0) := shapeRkAt_t3_zero' hb
  fin_cases i
  · exact h0
  · exact Or.inl pConstrained_t3_one
  · exact Or.inl pConstrained_t3_two
  · exact Or.inl pConstrained_t3_three

theorem centShapeRk_J23_level (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) : CentShapeRk 3 STypeThree (fun _ _ => True) J := by
  haveI := finite_J23
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRk : ∀ (T T' : Type) [Group T] [Group T'], T ≃* T' → True → True := fun _ _ _ _ _ h => h
  intro k hk1 hk3
  have hord : orderOf k = 3 := orderOf_eq_prime hk3 hk1
  obtain ⟨i, hconj⟩ := fi23_three_classes k hord
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have h := @ShapeRkAt.of_equiv ↥J ↥J _ finite_J23 inferInstance 3 Nat.prime_three
    STypeThree (fun _ _ => True) stypeThree_of_equiv hRk finite_J23 (MulAut.conj c⁻¹) (t3 i)
    (shapeRkAt_t3' hb i)
  have hk : (MulAut.conj c⁻¹) (t3 i) = k := by
    rw [MulAut.conj_apply, ← hc]
    group
  rw [hk] at h
  exact h

set_option maxRecDepth 100000 in
theorem srow_Fi23_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    SRow .Fi23 3 := by
  have hfin : Finite J := finite_J23
  have e : CFSG.Blueprint.NativeSporadic.Fi23 ≃* J := fi23EquivJ
  have hs : IsSimpleGroup J :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.Fi23.isSimpleGroup_Fi23 e.symm
  have hc : Nat.card J = 4089470473293004800 := CFSG.Sporadic.Fi23.card_J
  have hpr : ¬ (Nat.card J).Prime := by rw [hc]; norm_num
  have hnc : ∃ a c : J, a * c ≠ c * a :=
    @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple J _ hfin hs hpr
  have b : J ≃* (TauCeti.CFSGIndex.sporadic .Fi23).Group := e.symm.trans (hbr .Fi23).some
  exact @srow_of_centShape .Fi23 3 J _ hfin hs hOut b hnc Nat.prime_three (by norm_num)
    STypeThree (@CentShape.of_centShapeRk 3 STypeThree (fun _ _ => True) J _ (centShapeRk_J23_level hb))
    fun _ _ h => h

end CFSG.HardMathSupport.Dickson.I271.SporAltFi23
