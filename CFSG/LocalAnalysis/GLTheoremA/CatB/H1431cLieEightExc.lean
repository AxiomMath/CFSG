module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieEightBase
public import CFSG.RankThree.PartTwo.Census.Exceptional.LocalRankThreeTwo
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.E6BadTwMain
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.GraphTwisted
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.AmbientGroup
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Classification
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.Blueprint
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup LieOrderBridge)
open CFSG.HardMathSupport.Solomon.Coordinator.I1420 (lieOrderFormula)

theorem lieSEightNoAt_orders (hLO : LieOrderBridge) :
    LieSEightNoAt fun d => (∃ q, d = .G2 q) ∨ (∃ q, d = .trialityD4 q) ∨ (∃ m, d = .suzuki m) := by
  refine lieSEightNoAt_of_not_dvd hLO fun d hd hc hf => ?_
  rcases hd with ⟨q, hq⟩ | ⟨q, hq⟩ | ⟨m, hm⟩
  · rw [hq] at hf ⊢
    have h8 : q.card = 8 := hf
    simp only [lieOrderFormula, h8]
    decide +kernel
  · rw [hq] at hf ⊢
    have h8 : q.card = 8 := hf
    simp only [lieOrderFormula, h8]
    decide +kernel
  · rw [hm] at hf ⊢
    have h8 : 2 ^ (2 * m + 1) = 8 := hf
    simp only [lieOrderFormula, h8]
    decide +kernel

theorem lieSEightNoAt_other (hLO : LieOrderBridge) : LieSEightNoAt LieSEightOther := by
  rintro Y _ _ hY hcore hRk ⟨d, hv⟩ hd hc hf he α hα hα3 hα1
  have hrange := (TauCeti.LieTypeIndex.valid_iff _).1 hv
  have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).1 hrange.1
  cases d with
  | C n q =>
    simp only [] at hr
    exact absurd ((TauCeti.LieTypeIndex.characteristic_C n q).symm.trans hc) hr.2
  | reeG2 m =>
    rw [TauCeti.LieTypeIndex.characteristic_reeG2] at hc
    omega
  | tits =>
    simp only [KD264Lie.fieldSize] at hf
    omega
  | G2 q =>
    exact lieSEightNoAt_orders hLO Y hY hcore hRk ⟨_, hv⟩ (Or.inl ⟨q, rfl⟩) hc hf he α hα hα3 hα1
  | trialityD4 q =>
    exact lieSEightNoAt_orders hLO Y hY hcore hRk ⟨_, hv⟩ (Or.inr (Or.inl ⟨q, rfl⟩)) hc hf he α
      hα hα3 hα1
  | suzuki m =>
    exact lieSEightNoAt_orders hLO Y hY hcore hRk ⟨_, hv⟩ (Or.inr (Or.inr ⟨m, rfl⟩)) hc hf he α
      hα hα3 hα1
  | A _ _ => exact hd.elim
  | twistedA _ _ => exact hd.elim
  | B _ _ => exact hd.elim
  | D _ _ => exact hd.elim
  | twistedD _ _ => exact hd.elim
  | E6 _ => exact hd.elim
  | E7 _ => exact hd.elim
  | E8 _ => exact hd.elim
  | F4 _ => exact hd.elim
  | twistedE6 _ => exact hd.elim
  | reeF4 _ => exact hd.elim

section Rank

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule TauCeti
open CFSG.RankThree.PartTwo.Census.Exceptional
open scoped MatrixGroups commutatorElement

theorem lieSEight_ringChar_two {d : ValidLieTypeIndex} (h : Even d.fieldOrder) :
    ringChar d.fixedField = 2 := by
  have : Fintype d.fixedField := Fintype.ofFinite _
  refine (FiniteField.even_card_iff_char_two (F := d.fixedField)).2 ?_
  have hcard : Fintype.card d.fixedField = d.fieldOrder := by
    rw [← Nat.card_eq_fintype_card, ValidLieTypeIndex.card_fixedField]
  rw [hcard]
  exact Nat.even_iff.1 h

theorem lieSEight_four_le_e7Index
    (d : TypeE7LieIndex) (hch : ringChar d.1.fixedField = 2)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.steinberg) := by
  have hC : commutator ↥(e7Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e7 d.1.fixedField).1.commutator_eq_top
  obtain ⟨ρ, hinj, hcomm, hcen⟩ := exists_commuting_minuscule_SL2 e7Data_valid d.1.fixedField
    neighbour_cartan_E7 ![![0, 1, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0],
      ![0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1], ![2, 2, 3, 4, 3, 2, 1]]
    (by decide +kernel)
  refine four_le_localRank_three_of_five_commuting_SL2 (K := d.1.fixedField) hch
    (fun i => (toQuot (e7Embed d) hC).comp (ρ i))
    (fun i => toQuot_comp_injective (e7Embed_injective d) hC (ρ i) (hcen i))
    (fun i j hij A B => ?_)
  simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]

theorem lieSEight_four_le_E7
    (q : PrimePower) (hv : (LieTypeIndex.E7 q).Valid)
    (hq : q.card = 8) [hfin : Finite (CFSGIndex.lie ⟨.E7 q, hv⟩).Group] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (CFSGIndex.lie ⟨.E7 q, hv⟩).Group :=
  @lieSEight_four_le_e7Index ⟨⟨.E7 q, hv⟩, (LieTypeIndex.isTypeE7_iff _).2 trivial⟩
    (lieSEight_ringChar_two (by
      change Even (LieTypeIndex.E7 q).fieldOrder
      rw [LieTypeIndex.fieldOrder_E7, hq]
      decide)) hfin

open CFSG.LieType.Chevalley.RootOps in
theorem lieSEight_four_le_e6Index
    (d : TypeE6LieIndex) (hch : ringChar d.1.fixedField = 2)
    [Finite (FixedPointCandidate d.steinberg)] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.steinberg) := by
  obtain ⟨hr1, hr2, hso, hmod, hplus, hminus, h13⟩ := e6Two_check
  have hroot : ∀ {v}, isRootB .E6 v = true → IsRoot .E6 v := fun h => isRootB_iff.1 h
  have hnot : ∀ {v : Fin (Tag.rank .E6) → ℤ}, isRootB .E6 v = false → ¬ IsRoot .E6 v :=
    fun hv hr => by
      rw [← isRootB_iff, hv] at hr
      exact Bool.false_ne_true hr
  have h2 : ringChar d.1.fixedField = 2 := hch
  have : CharP d.1.fixedField 2 := ringChar.of_eq h2
  have hC : commutator ↥(e6Data_valid.minGroup d.1.fixedField) = ⊤ :=
    (CFSG.LieType.CurtisTits.isQuasisimple_e6 d.1.fixedField).1.commutator_eq_top
  set θ := toQuot (e6Embed d) hC with hθ
  choose ρ hinj hmem hcen using fun i =>
    exists_rootSL2' e6Data_valid d.1.fixedField neighbour_cartan_E6 (hroot (hr1 i))
  have hcomm : ∀ i j, i ≠ j → ∀ A B : SL(2, d.1.fixedField), ρ i A * ρ j B = ρ j B * ρ i A := by
    intro i j hij A B
    obtain ⟨h1, h2', h3, h4⟩ := hso i j hij
    exact (Subgroup.mem_centralizer_iff.1 (rankOne_le_centralizer e6Data_valid _ (hroot (hr1 i))
      (hroot (hr1 j)) h1 h2' (hnot h3) (hnot h4) (hmem i A)) (ρ j B) (hmem j B)).symm
  have hθρ : ∀ i, Function.Injective (θ.comp (ρ i)) := fun i =>
    toQuot_comp_injective (e6Embed_injective d) hC (ρ i) (hcen i)
  set PC : Subgroup ↥(e6Data_valid.minGroup d.1.fixedField) :=
    ⨆ j, e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j) with hPC
  have hP2 : IsPGroup 2 PC := by
    refine isPGroup_iSup_rootGroup e6Data_valid _ e6ModuleRoots fun i j x hx y hy => ?_
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hx
    obtain ⟨e, rfl⟩ := (e6Data_valid.mem_rootGroup _).1 hy
    by_cases hij : i = j
    · subst hij
      rw [← e6Data_valid.xm_add, ← e6Data_valid.xm_add, add_comm]
    · exact commute_xm e6Data_valid _ (hroot (hr2 i)) (hroot (hr2 j)) (hmod i j hij).1
        (hnot (hmod i j hij).2) c e
  have hnorm : ∀ i A, ρ i A ∈ Subgroup.normalizer (PC : Set _) := by
    intro i A
    refine (sup_le ?_ ?_ : _ ≤ Subgroup.normalizer (PC : Set _)) (hmem i A)
    · exact rootGroup_le_normalizer_iSup e6Data_valid _ (hroot (hr1 i)) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hplus i j).1, fun h => (hplus i j).2 (isRootB_iff.2 h)⟩
    · exact rootGroup_le_normalizer_iSup e6Data_valid _
        (CFSG.LieType.Chevalley.IsRoot.neg (hroot (hr1 i))) e6ModuleRoots
        (fun j => hroot (hr2 j)) fun j => ⟨(hminus i j).1, fun h => (hminus i j).2
          (isRootB_iff.2 h)⟩
  have hnc : e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1 ∉ Subgroup.center _ := by
    intro hc
    obtain ⟨σ, hσ, h⟩ := (e6Data_valid.commutator_xm d.1.fixedField (hroot (hr1 0))
      (hroot (hr2 0)) (hplus 0 0).1).1 (hroot h13)
    have h1 := h 1 1
    have h1' : ⁅e6Data_valid.xm d.1.fixedField (e6OrthoRoots 0) 1,
        e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1⁆ = 1 := by
      rw [commutatorElement_def, Subgroup.mem_center_iff.1 hc]
      group
    rw [h1', mul_one, mul_one] at h1
    have h0 := e6Data_valid.xm_injective d.1.fixedField (hroot h13)
      (h1.symm.trans (e6Data_valid.xm_zero _ _).symm)
    rcases hσ with rfl | rfl <;> simp at h0
  have hP : PC.map θ ≠ ⊥ := by
    intro hbot
    apply hnc
    refine mem_center_of_toQuot_eq_one (e6Embed_injective d) hC ?_
    have : θ (e6Data_valid.xm d.1.fixedField (e6ModuleRoots 0) 1) ∈ PC.map θ :=
      ⟨_, le_iSup (fun j => e6Data_valid.rootGroup d.1.fixedField (e6ModuleRoots j)) 0
        (e6Data_valid.xm_mem_rootGroup _ _ _), rfl⟩
    rwa [hbot, Subgroup.mem_bot] at this
  have h4 := card_le_localRank_three_of_commuting_SL2_of_le_normalizer (ι := Fin 4)
    (fun i => θ.comp (ρ i)) hθρ (fun i j hij A B => by
      simp only [MonoidHom.comp_apply, ← map_mul, hcomm i j hij A B]) hP (hP2.map θ)
    (fun i => Subgroup.le_normalizer_map θ ⟨_, hnorm i _, rfl⟩)
  rw [Fintype.card_fin] at h4
  exact h4


theorem lieSEight_four_le_E6
    (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq : q.card = 8) [hfin : Finite (CFSGIndex.lie ⟨.E6 q, hv⟩).Group] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (CFSGIndex.lie ⟨.E6 q, hv⟩).Group := by
  let d : TypeE6LieIndex := ⟨⟨.E6 q, hv⟩, (LieTypeIndex.isTypeE6_iff _).2 trivial⟩
  haveI : Finite (FixedPointCandidate d.steinberg) := hfin
  exact lieSEight_four_le_e6Index d (lieSEight_ringChar_two (by
    change Even (LieTypeIndex.E6 q).fieldOrder
    rw [LieTypeIndex.fieldOrder_E6, hq]
    decide))

open CFSG.LieType.Chevalley CFSG.TauCetiBridge in
theorem lieSEight_four_le_E8
    (q : PrimePower) (hv : (LieTypeIndex.E8 q).Valid) (hq : q.card = 8)
    [Finite (CFSGIndex.lie ⟨.E8 q, hv⟩).Group] :
    4 ≤ CFSG.Open.twoLocalPrimeRank 3 (CFSGIndex.lie ⟨.E8 q, hv⟩).Group := by
  set d : ValidLieTypeIndex := ⟨.E8 q, hv⟩ with hd
  have : Finite (FixedPointCandidate d.geckFrobenius) := ‹Finite (CFSGIndex.lie d).Group›
  change 4 ≤ CFSG.Open.twoLocalPrimeRank 3 (FixedPointCandidate d.geckFrobenius)
  have hch : ringChar d.fixedField = 2 := lieSEight_ringChar_two (by
    change Even (LieTypeIndex.E8 q).fieldOrder
    rw [LieTypeIndex.fieldOrder_E8, hq]
    decide)
  have hC : commutator ↥(adjointGroup .E8 d.fixedField) = ⊤ :=
    single_edge_perfect .E8 d.fixedField (by simp)
  obtain ⟨ι, hι, hcomm⟩ := exists_commuting_rootSL2 (K := d.fixedField) .E8
    ![![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0],
      ![0, 0, 0, 0, 0, 0, 1, 0], ![2, 3, 4, 6, 5, 4, 3, 2]] (by decide +kernel)
  exact four_le_localRank_three_geck_five d geckMatchE8 hC hch ι hι hcomm

end Rank

theorem lieSEightAt_E
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    LieSEightAt fun d => ∃ q, d = .E6 q ∨ d = .E7 q ∨ d = .E8 q := by
  rintro Y _ _ hY - hRk ⟨d, hv⟩ ⟨q, hdq⟩ - hf ⟨e⟩ - - - - J - - -
  have hq8 : q.card = 8 := by rcases hdq with rfl | rfl | rfl <;> exact hf
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center Y) :=
    I1431C2.cl_not_three_dvd_center hGA hY (d := ⟨d, hv⟩) (by
      rcases hdq with rfl | rfl | rfl
      · intro h
        simp only [CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverLieIndex] at h
        omega
      · exact fun h => h
      · exact fun h => h) e
  rcases hdq with rfl | rfl | rfl
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E6 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    exact (lieSEight_false_of_rkY_of_four_le hRk hZ e (lieSEight_four_le_E6 q hv hq8)).elim
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E7 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    exact (lieSEight_false_of_rkY_of_four_le hRk hZ e (lieSEight_four_le_E7 q hv hq8)).elim
  · haveI : Finite (TauCeti.CFSGIndex.lie ⟨.E8 q, hv⟩).Group := Finite.of_equiv _ e.toEquiv
    exact (lieSEight_false_of_rkY_of_four_le hRk hZ e (lieSEight_four_le_E8 q hv hq8)).elim

theorem lieSEightAt_twistedE6 :
    LieSEightAt fun d => ∃ q, d = .twistedE6 q := by
  rintro Y _ _ - - hRk ⟨d, hv⟩ ⟨q, hdq⟩ hc hf ⟨e⟩ - - - - J - - -
  subst hdq
  have hq8 : q.card = 8 := hf
  have hp : q.p = 2 := by simpa using hc
  have hexp : q.exponent = 3 := by
    have h := q.card_def
    rw [hq8, hp] at h
    exact (Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num : 8 = 2 ^ 3)))
  have hm := CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv hp e
  have hCE : ChevalleyExceptionalModel (Y ⧸ Subgroup.center Y) .twistedE6 2 q.exponent :=
    ⟨⟨Nat.prime_two, q.exponent_pos, rfl⟩, hm⟩
  have hLM : LieModel (Y ⧸ Subgroup.center Y) .twistedE6 0 2 q.exponent :=
    .inr (.inl ⟨rfl, by simp [chevalleyExceptionalTags], hCE⟩)
  exact (CFSG.HardMathSupport.Dickson.Sec6.I1431.rkY_false_twE6 hRk Nat.prime_two
    q.exponent_pos hCE hLM (by rw [hexp]; norm_num)).elim

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
