module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.InnerCover
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.FactorSp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.ClassicalBridgeB
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4B4
public import CFSG.HardMathSupport.Lang.AnisoF4.SpPairEvenSwap

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  SymplecticBlockPair linearBlockStandardPair_subgroupOf linearBlockStandardPair_le_sup
  symplecticBlockStandardPair_subgroupOf symplecticBlockStandardPair_le_sup
  symplecticBlockPair_subgroupOf symplecticBlockPair_le_sup iSup_subgroupOf_eq_top)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem innerRecog_of_range {p : ℕ} {Y G : Type} [Group Y] [Group G] (hY : LieFactorData p Y)
    (hA6 : IsEmpty ((Y ⧸ Subgroup.center Y) ≃* alternatingGroup (Fin 6))) (Ψ : Y →* G)
    (hker : Ψ.ker ≤ Subgroup.center Y) {H : Subgroup G} (hrange : Ψ.range = H) :
    InnerRecog p ↥H := by
  have hmem : ∀ y, Ψ y ∈ H := fun y => hrange ▸ ⟨y, rfl⟩
  refine ⟨Y, inferInstance, hY, hA6, Ψ.codRestrict H hmem, ?_, ?_⟩
  · rintro ⟨h, hh⟩
    obtain ⟨y, hy⟩ : h ∈ Ψ.range := hrange ▸ hh
    exact ⟨y, Subtype.ext hy⟩
  · intro y hy
    rw [MonoidHom.mem_ker] at hy
    exact hker (by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hy)

theorem innerRecog_of_sp3 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) {G : Type} [Group G] (Ψ : StatedSp 3 K →* G)
    (hker : Ψ.ker ≤ Subgroup.center (StatedSp 3 K)) {H : Subgroup G} (hrange : Ψ.range = H) :
    InnerRecog p ↥H := by
  haveI : Fintype K := Fintype.ofFinite K
  have hch : ringChar K = p := by
    haveI : CharP K (ringChar K) := ringChar.charP K
    obtain ⟨n, hq, hcard⟩ := FiniteField.card K (ringChar K)
    have hd : ringChar K ∣ p ^ f := by
      rw [← hK, Nat.card_eq_fintype_card, hcard]
      exact dvd_pow_self _ n.pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hd)
  have hne : (3, Fintype.card K) ≠ (2, 2) := by simp
  have hfd := spFactorFacts_holds K 3 (by norm_num) hne
  rw [hch] at hfd
  exact innerRecog_of_range hfd (spAltSixFacts_holds K 3 (by norm_num) hne) Ψ hker hrange


section Levi


@[expose] def b3Node : Fin 3 → Fin (Tag.rank .F4) := ![f4Node 0, f4Node 1, f4Node 2]

@[expose] def f4LeviB3 : Set (Fin (Tag.rank .F4)) := Set.range b3Node

theorem f4_cartan_02 : Tag.cartan .F4 (f4Node 0) (f4Node 2) = 0 := by decide

theorem f4Node_one_ne_two : f4Node 1 ≠ f4Node 2 := by decide

theorem map_subtype_iSup_b3 {K : Type} [Field K] :
    (⨆ k, rankOne (f4Datum K).rootGroup (b3Node k)).map (adjointGroup .F4 K).subtype =
      subsystemGroup .F4 K f4LeviB3 := by
  rw [Subgroup.map_iSup]
  simp only [f4Datum, map_subtype_rankOne_rootGroup]
  refine le_antisymm (iSup_le fun k => (Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_subsystemGroup (A := f4LeviB3) ⟨k, rfl⟩ c
    · exact yUnit_mem_subsystemGroup (A := f4LeviB3) ⟨k, rfl⟩ c
  · rintro _ ⟨i, ⟨k, rfl⟩, c, rfl | rfl⟩
    · exact Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
    · exact Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩))

theorem f4_linearPair {K : Type} [Field K] [Finite K] {i j k : Fin (Tag.rank .F4)} (hij : i ≠ j)
    (h1 : Tag.cartan .F4 i j = -1) (h2 : Tag.cartan .F4 j i = -1)
    (hk : ¬ (3 : ℤ) ∣ Tag.cartan .F4 i k + 2 * Tag.cartan .F4 j k) :
    ∃ W, LinearBlockStandardPair K W (rankOne (f4Datum K).rootGroup i)
      (rankOne (f4Datum K).rootGroup j) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  have hset : ∀ γ ∈ (f4Datum K).roots, ((f4Datum K).rootGroup γ : Set (adjointGroup .F4 K)) =
      Set.range (f4Par K γ) := fun γ hγ => Set.ext fun g => (hE.param γ hγ).1 g
  have hΦ := CFSG.LieType.RootSystem.isCTRootSystem (f4Datum K).isFiniteType
    (f4Datum K).divisible
  have hneg : ∀ l : Fin (Tag.rank .F4), -Pi.single l 1 ∈ (f4Datum K).roots := fun l =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots (f4Datum K).isFiniteType (hΦ.single_mem l)
  obtain ⟨emb, hinj, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl
    (i := i) (j := j) (k := k) hij h1 h2 hk
  refine ⟨emb.range, ClassicalInvolution.ModelFacts.linearBlockStandardPair_rankOne
    (f4Datum K).rootGroup (f4Par K) (hset _ (hΦ.single_mem _)) (hset _ (hneg _))
    (hset _ (hΦ.single_mem _)) (hset _ (hneg _)) emb ?_ hv⟩
  rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
  exact bot_le

theorem f4_spPair_odd {K : Type} [Field K] [Finite K] (hK4 : 4 ≤ Nat.card K)
    (h2 : (2 : K) ≠ 0) :
    ∃ W, SymplecticBlockStandardPair K W (rankOne (f4Datum K).rootGroup (f4Node 1))
      (rankOne (f4Datum K).rootGroup (f4Node 2)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  exact ClassicalInvolution.RouteD.exists_symplecticBlockStandardPair_rankOne hK4 h2 hE rfl
    (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12

theorem f4_spPair_even {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    ∃ W, SymplecticBlockStandardPair K W (rankOne (f4Datum K).rootGroup (f4Node 1))
      (rankOne (f4Datum K).rootGroup (f4Node 2)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  exact CFSG.HardMathSupport.Lang.AnisoF4.exists_symplecticBlockStandardPair_rankOne_even hK4 hE
    rfl (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12

theorem f4_spPair_even_swap {K : Type} [Field K] [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    ∃ W, SymplecticBlockStandardPair K W (rankOne (f4Datum K).rootGroup (f4Node 2))
      (rankOne (f4Datum K).rootGroup (f4Node 1)) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  exact CFSG.HardMathSupport.Lang.AnisoF4.exists_symplecticBlockStandardPair_rankOne_even_swap hK4
    hE rfl (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12

theorem f4_commutes_rankOne_zero_two {K : Type} [Field K] [Finite K] :
    Commutes (rankOne (f4Datum K).rootGroup (f4Node 0)) (rankOne (f4Datum K).rootGroup (f4Node 2)) :=
  ClassicalInvolution.RouteD.commutes_rankOne_of_cartan_eq_zero_of_longest (f4Datum K)
    (f4_steinbergExtras K) (fun ε hε => (ClassicalInvolution.RouteD.isLongestRoot_single_F4
      (k := f4Node 0) (by decide)).2 ε hε) f4_cartan_02

theorem f4_commutes_rankOne_one_three {K : Type} [Field K] [Finite K] :
    Commutes (rankOne (f4Datum K).rootGroup (f4Node 1)) (rankOne (f4Datum K).rootGroup (f4Node 3)) :=
  ClassicalInvolution.RouteD.commutes_rankOne_of_cartan_eq_zero_of_longest (f4Datum K)
    (f4_steinbergExtras K) (fun ε hε => (ClassicalInvolution.RouteD.isLongestRoot_single_F4
      (k := f4Node 1) (by decide)).2 ε hε) f4_cartan_13


theorem weakCT_symplectic_even_subgroup {n f : ℕ} (hadm : StatedLieAdmissible .PSp n 2 f)
    (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (hq : 4 ≤ Nat.card F) {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 1 = n → j.val + 2 = n →
      ∃ W, SymplecticBlockStandardPair F W (U i) (U j)) :
    ∃ Ψ : StatedSp n F →* G, Ψ.ker ≤ Subgroup.center (StatedSp n F) ∧ Ψ.range = ⨆ k, U k := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', hsurj, hker, -⟩ := CFSG.RankThree.PartOne.CTP.weakCT_symplectic_even hadm hn hF hq
    (U := fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hj => by
      obtain ⟨W, hW⟩ := hpair i j hij hj
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨W, hW⟩ := hsp i j hi hj
      exact ⟨W.subgroupOf Gs, symplecticBlockStandardPair_subgroupOf
        ((symplecticBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_⟩
  · intro x hx
    have : Ψ' x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    exact hker this
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

theorem weakCT_spinOdd_subgroup_full {n p f : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n p f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F)
    {G : Type} [Group G] (U : Fin n → Subgroup G)
    (hcomm : ∀ i j : Fin n, i.val + 1 < j.val → ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a)
    (hpair : ∀ i j : Fin n, i.val + 1 = j.val → j.val + 1 < n →
      ∃ W, LinearBlockStandardPair F W (U i) (U j))
    (hsp : ∀ i j : Fin n, i.val + 2 = n → j.val + 1 = n →
      ∃ W, SymplecticBlockPair F W (U i) (U j)) :
    CFSG.IsQuasisimple ↥(⨆ k, U k) ∧
      LieModel (↥(⨆ k, U k) ⧸ Subgroup.center ↥(⨆ k, U k)) .POmegaOdd n p f := by
  set Gs : Subgroup G := ⨆ k, U k with hGs
  have hUle : ∀ k, U k ≤ Gs := fun k => le_iSup U k
  obtain ⟨Ψ', -, -, hqs, -, hlie, -⟩ := CFSG.ClassicalInvolution.WeakCT.weakCT_spinOdd_of_pair hadm
    hF hq (X := ↥Gs) (fun k => (U k).subgroupOf Gs) (iSup_subgroupOf_eq_top U)
    (fun i j hij x hx y hy => Subtype.ext (hcomm i j hij x.1 hx y.1 hy))
    (fun i j hij hj => by
      obtain ⟨W, hW⟩ := hpair i j hij hj
      exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
        ((linearBlockStandardPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨W, hW⟩ := hsp i j hi hj
      exact ⟨W.subgroupOf Gs, symplecticBlockPair_subgroupOf
        ((symplecticBlockPair_le_sup hW).trans (sup_le (hUle i) (hUle j))) hW⟩)
  exact ⟨hqs, hlie⟩

theorem two_ne_zero_of_natCard_eq_pow {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 0 < f) (hK : Nat.card K = p ^ f) : (2 : K) ≠ 0 :=
  Ring.two_ne_zero (by rw [ringChar_eq_of_natCard_eq_pow hp hK hf]; exact hp2)

theorem innerRecog_f4_C3_odd {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    InnerRecog p ↥(subsystemGroup .F4 K f4LeviC3) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  obtain ⟨Ψ, hker, hrange, -, -⟩ := f4_levi_C3_recognition_frame hp hp2 hK
    (two_ne_zero_of_natCard_eq_pow hp hp2 hf hK)
  exact innerRecog_of_sp3 hp hf hK Ψ hker hrange

theorem innerRecog_f4_C3_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 0 < f)
    (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) :
    InnerRecog 2 ↥(subsystemGroup .F4 K f4LeviC3) := by
  obtain ⟨W, hW⟩ := f4_linearPair (K := K) (i := f4Node 2) (j := f4Node 3) (k := f4Node 1)
    f4Node_two_ne_three f4_cartan_23 f4_cartan_32 f4_sl3_witness
  obtain ⟨Wsp, hsp⟩ := f4_spPair_even (K := K) hK4
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_even_subgroup hadm le_rfl hK hK4
    (U := fun k => rankOne (f4Datum K).rootGroup (c3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact (f4_commutes_rankOne_one_three b hb a ha).symm)
    (fun i j hij hj => by
      obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
      exact ⟨W, hW.symm⟩)
    (fun i j hi hj => by
      obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
      exact ⟨Wsp, hsp⟩)
  refine innerRecog_of_sp3 Nat.prime_two hf hK ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

theorem innerRecog_f4_B3_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 0 < f)
    (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) :
    InnerRecog 2 ↥(subsystemGroup .F4 K f4LeviB3) := by
  obtain ⟨W, hW⟩ := f4_linearPair (K := K) (i := f4Node 0) (j := f4Node 1) (k := f4Node 2)
    f4Node_zero_ne_one f4_cartan_01 f4_cartan_10 f4_sl3_witness_01
  obtain ⟨Wsp, hsp⟩ := f4_spPair_even_swap (K := K) hK4
  have hadm : StatedLieAdmissible .PSp 3 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  obtain ⟨Ψ, hker, hrange⟩ := weakCT_symplectic_even_subgroup hadm le_rfl hK hK4
    (U := fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact f4_commutes_rankOne_zero_two a ha b hb)
    (fun i j hij hj => by
      obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
      exact ⟨W, hW⟩)
    (fun i j hi hj => by
      obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
      exact ⟨Wsp, hsp⟩)
  refine innerRecog_of_sp3 Nat.prime_two hf hK ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_b3]

theorem innerRecog_f4_B3_odd {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hK4 : 4 ≤ Nat.card K) :
    InnerRecog p ↥(subsystemGroup .F4 K f4LeviB3) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  obtain ⟨W, hW⟩ := f4_linearPair (K := K) (i := f4Node 0) (j := f4Node 1) (k := f4Node 2)
    f4Node_zero_ne_one f4_cartan_01 f4_cartan_10 f4_sl3_witness_01
  obtain ⟨Wsp, hsp⟩ := f4_spPair_odd (K := K) hK4 (two_ne_zero_of_natCard_eq_pow hp hp2 hf hK)
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hqs, hlie⟩ := weakCT_spinOdd_subgroup_full hadm hK hK4
    (U := fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact f4_commutes_rankOne_zero_two a ha b hb)
    (fun i j hij hj => by
      obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
      exact ⟨W, hW⟩)
    (fun i j hi hj => by
      have hij : i = 1 ∧ j = 2 := by revert i j; decide
      obtain ⟨rfl, rfl⟩ := hij
      exact ⟨Wsp, hsp.pair⟩)
  obtain ⟨hchev, hA6⟩ := lieModel_podd_chev hlie
  set Gs := ⨆ k, rankOne (f4Datum K).rootGroup (b3Node k) with hGs
  refine innerRecog_of_range (Y := ↥Gs) ⟨hqs.1.commutator_eq_top, hchev, fun ⟨e⟩ =>
    (hA6.false e).elim⟩ ⟨fun e => hA6.false e⟩
    ((adjointGroup .F4 K).subtype.comp Gs.subtype) ?_ ?_
  · intro x hx
    have : x = 1 := Subtype.ext (Subtype.ext (MonoidHom.mem_ker.mp hx))
    rw [this]
    exact Subgroup.one_mem _
  · rw [MonoidHom.range_comp, Gs.range_subtype, map_subtype_iSup_b3]


theorem mem_f4LeviB3 (j : Fin (Tag.rank .F4)) : j ∈ f4LeviB3 ↔ j.val ≤ 2 := by
  unfold f4LeviB3
  rw [Set.mem_range]
  revert j
  decide

theorem mem_f4LeviC3 (j : Fin (Tag.rank .F4)) : j ∈ f4LeviC3 ↔ 1 ≤ j.val := by
  unfold f4LeviC3
  rw [Set.mem_range]
  revert j
  decide

theorem innerRecog_f4_levi {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) (hK4 : 4 ≤ Nat.card K) :
    InnerRecog p ↥(subsystemGroup .F4 K J) := by
  by_cases hp2 : p = 2
  · subst hp2
    haveI : CharP K 2 := by
      have := ringChar_eq_of_natCard_eq_pow hp hK hf
      rw [← this]
      haveI : Fintype K := Fintype.ofFinite K
      exact ringChar.charP K
    rcases hJ with rfl | rfl
    · exact innerRecog_f4_B3_even hf hK hK4
    · exact innerRecog_f4_C3_even hf hK hK4
  · rcases hJ with rfl | rfl
    · exact innerRecog_f4_B3_odd hp hp2 hK hK4
    · exact innerRecog_f4_C3_odd hp hp2 hK

end Levi

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
