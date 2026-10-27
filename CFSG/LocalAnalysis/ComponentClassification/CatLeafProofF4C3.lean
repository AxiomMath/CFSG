module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Model
public import CFSG.ClassicalInvolution.RouteD.LocalTwinSp
public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.ModelFacts.StandardPair
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] def f4Node (i : Fin 4) : Fin (Tag.rank .F4) := i

@[expose] def c3Node : Fin 3 → Fin (Tag.rank .F4) := ![f4Node 3, f4Node 2, f4Node 1]

theorem f4_cartan_21 : Tag.cartan .F4 (f4Node 2) (f4Node 1) = -2 := by decide
theorem f4_cartan_12 : Tag.cartan .F4 (f4Node 1) (f4Node 2) = -1 := by decide
theorem f4_cartan_23 : Tag.cartan .F4 (f4Node 2) (f4Node 3) = -1 := by decide
theorem f4_cartan_32 : Tag.cartan .F4 (f4Node 3) (f4Node 2) = -1 := by decide
theorem f4_cartan_13 : Tag.cartan .F4 (f4Node 1) (f4Node 3) = 0 := by decide
theorem f4Node_two_ne_three : f4Node 2 ≠ f4Node 3 := by decide

theorem f4_sl3_witness :
    ¬ (3 : ℤ) ∣ Tag.cartan .F4 (f4Node 2) (f4Node 1) +
      2 * Tag.cartan .F4 (f4Node 3) (f4Node 1) := by
  decide

theorem fin3_lt_cases : ∀ i j : Fin 3, i.val + 1 < j.val → i = 0 ∧ j = 2 := by decide

theorem fin3_adj_cases : ∀ i j : Fin 3, i.val + 1 = j.val → j.val + 1 < 3 → i = 0 ∧ j = 1 := by
  decide

theorem fin3_end_cases : ∀ i j : Fin 3, i.val + 1 = 3 → j.val + 2 = 3 → i = 2 ∧ j = 1 := by
  decide

theorem exists_psi_C3_F4
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hq : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) :
    ∃ Ψ : StatedSp 3 K →* adjointGroup .F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = ⨆ k, rankOne (f4Datum K).rootGroup (c3Node k) ∧
      IsQuasisimple ↥(⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) ∧
      Blueprint.LieModel (↥(⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) ⧸
        Subgroup.center ↥(⨆ k, rankOne (f4Datum K).rootGroup (c3Node k))) .PSp 3 p f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
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
  have hlin : ∃ W, LinearBlockStandardPair K W (rankOne (f4Datum K).rootGroup (f4Node 2))
      (rankOne (f4Datum K).rootGroup (f4Node 3)) := by
    obtain ⟨emb, hinj, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl
      (i := f4Node 2) (j := f4Node 3) (k := f4Node 1) f4Node_two_ne_three f4_cartan_23
      f4_cartan_32 f4_sl3_witness
    refine ⟨emb.range, ClassicalInvolution.ModelFacts.linearBlockStandardPair_rankOne
      (f4Datum K).rootGroup (f4Par K) (hset _ (hΦ.single_mem _)) (hset _ (hneg _))
      (hset _ (hΦ.single_mem _)) (hset _ (hneg _)) emb ?_ hv⟩
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact bot_le
  have hsp := ClassicalInvolution.RouteD.exists_symplecticBlockStandardPair_rankOne hq h2 hE rfl
    (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12
  have hcomm : Commutes (rankOne (f4Datum K).rootGroup (f4Node 1))
      (rankOne (f4Datum K).rootGroup (f4Node 3)) :=
    ClassicalInvolution.RouteD.commutes_rankOne_of_cartan_eq_zero_of_longest (f4Datum K)
      (f4_steinbergExtras K) (fun ε hε => (ClassicalInvolution.RouteD.isLongestRoot_single_F4
        (k := f4Node 1) (by decide)).2 ε hε) f4_cartan_13
  have hc : ∀ i j : Fin 3, i.val + 1 < j.val →
      ∀ a ∈ rankOne (f4Datum K).rootGroup (c3Node i),
        ∀ b ∈ rankOne (f4Datum K).rootGroup (c3Node j), a * b = b * a := by
    intro i j hij a ha b hb
    obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
    exact (hcomm b hb a ha).symm
  have hpr : ∀ i j : Fin 3, i.val + 1 = j.val → j.val + 1 < 3 →
      ∃ W, LinearBlockStandardPair K W (rankOne (f4Datum K).rootGroup (c3Node i))
        (rankOne (f4Datum K).rootGroup (c3Node j)) := by
    intro i j hij hj
    obtain ⟨rfl, rfl⟩ := fin3_adj_cases i j hij hj
    obtain ⟨W, hW⟩ := hlin
    exact ⟨W, hW.symm⟩
  have hsr : ∀ i j : Fin 3, i.val + 1 = 3 → j.val + 2 = 3 →
      ∃ W, SymplecticBlockStandardPair K W (rankOne (f4Datum K).rootGroup (c3Node i))
        (rankOne (f4Datum K).rootGroup (c3Node j)) := by
    intro i j hi hj
    obtain ⟨rfl, rfl⟩ := fin3_end_cases i j hi hj
    exact hsp
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ :=
    ClassicalInvolution.Models.SymplecticPairs.weakCT_symplectic_subgroup hadm le_rfl hp2 hK hq
      (fun k => rankOne (f4Datum K).rootGroup (c3Node k)) hc hpr hsr
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

@[expose] def f4LeviC3 : Set (Fin (Tag.rank .F4)) := Set.range c3Node

theorem map_subtype_rootGroup
    {τ : Tag} {K : Type} [Field K]
    (F : RootOperatorFamily τ) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    (rootGroup F K δ).map (adjointGroup τ K).subtype = rootSubgroup τ K δ := by
  rw [rootGroup_of_isRoot hδ, ← F.subgroupOf_rootSubgroup_eq K ⟨δ, hδ⟩,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left (rootSubgroup_le_adjointGroup δ)]

theorem map_subtype_rankOne_rootGroup
    {τ : Tag} {K : Type} [Field K] (F : RootOperatorFamily τ)
    (i : Fin τ.rank) :
    (rankOne (rootGroup F K) i).map (adjointGroup τ K).subtype =
      Subgroup.closure (Set.range (xUnit τ K i) ∪ Set.range (yUnit τ K i)) := by
  rw [closure_xUnit_yUnit_eq_rootSubgroup_sup, ← map_subtype_rootGroup F (isRoot_single τ i),
    ← map_subtype_rootGroup F (isRoot_neg_single τ i), ← Subgroup.map_sup]
  rfl

theorem map_subtype_iSup_c3
    {K : Type} [Field K] :
    (⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)).map (adjointGroup .F4 K).subtype =
      subsystemGroup .F4 K f4LeviC3 := by
  rw [Subgroup.map_iSup]
  simp only [f4Datum, map_subtype_rankOne_rootGroup]
  refine le_antisymm (iSup_le fun k => (Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_)
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_subsystemGroup (A := f4LeviC3) ⟨k, rfl⟩ c
    · exact yUnit_mem_subsystemGroup (A := f4LeviC3) ⟨k, rfl⟩ c
  · rintro _ ⟨i, ⟨k, rfl⟩, c, rfl | rfl⟩
    · exact Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
    · exact Subgroup.mem_iSup_of_mem k (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩))

theorem f4_levi_C3_recognition
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (hq : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) :
    ∃ Ψ : StatedSp 3 K →* ModGL .F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviC3 ∧
      IsQuasisimple ↥(subsystemGroup .F4 K f4LeviC3) ∧
      Blueprint.LieModel (↥(subsystemGroup .F4 K f4LeviC3) ⧸
        Subgroup.center ↥(subsystemGroup .F4 K f4LeviC3)) .PSp 3 p f := by
  obtain ⟨Ψ, hker, hrange, hqs, hlie⟩ := exists_psi_C3_F4 hp hp2 hK hq h2
  set U := ⨆ k, rankOne (f4Datum K).rootGroup (c3Node k) with hU
  let e : U ≃* subsystemGroup .F4 K f4LeviC3 :=
    (U.equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr map_subtype_iSup_c3)
  refine ⟨(adjointGroup .F4 K).subtype.comp Ψ, ?_, ?_,
    LocalCores.isQuasisimple_of_mulEquiv e hqs,
    lieModel_of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hlie⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

end CFSG.ComponentClassification.CatLeafProof
