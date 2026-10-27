module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ1W
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicGenCensus
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.Sporadic.Schreier.J1Outer

public section

namespace CFSG.ComponentClassification.RankTwoSporadic.J1

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.Sporadic.Schreier
open CFSG.ABGLocalTools CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem j1Gens_zero : j1Gens[0]! = j1A1List.toArray := rfl

theorem j1Gens_one : j1Gens[1]! = j1A2List.toArray := rfl

theorem rep_j1Gens_zero : Rep 3080 j1Gens[0]! j1A1 := by
  have h := isPermList_j1A1List
  simp only [isPermList, Bool.and_eq_true, beq_iff_eq] at h
  rw [j1Gens_zero]
  exact (rep_permOfArr h.2).1

theorem rep_j1Gens_one : Rep 3080 j1Gens[1]! j1A2 := by
  have h := isPermList_j1A2List
  simp only [isPermList, Bool.and_eq_true, beq_iff_eq] at h
  rw [j1Gens_one]
  exact (rep_permOfArr h.2).1

theorem closure_j1Gens : closure (permsA 3080 j1Gens) = j1P := by
  have h : permsA 3080 j1Gens = {j1A1, j1A2} := by
    ext x
    simp only [permsA, Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have hk2 : k < 2 := hk
      interval_cases k
      · exact .inl (permOfArr_eq_of_rep rep_j1Gens_zero)
      · exact .inr (permOfArr_eq_of_rep rep_j1Gens_one)
    · rintro (rfl | rfl)
      · exact ⟨0, show 0 < 2 by norm_num, permOfArr_eq_of_rep rep_j1Gens_zero⟩
      · exact ⟨1, show 1 < 2 by norm_num, permOfArr_eq_of_rep rep_j1Gens_one⟩
  rw [h]
  rfl

theorem j1P_center_eq_bot :
    center ↥j1P = ⊥ := by
  have := isSimpleGroup_j1P
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥j1P) with h | h
  · exact h
  · exfalso
    let _ : CommGroup ↥j1P :=
      { (inferInstance : Group ↥j1P) with
        mul_comm := fun a b => mem_center_iff.mp (h ▸ mem_top b) a }
    have hp := IsSimpleGroup.prime_card (α := ↥j1P)
    rw [card_j1P] at hp
    exact absurd hp (by norm_num)

theorem j1P_allInner :
    ∀
    α : MulAut ↥j1P, ∃ g : ↥j1P, α = MulAut.conj g := by
  have : Finite (MulAut ↥j1P) :=
    Finite.of_injective (fun α : MulAut ↥j1P => (α : ↥j1P → ↥j1P)) DFunLike.coe_injective
  have hsub : Subsingleton (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥j1P) :=
    Finite.card_le_one_iff_subsingleton.1 outer_j1P_card_le
  intro α
  have h1 : (α : CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥j1P) = 1 :=
    Subsingleton.elim _ _
  obtain ⟨g, hg⟩ := (QuotientGroup.eq_one_iff α).1 h1
  exact ⟨g, hg.symm⟩

theorem j1AutModel :
    AutModel (Blueprint.NativeSporadic.Carrier .J1) ↥j1P (j1P.subgroupOf j1P) :=
  autModel_of_allInner j1PermEquiv.symm j1P_center_eq_bot j1P_allInner

theorem j1_yCensusII : YCensus (j1P.subgroupOf j1P) (· ≤ j1P.subgroupOf j1P) := by
  rw [subgroupOf_self]
  exact yCensus_top_le_top

theorem census_of_j1Check
    {prog : List (ℕ × ℕ)} {sG : Array ℕ}
    {nodes : Array CFSG.KC.Census.FNodeP} {cS : CFSG.KC.Census.ArrCertP}
    (h : j1CheckW prog sG nodes cS = true) :
    YCensusF (j1P.subgroupOf j1P) (fun _ => False) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [j1CheckW, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hslp, hc⟩, hgen⟩, hsize⟩ := h
  set regs := slpRegs 3080 j1Gens prog
  set sGens := sG.map (CFSG.KC.Census.unpackP 3080 12)
  have hmap : (j1P.subgroupOf j1P).map j1P.subtype = j1P := by
    rw [subgroupOf_map_subtype, inf_idem]
  have hmem : ∀ a, validA 3080 a = true → inRegsL 3080 regs a = true →
      permOfArr 3080 a ∈ j1P := fun a hv ha => closure_j1Gens ▸ mem_closure_of_inRegsL hslp hv ha
  have hin : ∀ a, validA 3080 a = true → inRegsL 3080 regs a = true →
      permOfArr 3080 a ∈ (j1P.subgroupOf j1P).map j1P.subtype := fun a hv ha => by
    rw [hmap]
    exact hmem a hv ha
  have hX : (j1P.subgroupOf j1P).map j1P.subtype ≤ closure (permsA 3080 j1Gens) := by
    rw [hmap, closure_j1Gens]
  have hc' := hc
  simp only [fCensusOKW, Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨hS, -⟩, -⟩, -⟩ := hc'
  set S' := closure (permsA 3080 sGens)
  have hS'le : S' ≤ j1P.subtype.range := by
    rw [closure_le, range_subtype]
    rintro _ ⟨k, hk, rfl⟩
    exact hmem _ (enumOK_gens_valid hS hk) (allLt_spec hgen hk)
  obtain ⟨-, hS'card, -⟩ := enumOK_spec j1PS_lt hS
  set S := S'.comap j1P.subtype
  have hSmap : S.map j1P.subtype = S' := map_comap_eq_self hS'le
  have hScard : Nat.card S = 8 := by
    rw [← card_map_of_injective j1P.subtype_injective, hSmap, hS'card, hsize]
  have hSyl : IsSylowOf 2 S ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right]
    refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hScard]; norm_num), ?_⟩
    have h1 := S.card_mul_index
    rw [hScard, card_j1P] at h1
    omega
  have hN : (j1P.subgroupOf j1P).Normal := by
    rw [subgroupOf_self]
    infer_instance
  refine yCensusF_of_le_sylow hN hSyl (fun _ _ h => h) fun E hES hE hE4 _ => Or.inr ?_
  have hES' : E.map j1P.subtype ≤ S' := hSmap ▸ map_mono hES
  have hF := fWitness_of_fCensusOKW j1PS_lt hin hX hc hES' (isElemAbelian_map hE _)
    (by rwa [card_map_of_injective j1P.subtype_injective])
  exact (fWitness_map_iff _ j1P.subtype_injective _ _).mp hF

theorem sporadicCaseOdd_J1_of_check
    {prog : List (ℕ × ℕ)} {sG : Array ℕ} {nodes : Array CFSG.KC.Census.FNodeP}
    {cS : CFSG.KC.Census.ArrCertP} (hc : j1CheckW prog sG nodes cS = true)
    (h32 : AS76b.Lemma32) (h33 : AS76b.Lemma33Three) : SporadicCaseOdd .J1 :=
  sporadicCaseOdd_of_yCensusF h32 h33 j1AutModel j1_yCensusII (census_of_j1Check hc)

end CFSG.ComponentClassification.RankTwoSporadic.J1
