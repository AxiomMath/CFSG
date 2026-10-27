module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4Small

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FamF42

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq blk spBlock edgeUp
  hom_ext_sl2 spBlock_zero_eq_shortBlock spBlock_one_eq_longBlock)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000


theorem exists_sp3Hom_f4_C3 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hK : Nat.card K = p ^ f) :
    ∃ Ψ : StatedSp 3 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviC3 := by
  classical
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨ψ0, hψ0a, hψ0b⟩ : ∃ ψ : SL(3, K) →* adjointGroup .F4 K,
      ψ.comp (blk K 0) = ρF (f4Node 2) ∧ ψ.comp (blk K 1) = ρF (f4Node 3) := by
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 2) (j := f4Node 3)
      (k := f4Node 1) f4Node_two_ne_three f4_cartan_23 f4_cartan_32 f4_sl3_witness
    exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 2)) (hρFv (f4Node 3))⟩
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 K →* adjointGroup .F4 K,
      φ.comp (spBlock K 1) = ρF (f4Node 1) ∧ φ.comp (spBlock K 0) = ρF (f4Node 2) := by
    obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    exact ⟨φ, hb1, hb0⟩
  obtain ⟨Ψ, hker, hrange, -⟩ := ClassicalInvolution.Q3.Q3V.weakCT_symplectic_subgroup_of_family
    hadm le_rfl hK (G := adjointGroup .F4 K)
    (fun k => rankOne (f4Datum K).rootGroup (c3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact (f4_commutes_rankOne_one_three b hb a ha).symm)
    (fun k => ρF (c3Node k)) (fun k => ⟨hρFi _, hρFr _⟩)
    (fun _ _ => ψ0)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0a)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0b)
    φ hφl hφs
  refine ⟨(adjointGroup .F4 K).subtype.comp Ψ, fun x hx => ?_, ?_⟩
  · exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

theorem exists_sp3Hom_f4_B3_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ Ψ : StatedSp 3 K →* ModGL Tag.F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviB3 := by
  classical
  haveI : CharP K 2 := by
    have := ringChar_eq_of_natCard_eq_pow Nat.prime_two (f := 1) (by rw [hK]; norm_num) Nat.one_pos
    rw [← this]
    haveI : Fintype K := Fintype.ofFinite K
    exact ringChar.charP K
  have hsq := CompsPF4Small.sq_eq_self_of_card_two hK
  have hK' : Nat.card K = 2 ^ 1 := by rw [hK]; norm_num
  have hadm : StatedLieAdmissible .PSp 3 2 1 := ⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨ψ0, hψ0a, hψ0b⟩ : ∃ ψ : SL(3, K) →* adjointGroup .F4 K,
      ψ.comp (blk K 0) = ρF (f4Node 1) ∧ ψ.comp (blk K 1) = ρF (f4Node 0) := by
    obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 1) (j := f4Node 0)
      (k := f4Node 2) f4Node_zero_ne_one.symm f4_cartan_10 f4_cartan_01
      CompsPF4Small.f4_sl3_witness_10_copy
    exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 1)) (hρFv (f4Node 0))⟩
  obtain ⟨φ, hφl, hφs⟩ : ∃ φ : StatedSp 2 K →* adjointGroup .F4 K,
      φ.comp (spBlock K 1) = ρF (f4Node 2) ∧ φ.comp (spBlock K 0) = ρF (f4Node 1) := by
    obtain ⟨φ₀, e, -, he1, he2, he3, he4, hφ⟩ :=
      exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
    obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
    refine ⟨φ₀.comp (CFSG.RankThree.PartTwo.KFacts.sp4Graph K).toMonoidHom, ?_, ?_⟩
    · rw [MonoidHom.comp_assoc, CompsPF4Small.sp4Graph_comp_spBlock_one, hb0]
    · rw [MonoidHom.comp_assoc, CompsPF4Small.sp4Graph_comp_spBlock_zero hsq, hb1]
  obtain ⟨Ψ, hker, hrange, -⟩ := ClassicalInvolution.Q3.Q3V.weakCT_symplectic_subgroup_of_family
    hadm le_rfl hK' (G := adjointGroup .F4 K)
    (fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hij a ha b hb => by
      obtain ⟨rfl, rfl⟩ := fin3_lt_cases i j hij
      exact f4_commutes_rankOne_zero_two a ha b hb)
    (fun k => ρF (b3Node k)) (fun k => ⟨hρFi _, hρFr _⟩)
    (fun _ _ => ψ0)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0a)
    (fun i h => by
      obtain rfl : i = 0 := Fin.ext (by have := i.2; omega)
      exact hψ0b)
    φ hφl hφs
  refine ⟨(adjointGroup .F4 K).subtype.comp Ψ, fun x hx => ?_, ?_⟩
  · exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_b3]

end CFSG.HardMathSupport.Dickson.Bal207.FamF42

end
