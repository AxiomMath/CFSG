module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPF4B2
public import CFSG.ClassicalInvolution.Q3.Q3VCtMainSub
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
  CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq blk spBlock edgeUp
  hom_ext_sl2 spBlock_zero_eq_shortBlock spBlock_one_eq_longBlock)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

section Small


namespace CompsPF4Small

theorem f4_sl3_witness_10_copy :
    ¬ (3 : ℤ) ∣ Tag.cartan .F4 (f4Node 1) (f4Node 2) +
      2 * Tag.cartan .F4 (f4Node 0) (f4Node 2) := by
  decide

theorem fin3_up_nadj : ∀ i j : Fin 3, i ≠ j → ¬ edgeUp 3 i j → ¬ edgeUp 3 j i →
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  decide

theorem fin3_up_single : ∀ i j : Fin 3, edgeUp 3 i j → ¬ (i = 1 ∧ j = 2) → i = 0 ∧ j = 1 := by
  decide

theorem sq_eq_self_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) (c : K) :
    c ^ 2 = c := by
  haveI : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card c
  rwa [← Nat.card_eq_fintype_card, hK] at h

theorem b3Frame_model {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h2 : (2 : K) ≠ 0) :
    IsQuasisimple ↥(⨆ k, rankOne (f4Datum K).rootGroup (b3Node k)) ∧
      LieModel (↥(⨆ k, rankOne (f4Datum K).rootGroup (b3Node k)) ⧸
        Subgroup.center ↥(⨆ k, rankOne (f4Datum K).rootGroup (b3Node k))) .POmegaOdd 3 p f := by
  obtain ⟨hf, hq3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaOdd 3 p f := ⟨hp, hf, le_rfl, hp2⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨O'⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum 3 K).isFiniteType
    (Dv := (Spin.oddDatum 3 K).divisible) rfl
  have hE' := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ 3) O' Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O')
  have hsq : ∀ k : Fin 3,
      Steinberg.weylElement (Steinberg.SpinOdd.x 3 K) k 1 ^ 2 ∈ (Spin.torusB K k).range := by
    intro k
    have h := (Spin.oddDatum_isCTGroupDatum 3 K
      (Spin.oddDatum_iSup_eq_top 3 K h2 (by norm_num))).sq_mem k
    have e := Steinberg.SpinOdd.weylElement_eq (n := 3) (K := K) k 1
    rw [map_one, one_mul] at e
    rw [e]
    exact h
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_dl_subgroup
    (CurtisTits.curtisTitsConclusion_spinOdd hadm hK) (leviConePresented_spinOdd h2 (by norm_num))
    hE' rfl (isQuasisimple_statedSp_two hq3) h2
    (ClassicalInvolution.WeakCT.doubleBondDiagram_cartanB (n := 3) (a := 1) (b := 2) rfl rfl)
    (Spin.oddDatum_steinbergExtras h2).torus_iSupIndep hsq
    (U := fun k => rankOne (f4Datum K).rootGroup (b3Node k))
    (fun i j hne hij hji u hu v hv => by
      rcases fin3_up_nadj i j hne hij hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact f4_commutes_rankOne_zero_two u hu v hv
      · exact (f4_commutes_rankOne_zero_two v hv u hu).symm)
    (ρ := fun k => ρF (b3Node k)) (fun k => hρFr _) (hρFi (f4Node 1))
    (fun i j hij hne => by
      obtain ⟨rfl, rfl⟩ := fin3_up_single i j hij hne
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 0) (j := f4Node 1)
        (k := f4Node 2) f4Node_zero_ne_one f4_cartan_01 f4_cartan_10 f4_sl3_witness_01
      exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 0)) (hρFv (f4Node 1))⟩)
    (by
      obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
        exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
      obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
      exact ⟨φ, hb1, hb0⟩)
  exact ⟨hqs, hlie⟩

end CompsPF4Small

theorem innerRecog_f4_B3_odd_any {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) :
    InnerRecog p ↥(subsystemGroup .F4 K f4LeviB3) := by
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  obtain ⟨hqs, hlie⟩ := CompsPF4Small.b3Frame_model hp hp2 hK (two_ne_zero_of_natCard_eq_pow hp hp2 hf hK)
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

theorem innerRecog_f4_C3_fam {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) : InnerRecog p ↥(subsystemGroup .F4 K f4LeviC3) := by
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
  refine innerRecog_of_sp3 hp hf hK ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_c3]

namespace CompsPF4Small

theorem sp4Graph_comp_spBlock_one {K : Type} [Field K] [Finite K] [CharP K 2] :
    (CFSG.RankThree.PartTwo.KFacts.sp4Graph K).toMonoidHom.comp (spBlock K 1) = spBlock K 0 := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_one_eq_longBlock,
      spBlock_zero_eq_shortBlock, tv01_eq_sl2Upper]
    exact CFSG.HardMathSupport.Lang.AnisoF4.sp4Graph_longBlock_sl2Upper c
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_one_eq_longBlock,
      spBlock_zero_eq_shortBlock, tv10_eq_sl2Lower]
    exact CFSG.HardMathSupport.Lang.AnisoF4.sp4Graph_longBlock_sl2Lower c

theorem sp4Graph_comp_spBlock_zero {K : Type} [Field K] [Finite K] [CharP K 2]
    (hsq : ∀ c : K, c ^ 2 = c) :
    (CFSG.RankThree.PartTwo.KFacts.sp4Graph K).toMonoidHom.comp (spBlock K 0) = spBlock K 1 := by
  refine hom_ext_sl2 (fun c => ?_) (fun c => ?_)
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_one_eq_longBlock,
      spBlock_zero_eq_shortBlock, tv01_eq_sl2Upper]
    rw [CFSG.HardMathSupport.Lang.AnisoF4.sp4Graph_shortBlock_sl2Upper c, hsq c]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spBlock_one_eq_longBlock,
      spBlock_zero_eq_shortBlock, tv10_eq_sl2Lower]
    rw [CFSG.HardMathSupport.Lang.AnisoF4.sp4Graph_shortBlock_sl2Lower c, hsq c]

theorem card_eq_two_of_lt_four {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 0 < f)
    (hK : Nat.card K = 2 ^ f) (h4 : ¬ 4 ≤ Nat.card K) : Nat.card K = 2 := by
  have hf1 : f < 2 := by
    by_contra h
    rw [not_lt] at h
    apply h4
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h
  interval_cases f
  simpa using hK

end CompsPF4Small

theorem innerRecog_f4_B3_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    InnerRecog 2 ↥(subsystemGroup .F4 K f4LeviB3) := by
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
  refine innerRecog_of_sp3 Nat.prime_two Nat.one_pos hK' ((adjointGroup .F4 K).subtype.comp Ψ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, map_subtype_iSup_b3]

theorem innerRecog_f4_levi_any {J : Set (Fin (Tag.rank .F4))}
    (hJ : J = f4LeviB3 ∨ J = f4LeviC3) {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hf : 0 < f) (hK : Nat.card K = p ^ f) : InnerRecog p ↥(subsystemGroup .F4 K J) := by
  by_cases hK4 : 4 ≤ Nat.card K
  · exact innerRecog_f4_levi hJ hp hf hK hK4
  · rcases hJ with rfl | rfl
    · by_cases hp2 : p = 2
      · subst hp2
        exact innerRecog_f4_B3_two (CompsPF4Small.card_eq_two_of_lt_four hf hK hK4)
      · exact innerRecog_f4_B3_odd_any hp hp2 hK
    · exact innerRecog_f4_C3_fam hp hf hK

theorem rationalLieType_of_f4Levi_class_any {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  refine rationalLieType_of_innerRecog_card S hTor i hinner (fun K' hfin hcardK' => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    show rootSpan Tag.F4 K' (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardf⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardf
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have hrec := innerRecog_f4_levi_any hJ hprime f.pos hK'card
  have hsub : subsystemGroup Tag.F4 ↥K' J = rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 J) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) ↥K'
  rw [hsub] at hrec
  exact innerRecog_rootSpan_smul v (fun α hα => hα.1) hrec

end Small

section Reduce


@[expose] def ExcRationalLieTypesF4B2TwoP (p : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.F4 L p₀)
    (a : Fin Tag.F4.rank → Lˣ), rootDiagUnit Tag.F4 a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
    rootDiagUnit Tag.F4 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) →
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      compRank (componentRoots (rootCharHom a) i) = 2 →
      (componentRoots (rootCharHom a) i).ncard = 8 →
      ¬ (3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excRationalLieTypesF4SmallP_of_B2two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ExcRationalLieTypesF4B2TwoP p) : ExcRationalLieTypesF4SmallP p := by
  intro L _ _ p₀ S a hT hap h1 i hA hinner hshape hq
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hshape with ⟨hr2, hn8, hQ⟩ | ⟨hr3, hn18, hQ⟩
  · exact h L p₀ S a hT hap h1 i hA hinner hr2 hn8 hQ hq
  · rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨v, J, hJ, hroots, -, -⟩
    · omega
    · exact (rationalLieType_of_f4Levi_class_any S hT i v hJ hroots hinner).lieCompData

theorem excRationalLieTypesF4Two_holds : ExcRationalLieTypesF4Two := by
  intro L _ _ p₀ S a hT hap h1 i hnonA hinner hQ hqs
  classical
  have hℓ3 : ringChar L ≠ 3 := ringChar_ne_three_of_pow_three hap h1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have hd : ringChar L ∣ 3 := (ringChar.spec L 3).1 (by exact_mod_cast h)
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h' | h'
    · exact CharP.ringChar_ne_one h'
    · exact hℓ3 h'
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      h3L hTp i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exact (not_comp_eq_B2_F4 (p := 3) le_rfl hμ hcomp).elim
  · exact rationalLieType_of_f4Levi_class_any S hT i v (J := f4LeviB3) (Or.inl rfl)
      (by
        rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
          (fun j => by rw [mem_f4LeviB3]; revert j; decide)]) hinner
  · exact rationalLieType_of_f4Levi_class_any S hT i v (J := f4LeviC3) (Or.inr rfl)
      (by
        rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
          (fun j => by rw [mem_f4LeviC3]; revert j; decide)]) hinner
  · exact (not_comp_eq_B4_F4 hμ hcomp).elim
  · exfalso
    apply h1
    refine eq_one_of_simple_mem_class i (fun j => ?_)
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := Set.univ) (by decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
    exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
      (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

end Reduce

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
