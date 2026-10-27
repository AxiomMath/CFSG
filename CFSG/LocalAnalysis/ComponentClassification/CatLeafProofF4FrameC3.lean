module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4C3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofFrameDLSubgroup

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq edgeDown)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem one_le_and_three_le_of_card {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) : 1 ≤ f ∧ 3 ≤ Nat.card K := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · have := Finite.one_lt_card (α := K)
      rw [hK, h0, pow_zero] at this
      omega
    · exact h0
  refine ⟨hf, ?_⟩
  have hp3 : 3 ≤ p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  rw [hK]
  calc 3 ≤ p := hp3
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf

theorem fin3_down_nadj : ∀ i j : Fin 3, i ≠ j → ¬ edgeDown 3 i j → ¬ edgeDown 3 j i →
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  decide

theorem fin3_down_single : ∀ i j : Fin 3, edgeDown 3 i j → ¬ (i = 2 ∧ j = 1) → i = 1 ∧ j = 0 := by
  decide

theorem exists_psi_C3_F4_frame
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h2 : (2 : K) ≠ 0) :
    ∃ Ψ : StatedSp 3 K →* adjointGroup .F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = ⨆ k, rankOne (f4Datum K).rootGroup (c3Node k) ∧
      IsQuasisimple ↥(⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) ∧
      Blueprint.LieModel (↥(⨆ k, rankOne (f4Datum K).rootGroup (c3Node k)) ⧸
        Subgroup.center ↥(⨆ k, rankOne (f4Datum K).rootGroup (c3Node k))) .PSp 3 p f := by
  obtain ⟨hf, hq3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .PSp 3 p f := ⟨hp, hf, by norm_num, by simp⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  obtain ⟨O'⟩ := Steinberg.nonempty_commOrder_ofCartan (Symplectic.rootDatum 3 K).isFiniteType
    (Dv := (Symplectic.rootDatum 3 K).divisible) rfl
  have hE' := Steinberg.Sp.chevalleyExtras (by omega : 2 ≤ 3) O' Steinberg.Sp.commC
    (Steinberg.Sp.commutatorFormula O')
  have hsq : ∀ k : Fin 3,
      Steinberg.weylElement (Steinberg.Sp.x 3 K) k 1 ^ 2 ∈ Symplectic.torus 3 K k := by
    intro k
    rw [ClassicalInvolution.WeakCT.weylElement_sp_one]
    exact (Symplectic.isCTGroupDatum 3 K).sq_mem k
  have hcomm13 : Commutes (rankOne (f4Datum K).rootGroup (f4Node 1))
      (rankOne (f4Datum K).rootGroup (f4Node 3)) :=
    ClassicalInvolution.RouteD.commutes_rankOne_of_cartan_eq_zero_of_longest (f4Datum K)
      (f4_steinbergExtras K) (fun ε hε => (ClassicalInvolution.RouteD.isLongestRoot_single_F4
        (k := f4Node 1) (by decide)).2 ε hε) f4_cartan_13
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_dl_subgroup
    (CurtisTits.curtisTitsConclusion_symplectic hadm hK le_rfl) (leviConePresented_symplectic 3 K)
    hE' rfl (isQuasisimple_statedSp_two hq3) h2
    (ClassicalInvolution.WeakCT.doubleBondDiagram_cartanC (n := 3) le_rfl (a := 2) (b := 1) rfl
      rfl)
    (Symplectic.steinbergExtras 3 K).torus_iSupIndep hsq
    (U := fun k => rankOne (f4Datum K).rootGroup (c3Node k))
    (fun i j hne hij hji u hu v hv => by
      rcases fin3_down_nadj i j hne hij hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hcomm13 v hv u hu).symm
      · exact hcomm13 u hu v hv)
    (ρ := fun k => ρF (c3Node k)) (fun k => hρFr _) (hρFi _)
    (fun i j hij hne => by
      obtain ⟨rfl, rfl⟩ := fin3_down_single i j hij hne
      obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 2) (j := f4Node 3)
        (k := f4Node 1) f4Node_two_ne_three f4_cartan_23 f4_cartan_32 f4_sl3_witness
      exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 2)) (hρFv (f4Node 3))⟩)
    (by
      obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
        exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
      obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
      exact ⟨φ, hb1, hb0⟩)
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

theorem f4_levi_C3_recognition_frame
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h2 : (2 : K) ≠ 0) :
    ∃ Ψ : StatedSp 3 K →* ModGL .F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 3 K) ∧
      Ψ.range = subsystemGroup .F4 K f4LeviC3 ∧
      IsQuasisimple ↥(subsystemGroup .F4 K f4LeviC3) ∧
      Blueprint.LieModel (↥(subsystemGroup .F4 K f4LeviC3) ⧸
        Subgroup.center ↥(subsystemGroup .F4 K f4LeviC3)) .PSp 3 p f := by
  obtain ⟨Ψ, hker, hrange, hqs, hlie⟩ := exists_psi_C3_F4_frame hp hp2 hK h2
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
