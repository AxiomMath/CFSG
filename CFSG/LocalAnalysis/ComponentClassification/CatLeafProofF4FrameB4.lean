module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4FrameC3
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4B4

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Timmesfeld.LevisExtras
open CFSG.ClassicalInvolution.WeakCT (exists_sl3Levi exists_b2Hom hom_block_eq edgeUp)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem f4_cartan_03 : Tag.cartan .F4 (f4Node 0) (f4Node 3) = 0 := by decide

theorem f4_sl3_witness_10 :
    ¬ (3 : ℤ) ∣ Tag.cartan .F4 (f4Node 1) (f4Node 2) +
      2 * Tag.cartan .F4 (f4Node 0) (f4Node 2) := by
  decide

theorem commute_weylElement_three_two
    {K : Type} [Field K] {y : adjointGroup .F4 K}
    (hy : y ∈ rankOne (f4Datum K).rootGroup (f4Node 0)) :
    Commute (Chevalley.weylElement .F4 K (f4Node 3) * Chevalley.weylElement .F4 K (f4Node 2))
      y := by
  have hn : ∀ i : Fin (Tag.rank .F4),
      Chevalley.weylElement .F4 K i ∈ rankOne (f4Datum K).rootGroup i := fun i =>
    Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .F4) i
  have h02 : Commutes (rankOne (f4Datum K).rootGroup (f4Node 0))
      (rankOne (f4Datum K).rootGroup (f4Node 2)) :=
    commutes_rootPair_F4 (isRoot_single _ _) (isRoot_single _ _) b4_root_ne.2.2.2.2.1
      b4_root_ne.2.2.2.2.2 iform_zero_two not_isRoot_b4_sums.2.2.2.2.1
      not_isRoot_b4_sums.2.2.2.2.2
  have h03 : Commutes (rankOne (f4Datum K).rootGroup (f4Node 0))
      (rankOne (f4Datum K).rootGroup (f4Node 3)) :=
    ClassicalInvolution.RouteD.commutes_rankOne_of_cartan_eq_zero_of_longest (f4Datum K)
      (f4_steinbergExtras K) (fun ε hε => (ClassicalInvolution.RouteD.isLongestRoot_single_F4
        (k := f4Node 0) (by decide)).2 ε hε) f4_cartan_03
  exact Commute.mul_left (h03 y hy _ (hn _)).symm (h02 y hy _ (hn _)).symm

theorem fin4_up_nadj : ∀ i j : Fin 4, i ≠ j → ¬ edgeUp 4 i j → ¬ edgeUp 4 j i →
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 0) ∨
      (i = 3 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by
  decide

theorem fin4_up_single : ∀ i j : Fin 4, edgeUp 4 i j → ¬ (i = 2 ∧ j = 3) →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by
  decide

theorem exists_psi_B4_F4_frame
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (h2 : (2 : K) ≠ 0) :
    ∃ Ψ : spinGroup (Spin.quadOdd 4 K) →* adjointGroup .F4 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadOdd 4 K)) ∧
      Ψ.range = ⨆ k, b4Chain K k ∧ IsQuasisimple ↥(⨆ k, b4Chain K k) ∧
      Blueprint.LieModel (↥(⨆ k, b4Chain K k) ⧸ Subgroup.center ↥(⨆ k, b4Chain K k))
        .POmegaOdd 4 p f := by
  obtain ⟨hf, hq3⟩ := one_le_and_three_le_of_card hp hp2 hK
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  choose ρF hρFi hρFr hρFv using exists_rankOne_param hE
  set n : adjointGroup .F4 K :=
    Chevalley.weylElement .F4 K (f4Node 3) * Chevalley.weylElement .F4 K (f4Node 2) with hn
  set ρ : Fin 4 → SL(2, K) →* adjointGroup .F4 K :=
    ![(MulAut.conj n).toMonoidHom.comp (ρF (f4Node 1)), ρF (f4Node 0), ρF (f4Node 1),
      ρF (f4Node 2)] with hρ
  have hρ0 : ((MulAut.conj n).toMonoidHom.comp (ρF (f4Node 1))).range = b4Chain K 0 := by
    rw [MonoidHom.range_comp, hρFr, hn, conj_mul_toMonoidHom, ← Subgroup.map_map]
    change (((f4Datum K).rootGroup (Pi.single (f4Node 1) 1) ⊔
      (f4Datum K).rootGroup (-Pi.single (f4Node 1) 1)).map _).map _ = _
    rw [map_conj_weylElement_rootPair_F4 _ (isRoot_single _ _),
      map_conj_weylElement_rootPair_F4 _ (IsRoot.reflect _ (isRoot_single _ _)),
      reflect_three_two_single_one]
    rfl
  have hρr : ∀ k, (ρ k).range = b4Chain K k := by
    intro k
    fin_cases k
    · exact hρ0
    · exact hρFr _
    · exact hρFr _
    · exact hρFr _
  have hc02 : Commutes (b4Chain K 0) (b4Chain K 2) :=
    commutes_rootPair_F4 isRoot_b4Root (isRoot_single _ _) b4_root_ne.1 b4_root_ne.2.1
      iform_b4Root_one not_isRoot_b4_sums.1 not_isRoot_b4_sums.2.1
  have hc03 : Commutes (b4Chain K 0) (b4Chain K 3) :=
    commutes_rootPair_F4 isRoot_b4Root (isRoot_single _ _) b4_root_ne.2.2.1 b4_root_ne.2.2.2.1
      iform_b4Root_two not_isRoot_b4_sums.2.2.1 not_isRoot_b4_sums.2.2.2.1
  have hc13 : Commutes (b4Chain K 1) (b4Chain K 3) :=
    commutes_rootPair_F4 (isRoot_single _ _) (isRoot_single _ _) b4_root_ne.2.2.2.2.1
      b4_root_ne.2.2.2.2.2 iform_zero_two not_isRoot_b4_sums.2.2.2.2.1
      not_isRoot_b4_sums.2.2.2.2.2
  obtain ⟨O'⟩ := Steinberg.nonempty_commOrder_ofCartan (Spin.oddDatum 4 K).isFiniteType
    (Dv := (Spin.oddDatum 4 K).divisible) rfl
  have hE' := Steinberg.SpinOdd.chevalleyExtras (by omega : 2 ≤ 4) O' Steinberg.SpinOdd.commC
    (Steinberg.SpinOdd.commutatorFormula O')
  have hsq : ∀ k : Fin 4,
      Steinberg.weylElement (Steinberg.SpinOdd.x 4 K) k 1 ^ 2 ∈ (Spin.torusB K k).range := by
    intro k
    have h := (Spin.oddDatum_isCTGroupDatum 4 K
      (Spin.oddDatum_iSup_eq_top 4 K h2 (by norm_num))).sq_mem k
    have e := Steinberg.SpinOdd.weylElement_eq (n := 4) (K := K) k 1
    rw [map_one, one_mul] at e
    rw [e]
    exact h
  obtain ⟨Ψ, hker, hrange, hqs, hlie, -⟩ := weakCT_of_frame_dl_subgroup
    (CurtisTits.curtisTitsConclusion_spinOdd hadm hK) (leviConePresented_spinOdd h2 (by norm_num))
    hE' rfl (isQuasisimple_statedSp_two hq3) h2
    (ClassicalInvolution.WeakCT.doubleBondDiagram_cartanB (n := 4) (a := 2) (b := 3) rfl rfl)
    (Spin.oddDatum_steinbergExtras h2).torus_iSupIndep hsq (U := b4Chain K)
    (fun i j hne hij hji u hu v hv => by
      rcases fin4_up_nadj i j hne hij hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc02 u hu v hv
      · exact hc03 u hu v hv
      · exact hc13 u hu v hv
      · exact (hc02 v hv u hu).symm
      · exact (hc03 v hv u hu).symm
      · exact (hc13 v hv u hu).symm)
    (ρ := ρ) hρr (hρFi (f4Node 1))
    (fun i j hij hne => by
      rcases fin4_up_single i j hij hne with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      ·
        obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 1) (j := f4Node 0)
          (k := f4Node 2) f4Node_zero_ne_one.symm f4_cartan_10 f4_cartan_01 f4_sl3_witness_10
        obtain ⟨h0, h1⟩ := sl3_comp_blk hv (hρFv (f4Node 1)) (hρFv (f4Node 0))
        refine ⟨(MulAut.conj n).toMonoidHom.comp emb, ?_, ?_⟩
        · rw [MonoidHom.comp_assoc, h0]
          rfl
        · rw [MonoidHom.comp_assoc, h1]
          refine MonoidHom.ext fun A => ?_
          have hA : ρF (f4Node 0) A ∈ rankOne (f4Datum K).rootGroup (f4Node 0) := by
            rw [← hρFr]
            exact ⟨A, rfl⟩
          rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            (commute_weylElement_three_two hA).eq, mul_inv_cancel_right]
          rfl
      ·
        obtain ⟨emb, -, -, hv⟩ := exists_sl3Levi hE rfl (i := f4Node 0) (j := f4Node 1)
          (k := f4Node 2) f4Node_zero_ne_one f4_cartan_01 f4_cartan_10 f4_sl3_witness_01
        exact ⟨emb, sl3_comp_blk hv (hρFv (f4Node 0)) (hρFv (f4Node 1))⟩)
    (by
      obtain ⟨φ, e, -, he1, he2, he3, he4, hφ⟩ :=
        exists_b2Hom hE (s := f4Node 2) (l := f4Node 1) rfl f4_cartan_21 f4_cartan_12
      obtain ⟨hb0, hb1⟩ := hom_block_eq he1 he2 he3 he4 hφ (hρFv (f4Node 2)) (hρFv (f4Node 1))
      exact ⟨φ, hb1, hb0⟩)
  exact ⟨Ψ, hker, hrange, hqs, hlie⟩

end CFSG.ComponentClassification.CatLeafProof
