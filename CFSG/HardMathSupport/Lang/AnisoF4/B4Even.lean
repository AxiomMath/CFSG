module

public import CFSG.HardMathSupport.Lang.AnisoF4.SpPairEven
public import CFSG.HardMathSupport.Lang.AnisoF4.Sp4Swap
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4B4

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoF4

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
  CFSG.RankThree.PartOne.CTP
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_subgroupOf symplecticBlockStandardPair_le_sup
  linearBlockStandardPair_subgroupOf linearBlockStandardPair_le_sup iSup_subgroupOf_eq_top)
open CFSG.ClassicalInvolution.Generic (Commutes)

set_option linter.unusedSectionVars false


@[expose] def SpPairSwapEven (K : Type) [Field K] : Prop :=
  ∀ {X : Type} [Group X] {W A B : Subgroup X}, SymplecticBlockStandardPair K W A B →
    ∃ W' : Subgroup X, SymplecticBlockStandardPair K W' B A

theorem exists_psi_B4_F4_frame_even {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hK4 : 4 ≤ Nat.card K) :
    ∃ Ψ : StatedSp 4 K →* adjointGroup .F4 K, Ψ.ker ≤ Subgroup.center (StatedSp 4 K) ∧
      Ψ.range = ⨆ k, b4Chain K k ∧ IsQuasisimple ↥(⨆ k, b4Chain K k) ∧
      Blueprint.LieModel (↥(⨆ k, b4Chain K k) ⧸ Subgroup.center ↥(⨆ k, b4Chain K k))
        .PSp 4 2 f := by
  have hswap : SpPairSwapEven K := fun h => ⟨_, symplecticBlockStandardPair_swap h⟩
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hadm : StatedLieAdmissible .PSp 4 2 f := ⟨Nat.prime_two, hf, by norm_num, by simp⟩
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
  have hlin : ∃ W, LinearBlockStandardPair K W (rankOne (f4Datum K).rootGroup (f4Node 0))
      (rankOne (f4Datum K).rootGroup (f4Node 1)) := by
    obtain ⟨emb, hinj, -, hv⟩ := ClassicalInvolution.WeakCT.exists_sl3Levi hE rfl
      (i := f4Node 0) (j := f4Node 1) (k := f4Node 2) f4Node_zero_ne_one f4_cartan_01
      f4_cartan_10 f4_sl3_witness_01
    refine ⟨emb.range, ClassicalInvolution.ModelFacts.linearBlockStandardPair_rankOne
      (f4Datum K).rootGroup (f4Par K) (hset _ (hΦ.single_mem _)) (hset _ (hneg _))
      (hset _ (hΦ.single_mem _)) (hset _ (hneg _)) emb ?_ hv⟩
    rw [(MonoidHom.ker_eq_bot_iff _).2 hinj]
    exact bot_le
  have hlinB : ∃ W, LinearBlockStandardPair K W (b4Chain K 0) (b4Chain K 1) := by
    obtain ⟨W, hW⟩ := hlin
    have h := ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj hW
      (weylElement .F4 K (f4Node 3) * weylElement .F4 K (f4Node 2))
    have e0 : (rankOne (f4Datum K).rootGroup (f4Node 0)).map
        (MulAut.conj (weylElement .F4 K (f4Node 3) * weylElement .F4 K (f4Node 2))).toMonoidHom =
        b4Chain K 1 := by
      rw [conj_mul_toMonoidHom, ← Subgroup.map_map]
      change (((f4Datum K).rootGroup (Pi.single (f4Node 0) 1) ⊔
        (f4Datum K).rootGroup (-Pi.single (f4Node 0) 1)).map _).map _ = _
      rw [map_conj_weylElement_rootPair_F4 _ (isRoot_single _ _), reflect_two_single_zero,
        map_conj_weylElement_rootPair_F4 _ (isRoot_single _ _), reflect_three_single_zero]
      rfl
    have e1 : (rankOne (f4Datum K).rootGroup (f4Node 1)).map
        (MulAut.conj (weylElement .F4 K (f4Node 3) * weylElement .F4 K (f4Node 2))).toMonoidHom =
        b4Chain K 0 := by
      rw [conj_mul_toMonoidHom, ← Subgroup.map_map]
      change (((f4Datum K).rootGroup (Pi.single (f4Node 1) 1) ⊔
        (f4Datum K).rootGroup (-Pi.single (f4Node 1) 1)).map _).map _ = _
      rw [map_conj_weylElement_rootPair_F4 _ (isRoot_single _ _),
        map_conj_weylElement_rootPair_F4 _ (IsRoot.reflect _ (isRoot_single _ _)),
        reflect_three_two_single_one]
      rfl
    rw [e0, e1] at h
    exact ⟨_, h.symm⟩
  obtain ⟨Wsp0, hsp0⟩ := exists_symplecticBlockStandardPair_rankOne_even hK4 hE rfl
    (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12
  obtain ⟨Wsp, hsp⟩ := hswap hsp0
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
  set Gs : Subgroup (adjointGroup .F4 K) := ⨆ k, b4Chain K k with hGs
  have hUle : ∀ k, b4Chain K k ≤ Gs := fun k => le_iSup (b4Chain K) k
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, -⟩ := weakCT_symplectic_even hadm (by norm_num) hK hK4
    (X := ↥Gs) (fun k => (b4Chain K k).subgroupOf Gs)
    (iSup_subgroupOf_eq_top (b4Chain K))
    (fun i j hij x hx y hy => by
      refine Subtype.ext ?_
      rcases fin4_lt_cases i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc02 x.1 hx y.1 hy
      · exact hc03 x.1 hx y.1 hy
      · exact hc13 x.1 hx y.1 hy)
    (fun i j hij hj => by
      rcases fin4_adj_cases i j hij hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨W, hW⟩ := hlinB
        exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
          ((linearBlockStandardPair_le_sup hW).trans
            (sup_le (hUle 0) (hUle 1))) hW⟩
      · obtain ⟨W, hW⟩ := hlin
        exact ⟨W.subgroupOf Gs, linearBlockStandardPair_subgroupOf
          ((linearBlockStandardPair_le_sup hW).trans
            (sup_le (hUle 1) (hUle 2))) hW⟩)
    (fun i j hi hj => by
      obtain ⟨rfl, rfl⟩ := fin4_end_cases j i hj hi
      exact ⟨Wsp.subgroupOf Gs, symplecticBlockStandardPair_subgroupOf
        ((symplecticBlockStandardPair_le_sup hsp).trans
          (sup_le (hUle 3) (hUle 2))) hsp⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

end CFSG.HardMathSupport.Lang.AnisoF4
