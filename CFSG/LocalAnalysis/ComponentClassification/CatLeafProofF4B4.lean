module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4B4Roots
public import CFSG.ClassicalInvolution.WeakCT.SpinOddWeak

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  SymplecticBlockPair linearBlockStandardPair_subgroupOf linearBlockStandardPair_le_sup
  symplecticBlockPair_subgroupOf symplecticBlockPair_le_sup iSup_subgroupOf_eq_top)
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] noncomputable def b4Chain
    (K : Type) [Field K] : Fin 4 → Subgroup (adjointGroup .F4 K) :=
  ![(f4Datum K).rootGroup b4Root ⊔ (f4Datum K).rootGroup (-b4Root),
    rankOne (f4Datum K).rootGroup (f4Node 0), rankOne (f4Datum K).rootGroup (f4Node 1),
    rankOne (f4Datum K).rootGroup (f4Node 2)]

theorem fin4_lt_cases : ∀ i j : Fin 4, i.val + 1 < j.val →
    (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by decide

theorem fin4_adj_cases : ∀ i j : Fin 4, i.val + 1 = j.val → j.val + 1 < 4 →
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by decide

theorem fin4_end_cases : ∀ i j : Fin 4, i.val + 2 = 4 → j.val + 1 = 4 → i = 2 ∧ j = 3 := by
  decide

theorem f4Node_zero_ne_one : f4Node 0 ≠ f4Node 1 := by decide

theorem f4_cartan_01 : Tag.cartan .F4 (f4Node 0) (f4Node 1) = -1 := by decide

theorem f4_cartan_10 : Tag.cartan .F4 (f4Node 1) (f4Node 0) = -1 := by decide

theorem f4_sl3_witness_01 :
    ¬ (3 : ℤ) ∣ Tag.cartan .F4 (f4Node 0) (f4Node 2) +
      2 * Tag.cartan .F4 (f4Node 1) (f4Node 2) := by
  decide

theorem conj_mul_toMonoidHom {G : Type*} [Group G] (a b : G) :
    (MulAut.conj (a * b)).toMonoidHom =
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
  ext x
  simp [mul_assoc]

theorem exists_psi_B4_F4
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hq : 4 ≤ Nat.card K) (h2 : (2 : K) ≠ 0) :
    ∃ Ψ : spinGroup (Spin.quadOdd 4 K) →* adjointGroup .F4 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadOdd 4 K)) ∧
      Ψ.range = ⨆ k, b4Chain K k ∧ IsQuasisimple ↥(⨆ k, b4Chain K k) ∧
      Blueprint.LieModel (↥(⨆ k, b4Chain K k) ⧸ Subgroup.center ↥(⨆ k, b4Chain K k))
        .POmegaOdd 4 p f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
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
  obtain ⟨Wsp, hsp⟩ := ClassicalInvolution.RouteD.exists_symplecticBlockStandardPair_rankOne hq
    h2 hE rfl (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12
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
  obtain ⟨Ψ', hsurj, hker, hqs, -, hlie, -⟩ := ClassicalInvolution.WeakCT.weakCT_spinOdd_of_pair
    hadm hK hq (X := ↥Gs) (fun k => (b4Chain K k).subgroupOf Gs)
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
      obtain ⟨rfl, rfl⟩ := fin4_end_cases i j hi hj
      exact ⟨Wsp.subgroupOf Gs, symplecticBlockPair_subgroupOf
        ((symplecticBlockPair_le_sup hsp.pair).trans
          (sup_le (hUle 2) (hUle 3))) hsp.pair⟩)
  refine ⟨Gs.subtype.comp Ψ', ?_, ?_, hqs, hlie⟩
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top,
      Subgroup.range_subtype]

end CFSG.ComponentClassification.CatLeafProof
