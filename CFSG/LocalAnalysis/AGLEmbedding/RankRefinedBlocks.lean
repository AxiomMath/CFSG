module

import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux2
import CFSG.LocalAnalysis.AGLEmbedding.BlockInnerNormalizer
import CFSG.LocalAnalysis.AGLEmbedding.LemmaPThree
import CFSG.LocalAnalysis.AGLEmbedding.RankRefined
import CFSG.LocalAnalysis.AGLEmbedding.RankRefinedBlocksAux
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.PhaseThreeConfig
import CFSG.LocalAnalysis.AGLEmbedding.A9MSideBlocksAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers

theorem stmtOneLieRRBlocks :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R Z : Subgroup G},
      D1PhaseThree p P M H R → Asc81bEightFour → Asc81bEightSix → D1NoXBlock → p = 3 →
      IsCyclic (CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M)) → Z ≤ H ⊓ M → IsElemAbelian 3 Z →
      ∀ (k d : ℕ) (L : Fin k → Subgroup G), Function.Injective L →
        (∀ i, IsWeakSBlock M (pCoreOf 2 H) (L i)) →
        (∀ i, Z ≤ blockClosure M (H ⊓ M) (L i)) →
        (∀ i, 3 ^ d ≤ (Z ⊓ blockCentralizer M (L i)).relIndex Z) → 1 ≤ k * d →
        k * d / 2 + 1 ≤ Open.pRank 3 (H ⊓ M) := by
  intro G _ _ p P M H R Z h h84 h86 hD2 _ hcyc hZK hZ k d L hLinj hL hZE hidx hkd
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  have hKeq := h.inf_eq_inf_normalizer_twoCore
  have hKM : H ⊓ M ≤ M := inf_le_right
  have hZM : Z ≤ M := hZK.trans inf_le_right
  set Zb := barM M Z with hZb
  set Lb : Fin k → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun i => barM M (L i) with hLb
  set C : Fin k → Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := fun i =>
    Subgroup.centralizer (Lb i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) with hC
  have hZbLC : ∀ i, Zb ≤ Lb i ⊔ C i := by
    intro i
    have hbarC : barM M (blockCentralizer M (L i)) ≤ C i := by
      rintro _ ⟨⟨c, hcM⟩, hc, rfl⟩
      exact (mem_blockCentralizer_iff ⟨c, hcM⟩).mp (Subgroup.mem_subgroupOf.mp hc)
    refine (barM_mono ((hZE i).trans
      (blockClosure_le_sup_blockCentralizer hKM (hL i).toIsTwoPrimeComponent))).trans ?_
    change ((L i ⊔ blockCentralizer M (L i)).subgroupOf M).map mk ≤ _
    rw [Subgroup.subgroupOf_sup (hL i).le (blockCentralizer_le M (L i)), Subgroup.map_sup]
    exact sup_le_sup le_rfl hbarC
  have hZb3 : ∀ x ∈ Zb, x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 3 = 1 := Subtype.ext (by simpa using hZ.2 a (Subgroup.mem_subgroupOf.mp ha))
    rw [← map_pow, h1, map_one]
  have hZbab : ∀ x ∈ Zb, ∀ y ∈ Zb, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h0 := (isMulCommutative_iff.mp hZ.1) ⟨a, Subgroup.mem_subgroupOf.mp ha⟩
      ⟨b, Subgroup.mem_subgroupOf.mp hb⟩
    have h1 : a * b = b * a := Subtype.ext (by simpa using congrArg Subtype.val h0)
    rw [← map_mul, ← map_mul, h1]
  have hZbp : IsPGroup 3 Zb := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hZb3 x x.2)⟩
  have hidxb : ∀ i, 3 ^ d ≤ (C i).relIndex Zb := by
    intro i
    have e : (Z ⊓ blockCentralizer M (L i)).relIndex Z = (C i).relIndex Zb := by
      rw [Subgroup.inf_relIndex_left]
      conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hZM]
      rw [show blockCentralizer M (L i) = ((C i).comap mk).map M.subtype from rfl,
        Subgroup.relIndex_map_map_of_injective _ _ M.subtype_injective, Subgroup.relIndex_comap]
      rfl
    exact e ▸ hidx i
  have hBex : ∀ i, ∃ B : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), B ≤ Lb i ⊓ (Zb ⊔ C i) ∧
      IsPGroup 3 B ∧ 3 ^ d ≤ (C i).relIndex B := fun i => by
    obtain ⟨B, hB, hB3, hBi⟩ := exists_isPGroup_le_inf_sup_centralizer (hZbLC i) hZbp
    exact ⟨B, hB, hB3, (hidxb i).trans hBi⟩
  choose B hBle hB3 hBidx using hBex
  have hBK : ∀ i, B i ≤ barM M (H ⊓ M) := by
    intro i b hb
    obtain ⟨hbL, hbW⟩ := hBle i hb
    have hZN : Zb ≤ Subgroup.normalizer (C i : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      (hZbLC i).trans (sup_centralizer_self_le_normalizer_centralizer (Lb i))
    have hb' : b ∈ ((Zb ⊔ C i : Subgroup _) : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := hbW
    rw [Subgroup.coe_mul_of_left_le_normalizer_right Zb (C i) hZN] at hb'
    obtain ⟨_, ⟨x, hx, rfl⟩, c, hc, hxc⟩ := hb'
    obtain ⟨l, hl, rfl⟩ := hbL
    have hxl : mk x * (mk l)⁻¹ ∈ C i := by
      rw [← hxc, mul_inv_rev, ← mul_assoc]
      exact (Subgroup.mem_normalizer_iff.mp (hZN ⟨x, hx, rfl⟩) _).mp ((C i).inv_mem hc)
    have hP := h.mk_mem_barM_of_mul_inv_mem h84 h86 hD2 (hL i)
      (hZK (Subgroup.mem_subgroupOf.mp hx)) (Subgroup.mem_subgroupOf.mp hl) hxl
    refine barM_mono (fun y hy => ?_) hP
    rw [hKeq]
    exact ⟨(hL i).le hy.2, hy.1⟩
  have hBC : ∀ i j, i ≠ j → B i ≤ C j := by
    intro i j hij
    have hne : Lb i ≠ Lb j := fun he => hij (hLinj
      ((hL i).toIsTwoPrimeComponent.eq_of_barM_eq (hL j).toIsTwoPrimeComponent he))
    exact ((hBle i).trans inf_le_left).trans ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp
      (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hL i).component
        (hL j).component hne))
  have hne0 : ∀ X Y : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M), X.relIndex Y ≠ 0 := fun X Y => by
    rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
  have key : ∀ s : Finset (Fin k), IsPGroup 3 ↥(s.sup B) ∧
      3 ^ (d * s.card) ≤ (s.inf C).relIndex (s.sup B) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sup_empty, Finset.inf_empty, Finset.card_empty, mul_zero, pow_zero,
        Subgroup.relIndex_bot_right]
      exact ⟨IsPGroup.of_bot, le_rfl⟩
    | insert j s hj ih =>
      rw [Finset.sup_insert, Finset.inf_insert, Finset.card_insert_of_notMem hj]
      have hsC : s.sup B ≤ C j :=
        Finset.sup_le fun i hi => hBC i j fun e => hj (e ▸ hi)
      have hsN : s.sup B ≤ Subgroup.normalizer (B j : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
        hsC.trans ((Subgroup.centralizer_le ((hBle j).trans inf_le_left)).trans
          (Subgroup.centralizer_le_normalizer _))
      refine ⟨IsPGroup.to_sup_of_normal_left' (hB3 j) ih.1 hsN, ?_⟩
      have h1 := Subgroup.relIndex_inf_mul_relIndex (s.inf C) (C j) (B j ⊔ s.sup B)
      have h2 : (C j).relIndex (B j) ≤ (C j).relIndex (B j ⊔ s.sup B) :=
        Subgroup.relIndex_le_of_le_right le_sup_left (hne0 _ _)
      have h3 : (s.inf C).relIndex (s.sup B) ≤ (s.inf C).relIndex (C j ⊓ (B j ⊔ s.sup B)) :=
        Subgroup.relIndex_le_of_le_right (le_inf hsC le_sup_right) (hne0 _ _)
      rw [inf_comm, ← h1, mul_add, mul_one, pow_add]
      exact Nat.mul_le_mul (ih.2.trans h3) ((hBidx j).trans h2)
  obtain ⟨hBB3, hBBidx⟩ := key Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hBBidx
  set BB := Finset.univ.sup B with hBB
  set D := Finset.univ.inf C with hD
  have hBBK : BB ≤ barM M (H ⊓ M) := Finset.sup_le fun i _ => hBK i
  have hBBW : ∀ j, BB ≤ Zb ⊔ C j := fun j => Finset.sup_le fun i _ => by
    by_cases hij : i = j
    · subst hij
      exact (hBle i).trans inf_le_right
    · exact (hBC i j hij).trans le_sup_right
  have hDC : ∀ j, D ≤ C j := fun j => Finset.inf_le (Finset.mem_univ j)
  have hmemD : ∀ x, (∀ j, x ∈ C j) → x ∈ D := fun x hx =>
    (Finset.le_inf fun j _ => (Subgroup.zpowers_le).mpr (hx j) :
      Subgroup.zpowers x ≤ D) (Subgroup.mem_zpowers x)
  set Z0 := BB ⊓ D with hZ0
  have hZ0c : Z0 ≤ Subgroup.centralizer (BB : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
    rw [Subgroup.le_centralizer_iff]
    refine Finset.sup_le fun i _ => ((hBle i).trans inf_le_left).trans ?_
    exact (Subgroup.le_centralizer_iff.mp le_rfl).trans
      (Subgroup.centralizer_le (inf_le_right.trans (hDC i)))
  have hZ0p : IsPGroup 3 Z0 := hBB3.to_le inf_le_left
  have hZ0O : Z0 ≤ CFSG.pCore 3 (↥M ⧸ CFSG.pCore 2 ↥M) := by
    set E : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M) := GLBLayer ⊤ with hE
    have hBBE : BB ≤ E :=
      Finset.sup_le fun i _ => ((hBle i).trans inf_le_left).trans (le_sSup (hL i).component)
    have hZ0E : Z0 ≤ Subgroup.centralizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M)) := by
      rw [Subgroup.le_centralizer_iff]
      refine sSup_le fun L' hL' => ?_
      rw [← Subgroup.le_centralizer_iff]
      by_cases hex : ∃ i, Lb i = L'
      · obtain ⟨i, rfl⟩ := hex
        exact inf_le_right.trans (hDC i)
      · push Not at hex
        refine inf_le_left.trans (Finset.sup_le fun i _ => ((hBle i).trans inf_le_left).trans ?_)
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer).mp
          (CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ (hL i).component hL'
            (hex i))
    have hEn : E.Normal := glbLayer_top_normal
    have hZn : (E ⊓ Subgroup.centralizer (E : Set (↥M ⧸ CFSG.pCore 2 ↥M))).Normal :=
      inferInstance
    exact le_pCore_of_le_normal_comm hZn (fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb.2 a
      ha.1) (le_inf (inf_le_left.trans hBBE) hZ0E) hZ0p
  have hZ0cyc : IsCyclic Z0 := Subgroup.isCyclic_of_le hZ0O
  have hpow : ∀ b ∈ BB, b ^ 3 ∈ Z0 := fun b hb =>
    ⟨BB.pow_mem hb 3, hmemD _ fun j => pow_mem_centralizer_of_mem_sup (hZbLC j) hZb3 (hBBW j hb)⟩
  have hcomm : ∀ a ∈ BB, ∀ b ∈ BB, a * b * a⁻¹ * b⁻¹ ∈ Z0 := fun a ha b hb =>
    ⟨BB.mul_mem (BB.mul_mem (BB.mul_mem ha hb) (BB.inv_mem ha)) (BB.inv_mem hb),
      hmemD _ fun j => commutator_mem_centralizer_of_mem_sup (hZbLC j) hZbab (hBBW j ha)
        (hBBW j hb)⟩
  have hidxZ0 : 3 ^ (k * d) ≤ Z0.relIndex BB := by
    rw [hZ0, Subgroup.inf_relIndex_left, mul_comm]
    exact hBBidx
  have hRR := div_two_add_one_le_pRank Nat.prime_three (by decide) BB Z0 (k * d) hBB3
    inf_le_left hZ0c hZ0cyc hpow hcomm hkd hidxZ0
  exact hRR.trans ((pRank_mono 3 Nat.prime_three hBBK).trans
    (pRank_barM_le Nat.prime_three (by decide) M (H ⊓ M) hKM))

end CFSG.AGLEmbedding
