module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511A
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526F1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526F2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526F3
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526G
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526H
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526I1b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526I2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526J1
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526J2
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0b
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1528Outer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.S15
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.S15.KFactsPair
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gamma_le_of_O812sixAt {M : Subgroup G} (hO : O812sixAt G M) (h7 : 7 ∈ sigmaM G M)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQ3 : IsPGroup 3 Q) (hQ2 : CFSG.Open.pRank 3 Q ≤ 2)
    (hr : 2 ≤ CFSG.Open.pRank 7 (M ⊓ Subgroup.centralizer (Q : Set G)))
    (hns : ¬ CFSG.HallHigman.IsPSolvable 7 ↥(M ⊓ Subgroup.centralizer (Q : Set G))) :
    rankThreeGamma 1 3 Q ≤ M := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  unfold rankThreeGamma GLBCore
  refine sSup_le ?_
  rintro N ⟨B, hBQ, hB1, rfl⟩
  have hB3 : IsPGroup 3 B := hQ3.to_le hBQ
  have hBne : B ≠ ⊥ := by
    intro hB
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨E, hEB, -, hEc⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 3)
      (H := B) (k := 1) hB1
    have hE : E = ⊥ := le_bot_iff.mp (hB ▸ hEB)
    rw [hE, Subgroup.card_bot] at hEc
    norm_num at hEc
  obtain ⟨F, hFB, hF0, hFea, hNB⟩ := exists_isElemAbelian_normalizer_le hB3 hBne
  have hFQ : F ≤ Q := hFB.trans hBQ
  have hrk : CFSG.Open.pRank 3 F ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hFQ).trans hQ2
  have hcent : M ⊓ Subgroup.centralizer (Q : Set G) ≤ M ⊓ Subgroup.centralizer (F : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hFQ))
  have hF := hO 7 h7 (by norm_num) F (hFQ.trans hQM) (hB3.to_le hFB) hF0
    (isSolvable_mulAut_of_isElemAbelian hFea hrk)
    (hr.trans (CFSG.SectionRank.pRank_mono (by norm_num) hcent))
    (fun hsolv =>
      hns (CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure.isPSolvable_of_le
        (p := 7) hsolv hcent))
  exact hNB.trans hF

theorem row1528_one_two_of_pRank_le_six (hKSML3 : KSML3) {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hO : O812sixAt G M) (ctx : S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    (hM7 : CFSG.Open.pRank 7 (⊤ : Subgroup ↥M) ≤ 6)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {I : Subgroup ↥M} (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1) {Q : Subgroup ↥M} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) :
    CFSG.Open.rankThreeGamma 1 3 (Q.map M.subtype) ≤ M ∧ CFSG.Open.pRank 3 Q ≤ 2 := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have h3σ : 3 ∉ sigmaM G M := by rw [h25.1]; simp
  have h3 : IsLThreeOfExp 1 ↥Ls := h25.2 Ls L hLs hL
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3 :=
    ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h3σ
  have hI2 := pRank_three_le_two_of_le_cMHat hL.1 hbar hZ hX3 hI
  have hQ2 : CFSG.Open.pRank 3 Q ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hQ.le).trans hI2
  refine ⟨?_, hQ2⟩
  have h2 : 1 < CFSG.Open.pRank 7 (cMBar L) := (h20 7 h7 Ls L hLs hL).2.1
  have hrank := two_le_pRank_centralizer_of_pComponent_le_six hKSML3 ctx.gn hLs.1 hL h3
    hM7 h2 hI hIc hI1 hQ hQ2
  have hQc : Q ≤ cMHat L := hQ.le.trans hI
  have hcomm : ⁅barO2 Q, barO2 L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨q, hq, rfl⟩
    exact hQc hq
  have hns := not_isPSolvable_centralizer_of_commute hQ.isPGroup hcomm
    (not_isPSolvable_barO2_of_isLThree hbar)
  obtain ⟨hr, hns'⟩ := transfer_centralizer Q hrank hns
  exact gamma_le_of_O812sixAt hO h7 (Subgroup.map_subtype_le Q)
    (hQ.isPGroup.map M.subtype) (by rw [pRank_map_subtype]; exact hQ2) hr hns'

theorem row1528_one_two_gen (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO : O812sixAt G M) (ctx : S15CtxGen G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {I : Subgroup ↥M} (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1) {Q : Subgroup ↥M} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) :
    CFSG.Open.rankThreeGamma 1 3 (Q.map M.subtype) ≤ M ∧ CFSG.Open.pRank 3 Q ≤ 2 := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  exact row1528_one_two_of_pRank_le_six hKSML3 hO ctx h20 h25
    ((pRank_seven_le_four_of_row1527 ctx h7 h27).trans (by norm_num)) hLs hL hI hIc hI1 hQ

theorem normalizer_le_of_sylow_L_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO : O812sixAt G M) (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {I : Subgroup ↥M} (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1) {A : Subgroup ↥M} (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L)
    (hA3 : Nat.card A = 3) :
    Subgroup.normalizer ((A.map M.subtype : Subgroup G) : Set G) ≤ M := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have h2 : 1 < CFSG.Open.pRank 7 (cMBar L) := (h20 7 h7 Ls L hLs hL).2.1
  have hcomm : ⁅barO2 A, barO2 I⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hIc' : I ≤ cMHat L := hI
    rintro _ ⟨a, ha, rfl⟩ _ ⟨i, hi, rfl⟩
    have := hIc' hi
    have h' := (Subgroup.mem_centralizer_iff.1 this) ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)) a)
      ⟨a, hA.le ha, rfl⟩
    exact h'.symm
  have hr := two_le_pRank_centralizer_of_le hA.isPGroup hA.le h2
  have hns := not_isPSolvable_centralizer_of_commute hA.isPGroup hcomm
    (not_isPSolvable_barO2_of_pComponent hI hIc hI1)
  obtain ⟨hr', hns'⟩ := transfer_centralizer A hr hns
  exact hO 7 h7 (by norm_num) (A.map M.subtype) (Subgroup.map_subtype_le A)
    (hA.isPGroup.map M.subtype)
    (by
      intro h
      have : A = ⊥ := (Subgroup.map_eq_bot_iff_of_injective A M.subtype_injective).1 h
      rw [this, Subgroup.card_bot] at hA3
      omega)
    (isSolvable_mulAut_of_card_three
      (by rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hA3))
    hr' hns'

theorem row1528_cyclic_gen (hKSML3 : KSML3) {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO : O812sixAt G M) (hP : P812At G M) (ctx : S15CtxGen G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂)
    (hLN : ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls → L.Normal)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {I : Subgroup ↥M} (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1) (hI3 : 1 ≤ CFSG.Open.pRank 3 I) {Q A : Subgroup ↥M}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L)
    (hA3 : Nat.card A = 3) (hQc : IsCyclic ↥Q) :
    A.map M.subtype ∈ uniqueSet M := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have h3σ : 3 ∉ sigmaM G M := by rw [h25.1]; simp
  have h3 : IsLThreeOfExp 1 ↥Ls := h25.2 Ls L hLs hL
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hLn : L.Normal := hLN Ls L hLs hL
  haveI : (cMHat L).Normal := cMHat_normal hLn
  have hIM : CFSG.IsPComponent 7 I := isPComponent_of_normal hI hIc
  have hLM : CFSG.IsPComponent 7 L := isPComponent_of_isLThree hL.1 hbar (Or.inr rfl)
  obtain ⟨hL3r, hL7r⟩ := pRank_eq_one_of_isLThree hL.1 hbar
  have hI3r : CFSG.Open.pRank 3 I = 1 := pRank_three_eq_one_of_cyclic_sylow hQ hQc hI3
  have hMtop : ∀ p, CFSG.Open.pRank p M = CFSG.Open.pRank p (⊤ : Subgroup ↥M) := fun p =>
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup M
  have hself : ∀ L : Subgroup ↥M, (L.map M.subtype).subgroupOf M = L := fun L =>
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective L
  have hLI := eq_one_of_mem_inf_of_pPow hL.1 hZ hI
  have hne : L.map M.subtype ≠ I.map M.subtype := by
    intro h
    have hLeq : L = I := Subgroup.map_injective M.subtype_injective h
    have hAbot : A ≠ ⊥ := by
      intro hA0
      rw [hA0, Subgroup.card_bot] at hA3
      omega
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hAbot
    obtain ⟨k, hk⟩ := hA.isPGroup a
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hk)
    refine ha1 (Subtype.ext (hLI a ⟨hA.le a.2, hLeq ▸ hA.le a.2⟩ ⟨j, ?_⟩))
    rw [← Subgroup.orderOf_mk (a : ↥M) a.2]
    exact hj
  refine hP 7 (by norm_num) (by norm_num) (ctx.strong 7 h7)
    (by
      rw [hMtop]
      have := ctx.three_le 7 h7
      omega)
    (L.map M.subtype) (I.map M.subtype)
    (Subgroup.map_subtype_le L) (Subgroup.map_subtype_le I) hne
    (by rw [hself]; exact hLM)
    (by rw [hself]; exact hIM)
    (by rw [hself]; exact hLn)
    (by rw [hMtop]; exact ctx.rank_odd_off 3 Nat.prime_three (by norm_num) h3σ)
    (by rw [pRank_map_subtype]; exact hL7r) (by rw [pRank_map_subtype]; exact hL3r)
    (by rw [pRank_map_subtype]; exact hI1) (by rw [pRank_map_subtype]; exact hI3r)
    (fun B hBM hB3 hr hns => normalizer_le_of_card_three_of_seven_gen hO h7 hBM hB3 hr hns)
    (A.map M.subtype) (by rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hA3)
    (Or.inl (Subgroup.map_mono hA.le))

theorem row1528_noncyclic_of_pRank_le_six (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut)
    {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M} (hO : O812sixAt G M) (hO991 : O991At G M)
    (hO1218 : O1218At G M) (hO98 : O98At G M) (ctx : S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂)
    (hM7 : CFSG.Open.pRank 7 (⊤ : Subgroup ↥M) ≤ 6)
    (hLN : ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls → L.Normal)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {I : Subgroup ↥M} (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1)
    (hIn : ∀ x : ↥M, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ Subgroup.normalizer (I : Set ↥M))
    {Q A : Subgroup ↥M} (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I)
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L) (hA3 : Nat.card A = 3) (hQnc : ¬ IsCyclic ↥Q) :
    A.map M.subtype ∈ uniqueSet M := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  have h3σ : 3 ∉ sigmaM G M := by rw [h25.1]; simp
  have h3 : IsLThreeOfExp 1 ↥Ls := h25.2 Ls L hLs hL
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hLn : L.Normal := hLN Ls L hLs hL
  have hrank : 1 < CFSG.Open.pRank 7 (cMBar L) := (h20 7 h7 Ls L hLs hL).2.1
  have hLI := eq_one_of_mem_inf_of_pPow hL.1 hZ hI
  obtain ⟨P, Q₁, B, hP, hAP, hQ₁, ⟨i, hi, hQ₁Q⟩, hBQ₁, hB3, hQ₁P, hPQ₁, hDZ, hDea, hD9⟩ :=
    exists_sylow_central_pair_of_pElem hLn hIn hQ hQnc hA hA3 hLI
  obtain ⟨hΓ, hQ₁2⟩ := row1528_one_two_of_pRank_le_six hKSML3 hO ctx h20 h25 hM7 hLs hL hI hIc
    hI1 hQ₁
  have hQ₁nc : ¬ IsCyclic ↥Q₁ := by rw [hQ₁Q, isCyclic_conjSub_iff]; exact hQnc
  obtain ⟨x, hx7, hxQ, hxA⟩ :=
    exists_sevenElement_centralizing_D_le_six hKSML3 hKOut ctx.gn hLs.1 hL h3 hM7
      hLn hrank hI hIc hI1 hQ₁ hQ₁2 hA (hAP.trans hPQ₁)
  have hN := isNatSum_of_K55 hK55 ctx.gn hLs.1 (ctx.shape Ls hLs).1 h3 hL
  have hNA := normalizer_le_of_sylow_L_gen hO h20 h25 hLs hL hI hIc hI1 hA hA3
  have hBne : 1 ≤ CFSG.Open.pRank 3 (B.map M.subtype) := by
    rw [pRank_map_subtype]
    exact one_le_pRank_of_dvd B Nat.prime_three (by rw [hB3])
  have hNB : Subgroup.normalizer ((B.map M.subtype : Subgroup G) : Set G) ≤ M :=
    (normalizer_le_gamma (Subgroup.map_mono hBQ₁) hBne).trans hΓ
  have hAB1 : ∀ y ∈ A ⊓ B, y = 1 := by
    intro y hy
    obtain ⟨k, hk⟩ := hA.isPGroup ⟨y, hy.1⟩
    have hdvd : orderOf (⟨y, hy.1⟩ : ↥A) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    exact hLI y ⟨hA.le hy.1, hQ₁.le (hBQ₁ hy.2)⟩
      ⟨j, by rw [← Subgroup.orderOf_mk y hy.1]; exact hj⟩
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    hDZ a (Subgroup.mem_sup_left ha) b (hQ₁P (hBQ₁ hb))
  have hC : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ B, b ≠ 1 →
      Subgroup.centralizer ({((a * b : ↥M) : G)} : Set G) ≤ M := by
    intro a ha ha1 b hb hb1
    have hab : a * b = b * a := hAB a ha b hb
    obtain ⟨ha3, hb3, hd3⟩ := orderOf_eq_three_of_card_three hA3 hB3 hAB1 ha ha1 hb hb1 hab
    have hdD : a * b ∈ A ⊔ B :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
    have hdQ : ∀ y ∈ Q₁, (a * b) * y = y * (a * b) := fun y hy => hDZ _ hdD y (hQ₁P hy)
    have hxd : x * (a * b) = (a * b) * x := by
      rw [← mul_assoc, hxA a ha, mul_assoc, hxQ b (hBQ₁ hb), ← mul_assoc]
    have hd7 := dvd_card_inf_centralizer hx7 hxd
    have hbI : b ∈ cMHat L := hI (hQ₁.le (hBQ₁ hb))
    obtain ⟨u, hu, hu1, hdu⟩ := exists_fixed_point_mul ctx.gn hLs.1 hL hN (hA.le ha) ha3 hbI hb3 hab
    have huV : u ∈ gnV (T.subgroupOf M) := by
      have hU : (⁅L, gnV (T.subgroupOf M)⁆ : Subgroup ↥M) ≤ gnV (T.subgroupOf M) := by
        rw [Subgroup.commutator_comm]; exact commutator_gnV_le _ L
      exact hU hu
    have hdO2 := pCoreOf_centralizer_ne_bot (M := M) (d := a * b) (u := u)
      (gnV_le_pCore ctx.gn huV) hu1 hdu
    exact centralizer_le_of_O98_gen hO1218 hO98 (ctx.strong 7 h7) h3σ h7 hQ₁.isPGroup hQ₁nc
      hΓ hd3 hdQ hd7 hdO2
  have hΓD := gamma_D_le_M_gen (ctx.strong 7 h7) hA3 hB3 hAB hAB1 hNA hNB hC
    ⟨x, hx7, fun a ha => hxA a ha, fun b hb => hxQ b (hBQ₁ hb)⟩
  have hDU := hO991 h3σ ((A ⊔ B).map M.subtype) (Subgroup.map_subtype_le _)
    (isElemAbelian_map_subtype hDea)
    (by rw [Subgroup.card_map_of_injective M.subtype_injective]; exact hD9) hΓD
  have hDle : (A ⊔ B).map M.subtype ≤ P.map M.subtype :=
    Subgroup.map_mono (sup_le hAP (hBQ₁.trans hQ₁P))
  exact mem_uniqueSet_of_D ctx.maxLocal (isSylowOf_map_subtype_top hP) hDle
    (by
      rintro _ ⟨d, hd, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hDZ d hd y hy))
    (Subgroup.map_mono le_sup_left) hNA hDU

theorem row1528_noncyclic_gen (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut) {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hO : O812sixAt G M) (hO991 : O991At G M) (hO1218 : O1218At G M)
    (hO98 : O98At G M) (ctx : S15CtxGen G M T T₁ T₂) (h20 : Row1520 G M T T₁ T₂)
    (h25 : Row1525 G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂)
    (hLN : ∀ (Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))) (L : Subgroup ↥M),
      GNYComponent (T.subgroupOf M) T₁ T₂ Ls → LiftOf (T.subgroupOf M) L Ls → L.Normal)
    {Ls : Subgroup (↥M ⧸ gnC (T.subgroupOf M))} {L : Subgroup ↥M}
    (hLs : GNYComponent (T.subgroupOf M) T₁ T₂ Ls) (hL : LiftOf (T.subgroupOf M) L Ls)
    {I : Subgroup ↥M} (hI : I ≤ cMHat L) (hIc : CFSG.IsPComponent 7 (I.subgroupOf (cMHat L)))
    (hI1 : CFSG.Open.pRank 7 I = 1) {Q A : Subgroup ↥M}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q I) (hA : CFSG.ABGLocalTools.IsSylowOf 3 A L)
    (hA3 : Nat.card A = 3) (hQnc : ¬ IsCyclic ↥Q) : A.map M.subtype ∈ uniqueSet M := by
  have h7 : 7 ∈ sigmaM G M := by rw [h25.1]; exact rfl
  exact row1528_noncyclic_of_pRank_le_six hK55 hKSML3 hKOut hO hO991 hO1218 hO98 ctx h20 h25
    ((pRank_seven_le_four_of_row1527 ctx h7 h27).trans (by norm_num)) hLN hLs hL hI hIc hI1
    (mem_normalizer_I_of_three_pow_of_row1527 hKSML3 ctx h7 h27 hLs hL (hLN Ls L hLs hL) hI
      hIc hI1) hQ hA hA3 hQnc

theorem row1528_gen (hK55 : K55) (hKSML3 : KSML3) (hKOut : KOut) {M T : Subgroup G}
    {T₁ T₂ : Subgroup ↥M} (hO : O812sixAt G M) (hP : P812At G M) (hO991 : O991At G M)
    (hO1218 : O1218At G M) (hO98 : O98At G M) (ctx : S15CtxGen G M T T₁ T₂)
    (h20 : Row1520 G M T T₁ T₂) (h25 : Row1525 G M T T₁ T₂) (h27 : Row1527 G M T T₁ T₂) :
    Row1528 G M T T₁ T₂ := by
  have hLN := hLN_of_rows_gen ctx.gn ctx.pair ctx.rank_N₁ ctx.rank_N₂ h25 h27
  intro p hp Ls L hLs hL I hI hIc hI1 hI3 Q A hQ hA
  have hp7 : p = 7 := by
    have := hp
    rw [h25.1] at this
    exact this
  subst hp7
  have hS : IsSimpleGroup ↥(Ystar (T.subgroupOf M) T₁ T₂) := isSimpleGroup_of_isLThreeOfExp_one h27
  have hY : yLifts (T.subgroupOf M) T₁ T₂ = L := yLifts_eq_of_simple ctx.gn hS hLs hL
  rw [hY] at hA
  have h3 : IsLThreeOfExp 1 ↥Ls := h25.2 Ls L hLs hL
  obtain ⟨hbar, hZ⟩ := barO2_isLThree_of_lift hKSML3 ctx.gn hLs.1 hL h3
  have hA3 : Nat.card A = 3 := card_sylow_three_of_isLThree hL.1 hbar hA
  obtain ⟨hΓ, hQ2⟩ := row1528_one_two_gen hKSML3 hO ctx h20 h25 h27 hLs hL hI hIc hI1 hQ
  refine ⟨hΓ, hQ2, ?_⟩
  by_cases hQc : IsCyclic ↥Q
  · exact row1528_cyclic_gen hKSML3 hO hP ctx h25 hLN hLs hL hI hIc hI1 hI3 hQ hA hA3 hQc
  · exact row1528_noncyclic_gen hK55 hKSML3 hKOut hO hO991 hO1218 hO98 ctx h20 h25 h27 hLN hLs hL
      hI hIc hI1 hQ hA hA3 hQc

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
