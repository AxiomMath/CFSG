module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesGen
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K1528
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row28NonG

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_O98_aux1 {M : Subgroup G} {Q : Subgroup ↥M} (hQ3 : IsPGroup 3 Q)
    (hQnc : ¬ IsCyclic ↥Q) :
    ∃ E : Subgroup G, E ≤ Q.map M.subtype ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have hQ3' : IsPGroup 3 ↥(Q.map M.subtype) := hQ3.map M.subtype
  have hnc : ¬ IsCyclic ↥(Q.map M.subtype) := by
    intro hc
    have e : ↥Q ≃* ↥(Q.map M.subtype) := Q.equivMapOfInjective M.subtype M.subtype_injective
    exact hQnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have h2 : 2 ≤ CFSG.Open.pRank 3 (Q.map M.subtype) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic Nat.prime_three
      (by norm_num) hQ3' hnc
  obtain ⟨E, hE, hEel, hEcard⟩ :=
    CFSG.AGLEmbedding.exists_isElemAbelian_card_sq_of_two_le_pRank Nat.prime_three h2
  exact ⟨E, hE, hEel, by rw [hEcard]; norm_num⟩

theorem centralizer_le_of_O98_aux2 {E Q M : Subgroup G} (hEQ : E ≤ Q)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 Q ≤ M) : CFSG.Open.rankThreeGamma 1 3 E ≤ M := by
  refine le_trans ?_ hΓ
  unfold CFSG.Open.rankThreeGamma CFSG.Open.GLBCore
  refine sSup_le_sSup ?_
  rintro N ⟨B, hBE, hk, rfl⟩
  exact ⟨B, hBE.trans hEQ, hk, rfl⟩

theorem centralizer_le_of_O98_aux3 {K M Y : Subgroup G} (hKY : K ≤ Y) :
    (((Y ⊓ M).subgroupOf Y).subgroupOf (K.subgroupOf Y)).map
        ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp
          (Subgroup.subgroupOfEquivOfLe hKY).toMonoidHom) =
      barMeet K M := by
  unfold barMeet
  rw [← Subgroup.map_map]
  congr 1
  ext k
  constructor
  · rintro ⟨k', hk', rfl⟩
    have h1 : ((k' : ↥Y) : G) ∈ Y ⊓ M := hk'
    exact Subgroup.mem_subgroupOf.2
      (Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 k'.2, (Subgroup.mem_inf.1 h1).2⟩)
  · intro hk
    have h1 : (k : G) ∈ K ⊓ M := hk
    refine ⟨(Subgroup.subgroupOfEquivOfLe hKY).symm k, ?_, ?_⟩
    · exact Subgroup.mem_inf.2 ⟨hKY (Subgroup.mem_inf.1 h1).1, (Subgroup.mem_inf.1 h1).2⟩
    · exact (Subgroup.subgroupOfEquivOfLe hKY).apply_symm_apply k

theorem centralizer_le_of_O98_aux4 {M K : Subgroup G}
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M) (hKM : ¬ K ≤ M)
    (hK : ThreeFourShape K M) {x : G} (hxM : x ∈ M)
    (hxN : x ∈ Subgroup.normalizer (K : Set G)) (hx7 : orderOf x = 7) : False := by
  set Y : Subgroup G := Subgroup.normalizer (K : Set G)
  have hKY : K ≤ Y := Subgroup.le_normalizer
  have hYM : ¬ Y ≤ M := fun h => hKM (hKY.trans h)
  have h7 : 7 ∣ Nat.card ↥(Y ⊓ M) := by
    have hle : Subgroup.zpowers x ≤ Y ⊓ M := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.2 ⟨hxN, hxM⟩
    have hc : Nat.card (Subgroup.zpowers x) = 7 := by rw [Nat.card_zpowers, hx7]
    rw [← hc]
    exact Subgroup.card_dvd_of_le hle
  have hD := isStronglyPEmbedded_subgroupOf_inf hM hYM h7
  have hKn : (K.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKY).2 le_rfl
  have hπ : Function.Surjective ((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥K)).comp
      (Subgroup.subgroupOfEquivOfLe hKY).toMonoidHom) :=
    (QuotientGroup.mk'_surjective _).comp (Subgroup.subgroupOfEquivOfLe hKY).surjective
  refine K1528_holds ↥Y (K.subgroupOf Y) ((Y ⊓ M).subgroupOf Y) hKn _ _ hπ hD ?_
  rw [centralizer_le_of_O98_aux3 hKY]
  rcases hK with ⟨⟨d, ⟨Q, hQ4, hdQ⟩, hiso⟩, hprime⟩ | ⟨hA11, hS9⟩
  · exact Or.inl ⟨⟨d, Q, hQ4, hdQ, hiso⟩, hprime⟩
  · exact Or.inr ⟨hA11, hS9⟩

theorem centralizer_le_of_O98_gen {M : Subgroup G}
    (hO1218 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1218At G M)
    (hO98 : CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O98At G M)
    (hs7 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 M)
    (h3 : 3 ∉ sigmaM G M) (h7 : 7 ∈ sigmaM G M) {Q : Subgroup ↥M}
    (hQ3 : IsPGroup 3 Q) (hQnc : ¬ IsCyclic ↥Q)
    (hΓ : CFSG.Open.rankThreeGamma 1 3 (Q.map M.subtype) ≤ M) {d : ↥M} (hd3 : orderOf d = 3)
    (hdQ : ∀ y ∈ Q, d * y = y * d)
    (hd7 : 7 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer ({(d : G)} : Set G)))
    (hdO2 : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({(d : G)} : Set G) ⊓ M) ≠ ⊥) :
    Subgroup.centralizer ({(d : G)} : Set G) ≤ M := by
  by_contra hCM
  set C : Subgroup G := Subgroup.centralizer ({(d : G)} : Set G) with hC
  obtain ⟨E, hEQ, hEel, hEcard⟩ := centralizer_le_of_O98_aux1 hQ3 hQnc
  have hEM : E ≤ M := hEQ.trans (Subgroup.map_subtype_le Q)
  have hEC : E ≤ C := by
    intro e he
    obtain ⟨y, hy, rfl⟩ := hEQ he
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hdQ y hy)).symm
  have hΓE : CFSG.Open.rankThreeGamma 1 3 E ≤ M := centralizer_le_of_O98_aux2 hEQ hΓ
  have hd7' : 7 ∣ Nat.card ↥(C ⊓ M) := by rwa [inf_comm]
  have hO2 : CFSG.Open.pCoreOf 2 C = ⊥ := by
    by_contra hne
    exact hCM (hO1218 7 3 h7 Nat.prime_three (by norm_num) E hEM hEel hEcard hΓE C hEC hd7' hne)
  have hQM : Q.map M.subtype ≤ M := Subgroup.map_subtype_le Q
  have hQ3' : IsPGroup 3 ↥(Q.map M.subtype) := hQ3.map M.subtype
  have hnc : ¬ IsCyclic ↥(Q.map M.subtype) := by
    intro hc
    have e : ↥Q ≃* ↥(Q.map M.subtype) := Q.equivMapOfInjective M.subtype M.subtype_injective
    exact hQnc (isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective)
  have hd3' : orderOf (d : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd3
  have hdQ' : ∀ y ∈ Q.map M.subtype, (d : G) * y = y * (d : G) := by
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hdQ y hy)
  obtain ⟨K, -, -, hKM, hKshape, hKnorm⟩ := hO98 h3 (Q.map M.subtype) hQM hQ3' hnc hΓ
    (d : G) d.2 hd3' hdQ' hCM hO2 hdO2
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(C ⊓ M)) 7 hd7'
  have hx7 : orderOf (x : G) = 7 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxN : (x : G) ∈ Subgroup.normalizer (K : Set G) :=
    hKnorm (x : G) x.2 hx7
  exact centralizer_le_of_O98_aux4 hs7 hKM hKshape (Subgroup.mem_inf.1 x.2).2 hxN hx7

end Row28NonG

end CFSG.LocalAnalysis.RankThreeUC.S15
