module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux10
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux11
import CFSG.LocalAnalysis.GLTheoremB.Lemma99Setup
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux2

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

omit [Finite G] in
private theorem isElemAbelian_subgroupOf' {p : ℕ} {B N : Subgroup G}
    (hB : IsElemAbelian p B) : IsElemAbelian p (B.subgroupOf N) :=
  CFSG.Open.IsElemAbelian.subgroupOf hB N

theorem lemma86 (i11 : Input11_3) (i5 : Input28_5) (i14 : Input28_14)
    (it : InputMcLaughlinTypeFacts)
    (hS : GLStanding G m p) {B M₀ : Subgroup G} (hB : IsBOneMax p B)
    (hM : IsPreUniquenessSubgroup p B M₀)
    {Q : Subgroup G} (hQ0 : Q ≠ ⊥) (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Q : Set G)))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G))
    {P : Sylow 2 G} (hPQ : Q ≤ (P : Subgroup G)) {U : Subgroup G}
    (hU : IsUGroup 2 (P : Subgroup G) U) (hUN : U ≤ Subgroup.normalizer (Q : Set G))
    (h85 : ∀ (P' : Sylow 2 G) (U' : Subgroup G), Q ≤ (P' : Subgroup G) →
      IsUGroup 2 (P' : Subgroup G) U' → U' ≤ Subgroup.normalizer (Q : Set G) → U' ≤ M₀ →
        pCoreOf 2 M₀ ≠ ⊥) :
    pCoreOf 2 M₀ ≠ ⊥ := by
  classical
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  have hm4 : 4 ≤ m := hS.four_le
  have hp1 : 1 < p := hp.one_lt
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN
  have hQ2 : IsPGroup 2 Q := hQ ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N
  have hQN : Q ≤ N := hQ ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 N
  have hloc : IsTwoLocal N := ⟨Q, hQ0, hQ2, rfl⟩
  have hC : N ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    have := hS.charTwo N hloc
    rw [← hQ] at this
    exact this
  have hQM : Q ≤ M₀ := by
    have := hM.pCoreOf_two_le hS hB hBQ
    rw [← hQ] at this
    exact this
  let L : LinPkg Q N := LinPkg.ofCore hQ2 le_rfl hQ hC
  have hcardB : Nat.card B = p ^ m := hS.card_eq hB
  have hBel : IsElemAbelian p B := hB.1.1
  have hrankN : CFSG.Open.pRank p N ≤ m :=
    (pRank_le_glaTwoLocalRank hp1 hloc).trans hS.rank_eq.le
  have : IsSimpleGroup G := hS.simple
  have hNtop : N ≠ ⊤ := normalizer_ne_top_of_isPGroup_two hS.nonabelian hQ0 hQ2
  have hK : CFSG.Open.IsKGroup ↥N := isKGroup_of_isKProper hS.kProper hNtop
  have hBmax : GLAIsBmax p (B.subgroupOf N) := by
    have hQt : (Q.subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).2 le_rfl
    have hQt0 : Q.subgroupOf N ≠ ⊥ := by
      intro h
      apply hQ0
      rw [← Subgroup.map_subgroupOf_eq_of_le hQN, h, Subgroup.map_bot]
    have hQt2 : IsPGroup 2 (Q.subgroupOf N) :=
      IsPGroup.of_equiv hQ2 (Subgroup.subgroupOfEquivOfLe hQN).symm
    have hloc' : IsTwoLocal (⊤ : Subgroup ↥N) :=
      ⟨Q.subgroupOf N, hQt0, hQt2, (Subgroup.normalizer_eq_top_iff.2 hQt).symm⟩
    have hge : m ≤ GLATwoLocalRank p ↥N := by
      have h1 := pRank_le_glaTwoLocalRank hp1 hloc'
      have h2 := pRank_eq_pRank_top_subtype hp1 N
      have h3 : m ≤ CFSG.Open.pRank p N :=
        CFSG.SectionRank.le_pRank hp1 hBQ hBel hcardB
      omega
    have hle : GLATwoLocalRank p ↥N ≤ m :=
      (glaTwoLocalRank_subgroup_le hp1 N).trans hS.rank_eq.le
    refine ⟨isElemAbelian_subgroupOf' hBel, ?_, Q.subgroupOf N, hQt0, hQt2, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv, hcardB,
        le_antisymm hle hge]
    · intro x _
      rw [Subgroup.normalizer_eq_top]
      exact Subgroup.mem_top x
  have hM1 : ∀ S : Subgroup G, B ≤ Subgroup.normalizer (S : Set G) → ¬ p ∣ Nat.card S →
      S ≤ M₀ := fun S hBS hS' => hM.le_of_normalized hS hB hBS hS'
  have hM3 : ∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set G) ≤ M₀ := fun E hEB h3 =>
    (le_sSup ⟨E, hEB, h3, rfl⟩ : Subgroup.normalizer (E : Set G) ≤ GLBCore p 3 B).trans hM.2.1
  have hP2 : IsPGroup 2 (P : Subgroup G) := P.isPGroup'
  rcases L.stage2 hP2 hPQ hU hUN hC with hUQ | ⟨u₀, hu₀U, hu₀Q, hcover, htv⟩
  · exact h85 P U hPQ hU hUN (hUQ.trans hQM)
  · obtain ⟨n, hn⟩ := L.core86 i11 i5 i14 it hp hp2 hm4 hQ2 (L.pCoreOf_range_eq_bot hQ2 hQ) hK
      hBQ hBel hcardB hrankN hBmax hM1 hQM hM3 u₀ htv
    have hnN : (n : G) ∈ N := n.2
    have hnQ : ∀ q ∈ Q, (n : G) * q * (n : G)⁻¹ ∈ Q := fun q hq =>
      (Subgroup.mem_normalizer_iff.1 hnN q).1 hq
    have hnQ' : ∀ q ∈ Q, (n : G)⁻¹ * q * (n : G) ∈ Q := fun q hq => by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hnN) q).1 hq
      simpa using this
    obtain ⟨P'', hP''eq⟩ : ∃ P'' : Sylow 2 G, (P'' : Subgroup G) = GLBConj (n : G) (P : Subgroup G) :=
      ⟨(n : G)⁻¹ • P, by
        ext y
        rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_gLBConj]
        simp [MulAut.conj_apply, mul_assoc]⟩
    have hP''mem : ∀ y : G, y ∈ (P'' : Subgroup G) ↔ (n : G) * y * (n : G)⁻¹ ∈ (P : Subgroup G) := by
      intro y
      rw [hP''eq, mem_gLBConj]
    have hQP'' : Q ≤ (P'' : Subgroup G) := fun q hq => (hP''mem q).2 (hPQ (hnQ q hq))
    have hU' : IsUGroup 2 (P'' : Subgroup G) (GLBConj (n : G) U) := by
      rw [hP''eq]
      exact isUGroup_gLBConj hU _
    have hU'N : GLBConj (n : G) U ≤ N := by
      intro y hy
      rw [mem_gLBConj] at hy
      have h1 : (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G) ∈ N :=
        N.mul_mem (N.mul_mem (N.inv_mem hnN) (hUN hy)) hnN
      simpa [mul_assoc] using h1
    have hU'M : GLBConj (n : G) U ≤ M₀ := by
      intro y hy
      rw [mem_gLBConj] at hy
      have hy' : y = (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G) := by group
      rcases hcover _ hy with h | h
      · rw [hy']
        exact hQM (hnQ' _ h)
      · have e : y = ((n : G)⁻¹ * (u₀ : G) * n) *
            ((n : G)⁻¹ * ((u₀ : G)⁻¹ * ((n : G) * y * (n : G)⁻¹)) * (n : G)) := by group
        rw [e]
        exact M₀.mul_mem hn (hQM (hnQ' _ h))
    exact h85 P'' (GLBConj (n : G) U) hQP'' hU' hU'N hU'M

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
