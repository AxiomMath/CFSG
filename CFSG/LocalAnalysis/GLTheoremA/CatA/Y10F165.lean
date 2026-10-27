module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

@[expose] def I165Fact : Prop :=
  ∀ (K : Type) [Group K] [Finite K], HasLabel K (fun _ => True) →
    ∀ p q : ℕ, p.Prime → p ≠ 2 → q.Prime → q ≠ 2 → q ≠ p →
      (∀ lab : GLALabel, HasLabel K (fun l : GLALabel => l = lab) → ¬ GLASplit16 p lab) →
      ¬ p ∣ Nat.card (Subgroup.center K) →
      ∀ A : Subgroup K, IsElemAbelian p A →
        (∀ g : K, g ∈ Subgroup.centralizer (A : Set K) → orderOf g = p → g ∈ A) →
        GLATwoLocalRank p K ≤ CFSG.Open.pRank p A →
        CFSG.Open.pRank p (⊤ : Subgroup K) ≤ CFSG.Open.pRank p A →
        (⁅A, nGen A (⊤ : Subgroup K)⁆ ≠ ⊥ ∨ CFSG.Open.pRank p A + 2 ≤ evenRank K) →
        evenRank K = GLATwoLocalRank q K → CFSG.Open.pRank p A + 1 ≤ evenRank K →
        4 ≤ CFSG.Open.pRank p A + 1 →
        ∃ D E F J : Subgroup K, D ≤ E ∧ E ≤ A ∧ Nat.card D = p ∧ Nat.card E = p ^ 2 ∧
          GLAPComponent p (Subgroup.centralizer (D : Set K)) J ∧
          A ≤ Subgroup.normalizer (J : Set K) ∧
          GLAPLayer p (J ⊓ Subgroup.centralizer (E : Set K)) ≠ ⊥ ∧
          F ≤ Subgroup.centralizer (D : Set K) ∧ IsElemAbelian q F ∧
          F ≤ Subgroup.normalizer (J : Set K) ∧ 3 ≤ CFSG.Open.pRank q F

variable {G : Type} [Group G] [Finite G]

theorem i165At_of_facts (h : I165Fact) : I165At G := by
  intro p q hp hp2 hq hq2 hqp K A hK hNS hZ hSC hr1 hmax hb he hm1 hm4
  obtain ⟨hAK, hA, hSCc⟩ := isSCIn_iff.1 hSC
  set A' : Subgroup K := A.subgroupOf K with hA'
  have hAmap : A'.map K.subtype = A := subgroupOf_map_subtype_of_le hAK
  have hpr : CFSG.Open.pRank p A' = CFSG.Open.pRank p A := pRank_subgroupOf hAK
  have htop : CFSG.Open.pRank p (⊤ : Subgroup K) = CFSG.Open.pRank p K := by
    rw [← Subgroup.subgroupOf_self]
    exact pRank_subgroupOf le_rfl
  have hcomm : (⁅A', nGen A' (⊤ : Subgroup K)⁆ : Subgroup K) ≠ ⊥ ↔ (⁅A, nGen A K⁆ : Subgroup G) ≠ ⊥ := by
    have h1 : (⁅A, nGen A K⁆ : Subgroup G) = (⁅A', nGen A' (⊤ : Subgroup K)⁆).map K.subtype := by
      rw [Subgroup.map_commutator, hAmap, ← nGen_map_subtype, hAmap]
    rw [h1]
    exact not_congr (map_subtype_eq_bot_iff _).symm
  obtain ⟨D', E', F', J', hDE, hEA, hD, hE, hJ, hAJ, hlay, hFD, hF, hFJ, hF3⟩ :=
    h ↥K hK p q hp hp2 hq hq2 hqp hNS hZ A' hA hSCc (by rw [hpr]; exact hr1)
      (by rw [htop, hpr]; exact hmax)
      (by rcases hb with hb | hb
          · exact Or.inl (hcomm.2 hb)
          · exact Or.inr (by rw [hpr]; exact hb))
      he (by rw [hpr]; exact hm1) (by rw [hpr]; exact hm4)
  refine ⟨D'.map K.subtype, E'.map K.subtype, F'.map K.subtype, J'.map K.subtype,
    Subgroup.map_mono hDE, ?_, by rw [card_map_subtype]; exact hD, by rw [card_map_subtype]; exact hE,
    ?_, ?_, ?_, ?_, (isElemAbelian_map_subtype_iff F').2 hF, ?_, by rw [pRank_map_subtype]; exact hF3⟩
  · rw [← hAmap]; exact Subgroup.map_mono hEA
  · rw [← map_centralizer_subtype]
    exact (glaPComponent_map_iff hp K.subtype_injective).2 hJ
  · rw [← hAmap]; exact map_le_normalizer_map hAJ
  · rw [inf_centralizer_map, glaPLayer_map hp K.subtype_injective]
    exact fun h0 => hlay ((map_subtype_eq_bot_iff _).1 h0)
  · rw [map_le_centralizer_iff]; exact hFD
  · exact map_le_normalizer_map hFJ

end CFSG.LocalAnalysis.GLTheoremA.Y10F
