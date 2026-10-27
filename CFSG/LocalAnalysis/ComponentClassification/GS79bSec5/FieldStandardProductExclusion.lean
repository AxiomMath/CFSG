module

public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardProduct
public import CFSG.LocalAnalysis.ComponentClassification.GS79bSec5.FieldStandardProductUnique

public section

open Subgroup

namespace CFSG.ComponentClassification.GS79bSec5

open CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.LocalAnalysis.EvenBN.LinearThree
open CFSG.OddStandard.Seitz77 (Datum)

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

theorem unique_of_caseB_of_frameData {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 2 ≤ f)
    (hKc : Nat.card K = 2 ^ f)
    {w₀ : WData d (F.rad 0) (2 ^ f)} {w₁ : WData d (F.rad 1) (2 ^ f)}
    (N₀ : CaseBNotation w₀ (F.leviData 0)) (N₁ : CaseBNotation w₁ (F.leviData 1))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    {G₁ : Subgroup G} (hq : CFSG.Open.IsQuasisimple G₁)
    (h₁₂ : G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G))
    (hZ : Odd (Nat.card (center ↥(G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom))))
    (he₁ : Nonempty (↥G₁ ⧸ center ↥G₁ ≃* projectiveSL 3 K))
    (hM₀ : N₀.M₁ ⊔ N₀.M₁.map (MulAut.conj d.t).toMonoidHom ≤
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom)
    (hM₁ : N₁.M₁ ⊔ N₁.M₁.map (MulAut.conj d.t).toMonoidHom ≤
      G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom)
    (hnonswap : ∀ P₁ P₂ : Subgroup G, CFSG.Open.IsQuasisimple P₁ → CFSG.Open.IsQuasisimple P₂ →
      P₂ ≤ centralizer (P₁ : Set G) → Odd (Nat.card (center ↥(P₁ ⊔ P₂))) →
      Nonempty (↥P₁ ⧸ center ↥P₁ ≃* projectiveSL 3 K) →
      Nonempty (↥P₂ ⧸ center ↥P₂ ≃* projectiveSL 3 K) →
      P₁.map (MulAut.conj d.t).toMonoidHom = P₁ → P₂.map (MulAut.conj d.t).toMonoidHom = P₂ →
      False) :
    ∀ g : G, g⁻¹ * d.t * g ∈
        normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) →
      g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
  refine SeitzReduction.F4Pilot.unique_of_forall_conjugate_eq fun g htM => ?_
  set G₂ := G₁.map (MulAut.conj d.t).toMonoidHom with hG₂
  have hM : CFSG.conjugate (G₁ ⊔ G₂) g = CFSG.conjugate G₁ g ⊔ CFSG.conjugate G₂ g :=
    Subgroup.map_sup _ _ _
  have hZg : Odd (Nat.card (center ↥(CFSG.conjugate G₁ g ⊔ CFSG.conjugate G₂ g))) := by
    have hZ' : Nat.card (center ↥(CFSG.conjugate (G₁ ⊔ G₂) g)) =
        Nat.card (center ↥(G₁ ⊔ G₂)) :=
      (Nat.card_congr (Subgroup.centerCongr
        ((G₁ ⊔ G₂).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
          (MulAut.conj g⁻¹).injective)).toEquiv).symm
    rw [← hM, hZ']
    exact hZ
  rw [hM] at htM
  have hqA := CFSG.SeitzReduction.LinearPilot.isQuasisimple_conjugate hq g
  have hqB := CFSG.SeitzReduction.LinearPilot.isQuasisimple_conjugate
    (CFSG.SeitzReduction.LinearPilot.isQuasisimple_map_conj hq d.t) g
  have hAB := CFSG.SeitzReduction.LinearPilot.conjugate_le_centralizer_of_le_centralizer h₁₂ g
  have hBA := le_centralizer_iff.1 hAB
  obtain ⟨hpA, hbA, hnA⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqA
  obtain ⟨hpB, hbB, hnB⟩ := SeitzReduction.F4Pilot.perfect_ne_bot_dichotomy_of_isQuasisimple hqB
  have he₁g : Nonempty (↥(CFSG.conjugate G₁ g) ⧸
      center ↥(CFSG.conjugate G₁ g) ≃* projectiveSL 3 K) :=
    he₁.map fun e₁ =>
      (CFSG.SeitzReduction.LinearPilot.conjugateQuotientCenterEquiv G₁ g).symm.trans e₁
  obtain ⟨e₁⟩ := he₁
  have htinv : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right d.t_mul_self
  have hG₂conj : G₂ = CFSG.conjugate G₁ d.t := by
    rw [CFSG.conjugate, hG₂, htinv]
  have he₂ : Nonempty (↥G₂ ⧸ center ↥G₂ ≃* projectiveSL 3 K) := by
    rw [hG₂conj]
    exact ⟨(CFSG.SeitzReduction.LinearPilot.conjugateQuotientCenterEquiv G₁ d.t).symm.trans e₁⟩
  have he₂g : Nonempty (↥(CFSG.conjugate G₂ g) ⧸
      center ↥(CFSG.conjugate G₂ g) ≃* projectiveSL 3 K) :=
    he₂.map fun e₂ =>
      (CFSG.SeitzReduction.LinearPilot.conjugateQuotientCenterEquiv G₂ g).symm.trans e₂
  rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect hAB hpA hbA hnA hnB htM with
    hAA | hswap
  · exfalso
    rcases SeitzReduction.F4Pilot.map_conj_eq_or_eq_of_perfect hBA hpB hbB hnB hnA
        (by rw [sup_comm]; exact htM) with hBB | hBA'
    · exact hnonswap _ _ hqA hqB hAB hZg he₁g he₂g hAA hBB
    · have hAB' : CFSG.conjugate G₂ g = CFSG.conjugate G₁ g :=
        SeitzReduction.F4Pilot.map_conj_toMonoidHom_inj.1 (hBA'.trans hAA.symm)
      rw [hAB'] at hAB
      exact hbA (by rw [← hpA, commutator_eq_bot_iff_le_centralizer.2 hAB])
  · exact conjugate_eq_of_swap_of_frameData F e hf hKc N₀ N₁ hB₀ hB₁ hq h₁₂ hZ ⟨e₁⟩
      hM₀ hM₁ g hswap

private theorem exists_quasisimple_of_caseB_of_frameData {K : Type} [Field K] [Finite K]
    [CharP K 2] (F : FrameData A d.V K) (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ}
    (hf : 3 ≤ f) (hKc : Nat.card K = 2 ^ f)
    (w₀ : WData d (F.rad 0) (2 ^ f)) (w₁ : WData d (F.rad 1) (2 ^ f))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    (hO₀ : ⁅CFSG.Open.standardComponentOddCore w₀.Nbar, w₀.Ebar (F.leviData 0).lev.range⁆ = ⊥)
    (hO₁ : ⁅CFSG.Open.standardComponentOddCore w₁.Nbar, w₁.Ebar (F.leviData 1).lev.range⁆ = ⊥)
    (hnonswap : ∀ P₁ P₂ : Subgroup G, CFSG.Open.IsQuasisimple P₁ → CFSG.Open.IsQuasisimple P₂ →
      P₂ ≤ centralizer (P₁ : Set G) → Odd (Nat.card (center ↥(P₁ ⊔ P₂))) →
      Nonempty (↥P₁ ⧸ center ↥P₁ ≃* projectiveSL 3 K) →
      Nonempty (↥P₂ ⧸ center ↥P₂ ≃* projectiveSL 3 K) →
      P₁.map (MulAut.conj d.t).toMonoidHom = P₁ → P₂.map (MulAut.conj d.t).toMonoidHom = P₂ →
      False) :
    ∃ G₁ : Subgroup G, CFSG.Open.IsQuasisimple G₁ ∧
      G₁.map (MulAut.conj d.t).toMonoidHom ≤ centralizer (G₁ : Set G) ∧
      G₁.map (MulAut.conj d.t).toMonoidHom ≠ G₁ ∧
      ∀ g : G, g⁻¹ * d.t * g ∈
          normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) →
        g ∈ normalizer ((G₁ ⊔ G₁.map (MulAut.conj d.t).toMonoidHom : Subgroup G) : Set G) := by
  obtain ⟨N₀, N₁, hq, h₁₂, hne, hZ, he₁, -, hr₀, hr₁, hprod, -, -⟩ :=
    exists_seitz43_product F e hf hKc w₀ w₁ hB₀ hB₁ hO₀ hO₁
  refine ⟨N₀.ℓ.range ⊔ N₁.ℓ.range, hq, h₁₂, hne, ?_⟩
  refine unique_of_caseB_of_frameData F e (by omega) hKc N₀ N₁ hB₀ hB₁ hq h₁₂ hZ he₁ ?_ ?_
    hnonswap
  · rw [← hr₀, hprod]
    exact le_sup_left
  · rw [← hr₁, hprod]
    exact le_sup_right

theorem false_of_caseB_of_frameData [IsSimpleGroup G] {K : Type} [Field K] [Finite K] [CharP K 2]
    (F : FrameData A d.V K) (e : (A ⧸ center A) ≃* projectiveSL 3 K) {f : ℕ} (hf : 3 ≤ f)
    (hKc : Nat.card K = 2 ^ f)
    (w₀ : WData d (F.rad 0) (2 ^ f)) (w₁ : WData d (F.rad 1) (2 ^ f))
    (hB₀ : w₀.CaseB (F.leviData 0).lev.range) (hB₁ : w₁.CaseB (F.leviData 1).lev.range)
    (hO₀ : ⁅CFSG.Open.standardComponentOddCore w₀.Nbar, w₀.Ebar (F.leviData 0).lev.range⁆ = ⊥)
    (hO₁ : ⁅CFSG.Open.standardComponentOddCore w₁.Nbar, w₁.Ebar (F.leviData 1).lev.range⁆ = ⊥)
    (hnonswap : ∀ P₁ P₂ : Subgroup G, CFSG.Open.IsQuasisimple P₁ → CFSG.Open.IsQuasisimple P₂ →
      P₂ ≤ centralizer (P₁ : Set G) → Odd (Nat.card (center ↥(P₁ ⊔ P₂))) →
      Nonempty (↥P₁ ⧸ center ↥P₁ ≃* projectiveSL 3 K) →
      Nonempty (↥P₂ ⧸ center ↥P₂ ≃* projectiveSL 3 K) →
      P₁.map (MulAut.conj d.t).toMonoidHom = P₁ → P₂.map (MulAut.conj d.t).toMonoidHom = P₂ →
      False) :
    False := by
  obtain ⟨G₁, hq, h₁₂, -, huniq⟩ :=
    exists_quasisimple_of_caseB_of_frameData F e hf hKc w₀ w₁ hB₀ hB₁ hO₀ hO₁ hnonswap
  exact SeitzReduction.F4Pilot.false_of_simple_of_swap_of_isQuasisimple d.sector.t_order hq
    h₁₂ rfl huniq

end CFSG.ComponentClassification.GS79bSec5
