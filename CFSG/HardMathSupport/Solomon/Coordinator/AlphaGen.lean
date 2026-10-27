module

public import CFSG.HardMathSupport.Solomon.Coordinator.Prop42
public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_or_isEkIn_of_index_le {p k : ℕ} (hp : p.Prime) {E F : Subgroup G}
    (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ (k + 1)) (hFE : F ≤ E)
    (hidx : (F.subgroupOf E).index ≤ p) : F = E ∨ IsEkIn p k E F := by
  have hmul : Nat.card (F.subgroupOf E) * (F.subgroupOf E).index = Nat.card E :=
    Subgroup.card_mul_index _
  have hFcard : Nat.card (F.subgroupOf E) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFE).toEquiv
  have hdvd : (F.subgroupOf E).index ∣ p ^ (k + 1) := hcard ▸ Subgroup.index_dvd_card _
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hj1 : j ≤ 1 := by
    by_contra h
    have : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.pos (by omega)
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj1 with rfl | rfl
  · left
    rw [pow_zero, Subgroup.index_eq_one] at hjeq
    refine le_antisymm hFE fun x hx => ?_
    have : (⟨x, hx⟩ : ↥E) ∈ F.subgroupOf E := hjeq ▸ Subgroup.mem_top _
    exact this
  · right
    refine ⟨hFE, isElemAbelian_mono hE hFE, ?_⟩
    rw [pow_one] at hjeq
    rw [hjeq, hFcard, hcard, pow_succ] at hmul
    exact Nat.eq_of_mul_eq_mul_right hp.pos hmul

theorem alphaGenHyp_of_isKProper (h713 : I_7_13_1_pPrime) (hK : CFSG.Open.IsKProper G) {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (hpG : p ∣ Nat.card G) {A : Subgroup G}
    (hA : IsElemAbelian p A) : AlphaGenHyp p k A := by
  intro D₀ hD₀ E hE
  have hD₀ne : D₀ ≠ ⊥ := hD₀.ne_bot hp hk
  have hXp : ¬ p ∣ Nat.card (GLADelta p D₀) := not_dvd_card_glaDelta hp hD₀ne
  have hXne : GLADelta p D₀ ≠ ⊤ := by
    intro htop
    apply hXp
    rw [htop, Subgroup.card_top]
    exact hpG
  have hXK : CFSG.Open.IsKGroup ↥(GLADelta p D₀) :=
    CFSG.ComponentClassification.CatalogueKProper.proper_subgroup_open_isKGroup hK _ hXne
  have hEX : E ≤ Subgroup.normalizer (GLADelta p D₀ : Set G) :=
    hE.1.trans (le_normalizer_glaDelta hA hD₀.1)
  rw [commutator_eq_iSup_commutator_centralizer h713 hp hp2 hE.2.1 hEX hXp hXK le_rfl]
  refine iSup₂_le fun F hF => ?_
  rcases eq_or_isEkIn_of_index_le hp hE.2.1 hE.2.2 hF.1 hF.2 with rfl | hFk
  · have : ⁅GLADelta p D₀ ⊓ Subgroup.centralizer (F : Set G), F⁆ = ⊥ :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer).2 inf_le_right
    rw [this]
    exact bot_le
  · exact le_iSup₂_of_le F hFk le_rfl

theorem alphaGenHypAll_of_i713 (h713 : I_7_13_1_pPrime) : AlphaGenHypAll := by
  intro G _ _ m p hS B hB
  exact alphaGenHyp_of_isKProper h713 hS.kProper hS.prime hS.ne_two (by norm_num)
    hS.beta.2.2.1 hB.1.1

end CFSG.HardMathSupport.Solomon.Coordinator
