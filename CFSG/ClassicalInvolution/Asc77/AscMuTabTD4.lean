module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabOrderFour
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Chart

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.G2D4Models
  CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.CurtisTits
open scoped MatrixGroups

namespace MuTab

section TD4

theorem td4_orderFour_core {K : Type} [Field K] [Finite K] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) (hoddK : Odd (Nat.card K))
    (hoddF : Odd (Nat.card (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField σ)))
    (i : Fin (Tag.rank .G2)) (g₀ : twistedGroup σ) :
    ∃ c j d : twistedGroup σ, IsUniqueInvolution (conjSub g₀ (rankOne (twistedRootGroup σ) i)) c ∧
      j ∈ conjSub g₀ (rankOne (twistedRootGroup σ) i) ∧ orderOf j = 4 ∧ d * d = 1 ∧ d ≠ 1 ∧
        d ≠ c ∧ j * d = d * j := by
  have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
    have := i.2
    change (i : ℕ) < 2 at this
    omega
  rcases hi with hi | hi
  · have hi0 : i = ng 0 := Fin.ext hi
    subst hi0
    rw [ModelFacts.rankOne_long_eq_range hσ]
    exact exists_orderFour_of_charts hoddF (slLong_injective hσ) (slLong_comm_slB hσ)
      (slB_neg_one hσ).symm g₀
  · have hi1 : i = ng 1 := Fin.ext hi
    subst hi1
    have hB' : (slB σ hσ).range = conjSub (nB σ) (slShort σ hσ).range := by
      unfold slB
      rw [MonoidHom.range_comp]
      rfl
    have hB : (slShort σ hσ).range = conjSub (nB σ)⁻¹ (slB σ hσ).range := by
      rw [hB', conjSub_inv_conjSub]
    rw [ModelFacts.rankOne_short_eq_range hσ, hB, ← conjSub_mul]
    exact exists_orderFour_of_charts hoddK (slB_injective hσ)
      (fun A B => (slLong_comm_slB hσ B A).symm) (slB_neg_one hσ) _

variable {p : ℕ} [Fact p.Prime]

theorem td4_exists_orderFour (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {R : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D) :
    ∃ c j d : (modelUniv .trialityD4 0 p e Fact.out).K, IsUniqueInvolution R c ∧ j ∈ R ∧
      orderOf j = 4 ∧ d * d = 1 ∧ d ≠ 1 ∧ d ≠ c ∧ j * d = d * j := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  have hoddK : Odd (Nat.card (GaloisField p (3 * e))) := by
    rw [GaloisField.card p (3 * e) (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hoddF : Odd (Nat.card (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField
      (iterateFrobenius (GaloisField p (3 * e)) p e))) := by
    rw [ModelFacts.card_fixedField_iterateFrobenius he]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨i, g₀, rfl⟩ := exists_conj_rankOne_node_of_trialityD4 0 p e hadm hR
  exact td4_orderFour_core hσ hoddK hoddF i g₀

end TD4

end MuTab

section TD4Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {e : ℕ}

theorem MuTab.td4_omegaStarNbr_nonempty (M : Ih8Model p f Ω .trialityD4 0 e)
    (hΩ : HypOmegaMod p f Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hne : Ω.Nonempty) :
    ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty := by
  have he : 1 ≤ e := M.admissible.2.1
  have hinj : Function.Injective M.ψ :=
    RouteD.G2D4.injective_of_ker_le_center hp2 (Or.inr rfl) 0 he M.ψ M.ker_le_center
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨R, hR, -⟩ := (M.mem_iff K₀).mp hK₀
  obtain ⟨c, j, d, hc, hj, hj4, hd, hd1, hdc, hjd⟩ :=
    MuTab.td4_exists_orderFour hp2 M.admissible (M.cls_sub hR)
  exact M.muTab_omegaStarNbr_of_orderFour hΩ hp2 hq hinj
    (fun u u' hu hu' hu1 hu1' =>
      Balance.Bootstrap.trialityD4_involutions_conj hp2 he hu hu' hu1 hu1')
    hR hc hj hj4 hd hd1 hdc hjd

end TD4Datum

end CFSG.ClassicalInvolution.Asc77
