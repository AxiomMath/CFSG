module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabG2
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.ModelFacts.G2D4TD4Chart
public import CFSG.ClassicalInvolution.Q3.LieSystem
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.G2D4Models
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

@[expose] def SqrtFund (c : CompData) : Prop :=
  ∀ R ∈ c.fund, ∃ k : c.G, (∀ x ∈ R, k * x = x * k) ∧ k * k ∈ R ∧ k * k ≠ 1 ∧
    (k * k) * (k * k) = 1

section Charts

variable {G : Type} [Group G] {F F' : Type} [Field F] [Finite F] [Field F']

theorem sqrt_of_charts (hodd : Odd (Nat.card F)) {Φc : SL(2, F) →* G} {Ψc : SL(2, F') →* G}
    (hΦ : Function.Injective Φc) (hcomm : ∀ A B, Φc A * Ψc B = Ψc B * Φc A)
    (hneg : Φc (-1) = Ψc (-1)) (g₀ : G) :
    ∃ k : G, (∀ x ∈ conjSub g₀ Φc.range, k * x = x * k) ∧ k * k ∈ conjSub g₀ Φc.range ∧
      k * k ≠ 1 ∧ (k * k) * (k * k) = 1 := by
  set w := Ψc (MuTab.wFour F') with hw
  have hkk : g₀ * w * g₀⁻¹ * (g₀ * w * g₀⁻¹) = g₀ * Φc (-1) * g₀⁻¹ := by
    calc g₀ * w * g₀⁻¹ * (g₀ * w * g₀⁻¹) = g₀ * (w * w) * g₀⁻¹ := by group
      _ = g₀ * Φc (-1) * g₀⁻¹ := by rw [hw, ← map_mul, MuTab.wFour_mul_self, hneg]
  have hcc : Φc (-1) * Φc (-1) = 1 := (isUniqueInvolution_range_sl2 hodd hΦ).sq
  refine ⟨g₀ * w * g₀⁻¹, fun x hx => ?_, ?_, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := mem_conjSub_iff.mp hx
    have hxe : x = g₀ * Φc A * g₀⁻¹ := by rw [hA]; group
    rw [hxe]
    calc g₀ * w * g₀⁻¹ * (g₀ * Φc A * g₀⁻¹) = g₀ * (w * Φc A) * g₀⁻¹ := by group
      _ = g₀ * (Φc A * w) * g₀⁻¹ := by rw [hw, hcomm]
      _ = g₀ * Φc A * g₀⁻¹ * (g₀ * w * g₀⁻¹) := by group
  · rw [hkk]
    exact conj_mem_conjSub ⟨-1, rfl⟩
  · rw [hkk]
    intro h
    apply CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
    apply hΦ
    rw [map_one]
    calc Φc (-1) = g₀⁻¹ * (g₀ * Φc (-1) * g₀⁻¹) * g₀ := by group
      _ = 1 := by rw [h]; group
  · rw [hkk]
    calc g₀ * Φc (-1) * g₀⁻¹ * (g₀ * Φc (-1) * g₀⁻¹) = g₀ * (Φc (-1) * Φc (-1)) * g₀⁻¹ := by
          group
      _ = 1 := by rw [hcc]; group

end Charts

section G2

variable {p e : ℕ} [Fact p.Prime]

theorem g2_sqrt (hp2 : p ≠ 2) (he : 1 ≤ e)
    {R : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) :
    ∃ k : ↥(adjointGroup Tag.G2 (GaloisField p e)), (∀ x ∈ R, k * x = x * k) ∧ k * k ∈ R ∧
      k * k ≠ 1 ∧ (k * k) * (k * k) = 1 := by
  obtain ⟨g₀, γ, hγ, rfl⟩ := hR
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨Φ, Ψ, hΦ, hcomm, hneg, hrange⟩ := MuTab.g2_exists_commuting_charts hp2 he hγroot
  rw [← hrange]
  exact sqrt_of_charts hodd hΦ hcomm hneg g₀

end G2

section TD4

open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.CurtisTits

theorem td4_sqrt_core {K : Type} [Field K] [Finite K] {σ : K →+* K}
    (hσ : ∀ c, σ (σ (σ c)) = c) (hoddK : Odd (Nat.card K))
    (hoddF : Odd (Nat.card (CFSG.ClassicalInvolution.Models.TwistedPairs.fixedField σ)))
    (i : Fin (Tag.rank .G2)) (g₀ : twistedGroup σ) :
    ∃ k : twistedGroup σ, (∀ x ∈ conjSub g₀ (rankOne (twistedRootGroup σ) i), k * x = x * k) ∧
      k * k ∈ conjSub g₀ (rankOne (twistedRootGroup σ) i) ∧ k * k ≠ 1 ∧
        (k * k) * (k * k) = 1 := by
  have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
    have := i.2
    change (i : ℕ) < 2 at this
    omega
  rcases hi with hi | hi
  · have hi0 : i = ng 0 := Fin.ext hi
    subst hi0
    rw [ModelFacts.rankOne_long_eq_range hσ]
    exact sqrt_of_charts hoddF (slLong_injective hσ) (slLong_comm_slB hσ) (slB_neg_one hσ).symm g₀
  · have hi1 : i = ng 1 := Fin.ext hi
    subst hi1
    have hB' : (slB σ hσ).range = conjSub (nB σ) (slShort σ hσ).range := by
      unfold slB
      rw [MonoidHom.range_comp]
      rfl
    have hB : (slShort σ hσ).range = conjSub (nB σ)⁻¹ (slB σ hσ).range := by
      rw [hB', conjSub_inv_conjSub]
    rw [ModelFacts.rankOne_short_eq_range hσ, hB, ← conjSub_mul]
    exact sqrt_of_charts hoddK (slB_injective hσ) (fun A B => (slLong_comm_slB hσ B A).symm)
      (slB_neg_one hσ) _

variable {p : ℕ} [Fact p.Prime]

theorem td4_sqrt (hp2 : p ≠ 2) {e : ℕ} (hadm : StatedLieAdmissible .trialityD4 0 p e)
    {R : Subgroup (modelUniv .trialityD4 0 p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 0 p e Fact.out).D) :
    ∃ k : (modelUniv .trialityD4 0 p e Fact.out).K, (∀ x ∈ R, k * x = x * k) ∧ k * k ∈ R ∧
      k * k ≠ 1 ∧ (k * k) * (k * k) = 1 := by
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
  exact td4_sqrt_core hσ hoddK hoddF i g₀

end TD4

end CFSG.ClassicalInvolution.Q3.TL4
