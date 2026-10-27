module

public import CFSG.ClassicalInvolution.AschTight.S19QF2b
public import CFSG.ClassicalInvolution.AschTight.S1911P3h
public import CFSG.ClassicalInvolution.AschTight.S19QFund

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19L

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Disconnected.AschTight.S19Q (secY secE secFam secK)

variable {p : ℕ} [Fact p.Prime]

theorem oddCoreOf_map_eq_bot_psl {e₀ e₁ : ℕ} {E : Type} [Group E] [Finite E]
    {Ω : Set (Subgroup E)} {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e : ℕ}
    (M : Ih8Model p e₀ Ω t k e)
    (hΩ : HypOmegaMod p e₁ Ω) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e₁) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) {R : Subgroup (modelUniv t k p e Fact.out).K} (hR : R ∈ M.cls) :
    oddCoreOf (R.map M.ψ) = ⊥ ∧ 5 ≤ p ^ e₀ := by
  obtain ⟨φ⟩ := M.cls_equiv_sl2 hp2 hG2 hD4 hR
  have hodd := M.natCard_galoisField_odd hp2
  obtain ⟨z, hz⟩ := hΩ.classical _ (M.map_mem hR)
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    by_contra h4
    obtain ⟨e'⟩ := hz.nonempty_equiv
    have hF2 : 2 ≤ Nat.card (GaloisField p e) := by
      have := Fintype.ofFinite (GaloisField p e)
      rw [Nat.card_eq_fintype_card]
      exact Fintype.one_lt_card
    have hF3 : Nat.card (GaloisField p e) ≤ 3 := by omega
    have hR24 : Nat.card R ≤ 24 := by
      rw [Nat.card_congr φ.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
      have : Nat.card (GaloisField p e) ^ 2 ≤ 9 := by nlinarith
      have h1 : Nat.card (GaloisField p e) ^ 2 - 1 ≤ 8 := by omega
      calc Nat.card (GaloisField p e) * (Nat.card (GaloisField p e) ^ 2 - 1) ≤ 3 * 8 :=
            Nat.mul_le_mul hF3 h1
        _ = 24 := by norm_num
    have : Finite R := Finite.of_equiv _ φ.symm.toEquiv
    have hmap : Nat.card (R.map M.ψ) ≤ Nat.card R :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.Open.classicalInvolutionOddCore ↥(R.map M.ψ))
    have hpos : 0 < Nat.card (CFSG.Open.classicalInvolutionOddCore ↥(R.map M.ψ)) := Nat.card_pos
    have hqcard : Nat.card (↥(R.map M.ψ) ⧸ CFSG.Open.classicalInvolutionOddCore ↥(R.map M.ψ)) =
        p ^ e₁ * ((p ^ e₁) ^ 2 - 1) := by
      rw [Nat.card_congr e'.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
        GaloisField.card p e₁ (by rintro rfl; simp at hq)]
    have hbig : 120 ≤ p ^ e₁ * ((p ^ e₁) ^ 2 - 1) := by
      have h25 : 25 ≤ (p ^ e₁) ^ 2 := by nlinarith
      have : 24 ≤ (p ^ e₁) ^ 2 - 1 := by omega
      calc 120 = 5 * 24 := by norm_num
        _ ≤ p ^ e₁ * ((p ^ e₁) ^ 2 - 1) := Nat.mul_le_mul hq this
    have : p ^ e₁ * ((p ^ e₁) ^ 2 - 1) ≤ Nat.card (R.map M.ψ) := by
      rw [← hqcard, hquot]
      exact Nat.le_mul_of_pos_right _ hpos
    omega
  refine ⟨ih8_oddCoreOf_map_eq_bot M.ψ hodd h4 φ ⟨z, hz.mem, hz.orderOf_eq_two⟩, ?_⟩
  have he : e ≠ 0 := by have := M.admissible.2.1; omega
  have hcard : Nat.card (GaloisField p e) = p ^ e₀ := by
    rw [GaloisField.card p e he, M.exp_eq_f hD4]
  rw [hcard] at h4 hodd
  rcases (by omega : p ^ e₀ = 4 ∨ 5 ≤ p ^ e₀) with h | h
  · rw [h] at hodd
    exact absurd hodd (by decide)
  · exact h

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Subgroup G} {z : G} {S : Sylow 2 G}
  {W : Subgroup G}

theorem secK_exact (hd : Sec19Data p f K z S W) {a : G} {e₁ : ℕ} (h5 : 5 ≤ p ^ e₁)
    (hΩ : HypOmegaMod p e₁ (S1911.conjFamily (S1911.perfectCoreIn K a)))
    (hDE : Disconnected.DEdgeless (S1911.conjFamily (S1911.perfectCoreIn K a)))
    {e₀ : ℕ} {tg : CFSG.Assembly.LowTwoRank.StatedLieTag} {k e' : ℕ}
    (M : Ih8Model p e₀ (secFam K a) tg k e')
    (htg : tg = .PSL ∨ tg = .PSU) :
    oddCoreOf (secK K a) = ⊥ ∧ 5 ≤ p ^ e₀ := by
  have hp2 : p ≠ 2 := hd.tight.branch.odd
  obtain ⟨hΩ', -, -, -, -⟩ := section_facts hp2 h5 hΩ ⟨_, ⟨1, conjSub_one _⟩⟩ hDE
  have hKΦ : secK K a ∈ secFam K a :=
    (S1911.mem_secFamily_iff (S1911.perfectCoreIn K a) (secK K a)).mpr ⟨1, by rw [conjSub_one]⟩
  obtain ⟨R, hR, hRK⟩ := (M.mem_iff _).mp hKΦ
  have hG2 : tg ≠ .G2 := by rcases htg with rfl | rfl <;> decide
  have hD4 : tg ≠ .trialityD4 := by rcases htg with rfl | rfl <;> decide
  rw [hRK]
  exact oddCoreOf_map_eq_bot_psl M hΩ' hp2 h5 hG2 hD4 hR

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19L
