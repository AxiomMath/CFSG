module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Ree
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimOrders

public section

namespace CFSG.AGLEmbedding

open Equiv

noncomputable def mulAutEquivPermOfAlternating {p : ℕ} (hp : 3 ≤ p) {L : Type} [Group L]
    (e : L ≃* alternatingGroup (Fin (3 * p))) : MulAut L ≃* Perm (Fin (3 * p)) :=
  (MulAut.congr e).trans (MulEquiv.ofBijective _
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj (3 * p) (by omega)
      (by omega))).symm

theorem card_mulAut_of_alternating {p : ℕ} (hp : 3 ≤ p) {L : Type} [Group L]
    (e : L ≃* alternatingGroup (Fin (3 * p))) :
    Nat.card (MulAut L) = (3 * p).factorial := by
  rw [Nat.card_congr (mulAutEquivPermOfAlternating hp e).toEquiv, Nat.card_perm, Nat.card_fin]

theorem le_four_of_pow_dvd_factorial {p k : ℕ} [Fact p.Prime] (hp : 3 ≤ p)
    (h : p ^ k ∣ (3 * p).factorial) : k ≤ 4 := by
  have hne : (3 * p).factorial ≠ 0 := Nat.factorial_ne_zero _
  rw [padicValNat_dvd_iff_le hne, mul_comm, padicValNat_factorial_mul] at h
  have h6 : padicValNat p (Nat.factorial 3) ≤ 1 := by
    by_contra h2
    push Not at h2
    have := (padicValNat_dvd_iff_le (p := p) (by decide : Nat.factorial 3 ≠ 0)).mpr h2
    have h3 : p ^ 2 ≤ Nat.factorial 3 := Nat.le_of_dvd (by decide) this
    nlinarith [show Nat.factorial 3 = 6 by decide]
  omega

theorem kFactJStarElimReeAlt_of (hRee : KFactReeOrder) : KFactJStarElimReeAlt := by
  rintro d₀ hd₀ L _ _ ⟨e⟩ ⟨A, J, -, -, -, φ, hφ, -⟩
  have hn3 : 3 ≤ d₀.1.fieldExponent := hd₀.three_le_fieldExponent
  have hfin : Finite (CatGroup d₀) := Finite.of_surjective φ hφ
  have hcard := hRee (CatGroup d₀) d₀ hd₀ ⟨MulEquiv.refl _⟩
  have hdvd : Nat.card (CatGroup d₀) ∣ (3 * 3).factorial := by
    rw [← card_mulAut_of_alternating (p := 3) le_rfl e]
    exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card J)
  have hle := Nat.le_of_dvd (Nat.factorial_pos _) hdvd
  rw [hcard] at hle
  set q := 3 ^ d₀.1.fieldExponent with hq
  have hq27 : 27 ≤ q := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q := Nat.pow_le_pow_right (by norm_num) hn3
  have h1 : 27 ^ 3 ≤ q ^ 3 := Nat.pow_le_pow_left hq27 3
  have h2 : 1 ≤ q ^ 3 + 1 := Nat.le_add_left 1 _
  have h3 : 26 ≤ q - 1 := by omega
  have h4 : q ^ 3 * 1 * 26 ≤ q ^ 3 * (q ^ 3 + 1) * (q - 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul le_rfl h2) h3
  have h5 : (3 * 3).factorial = 362880 := by decide
  omega

theorem kFactJStarElimReeAlt
    : KFactJStarElimReeAlt :=
  kFactJStarElimReeAlt_of kFactReeOrder

theorem kFactJStarElimUnitaryAlt : KFactJStarElimUnitaryAlt := by
  rintro p _ d₀ hp2 hd₀ hn L _ _ ⟨e⟩ ⟨A, J, -, -, -, φ, hφ, -⟩
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hfin : Finite (CatGroup d₀) := Finite.of_surjective φ hφ
  have hdvd : Nat.card (CatGroup d₀) ∣ (3 * p).factorial := by
    rw [← card_mulAut_of_alternating hp3 e]
    exact (Subgroup.card_dvd_of_surjective hφ).trans (Subgroup.card_subgroup_dvd_card J)
  have h4 := le_four_of_pow_dvd_factorial hp3
    ((pow_dvd_card_catGroup_unitary hd₀).trans hdvd)
  omega

end CFSG.AGLEmbedding
