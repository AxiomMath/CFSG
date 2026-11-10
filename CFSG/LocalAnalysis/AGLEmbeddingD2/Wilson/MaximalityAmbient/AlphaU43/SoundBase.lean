
module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
public import CFSG.RankThree.PartTwo.Sec6.Item611Res6ProofU43

@[expose] public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Certificates
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Aut
  CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.U43Inv CFSG.LieType.Multipliers.U43
  CFSG.RankThree.PartTwo.Sec6.Res611Res6.U43P

def ClassClaim (l : ℕ) : Prop :=
  ∀ n : Gp, n ∈ Nrm → n ∉ Nsub → n * n = 1 →
    n * psi (ev (repW (l + 1))) = psi (ev (repW (l + 1))) * n →
    ∃ c : Gp, c ∈ Nsub ∧ c * psi (ev (repW (l + 1))) = psi (ev (repW (l + 1))) * c ∧ n * c ≠ c * n

section Claim

theorem exists_conj_rep {z : X₀} (hz : orderOf z = 3) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ 4 ∧ ∃ c : X₀, c * z * c⁻¹ = ev (repW l) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : z ^ 3 = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz] at this
  obtain ⟨g, hg⟩ := CFSG.RankThree.PartTwo.Sec6.Res611Res6.exists_conj_mem_of_card
    (P := p3.H) (by rw [card_p3, factorization_three_card_X₀]; norm_num) hz3
  obtain ⟨k, hk, hke⟩ := p3.exists_eq_elem p3_chkBase p3_chkTree p3_chkClosed (by decide) hg
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [p3.elem_zero] at hke
    have : z = 1 := by
      have := congrArg (fun y => g * y * g⁻¹) hke
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hk3 : p3.elem k ^ 3 = 1 := by
    have e3 : (g⁻¹ * z * g) ^ 3 = g⁻¹ * z ^ 3 * g := by
      have := conj_pow (a := g⁻¹) (b := z) (i := 3)
      rwa [inv_inv] at this
    rw [← hke, e3, hz3]
    group
  obtain ⟨l, hl1, hl4, c, hc⟩ := p3_exists_conj_rep hk hk0 hk3
  refine ⟨l, hl1, hl4, c * g⁻¹, ?_⟩
  rw [← hc, ← hke]
  group

theorem outer_not_fix_of_claim (hclaim : ∀ l < 4, ClassClaim l) {b : X₀} (hb : orderOf b = 3)
    (τ : MulAut X₀) (hτ2 : τ ^ 2 = 1) (hτo : τ ∉ (MulAut.conj : X₀ →* MulAut X₀).range) :
    ¬ ∀ c ∈ Subgroup.centralizer ({b} : Set X₀), τ c = c := by
  intro hfix
  obtain ⟨e, he⟩ := autModel
  set a : Gp := ((e.symm τ : (Nrm : Subgroup Gp)) : Gp) with ha
  have haN : a ∈ Nrm := (e.symm τ).2
  have hae : ∀ x, psi (τ x) = a * psi x * a⁻¹ := by
    intro x
    have := he (e.symm τ) x
    rwa [e.apply_symm_apply] at this
  have hττ : ∀ x, τ (τ x) = x := by
    intro x
    have := DFunLike.congr_fun hτ2 x
    simpa [pow_two] using this
  have hsq : a * a = 1 := by
    refine centralizer_trivial autFacts (a * a) ?_
    rintro _ ⟨x, rfl⟩
    have h1 : psi x = a * (a * psi x * a⁻¹) * a⁻¹ := by
      rw [← hae, ← hae, hττ]
    calc a * a * psi x = (a * (a * psi x * a⁻¹) * a⁻¹) * (a * a) := by group
      _ = psi x * (a * a) := by rw [← h1]
  have haNs : a ∉ Nsub := by
    rintro ⟨y, hy⟩
    apply hτo
    refine ⟨y, ?_⟩
    ext x
    apply psi_injective
    rw [MulAut.conj_apply, hae, ← hy]
    simp [map_mul, map_inv]
  obtain ⟨l, hl1, hl4, c, hc⟩ := exists_conj_rep hb
  have hl : l - 1 < 4 := by omega
  have hll : l - 1 + 1 = l := by omega
  have hρ : psi (ev (repW l)) = psi c * psi b * (psi c)⁻¹ := by
    rw [← hc]
    simp [map_mul, map_inv]
  have hψc : psi c ∈ Nsub := ⟨c, rfl⟩
  have hab : a * psi b = psi b * a := by
    have hb' : τ b = b := hfix b (Subgroup.mem_centralizer_singleton_iff.2 rfl)
    have := hae b
    rw [hb'] at this
    calc a * psi b = (a * psi b * a⁻¹) * a := by group
      _ = psi b * a := by rw [← this]
  set a' : Gp := psi c * a * (psi c)⁻¹ with ha'
  have ha'N : a' ∈ Nrm := mul_mem (mul_mem (Nsub_le_Nrm hψc) haN) (inv_mem (Nsub_le_Nrm hψc))
  have ha'Ns : a' ∉ Nsub := by
    intro h
    apply haNs
    have := Nsub.mul_mem (Nsub.mul_mem (Nsub.inv_mem hψc) h) hψc
    have e : (psi c)⁻¹ * a' * psi c = a := by rw [ha']; group
    rwa [e] at this
  have ha'sq : a' * a' = 1 := by
    calc a' * a' = psi c * (a * a) * (psi c)⁻¹ := by rw [ha']; group
      _ = 1 := by rw [hsq]; group
  have ha'ρ : a' * psi (ev (repW (l - 1 + 1))) = psi (ev (repW (l - 1 + 1))) * a' := by
    rw [hll, hρ]
    calc a' * (psi c * psi b * (psi c)⁻¹) = psi c * (a * psi b) * (psi c)⁻¹ := by rw [ha']; group
      _ = psi c * (psi b * a) * (psi c)⁻¹ := by rw [hab]
      _ = (psi c * psi b * (psi c)⁻¹) * a' := by rw [ha']; group
  obtain ⟨w, hwN, hwρ, hna⟩ := hclaim (l - 1) hl a' ha'N ha'Ns ha'sq ha'ρ
  rw [hll, hρ] at hwρ
  obtain ⟨y, hy⟩ := hwN
  set c₀ : X₀ := c⁻¹ * y * c with hc₀
  have hψc₀ : psi c₀ = (psi c)⁻¹ * w * psi c := by
    rw [hc₀, ← hy]
    simp [map_mul, map_inv]
  have hc₀b : c₀ ∈ Subgroup.centralizer ({b} : Set X₀) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply psi_injective
    rw [map_mul psi c₀ b, map_mul psi b c₀, hψc₀]
    calc (psi c)⁻¹ * w * psi c * psi b
        = (psi c)⁻¹ * (w * (psi c * psi b * (psi c)⁻¹)) * psi c := by group
      _ = (psi c)⁻¹ * ((psi c * psi b * (psi c)⁻¹) * w) * psi c := by rw [hwρ]
      _ = psi b * ((psi c)⁻¹ * w * psi c) := by group
  have hτc₀ := hfix c₀ hc₀b
  have h1 : a * psi c₀ * a⁻¹ = psi c₀ := by rw [← hae, hτc₀]
  apply hna
  have e1 : w = psi c * psi c₀ * (psi c)⁻¹ := by rw [hψc₀]; group
  have h2 : a * psi c₀ = psi c₀ * a := by
    calc a * psi c₀ = (a * psi c₀ * a⁻¹) * a := by group
      _ = psi c₀ * a := by rw [h1]
  calc a' * w = psi c * (a * psi c₀) * (psi c)⁻¹ := by rw [ha', e1]; group
    _ = psi c * (psi c₀ * a) * (psi c)⁻¹ := by rw [h2]
    _ = w * a' := by rw [ha', e1]; group

end Claim

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.AlphaU43
