module

public import CFSG.GH74.GLS.Stage4.LocalSL2

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.GH74.GLS.Stage4.SL2 CFSG.GH74.GLS.Stage4.Hex Subgroup Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem card_eq_two_pow_of_charP : ∃ f : ℕ, 1 ≤ f ∧ Nat.card F = 2 ^ f := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem exists_conj_le_upperSub {T : Subgroup (SL2 F)} (hT : IsPGroup 2 T) :
    ∃ g : SL2 F, ∀ x ∈ T, g⁻¹ * x * g ∈ upperSub F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf, hFf⟩ := card_eq_two_pow_of_charP (F := F)
  have hU1 : IsPGroup 2 (upperSub F) := IsPGroup.of_card ((card_upperSub (F := F)).trans hFf)
  have hU2 : ¬ 2 ∣ (upperSub F).index := by
    intro hdvd
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hind : (upperSub F).index = Nat.card F ^ 2 - 1 := by
      have := (upperSub F).card_mul_index
      rw [card_upperSub, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at this
      exact Nat.eq_of_mul_eq_mul_left (by omega) this
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hpq : 2 ∣ Nat.card F := hFf ▸ dvd_pow_self 2 (by omega)
    have h2 : 2 ∣ Nat.card F ^ 2 - 1 + 1 := by
      rw [Nat.sub_add_cancel h1]
      exact dvd_pow hpq two_ne_zero
    rw [hind] at hdvd
    exact Nat.prime_two.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp h2))
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F) (hU1.toSylow hU2) Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ (Q : Subgroup (SL2 F)) := hTQ hx
  rw [← hg, Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxQ
  simpa [MulAut.smul_def, mul_assoc] using hxQ

theorem eq_one_of_order_three_normalizes_two (h3 : ¬ 3 ∣ Nat.card F - 1) {T : Subgroup (SL2 F)}
    (hT : IsPGroup 2 T) (hne : T ≠ ⊥) {g : SL2 F} (hg3 : g ^ 3 = 1)
    (hN : g ∈ Subgroup.normalizer (T : Set (SL2 F))) : g = 1 := by
  obtain ⟨h, hh⟩ := exists_conj_le_upperSub hT
  obtain ⟨x, hxT, hx1⟩ : ∃ x ∈ T, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_bot_iff_forall T).2 hcon)
  obtain ⟨s, hs⟩ := (mem_upperSub_iff _).1 (hh x hxT)
  have hs0 : s ≠ 0 := by
    rintro rfl
    apply hx1
    have h1 : h⁻¹ * x * h = 1 := by rw [hs, sl2U_zero]
    calc x = h * (h⁻¹ * x * h) * h⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨g', hg'⟩ : ∃ g' : SL2 F, g' = h⁻¹ * g * h := ⟨_, rfl⟩
  have hmem : g' * sl2U s * g'⁻¹ ∈ upperSub F := by
    have h1 : g * x * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hN x).1 hxT
    have h2 := hh _ h1
    have : g' * sl2U s * g'⁻¹ = h⁻¹ * (g * x * g⁻¹) * h := by
      rw [← hs, hg']
      group
    rw [this]
    exact h2
  have hc : (g' : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := c_zero_of_conj_mem_upper g' hs0 hmem
  obtain ⟨a, ha⟩ : ∃ a : F, (g' : Matrix (Fin 2) (Fin 2) F) 0 0 = a := ⟨_, rfl⟩
  have hg'3 : g' ^ 3 = 1 := by
    have e : (h⁻¹ * g * h) ^ 3 = h⁻¹ * g ^ 3 * h := by
      simpa using conj_pow (a := h⁻¹) (b := g) (i := 3)
    rw [hg', e, hg3]
    group
  have h3' : g' * g' * g' = 1 := by
    have := hg'3
    rwa [pow_succ, pow_succ, pow_one] at this
  have hsix : a ^ 6 = 1 := by
    have h1 : g' * (g' * (g' * sl2U 1 * g'⁻¹) * g'⁻¹) * g'⁻¹ = sl2U 1 := by
      have e : g' * (g' * (g' * sl2U 1 * g'⁻¹) * g'⁻¹) * g'⁻¹ =
          (g' * g' * g') * sl2U 1 * (g' * g' * g')⁻¹ := by
        simp only [_root_.mul_inv_rev, mul_assoc]
      rw [e, h3', inv_one]
      simp
    rw [conj_sl2U_of_c_zero g' hc, ha, conj_sl2U_of_c_zero g' hc, ha,
      conj_sl2U_of_c_zero g' hc, ha] at h1
    have h2 := sl2U_injective h1
    have : a ^ 6 = a ^ 2 * (a ^ 2 * (a ^ 2 * 1)) := by ring
    rw [this]
    exact h2
  have hdet := sl2_entries g'
  rw [hc, ha] at hdet
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have hq : a ^ (Nat.card F - 1) = 1 := by
    letI := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card (α := F)]
    exact FiniteField.pow_card_sub_one_eq_one a ha0
  obtain ⟨f, hf, hFf⟩ := card_eq_two_pow_of_charP (F := F)
  have hcop : Nat.gcd 6 (Nat.card F - 1) = 1 := by
    have hodd : ¬ 2 ∣ Nat.card F - 1 := by
      rw [hFf]
      intro hd
      have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      omega
    have h2' : Nat.Coprime 2 (Nat.card F - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    have h3'' : Nat.Coprime 3 (Nat.card F - 1) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
    exact Nat.Coprime.mul_left h2' h3''
  have ha1 : a = 1 := by
    have := (pow_gcd_eq_one (a := a)).2 ⟨hsix, hq⟩
    rwa [hcop, pow_one] at this
  subst ha1
  have hd1 : (g' : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    simpa using hdet
  have hu : g' = sl2U ((g' : Matrix (Fin 2) (Fin 2) F) 0 1) := by
    apply sl2_ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc, ha, hd1]
  have hsq : g' ^ 2 = 1 := by
    rw [hu, pow_two, ← sl2U_add, CharTwo.add_self_eq_zero, sl2U_zero]
  have hg1 : g' = 1 := by
    calc g' = g' ^ 3 * (g' ^ 2)⁻¹ := by group
      _ = 1 := by rw [hg'3, hsq]; group
  calc g = h * g' * h⁻¹ := by rw [hg']; group
    _ = 1 := by rw [hg1]; group

end CFSG.LocalAnalysis.GLTheoremA
