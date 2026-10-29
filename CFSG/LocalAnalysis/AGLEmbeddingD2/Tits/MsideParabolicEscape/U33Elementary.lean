module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Pair
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33Centralizer

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33

open Matrix

variable {F : Type} [Field F] [Finite F]

abbrev mat (g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F := (g : Matrix (Fin 3) (Fin 3) F)

theorem two_ne_zero_of_charP (hF : Nat.card F = 9) : (2 : F) ≠ 0 := by
  haveI := charP_three hF
  intro h
  have : ((2 : ℕ) : F) = 0 := by simpa using h
  have := (CharP.cast_eq_zero_iff F 3 2).mp this
  omega

theorem adj_eq_neg_of_sq_zero (σ : F →+* F) (X : Matrix (Fin 3) (Fin 3) F)
    (hX : adj σ X * X = 1) (hν2 : (X - 1) * (X - 1) = 0) : adj σ (X - 1) = -(X - 1) := by
  have h1 : X * (1 - (X - 1)) = 1 := by
    have : X * (1 - (X - 1)) = 1 - (X - 1) * (X - 1) := by noncomm_ring
    rw [this, hν2, sub_zero]
  have h2 : adj σ X = 1 - (X - 1) := by
    calc adj σ X = adj σ X * (X * (1 - (X - 1))) := by rw [h1, mul_one]
      _ = (adj σ X * X) * (1 - (X - 1)) := by rw [mul_assoc]
      _ = 1 - (X - 1) := by rw [hX, one_mul]
  rw [adj_sub, adj_one, h2]
  abel

theorem sq_sum_commute (a b : Matrix (Fin 3) (Fin 3) F) (hab : a * b = b * a) (ha : a * a = 0)
    (hb : b * b = 0) : (a + b + a * b) * (a + b + a * b) = (2 : F) • (a * b) := by
  have f1 : a * (a * b) = 0 := by rw [← mul_assoc, ha, zero_mul]
  have f2 : b * (a * b) = 0 := by rw [← mul_assoc, ← hab, mul_assoc, hb, mul_zero]
  have f3 : (a * b) * a = 0 := by rw [mul_assoc, ← hab, f1]
  have f4 : (a * b) * b = 0 := by rw [mul_assoc, hb, mul_zero]
  have f5 : (a * b) * (a * b) = 0 := by rw [mul_assoc, f2, mul_zero]
  simp only [mul_add, add_mul, ha, hb, f1, f2, f3, f4, f5, ← hab, add_zero, zero_add]
  rw [two_smul]

theorem frob_frob (hF : Nat.card F = 9) (x : F) : frob hF (frob hF x) = x := by
  haveI := Fintype.ofFinite F
  rw [frob_apply, frob_apply, ← pow_mul]
  have := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hF] at this

theorem exists_regular_of_elemAbelian (hF : Nat.card F = 9) (Q : Subgroup ↥(SU F))
    (hQ3 : ∀ x ∈ Q, x ^ 3 = 1) (hQc : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hQ9 : Nat.card Q = 9) :
    ∃ y ∈ Q, (mat (y : GL (Fin 3) F) - 1) ^ 2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  haveI := charP_three hF
  set σ : F →+* F := frob hF with hσ
  obtain ⟨x, hxQ, hx1⟩ : ∃ x ∈ Q, x ≠ 1 := by
    by_contra h
    push Not at h
    have : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).mpr h
    rw [this, Subgroup.card_bot] at hQ9
    omega
  obtain ⟨y, hyQ, hyx⟩ : ∃ y ∈ Q, y ∉ Subgroup.zpowers x := by
    by_contra h
    push Not at h
    have hle : Q ≤ Subgroup.zpowers x := h
    have h1 : Nat.card Q ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one (hQ3 x hxQ)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  set X := mat ((x : ↥(SU F)) : GL (Fin 3) F) with hX
  set Y := mat ((y : ↥(SU F)) : GL (Fin 3) F) with hY
  set ν := X - 1 with hν
  set μ := Y - 1 with hμ
  have hν2 : ν * ν = 0 := by
    have := hcon x hxQ
    rwa [pow_two] at this
  have hμ2 : μ * μ = 0 := by
    have := hcon y hyQ
    rwa [pow_two] at this
  have hUx : adj σ X * X = 1 := ((mem_statedSU_iff hF _).mp x.2).1
  have hUy : adj σ Y * Y = 1 := ((mem_statedSU_iff hF _).mp y.2).1
  have hadjν : adj σ ν = -ν := adj_eq_neg_of_sq_zero σ X hUx hν2
  have hadjμ : adj σ μ = -μ := adj_eq_neg_of_sq_zero σ Y hUy hμ2
  have hXY : X * Y = Y * X := by
    have := congrArg (fun z : ↥(SU F) => mat (z : GL (Fin 3) F)) (hQc x hxQ y hyQ)
    simpa [mat, hX, hY] using this
  have hνμc : ν * μ = μ * ν := by
    simp only [hν, hμ, sub_mul, mul_sub, hXY, one_mul, mul_one]
    abel
  have hXν : X = 1 + ν := by rw [hν]; abel
  have hYμ : Y = 1 + μ := by rw [hμ]; abel
  have hxyν : mat (((x * y : ↥(SU F)) : GL (Fin 3) F)) - 1 = ν + μ + ν * μ := by
    have : mat (((x * y : ↥(SU F)) : GL (Fin 3) F)) = X * Y := rfl
    rw [this, hXν, hYμ]
    noncomm_ring
  have hxy2 := hcon (x * y) (Q.mul_mem hxQ hyQ)
  rw [hxyν, pow_two, sq_sum_commute ν μ hνμc hν2 hμ2] at hxy2
  have hνμ : ν * μ = 0 := by
    rcases smul_eq_zero.mp hxy2 with h | h
    · exact absurd h (two_ne_zero_of_charP hF)
    · exact h
  have hν0 : ν ≠ 0 := by
    intro h
    apply hx1
    have : X = 1 := by rw [hXν, h, add_zero]
    exact Subtype.ext (Units.ext this)
  obtain ⟨c, hc⟩ := pair_proportional σ (frob_frob hF) ν μ hν2 hμ2 hνμ hadjν hadjμ hν0
  have hσc : σ c = c := by
    have h1 : adj σ μ = -μ := hadjμ
    rw [hc, adj_smul, hadjν, smul_neg] at h1
    have h2 : (σ c - c) • ν = 0 := by
      rw [sub_smul]
      have := neg_inj.mp h1
      rw [this, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hν0
  have hc3 : c * (c - 1) * (c + 1) = 0 := by
    have : c ^ 3 = c := by rw [← frob_apply hF]; exact hσc
    linear_combination this
  apply hyx
  rcases mul_eq_zero.mp hc3 with h | h
  · rcases mul_eq_zero.mp h with h0 | h1
    ·
      have : Y = 1 := by rw [hYμ, hc, h0, zero_smul, add_zero]
      have hy1 : y = 1 := Subtype.ext (Units.ext this)
      rw [hy1]; exact Subgroup.one_mem _
    ·
      have hc1 : c = 1 := sub_eq_zero.mp h1
      have : Y = X := by rw [hYμ, hXν, hc, hc1, one_smul]
      have hyx' : y = x := Subtype.ext (Units.ext this)
      rw [hyx']; exact Subgroup.mem_zpowers x
  ·
    have hc1 : c = -1 := eq_neg_of_add_eq_zero_left h
    have h3 : (3 : F) = 0 := by
      have := CharP.cast_eq_zero F 3
      simpa using this
    have : Y = mat (((x ^ 2 : ↥(SU F)) : GL (Fin 3) F)) := by
      have e : mat (((x ^ 2 : ↥(SU F)) : GL (Fin 3) F)) = X * X := by simp [mat, hX, pow_two]
      rw [e, hXν, hYμ, hc, hc1]
      have : (1 + ν) * (1 + ν) = 1 + (2 : F) • ν := by
        have : (1 + ν) * (1 + ν) = 1 + ν + ν + ν * ν := by noncomm_ring
        rw [this, hν2, add_zero, add_assoc, ← two_smul F ν]
      rw [this]
      have h2 : (2 : F) = -1 := by linear_combination h3
      rw [h2, neg_smul, one_smul, ← sub_eq_add_neg]
    have hy2 : y = x ^ 2 := Subtype.ext (Units.ext this)
    rw [hy2]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) 2 |> fun h => by simpa using h

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.U33
