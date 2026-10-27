module

public import CFSG.CGT.Timmesfeld75.Sec63Basic
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

section Count

variable {G : Type} [Group G] {T T₁ T₃ : Subgroup G} {n m : ℕ} {x : G}

theorem card_mul_le_of_inf_eq_bot [Finite G] {P Q R : Subgroup G} (hP : P ≤ R) (hQ : Q ≤ R)
    (hPQ : P ⊓ Q = ⊥) : Nat.card P * Nat.card Q ≤ Nat.card R := by
  let φ : P × Q → R := fun p => ⟨(p.1 : G) * p.2, R.mul_mem (hP p.1.2) (hQ p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    have h1 : (p : G) * q = p' * q' := congrArg Subtype.val h
    have h2 : (p' : G)⁻¹ * p = q' * (q : G)⁻¹ := by
      calc (p' : G)⁻¹ * p = (p' : G)⁻¹ * (p * q) * (q : G)⁻¹ := by group
        _ = q' * (q : G)⁻¹ := by rw [h1]; group
    have hmem : (p' : G)⁻¹ * p ∈ P ⊓ Q :=
      ⟨P.mul_mem (P.inv_mem p'.2) p.2, by rw [h2]; exact Q.mul_mem q'.2 (Q.inv_mem q.2)⟩
    rw [hPQ, Subgroup.mem_bot] at hmem
    have hp : p' = p := Subtype.ext (inv_mul_eq_one.1 hmem)
    have hq : q' = q := Subtype.ext (mul_inv_eq_one.1 (h2 ▸ hmem))
    rw [hp, hq]
  rw [← Nat.card_prod]
  exact Nat.card_le_card_of_injective φ hinj

theorem Sec63Cfg.sec3Iso (c : Sec63Cfg T T₁ n m x T₃) : Sec3Iso T T₃ := by
  have := c.ctx.finite
  obtain ⟨g, hg⟩ := c.conj
  have hne : conjSubgroup g T ≠ T := hg ▸ c.ne_left
  have hbot : normIn T (conjSubgroup g T) ≠ ⊥ := hg ▸ c.normIn_ne_bot
  exact hg ▸ c.ctx.hI g hne hbot

theorem Sec63Cfg.card_le_sq (c : Sec63Cfg T T₁ n m x T₃) :
    Nat.card T ≤ Nat.card ↥(normIn T T₃) ^ 2 := by
  have := c.ctx.finite
  obtain ⟨hN, f, hf, hiso⟩ := c.sec3Iso
  have hS := c.sec3
  have hpair := hS.isL2Pair_quotient hf hiso
  have h1 := hS.card_eq_mul hf hiso
  have hM : 2 ^ (2 * f) ≤ Nat.card ↥(cfgM T T₃) := by
    refine Sec3.two_pow_le_card_of_normal hS rfl rfl (Nat.pos_of_ne_zero hf) hpair le_rfl
      (fun z hz n hn => hS.cfg.conj_mem_cfgM hz hn) ?_
    intro h0
    exact c.normIn_ne_bot (le_bot_iff.1 ((Cfg.normIn_le_cfgM_left T T₃).trans h0.le))
  rw [hS.card_cfgM_eq_sq, pow_mul'] at hM
  have h2 : 2 ^ f ≤ Nat.card ↥(normIn T T₃) := by
    by_contra hlt
    push Not at hlt
    have := Nat.pow_lt_pow_left hlt (two_ne_zero : (2 : ℕ) ≠ 0)
    omega
  have h3 : 0 < Nat.card ↥(normIn T T₃) := Nat.card_pos
  rw [h1, pow_two]
  exact Nat.mul_le_mul_left _ h2

theorem Sec63Cfg.card_lt_mul (c : Sec63Cfg T T₁ n m x T₃) :
    Nat.card T < Nat.card ↥(normIn T T₁) * Nat.card ↥(normIn T₃ T) := by
  have := c.ctx.finite
  have h1 := c.card_le_sq
  have h2 := c.card_normIn_lt
  have h3 : Nat.card ↥(normIn T₃ T) = Nat.card ↥(normIn T T₃) := c.sec3.card_normIn_swap
  have h4 : 0 < Nat.card ↥(normIn T T₃) := Nat.card_pos
  rw [h3] at h2 ⊢
  nlinarith

theorem Sec63Cfg.inf_ne_bot (c : Sec63Cfg T T₁ n m x T₃) :
    normIn T T₁ ⊓ normIn T T₃ ≠ ⊥ := by
  have := c.ctx.finite
  intro hbot
  have h1 := card_mul_le_of_inf_eq_bot (normIn_le T T₁) (normIn_le T T₃) hbot
  have h2 := c.card_lt_mul
  have h3 : Nat.card ↥(normIn T₃ T) = Nat.card ↥(normIn T T₃) := c.sec3.card_normIn_swap
  rw [h3] at h2
  omega

theorem Sec63Cfg.exists_comm (c : Sec63Cfg T T₁ n m x T₃) {y : G} (hy : y ∈ normIn T₁ T)
    (hy1 : y ≠ 1) (hs : ∀ a ∈ normIn T₃ T, ∃ s ∈ T, a * y * a⁻¹ = s⁻¹ * y * s) :
    ∃ a ∈ normIn T₃ T, a ≠ 1 ∧ a * y = y * a := by
  have := c.ctx.finite
  by_contra hcon
  push Not at hcon
  choose! s hsT hsa using hs
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  have hCT : Nat.card ↥(T ⊓ C) = Nat.card ↥(normIn T T₁) := by
    rw [hC, c.ctx.sec3.cfg.inf_centralizer_eq_normIn hy hy1]
  have hu : ∀ a ∈ normIn T₃ T, s a * a ∈ C := by
    intro a ha
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    have := hsa a ha
    calc s a * a * y = s a * (a * y * a⁻¹) * a := by group
      _ = s a * ((s a)⁻¹ * y * s a) * a := by rw [this]
      _ = y * (s a * a) := by group
  let f : normIn T₃ T → ↥T ⧸ (T ⊓ C).subgroupOf T := fun a =>
    QuotientGroup.mk ⟨(s a)⁻¹, T.inv_mem (hsT a a.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := QuotientGroup.eq.1 hab
    have h2 : s a * (s b)⁻¹ ∈ T ⊓ C := by
      have := Subgroup.mem_subgroupOf.1 h1
      simpa using this
    have h3 : (a : G)⁻¹ * b ∈ C := by
      have e : (a : G)⁻¹ * b = (s a * a)⁻¹ * (s a * (s b)⁻¹) * (s b * b) := by group
      rw [e]
      exact C.mul_mem (C.mul_mem (C.inv_mem (hu a a.2)) h2.2) (hu b b.2)
    by_contra hne
    have hab' : (a : G)⁻¹ * b ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.1 h))
    exact hcon _ ((normIn T₃ T).mul_mem ((normIn T₃ T).inv_mem a.2) b.2) hab'
      (Subgroup.mem_centralizer_singleton_iff.1 h3)
  have h1 := Nat.card_le_card_of_injective f hinj
  have h2 := Subgroup.card_mul_index ((T ⊓ C).subgroupOf T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : T ⊓ C ≤ T)).toEquiv,
    hCT] at h2
  have h3 : Nat.card ↥(normIn T₃ T) ≤ ((T ⊓ C).subgroupOf T).index := h1
  have h4 := c.card_lt_mul
  have h5 := Nat.mul_le_mul_left (Nat.card ↥(normIn T T₁)) h3
  omega

end Count

end CFSG.CGT.Timmesfeld75
