module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwKlein
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwCodesB
public import Certificates.Certificate33201

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four

theorem pow_e_of_swap {x : WrE} (hx : x.e = true) (n : ℕ) : (x ^ n).e = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, mul_e, ih, hx]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.add_mod]

theorem four_le_orderOf {h : WrE} (he : h.e = true) (h13 : h * h ≠ 1) : 4 ≤ orderOf h := by
  have hpos : 0 < orderOf h := orderOf_pos h
  have hpow : h ^ orderOf h = 1 := pow_orderOf_eq_one h
  have hevn : orderOf h % 2 = 0 := by
    have := pow_e_of_swap he (orderOf h)
    rw [hpow] at this
    have h1 : (1 : WrE).e = false := rfl
    rw [h1] at this
    rcases Nat.mod_two_eq_zero_or_one (orderOf h) with h2 | h2
    · exact h2
    · simp [h2] at this
  have hne2 : orderOf h ≠ 2 := fun h2 => h13 (by rw [← pow_two, ← h2]; exact hpow)
  omega

theorem sq_g5 : g₅ * g₅ = 1 := PSL3Four.g₅_mul_g₅

theorem sq_g6 : g₆ * g₆ = 1 := PSL3Four.g₆_mul_g₆

theorem sq_conj (a b : Equiv.Perm (Fin 42)) (ha : a * a = 1) (hb : b * b = 1) :
    (a * b * a) * (a * b * a) = 1 := by
  calc (a * b * a) * (a * b * a) = a * b * (a * a) * b * a := by group
    _ = a * (b * b) * a := by rw [ha]; group
    _ = 1 := by rw [hb, mul_one, ha]

theorem swap_sq (x y : Equiv.Perm (Fin 42)) :
    (⟨x, y, true⟩ : WrE) * ⟨x, y, true⟩ = ⟨y * x, x * y, false⟩ := rfl

theorem pow_four_swap (x y : Equiv.Perm (Fin 42)) (h₁ : (y * x) * (y * x) = 1)
    (h₂ : (x * y) * (x * y) = 1) : (⟨x, y, true⟩ : WrE) ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, swap_sq, mk_mul_mk, h₁, h₂]
  rfl

private theorem g5_mem : g₅ ∈ RA := g₅_mem_RA

private theorem g6_mem : g₆ ∈ RA := g₆_mem_RA

private theorem g56_mem : g₅ * g₆ ∈ RA := RA.mul_mem g₅_mem_RA g₆_mem_RA

private theorem pair_aux : ∀ c₁ c₂ : Fin 4, (cosXor c₁ c₂ = 1 ∨ cosXor c₁ c₂ = 2) →
    (c₁ = 0 ∧ c₂ = 1) ∨ (c₁ = 0 ∧ c₂ = 2) ∨ (c₁ = 1 ∧ c₂ = 0) ∨ (c₁ = 1 ∧ c₂ = 3) ∨
      (c₁ = 2 ∧ c₂ = 0) ∨ (c₁ = 2 ∧ c₂ = 3) ∨ (c₁ = 3 ∧ c₂ = 1) ∨ (c₁ = 3 ∧ c₂ = 2) := by
  decide


theorem exists_order_four (c₁ c₂ : Fin 4) (hδ : cosXor c₁ c₂ = 1 ∨ cosXor c₁ c₂ = 2) :
    ∃ p : WrE, p ∈ Pw ∧ cc p = (c₁, c₂, true) ∧ p ^ 4 = 1 := by
  have e5 : g₅ * (g₅ * g₆) = g₆ := by rw [← mul_assoc, sq_g5, one_mul]
  have e6 : g₆ * (g₅ * g₆) = g₆ * g₅ * g₆ := by rw [mul_assoc]
  have e5' : g₅ * g₆ * g₆ = g₅ := by rw [mul_assoc, sq_g6, mul_one]
  have c1 : cosRA 1 = 0 := cosRA_one
  rcases pair_aux c₁ c₂ hδ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨⟨1, g₅, true⟩, ⟨RA.one_mem, g5_mem⟩, by
      show (cosRA 1, cosRA g₅, true) = _
      rw [cosRA_one, cosRA_g5],
      pow_four_swap _ _ (by rw [mul_one, sq_g5]) (by rw [one_mul, sq_g5])⟩
  · exact ⟨⟨1, g₆, true⟩, ⟨RA.one_mem, g6_mem⟩, by
      show (cosRA 1, cosRA g₆, true) = _
      rw [cosRA_one, cosRA_g6],
      pow_four_swap _ _ (by rw [mul_one, sq_g6]) (by rw [one_mul, sq_g6])⟩
  · exact ⟨⟨g₅, 1, true⟩, ⟨g5_mem, RA.one_mem⟩, by
      show (cosRA g₅, cosRA 1, true) = _
      rw [cosRA_one, cosRA_g5],
      pow_four_swap _ _ (by rw [one_mul, sq_g5]) (by rw [mul_one, sq_g5])⟩
  · exact ⟨⟨g₅, g₅ * g₆, true⟩, ⟨g5_mem, g56_mem⟩, by
      show (cosRA g₅, cosRA (g₅ * g₆), true) = _
      rw [cosRA_g56, cosRA_g5],
      pow_four_swap _ _ (sq_conj g₅ g₆ sq_g5 sq_g6) (by rw [e5, sq_g6])⟩
  · exact ⟨⟨g₆, 1, true⟩, ⟨g6_mem, RA.one_mem⟩, by
      show (cosRA g₆, cosRA 1, true) = _
      rw [cosRA_one, cosRA_g6],
      pow_four_swap _ _ (by rw [one_mul, sq_g6]) (by rw [mul_one, sq_g6])⟩
  · exact ⟨⟨g₆, g₅ * g₆, true⟩, ⟨g6_mem, g56_mem⟩, by
      show (cosRA g₆, cosRA (g₅ * g₆), true) = _
      rw [cosRA_g56, cosRA_g6],
      pow_four_swap _ _ (by rw [e5', sq_g5]) (by rw [e6]; exact sq_conj g₆ g₅ sq_g6 sq_g5)⟩
  · exact ⟨⟨g₅ * g₆, g₅, true⟩, ⟨g56_mem, g5_mem⟩, by
      show (cosRA (g₅ * g₆), cosRA g₅, true) = _
      rw [cosRA_g56, cosRA_g5],
      pow_four_swap _ _ (by rw [e5, sq_g6]) (sq_conj g₅ g₆ sq_g5 sq_g6)⟩
  · exact ⟨⟨g₅ * g₆, g₆, true⟩, ⟨g56_mem, g6_mem⟩, by
      show (cosRA (g₅ * g₆), cosRA g₆, true) = _
      rw [cosRA_g56, cosRA_g6],
      pow_four_swap _ _ (by rw [e6]; exact sq_conj g₆ g₅ sq_g6 sq_g5) (by rw [e5', sq_g5])⟩


theorem klein_of_inv {s : Equiv.Perm (Fin 42)} (hs : s ∈ RA) (hs2 : s * s = 1)
    (hc : cosRA s = 1 ∨ cosRA s = 2) :
    ∃ e₁ e₂ : Equiv.Perm (Fin 42), e₁ ∈ L34Facts.T0 ∧ e₂ ∈ L34Facts.T0 ∧ e₁ * e₁ = 1 ∧
      e₂ * e₂ = 1 ∧ e₁ ≠ 1 ∧ e₂ ≠ 1 ∧ e₂ ≠ e₁ ∧ e₁ * e₂ = e₂ * e₁ ∧ e₁ * s = s * e₁ ∧
        e₂ * s = s * e₂ :=
  Certificates.certificate33201 s hs hs2 hc

theorem no_delta_one_two {X : Subgroup WrE} (hXP : X ≤ Pw) (hN : N0w ≤ X) (hX : GoodX X)
    {x : WrE} (hx : x ∈ X) (hxe : x.e = true)
    (hδ : cosXor (cosRA x.a) (cosRA x.b) = 1 ∨ cosXor (cosRA x.a) (cosRA x.b) = 2) : False := by
  have hcc : cc x = (cosRA x.a, cosRA x.b, true) := by
    show (cosRA x.a, cosRA x.b, x.e) = _
    rw [hxe]
  obtain ⟨p, hpP, hpc, hp4⟩ := exists_order_four _ _ hδ
  have hpX : p ∈ X := mem_of_cc_eq hN hpP hx (hXP hx) (hpc.trans hcc.symm)
  have hpe : p.e = true := congrArg (fun c => c.2.2) hpc
  have hmin : ∀ h ∈ X, h.e = true → orderOf p ≤ orderOf h := fun h hh he =>
    (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hp4)).trans
      (four_le_orderOf he (hX.h13 h hh he))
  obtain ⟨s, s', e, hpp⟩ : ∃ (s s' : Equiv.Perm (Fin 42)) (e : Bool), p * p = ⟨s, s', e⟩ :=
    ⟨(p * p).a, (p * p).b, (p * p).e, rfl⟩
  have he : e = false := by
    have := mul_e p p
    rw [hpp, hpe] at this
    exact this
  subst he
  have h44 : p ^ 4 = (p * p) * (p * p) := by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two]
  have hq2 : (⟨s, s', false⟩ : WrE) * ⟨s, s', false⟩ = 1 := by rw [← hpp, ← h44]; exact hp4
  have hs2 : s * s = 1 := by
    have := congrArg WrE.a hq2
    exact this
  have hs2' : s' * s' = 1 := by
    have := congrArg WrE.b hq2
    exact this
  have hppP : (⟨s, s', false⟩ : WrE) ∈ Pw := hpp ▸ Pw.mul_mem hpP hpP
  have hcpp : cc (⟨s, s', false⟩ : WrE) = (cosXor (cosRA x.b) (cosRA x.a),
      cosXor (cosRA x.a) (cosRA x.b), false) := by
    rw [← hpp, cc_mul hpP hpP, hpc, qmulC_sw_sw]
  have hcs : cosRA s = cosXor (cosRA x.a) (cosRA x.b) := by
    have := congrArg (fun c => c.1) hcpp
    simp only [cc] at this
    rw [this, cosXor_comm]
  have hcs' : cosRA s' = cosXor (cosRA x.a) (cosRA x.b) := by
    have := congrArg (fun c => c.2.1) hcpp
    simpa only [cc] using this
  obtain ⟨e₁, e₂, he₁, he₂, he₁2, he₂2, he₁1, he₂1, he₂₁, hee, hes₁, hes₂⟩ :=
    klein_of_inv hppP.1 hs2 (hcs ▸ hδ)
  obtain ⟨f₁, f₂, hf₁, hf₂, hf₁2, hf₂2, hf₁1, hf₂1, hf₂₁, hff, hfs₁, hfs₂⟩ :=
    klein_of_inv hppP.2 hs2' (hcs' ▸ hδ)
  obtain ⟨F, hF, hF8, w, hw, hw2, hwF, hwn⟩ := klein_violation hN hpp he₁ he₂ hf₁ hf₂ he₁2 he₂2
    hf₁2 hf₂2 he₁1 he₂1 he₂₁.symm hf₁1 hf₂1 hf₂₁ hee hff hes₁ hes₂ hfs₁ hfs₂
  exact hX.h22 p hpX hpe hmin ⟨F, hF, hF8, w, hw, hw2, hwF, hwn⟩

theorem swap_isC4 {X : Subgroup WrE} (hXP : X ≤ Pw) (hN : N0w ≤ X) (hX : GoodX X) :
    ∀ x ∈ X, x.e = true → IsC4 (cc x) := by
  intro x hx hxe
  have hcc : cc x = (cosRA x.a, cosRA x.b, true) := by
    show (cosRA x.a, cosRA x.b, x.e) = _
    rw [hxe]
  refine ⟨hxe, ?_⟩
  show cosXor (cosRA x.a) (cosRA x.b) = 3
  by_contra hne
  rcases (by decide : ∀ d : Fin 4, d ≠ 3 → d = 0 ∨ d = 1 ∨ d = 2)
    (cosXor (cosRA x.a) (cosRA x.b)) hne with h0 | h1 | h2
  · have hxxP : x * x ∈ Pw := Pw.mul_mem (hXP hx) (hXP hx)
    have h' : cc (x * x) = (0, 0, false) := by
      rw [cc_mul (hXP hx) (hXP hx), hcc, qmulC_sw_sw, cosXor_comm (cosRA x.b), h0]
    have hN0 : x * x ∈ N0w := (mem_N0w_iff_cc hxxP).2 h'
    exact hX.h20 x hx hxe (L34Facts.T0_le_S (mem_N0w_iff.1 hN0).2.1)
  · exact no_delta_one_two hXP hN hX hx hxe (Or.inl h1)
  · exact no_delta_one_two hXP hN hX hx hxe (Or.inr h2)

end CFSG.ComponentClassification.GrSLit.L34Tw
