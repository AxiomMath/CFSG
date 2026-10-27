module

public import CFSG.ClassicalInvolution.Q3.Q3AMBadPsp

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Axis


variable {G : Type} [Group G] {K₁ K₂ K₃ : Subgroup G} {z₁ z₂ t₁ t₂ t₃ : G}
  {R₁ R₂ R₃ : Subgroup G}

theorem BadAxis.exists_noncomm_involutions [Finite G]
    (h : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ R₁ R₂ R₃) (hK₂ : IsClassicalMember3 K₂ z₂) :
    ∃ a b : G, a ∈ Subgroup.centralizer ({z₁} : Set G) ∧
      b ∈ Subgroup.centralizer ({z₁} : Set G) ∧ orderOf a = 2 ∧ orderOf b = 2 ∧
        a * b ≠ b * a := by
  obtain ⟨x, hx, y, hy, hxx, hyy, hxy⟩ :=
    exists_quaternion_pair_of_isSylow2In hK₂ h.syl₂ h.z_mem₂
  have hz₂ : z₂ ≠ 1 := h.uniq₂.ne_one
  have hnc : x * y ≠ y * x := by
    intro heq
    apply hz₂
    rw [← hxy, heq]
    group
  have hAx : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ x t₃ R₁ R₂ R₃ :=
    { h with mem₂ := hx, sq₂ := hxx, noncomm₂ := ⟨y, hy, hnc⟩ }
  have hAy : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ y t₃ R₁ R₂ R₃ :=
    { h with mem₂ := hy, sq₂ := hyy, noncomm₂ := ⟨x, hx, fun e => hnc e.symm⟩ }
  have hinv : ∀ {s : G}, s * s = 1 → s ∉ Subgroup.closure ({z₁, z₂} : Set G) →
      orderOf s = 2 := fun {s} hs hs' =>
    orderOf_eq_prime (by rw [pow_two]; exact hs) (fun h1 => hs' (h1 ▸ Subgroup.one_mem _))
  refine ⟨t₁ * x * t₃, t₁ * y * t₃,
    Subgroup.mem_centralizer_singleton_iff.mpr hAx.s_comm₁.symm.eq,
    Subgroup.mem_centralizer_singleton_iff.mpr hAy.s_comm₁.symm.eq,
    hinv hAx.s_mul_self hAx.s_not_mem_pair, hinv hAy.s_mul_self hAy.s_not_mem_pair, ?_⟩
  intro hc
  have c12 : ∀ v ∈ R₂, t₁ * v = v * t₁ := fun v hv => h.comm₁₂ t₁ h.mem₁ v hv
  have c23 : ∀ v ∈ R₂, v * t₃ = t₃ * v := fun v hv => h.comm₂₃ v hv t₃ h.mem₃
  have e1 : t₁ * x * t₃ * (t₁ * y * t₃) = (t₁ * t₃) * (t₁ * t₃) * (x * y) := by
    calc t₁ * x * t₃ * (t₁ * y * t₃) = t₁ * (x * t₃) * t₁ * y * t₃ := by group
      _ = t₁ * t₃ * (x * t₁) * y * t₃ := by rw [c23 x hx]; group
      _ = t₁ * t₃ * t₁ * x * (y * t₃) := by rw [← c12 x hx]; group
      _ = t₁ * t₃ * t₁ * (x * t₃) * y := by rw [c23 y hy]; group
      _ = (t₁ * t₃) * (t₁ * t₃) * (x * y) := by rw [c23 x hx]; group
  have e2 : t₁ * y * t₃ * (t₁ * x * t₃) = (t₁ * t₃) * (t₁ * t₃) * (y * x) := by
    calc t₁ * y * t₃ * (t₁ * x * t₃) = t₁ * (y * t₃) * t₁ * x * t₃ := by group
      _ = t₁ * t₃ * (y * t₁) * x * t₃ := by rw [c23 y hy]; group
      _ = t₁ * t₃ * t₁ * y * (x * t₃) := by rw [← c12 y hy]; group
      _ = t₁ * t₃ * t₁ * (y * t₃) * x := by rw [c23 x hx]; group
      _ = (t₁ * t₃) * (t₁ * t₃) * (y * x) := by rw [c23 y hy]; group
  rw [e1, e2] at hc
  exact hnc (mul_left_cancel hc)

theorem BadAxis.eq_of_orderOf_eq_two₁ (h : BadAxis K₁ K₂ K₃ z₁ z₂ t₁ t₂ t₃ R₁ R₂ R₃) :
    ∀ x ∈ R₁, ∀ y ∈ R₁, orderOf x = 2 → orderOf y = 2 → x = y := by
  have key : ∀ {w : G}, w ∈ R₁ → orderOf w = 2 → w = z₁ := by
    intro w hw hw2
    have hsq : w * w = 1 := by
      rw [← pow_two]
      exact hw2 ▸ pow_orderOf_eq_one w
    rcases h.uniq₁.unique w (h.syl₁.1 hw) hsq with h1 | h1
    · rw [h1, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    · exact h1
  intro x hx y hy hx2 hy2
  exact (key hx hx2).trans (key hy hy2).symm

end Axis

section Sylow

variable {Y : Type} [Group Y] [Finite Y] {L R : Subgroup Y} {z : Y}

theorem eight_le_card_of_classical3 (hz : IsClassicalMember3 L z)
    (hR : IsSylow2In R L) : 8 ≤ Nat.card R := by
  obtain ⟨e⟩ := hz.nonempty_equiv
  have hK : Nat.card L = 24 * Nat.card (classicalInvolutionOddCore L) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (classicalInvolutionOddCore L),
      Nat.card_congr e.toEquiv, natCard_sl2Three]
  have hodd : Odd (Nat.card (classicalInvolutionOddCore L)) :=
    CFSG.ComponentClassification.OddCore.odd_card L
  have h2 : ¬ 2 ∣ Nat.card (classicalInvolutionOddCore L) := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [Asc77.natCard_eq_pow_of_isSylow2In hR, hK,
    Nat.factorization_mul (by norm_num) Nat.card_pos.ne', Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd h2]
  have : (24 : ℕ).factorization 2 = 3 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization Nat.prime_three]
    simp
  rw [this]
  norm_num

end Sylow

section Setting


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J K' : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}

theorem PspSetting.exists_noncomm_involutions [IsSimpleGroup G]
    (hset : PspSetting Ω K J S R T W z t K') {t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}
    (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) :
    ∃ a b : G, a ∈ Subgroup.centralizer ({z} : Set G) ∧
      b ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf a = 2 ∧ orderOf b = 2 ∧
        a * b ≠ b * a :=
  hax.exists_noncomm_involutions (Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution
    hset.bad.std.stand.modU hset.bad.std.hJ.1 hset.bad.std.ht)

theorem PspSetting.goldschmidt_inputs [IsSimpleGroup G]
    (hset : PspSetting Ω K J S R T W z t K') {t₁ t₂ t₃ : G} {R₁ R₂ R₃ : Subgroup G}
    (hax : BadAxis K J K' z t t₁ t₂ t₃ R₁ R₂ R₃) :
    (∃ a b : G, a * b ≠ b * a) ∧ orderOf z = 2 ∧ IsPGroup 2 R₁ ∧ 8 ≤ Nat.card R₁ ∧
      (∀ x ∈ R₁, ∀ y ∈ R₁, orderOf x = 2 → orderOf y = 2 → x = y) ∧ 3 ≤ twoRank G := by
  refine ⟨hset.bad.nonabelian, ?_, hax.syl₁.2.1, ?_, hax.eq_of_orderOf_eq_two₁,
    hset.bad.std.stand.rank⟩
  · exact orderOf_eq_prime (by rw [pow_two]; exact hset.bad.std.hz.sq)
      hset.bad.std.hz.ne_one
  · exact eight_le_card_of_classical3 (Q3T8.Asc77.isClassicalMember3_of_uniqueInvolution
      hset.bad.std.stand.modU hset.bad.std.stand.mem hset.bad.std.hz) hax.syl₁

end Setting

end CFSG.ClassicalInvolution.Q3.Q3AM
