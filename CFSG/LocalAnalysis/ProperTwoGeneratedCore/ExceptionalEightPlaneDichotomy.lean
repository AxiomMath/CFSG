module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneAbelian

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

open scoped Pointwise

variable {Y : Type*} [Group Y]

theorem mul_mul_self_of_commute {x y : Y} (hxy : x * y = y * x) :
    x * y * (x * y) = x * x * (y * y) := by
  calc x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (x * y) * y := by rw [hxy]
    _ = x * x * (y * y) := by group

theorem card_sup_of_le_normalizer_of_inf_eq_bot [Finite Y] (N K : Subgroup Y)
    (hK : K ≤ Subgroup.normalizer (N : Set Y)) (h : N ⊓ K = ⊥) :
    Nat.card (N ⊔ K : Subgroup Y) = Nat.card N * Nat.card K := by
  set H := N ⊔ K with hH
  have hNH : N ≤ H := le_sup_left
  have hKH : K ≤ H := le_sup_right
  have hcompl : (N.subgroupOf H).IsComplement' (K.subgroupOf H) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxN hxK
      have : (x : Y) ∈ N ⊓ K := ⟨hxN, hxK⟩
      rw [h, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · ext x
      simp only [Set.mem_univ, iff_true]
      have hx : (x : Y) ∈ ((N ⊔ K : Subgroup Y) : Set Y) := x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left N K hK] at hx
      obtain ⟨n, hn, k, hk, hnk⟩ := Set.mem_mul.mp hx
      refine Set.mem_mul.mpr ⟨⟨n, hNH hn⟩, hn, ⟨k, hKH hk⟩, hk, Subtype.ext ?_⟩
      simpa using hnk
  rw [← hcompl.card_mul_card, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]

theorem mem_zpowers_of_orderOf_eq_two {g x : Y} (hg : orderOf g = 2)
    (hx : x ∈ Subgroup.zpowers g) : x = 1 ∨ x = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hmod := zpow_mod_orderOf g k
  rw [hg] at hmod
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · left
    rw [← hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_zero]
  · right
    rw [← hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, hk, zpow_one]

namespace PlaneHyp

variable {U B : Subgroup Y} {b₁ b₂ u₀ c₁ c₂ : Y} [U.Normal] [IsElementaryAbelian 2 U]
  (h : PlaneHyp U B b₁ b₂ u₀) (hl : PlaneLifts B b₁ b₂ u₀ c₁ c₂)
include h hl

theorem sq_eq_of_tau_eq {x d : Y} (hx : x ∈ planeD B c₁ c₂) (hd : d ∈ planeD B c₁ c₂)
    (hτ : planeTau u₀ x = planeTau u₀ d) : x * x = d * d := by
  have hdC := planeD_le_centralizer B c₁ c₂ hd
  have hxC := planeD_le_centralizer B c₁ c₂ hx
  have heD : d⁻¹ * x ∈ planeD B c₁ c₂ := Subgroup.mul_mem _ (Subgroup.inv_mem _ hd) hx
  have hτ1 : planeTau u₀ (1 : Y) = 1 := h.planeTau_of_mem_U U.one_mem
  have heB : d⁻¹ * x ∈ B := by
    refine h.mem_B_of_mem_planeD hl heD ?_
    have h1 := h.planeTau_mul (Subgroup.inv_mem _ hdC) hdC
    rw [inv_mul_cancel, hτ1] at h1
    rw [h.planeTau_mul (Subgroup.inv_mem _ hdC) hxC, hτ]
    exact h1.symm
  have hx' : x = d * (d⁻¹ * x) := by group
  rw [hx', mul_mul_self_of_commute (h.planeD_comm hl hd heD),
    mul_self_eq_one_of_mem (h.le heB), mul_one]

theorem sq_dichotomy [Finite Y] :
    (∀ d ∈ planeD B c₁ c₂, d * d = 1) ∨ (∀ d ∈ planeD B c₁ c₂, d * d = planeTau u₀ d) := by
  classical
  have _ := h.isKleinFour_B
  have hb₁U := h.b₁_mem_U
  have hb₂U := h.b₂_mem_U
  let β₁ : B := ⟨b₁, h.b₁_mem⟩
  let β₂ : B := ⟨b₂, h.b₂_mem⟩
  let β₃ : B := ⟨b₁ * b₂, B.mul_mem h.b₁_mem h.b₂_mem⟩
  have hb₁₂ : b₁ * b₂ ≠ b₁ := fun e => h.b₂_ne_one (left_eq_mul.mp e.symm)
  have hb₁₂' : b₁ * b₂ ≠ b₂ := fun e => h.b₁_ne_one (left_eq_mul.mp
    ((mul_comm_of_mem hb₁U hb₂U).symm.trans e).symm)
  have hb₁₂1 : b₁ * b₂ ≠ 1 := by
    intro e
    apply h.b₂_ne_b₁
    have := eq_inv_of_mul_eq_one_right e
    rwa [inv_eq_self_of_mem hb₁U] at this
  have n12 : (1 : B) ≠ β₂ := fun e => h.b₂_ne_one (congrArg Subtype.val e).symm
  have n13 : (1 : B) ≠ β₃ := fun e => hb₁₂1 (congrArg Subtype.val e).symm
  have n11 : (1 : B) ≠ β₁ := fun e => h.b₁_ne_one (congrArg Subtype.val e).symm
  have n23 : β₁ ≠ β₂ := fun e => h.b₂_ne_b₁ (congrArg Subtype.val e).symm
  have n123 : β₁ ≠ β₃ := fun e => hb₁₂ (congrArg Subtype.val e).symm
  let α₁ : MulAut B :=
    IsKleinFour.mulEquiv (Equiv.swap β₂ β₃) (Equiv.swap_apply_of_ne_of_ne n12 n13)
  let α₂ : MulAut B :=
    IsKleinFour.mulEquiv (Equiv.swap β₁ β₂) (Equiv.swap_apply_of_ne_of_ne n11 n12)
  have hα₁β₁ : α₁ β₁ = β₁ := Equiv.swap_apply_of_ne_of_ne n23 n123
  have hα₁β₂ : α₁ β₂ = β₃ := Equiv.swap_apply_left β₂ β₃
  have hα₁β₃ : α₁ β₃ = β₂ := Equiv.swap_apply_right β₂ β₃
  have hα₂β₁ : α₂ β₁ = β₂ := Equiv.swap_apply_left β₁ β₂
  obtain ⟨n₁, hn₁, hα₁⟩ := h.exists_normalizer_of_mulAut α₁
  obtain ⟨n₂, hn₂, hα₂⟩ := h.exists_normalizer_of_mulAut α₂
  have hc₁D := c₁_mem_planeD hl
  have hc₂D := c₂_mem_planeD hl
  have hσB : c₁ * c₁ ∈ B := h.mul_self_mem_B hl.c₁_mem
  have hτn₁ : planeTau u₀ (n₁ * c₁ * n₁⁻¹) = planeTau u₀ c₁ := by
    rw [h.planeTau_conj hn₁ hl.c₁_mem, hl.tau₁]
    have := hα₁ β₁
    rw [hα₁β₁] at this
    exact this.symm
  have hσ₁ : n₁ * (c₁ * c₁) * n₁⁻¹ = c₁ * c₁ := by
    have := h.sq_eq_of_tau_eq hl (h.conj_mem_planeD hl hn₁ hc₁D) hc₁D hτn₁
    rwa [show n₁ * c₁ * n₁⁻¹ * (n₁ * c₁ * n₁⁻¹) = n₁ * (c₁ * c₁) * n₁⁻¹ by group] at this
  have hσcases : c₁ * c₁ = 1 ∨ c₁ * c₁ = b₁ := by
    rcases h.mem_B_cases hσB with hσ | hσ | hσ | hσ
    · exact Or.inl hσ
    · exact Or.inr hσ
    · exfalso
      have h1 := hα₁ β₂
      rw [hα₁β₂] at h1
      change b₁ * b₂ = n₁ * b₂ * n₁⁻¹ at h1
      rw [← hσ, hσ₁, hσ] at h1
      exact hb₁₂' h1
    · exfalso
      have h1 := hα₁ β₃
      rw [hα₁β₃] at h1
      change b₂ = n₁ * (b₁ * b₂) * n₁⁻¹ at h1
      rw [← hσ, hσ₁, hσ] at h1
      exact hb₁₂' h1.symm
  have hτn₂ : planeTau u₀ (n₂ * c₁ * n₂⁻¹) = planeTau u₀ c₂ := by
    rw [h.planeTau_conj hn₂ hl.c₁_mem, hl.tau₁, hl.tau₂]
    have := hα₂ β₁
    rw [hα₂β₁] at this
    exact this.symm
  have hσ₂ : n₂ * (c₁ * c₁) * n₂⁻¹ = c₂ * c₂ := by
    have := h.sq_eq_of_tau_eq hl (h.conj_mem_planeD hl hn₂ hc₁D) hc₂D hτn₂
    rwa [show n₂ * c₁ * n₂⁻¹ * (n₂ * c₁ * n₂⁻¹) = n₂ * (c₁ * c₁) * n₂⁻¹ by group] at this
  have hcb : ∀ x ∈ Subgroup.centralizer (B : Set Y), ∀ b ∈ B, x * b = b * x := fun x hx b hb =>
    ((Subgroup.mem_centralizer_iff.mp hx) b hb).symm
  have hτ1 : planeTau u₀ (1 : Y) = 1 := h.planeTau_of_mem_U U.one_mem
  have hτb : ∀ b ∈ B, planeTau u₀ b = 1 := fun b hb => h.planeTau_of_mem_U (h.le hb)
  have hc₁₂C : c₁ * c₂ ∈ Subgroup.centralizer (B : Set Y) := Subgroup.mul_mem _ hl.c₁_mem hl.c₂_mem
  rcases hσcases with hσ | hσ
  · left
    have hc₂sq : c₂ * c₂ = 1 := by rw [← hσ₂, hσ]; group
    intro d hd
    obtain ⟨b, hb, hdd⟩ := h.planeD_decomp hl hd
    have hbb : b * b = 1 := mul_self_eq_one_of_mem (h.le hb)
    rcases hdd with hdd | hdd | hdd | hdd <;> rw [hdd]
    · exact hbb
    · rw [mul_mul_self_of_commute (hcb c₁ hl.c₁_mem b hb), hσ, hbb, one_mul]
    · rw [mul_mul_self_of_commute (hcb c₂ hl.c₂_mem b hb), hc₂sq, hbb, one_mul]
    · rw [mul_mul_self_of_commute (hcb _ hc₁₂C b hb), mul_mul_self_of_commute hl.comm, hσ,
        hc₂sq, hbb, one_mul, one_mul]
  · right
    have hc₂sq : c₂ * c₂ = b₂ := by
      rw [← hσ₂, hσ]
      have := hα₂ β₁
      rw [hα₂β₁] at this
      exact this.symm
    intro d hd
    obtain ⟨b, hb, hdd⟩ := h.planeD_decomp hl hd
    have hbb : b * b = 1 := mul_self_eq_one_of_mem (h.le hb)
    have hbC := le_centralizer_of_le h.le hb
    rcases hdd with hdd | hdd | hdd | hdd <;> rw [hdd]
    · rw [hbb, hτb b hb]
    · rw [mul_mul_self_of_commute (hcb c₁ hl.c₁_mem b hb), hσ, hbb, mul_one,
        h.planeTau_mul hl.c₁_mem hbC, hl.tau₁, hτb b hb, mul_one]
    · rw [mul_mul_self_of_commute (hcb c₂ hl.c₂_mem b hb), hc₂sq, hbb, mul_one,
        h.planeTau_mul hl.c₂_mem hbC, hl.tau₂, hτb b hb, mul_one]
    · rw [mul_mul_self_of_commute (hcb _ hc₁₂C b hb), mul_mul_self_of_commute hl.comm, hσ,
        hc₂sq, hbb, mul_one, h.planeTau_mul hc₁₂C hbC, h.planeTau_mul hl.c₁_mem hl.c₂_mem,
        hl.tau₁, hl.tau₂, hτb b hb, mul_one]

section CaseTwo

variable (hsq : ∀ d ∈ planeD B c₁ c₂, d * d = planeTau u₀ d)
include hsq

theorem mul_self_eq_one_iff_of_sq {d : Y} (hd : d ∈ planeD B c₁ c₂) : d * d = 1 ↔ d ∈ B := by
  rw [hsq d hd]
  constructor
  · intro h1
    exact h.mem_B_of_mem_planeD hl hd h1
  · intro hdB
    exact h.planeTau_of_mem_U (h.le hdB)

omit hl in
theorem u₀_inverts {d : Y} (hd : d ∈ planeD B c₁ c₂) : u₀ * d * u₀⁻¹ = d⁻¹ := by
  have hdC := planeD_le_centralizer B c₁ c₂ hd
  have hc := h.commutator_u₀ hdC
  rw [← hsq d hd] at hc
  have h1 : u₀ * d⁻¹ * u₀⁻¹ = d := by
    have := congrArg (fun z => d⁻¹ * z) hc
    rw [show d⁻¹ * (d * u₀ * d⁻¹ * u₀⁻¹) = u₀ * d⁻¹ * u₀⁻¹ by group,
      show d⁻¹ * (d * d) = d by group] at this
    exact this
  calc u₀ * d * u₀⁻¹ = (u₀ * d⁻¹ * u₀⁻¹)⁻¹ := by group
    _ = d⁻¹ := by rw [h1]

omit [U.Normal] hl hsq in
theorem orderOf_u₀ : orderOf u₀ = 2 := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]; exact mul_self_eq_one_of_mem h.u₀_mem
  · intro h1; exact h.u₀_not_mem (h1 ▸ B.one_mem)

omit hsq in
theorem u₀_not_mem_planeD : u₀ ∉ planeD B c₁ c₂ := by
  intro hu
  apply h.u₀_not_mem
  rw [← h.planeD_inf_U hl]
  exact ⟨hu, h.u₀_mem⟩

omit hsq in
theorem planeD_sup_zpowers : planeD B c₁ c₂ ⊔ Subgroup.zpowers u₀ =
    Subgroup.centralizer (B : Set Y) := by
  apply le_antisymm
  · refine sup_le (planeD_le_centralizer B c₁ c₂) ?_
    rw [Subgroup.zpowers_le]
    exact h.U_le_centralizer h.u₀_mem
  · rw [← h.planeD_sup_U hl]
    refine sup_le le_sup_left ?_
    intro x hx
    rcases h.mem_U_cases hx with hxB | hxB
    · exact Subgroup.mem_sup_left (h.B_le_planeD hl hxB)
    · have hx' : x = u₀ * (u₀ * x) := by
        rw [← mul_assoc, mul_self_eq_one_of_mem h.u₀_mem, one_mul]
      rw [hx', mul_comm_of_mem h.u₀_mem (h.le hxB)]
      exact Subgroup.mul_mem_sup (h.B_le_planeD hl hxB) (Subgroup.mem_zpowers u₀)

omit hsq in
theorem planeD_inf_zpowers : planeD B c₁ c₂ ⊓ Subgroup.zpowers u₀ = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxD, hxZ⟩
  rcases mem_zpowers_of_orderOf_eq_two h.orderOf_u₀ hxZ with rfl | rfl
  · exact Subgroup.one_mem _
  · exact absurd hxD (h.u₀_not_mem_planeD hl)

omit hsq in
theorem eq_mul_u₀_of_not_mem {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) : ∃ d ∈ planeD B c₁ c₂, x = d * u₀ := by
  have hxCU : x ∈ planeD B c₁ c₂ ⊔ U := by rw [h.planeD_sup_U hl]; exact hxC
  obtain ⟨d₀, hd₀, y, hy, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hxCU
  have hyB : y ∉ B := fun hyB => hxD (Subgroup.mul_mem _ hd₀ (h.B_le_planeD hl hyB))
  have hb := (h.not_mem_iff hy).mp hyB
  refine ⟨d₀ * (u₀ * y), Subgroup.mul_mem _ hd₀ (h.B_le_planeD hl hb), ?_⟩
  rw [mul_assoc, mul_comm_of_mem h.u₀_mem hy, mul_assoc, mul_self_eq_one_of_mem h.u₀_mem,
    mul_one]

theorem outside_mul_self {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) : x * x = 1 := by
  obtain ⟨d, hd, rfl⟩ := h.eq_mul_u₀_of_not_mem hl hxC hxD
  have hinv := h.u₀_inverts hsq hd
  calc d * u₀ * (d * u₀) = d * (u₀ * d * u₀⁻¹) * (u₀ * u₀) := by group
    _ = 1 := by rw [hinv, mul_self_eq_one_of_mem h.u₀_mem]; group

theorem outside_orderOf {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) : orderOf x = 2 := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ ?_
  · rw [pow_two]; exact h.outside_mul_self hl hsq hxC hxD
  · rintro rfl; exact hxD (Subgroup.one_mem _)

omit hsq in
theorem outside_centralizer {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) :
    Subgroup.centralizer {x} ⊓ Subgroup.centralizer (B : Set Y) = B ⊔ Subgroup.zpowers x := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgx', hgC⟩ := Subgroup.mem_inf.mp hg
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hgx'
    by_cases hgD : g ∈ planeD B c₁ c₂
    · exact Subgroup.mem_sup_left
        ((h.comm_iff_of_not_mem_planeD hl hxC hxD hgD).mp hgx.symm)
    · obtain ⟨d', hd', rfl⟩ := h.eq_mul_u₀_of_not_mem hl hgC hgD
      obtain ⟨d, hd, rfl⟩ := h.eq_mul_u₀_of_not_mem hl hxC hxD
      have hed : d' * d⁻¹ ∈ planeD B c₁ c₂ := Subgroup.mul_mem _ hd' (Subgroup.inv_mem _ hd)
      have hcomm : d * u₀ * (d' * d⁻¹) = d' * d⁻¹ * (d * u₀) := by
        calc d * u₀ * (d' * d⁻¹) = d * u₀ * (d' * u₀ * (d * u₀)⁻¹) := by group
          _ = d * u₀ * (d' * u₀) * (d * u₀)⁻¹ := by group
          _ = d' * u₀ * (d * u₀) * (d * u₀)⁻¹ := by rw [hgx]
          _ = d' * d⁻¹ * (d * u₀) := by group
      have hedB := (h.comm_iff_of_not_mem_planeD hl hxC hxD hed).mp hcomm
      rw [show d' * u₀ = d' * d⁻¹ * (d * u₀) by group]
      exact Subgroup.mul_mem_sup hedB (Subgroup.mem_zpowers _)
  · refine sup_le ?_ ?_
    · intro b hb
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hxC) b hb), le_centralizer_of_le h.le hb⟩
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxC⟩

theorem outside_inf {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) : B ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyB, hyZ⟩
  rcases mem_zpowers_of_orderOf_eq_two (h.outside_orderOf hl hsq hxC hxD) hyZ with rfl | rfl
  · exact Subgroup.one_mem _
  · exact absurd (h.B_le_planeD hl hyB) hxD

theorem outside_card [Finite Y] {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) :
    Nat.card (Subgroup.centralizer {x} ⊓ Subgroup.centralizer (B : Set Y) : Subgroup Y) = 8 := by
  rw [h.outside_centralizer hl hxC hxD,
    card_sup_of_le_normalizer_of_inf_eq_bot B _ ?_ (h.outside_inf hl hsq hxC hxD),
    h.card_B, Nat.card_zpowers, h.outside_orderOf hl hsq hxC hxD]
  rw [Subgroup.zpowers_le]
  exact centralizer_le_normalizer hxC

omit hsq in
theorem outside_class {x : Y} (hxC : x ∈ Subgroup.centralizer (B : Set Y))
    (hxD : x ∉ planeD B c₁ c₂) :
    {y | ∃ g ∈ Subgroup.centralizer (B : Set Y), g * x * g⁻¹ = y} = x • (B : Set Y) := by
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_smul_set, SetLike.mem_coe, smul_eq_mul]
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hk := h.commutator_mem_B hg hxC
    refine ⟨g * x * g⁻¹ * x⁻¹, hk, ?_⟩
    rw [← (Subgroup.mem_centralizer_iff.mp hxC) _ hk]
    group
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨d, hd, hτ⟩ := h.exists_planeD_of_tau hl hb
    obtain ⟨d₁, hd₁, rfl⟩ := h.eq_mul_u₀_of_not_mem hl hxC hxD
    have hdC := planeD_le_centralizer B c₁ c₂ hd
    refine ⟨d, hdC, ?_⟩
    have hdd₁ := h.planeD_comm hl hd hd₁
    calc d * (d₁ * u₀) * d⁻¹ = d₁ * (d * u₀ * d⁻¹) := by
          rw [← mul_assoc, hdd₁]; group
      _ = d₁ * u₀ * b := by rw [h.conj_u₀ d, hτ]; group

omit hl in
theorem pow_four_eq_one_of_mem {d : Y} (hd : d ∈ planeD B c₁ c₂) : d ^ 4 = 1 := by
  have hτB := h.planeTau_mem (planeD_le_centralizer B c₁ c₂ hd)
  calc d ^ 4 = d * d * (d * d) := by rw [pow_succ, pow_succ, pow_succ, pow_one, mul_assoc]
    _ = 1 := by rw [hsq d hd]; exact mul_self_eq_one_of_mem (h.le hτB)

theorem nonempty_planeD_mulEquiv [Finite Y] :
    Nonempty (planeD B c₁ c₂ ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) := by
  have hc₁D := c₁_mem_planeD hl
  have hc₂D := c₂_mem_planeD hl
  have h₁ := h.pow_four_eq_one_of_mem hsq hc₁D
  have h₂ := h.pow_four_eq_one_of_mem hsq hc₂D
  have hcomm : ∀ m n : ℕ, c₂ ^ m * c₁ ^ n = c₁ ^ n * c₂ ^ m := fun m n =>
    ((Commute.pow_pow (show Commute c₂ c₁ from hl.comm.symm)) m n)
  have hmem : ∀ p : Multiplicative (ZMod 4) × Multiplicative (ZMod 4),
      c₁ ^ p.1.toAdd.val * c₂ ^ p.2.toAdd.val ∈ planeD B c₁ c₂ := fun p =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ hc₁D _) (Subgroup.pow_mem _ hc₂D _)
  let f : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* planeD B c₁ c₂ :=
    { toFun := fun p => ⟨c₁ ^ p.1.toAdd.val * c₂ ^ p.2.toAdd.val, hmem p⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro p q
        apply Subtype.ext
        simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, Subgroup.coe_mul]
        rw [ZMod.val_add, ZMod.val_add, ← pow_eq_pow_mod _ h₁, ← pow_eq_pow_mod _ h₂, pow_add,
          pow_add]
        rw [show c₁ ^ (p.1.toAdd).val * c₁ ^ (q.1.toAdd).val *
            (c₂ ^ (p.2.toAdd).val * c₂ ^ (q.2.toAdd).val) =
            c₁ ^ (p.1.toAdd).val * (c₁ ^ (q.1.toAdd).val * c₂ ^ (p.2.toAdd).val) *
              c₂ ^ (q.2.toAdd).val by group, ← hcomm]
        group }
  have hf : ∀ p, ((f p : planeD B c₁ c₂) : Y) = c₁ ^ p.1.toAdd.val * c₂ ^ p.2.toAdd.val :=
    fun p => rfl
  have hv1 : (1 : ZMod 4).val = 1 := rfl
  have hc₁r : (⟨c₁, hc₁D⟩ : planeD B c₁ c₂) ∈ f.range :=
    ⟨(Multiplicative.ofAdd 1, 1), Subtype.ext (by rw [hf]; simp [hv1])⟩
  have hc₂r : (⟨c₂, hc₂D⟩ : planeD B c₁ c₂) ∈ f.range :=
    ⟨(1, Multiplicative.ofAdd 1), Subtype.ext (by rw [hf]; simp [hv1])⟩
  have hBr : ∀ b ∈ B, ∀ hb' : b ∈ planeD B c₁ c₂, (⟨b, hb'⟩ : planeD B c₁ c₂) ∈ f.range := by
    intro b hb hb'
    have hsq₁ : c₁ * c₁ = b₁ := (hsq c₁ hc₁D).trans hl.tau₁
    have hsq₂ : c₂ * c₂ = b₂ := (hsq c₂ hc₂D).trans hl.tau₂
    rcases h.mem_B_cases hb with hbb | hbb | hbb | hbb
    · have : (⟨b, hb'⟩ : planeD B c₁ c₂) = 1 := Subtype.ext hbb
      rw [this]; exact Subgroup.one_mem _
    · have : (⟨b, hb'⟩ : planeD B c₁ c₂) = ⟨c₁, hc₁D⟩ * ⟨c₁, hc₁D⟩ :=
        Subtype.ext (hbb.trans hsq₁.symm)
      rw [this]; exact Subgroup.mul_mem _ hc₁r hc₁r
    · have : (⟨b, hb'⟩ : planeD B c₁ c₂) = ⟨c₂, hc₂D⟩ * ⟨c₂, hc₂D⟩ :=
        Subtype.ext (hbb.trans hsq₂.symm)
      rw [this]; exact Subgroup.mul_mem _ hc₂r hc₂r
    · have : (⟨b, hb'⟩ : planeD B c₁ c₂) =
          ⟨c₁, hc₁D⟩ * ⟨c₁, hc₁D⟩ * (⟨c₂, hc₂D⟩ * ⟨c₂, hc₂D⟩) :=
        Subtype.ext (show b = c₁ * c₁ * (c₂ * c₂) by rw [hbb, hsq₁, hsq₂])
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₁r hc₁r) (Subgroup.mul_mem _ hc₂r hc₂r)
  have hsurj : Function.Surjective f := by
    rw [← MonoidHom.range_eq_top, eq_top_iff]
    rintro ⟨d, hd⟩ -
    obtain ⟨b, hb, hdd⟩ := h.planeD_decomp hl hd
    have hbD := h.B_le_planeD hl hb
    have hbr := hBr b hb hbD
    rcases hdd with hdd | hdd | hdd | hdd
    · have : (⟨d, hd⟩ : planeD B c₁ c₂) = ⟨b, hbD⟩ := Subtype.ext hdd
      rw [this]; exact hbr
    · have : (⟨d, hd⟩ : planeD B c₁ c₂) = ⟨c₁, hc₁D⟩ * ⟨b, hbD⟩ := Subtype.ext hdd
      rw [this]; exact Subgroup.mul_mem _ hc₁r hbr
    · have : (⟨d, hd⟩ : planeD B c₁ c₂) = ⟨c₂, hc₂D⟩ * ⟨b, hbD⟩ := Subtype.ext hdd
      rw [this]; exact Subgroup.mul_mem _ hc₂r hbr
    · have : (⟨d, hd⟩ : planeD B c₁ c₂) = ⟨c₁, hc₁D⟩ * ⟨c₂, hc₂D⟩ * ⟨b, hbD⟩ :=
        Subtype.ext hdd
      rw [this]; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc₁r hc₂r) hbr
  have hbij : Function.Bijective f := by
    refine (Nat.bijective_iff_surjective_and_card f).mpr ⟨hsurj, ?_⟩
    rw [h.card_planeD hl, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  exact ⟨(MulEquiv.ofBijective f hbij).symm⟩

end CaseTwo

end PlaneHyp

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
