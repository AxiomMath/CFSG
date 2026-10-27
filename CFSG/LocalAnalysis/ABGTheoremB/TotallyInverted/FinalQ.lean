module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalData

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem pGroupR_of_R01 (Δ : Data σ r) (h : IsPGroup r (R Δ 0 ⊔ R Δ 1 : Subgroup G)) :
    PGroupR Δ := by
  have h' := isPGroup_conjSub h (Δ.a ^ ((2 : Fin 3) : ℕ))
  rw [conjSub_sup, conjSub_a_pow_R, conjSub_a_pow_R, sup_comm] at h'
  exact h'

theorem pGroupR_of_R12 (Δ : Data σ r) (h : IsPGroup r (R Δ 1 ⊔ R Δ 2 : Subgroup G)) :
    PGroupR Δ := by
  have h' := isPGroup_conjSub h (Δ.a ^ ((1 : Fin 3) : ℕ))
  rw [conjSub_sup, conjSub_a_pow_R, conjSub_a_pow_R, sup_comm] at h'
  exact h'

theorem one_lt_q (hσ : σ.IsValid) : 1 < σ.q := by
  have := hσ.five_lt_q
  omega

section Q

variable (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
include hδq

theorem Q_ne_Qs (i : Fin 3) : Δ.Q i ≠ Δ.Qs i := (Δ.Q_cases hδq i).1

theorem card_Q (i : Fin 3) : Nat.card (Δ.Q i) = σ.q := (Δ.Q_cases hδq i).2.1

theorem card_Qs (i : Fin 3) : Nat.card (Δ.Qs i) = σ.q := (Δ.Q_cases hδq i).2.2.1

theorem J_conj_eq (i : Fin 3) : conjSub (Δ.a ^ (i : ℕ)) Δ.J = Δ.Q i ⊔ Δ.Qs i :=
  (Δ.Q_cases hδq i).2.2.2.1

theorem Q_irred (i : Fin 3) {X : Subgroup G} (hX : X ≤ Δ.Q i)
    (hC : σ.C ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ ∨ X = Δ.Q i :=
  (Δ.Q_cases hδq i).2.2.2.2.2.2.1 X hX hC

theorem Qs_irred (i : Fin 3) {X : Subgroup G} (hX : X ≤ Δ.Qs i)
    (hC : σ.C ≤ Subgroup.normalizer (X : Set G)) : X = ⊥ ∨ X = Δ.Qs i :=
  (Δ.Q_cases hδq i).2.2.2.2.2.2.2.1 X hX hC

theorem Q_le_centralizer_Ps (i : Fin 3) :
    Δ.Q i ≤ Subgroup.centralizer (σ.Ps r i : Set G) :=
  (Δ.Q_cases hδq i).2.2.2.2.2.2.2.2.1

theorem Qs_le_centralizer_Ps (i : Fin 3) :
    Δ.Qs i ≤ Subgroup.centralizer (σ.Ps r i : Set G) :=
  (Δ.Q_cases hδq i).2.2.2.2.2.2.2.2.2

theorem Q_ne_bot (hσ : σ.IsValid) (i : Fin 3) : Δ.Q i ≠ ⊥ := by
  intro h
  have := card_Q Δ hδq i
  rw [h, Subgroup.card_bot] at this
  exact (one_lt_q hσ).ne this

theorem Qs_ne_bot (hσ : σ.IsValid) (i : Fin 3) : Δ.Qs i ≠ ⊥ := by
  intro h
  have := card_Qs Δ hδq i
  rw [h, Subgroup.card_bot] at this
  exact (one_lt_q hσ).ne this

theorem J_inf_ON : Δ.J ⊓ σ.ON = ⊥ := J_inf_ON_of_deltaEps Δ hδq.1

end Q

omit [Finite G] in
theorem conjSub_centralizer (g : G) (X : Subgroup G) :
    conjSub g (Subgroup.centralizer (X : Set G)) = Subgroup.centralizer (conjSub g X : Set G) := by
  ext y
  rw [mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    rw [SetLike.mem_coe, mem_conjSub_iff] at hx
    have := h _ hx
    calc x * y = g * (g⁻¹ * x * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
      _ = y * x := by group
  · intro h x hx
    have := h _ (conj_mem_conjSub (g := g) hx)
    calc x * (g⁻¹ * y * g) = g⁻¹ * (g * x * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * x := by group

theorem abelian_of_irred {p : ℕ} [Fact p.Prime] {X C : Subgroup G} (hX : IsPGroup p X)
    (hX1 : X ≠ ⊥) (hC : C ≤ Subgroup.normalizer (X : Set G))
    (hirr : ∀ Y : Subgroup G, Y ≤ X → C ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X) :
    ∀ g ∈ X, ∀ h ∈ X, g * h = h * g := by
  set Z : Subgroup G := X ⊓ Subgroup.centralizer (X : Set G) with hZ
  have hCZ : C ≤ Subgroup.normalizer (Z : Set G) := by
    intro c hc
    have hcX := conjSub_eq_self_iff.mpr (hC hc)
    have hcZ : c ∈ Subgroup.normalizer
        ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) := by
      rw [← conjSub_eq_self_iff, conjSub_centralizer, hcX]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hC hc, hcZ⟩
  have hZne : Z ≠ ⊥ := by
    have : Nontrivial X := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      exact hX1
    have := hX.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center X)
    intro h
    apply hz1
    have hzZ : (z : G) ∈ Z := by
      refine ⟨z.2, ?_⟩
      show (z : G) ∈ Subgroup.centralizer (X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := Subgroup.mem_center_iff.mp hz ⟨x, hx⟩
      exact congrArg Subtype.val this
    rw [h, Subgroup.mem_bot] at hzZ
    exact Subtype.ext (Subtype.ext hzZ)
  rcases hirr Z inf_le_left hCZ with h | h
  · exact absurd h hZne
  · intro g hg k hk
    have : g ∈ Z := h ▸ hg
    exact (Subgroup.mem_centralizer_iff.mp this.2 k hk).symm

section Q

variable (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
include hδq

theorem Q_abelian (hσ : σ.IsValid) (i : Fin 3) : ∀ g ∈ Δ.Q i, ∀ h ∈ Δ.Q i, g * h = h * g := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  exact abelian_of_irred (Δ.Q_pgroup i).1 (Q_ne_bot Δ hδq hσ i) (C_le_normalizer_Q Δ i)
    (fun Y hY hCY => Q_irred Δ hδq i hY hCY)

theorem Qs_abelian (hσ : σ.IsValid) (i : Fin 3) :
    ∀ g ∈ Δ.Qs i, ∀ h ∈ Δ.Qs i, g * h = h * g := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  exact abelian_of_irred (Δ.Q_pgroup i).2 (Qs_ne_bot Δ hδq hσ i) (C_le_normalizer_Qs Δ i)
    (fun Y hY hCY => Qs_irred Δ hδq i hY hCY)

theorem Q_inf_Ps (i : Fin 3) : Δ.Q i ⊓ σ.Ps r i = ⊥ := by
  have h0 : Δ.Q 0 ⊓ σ.Ps r 0 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hJ : g ∈ Δ.J := by simpa [conjSub_one] using Q_le_J_conj Δ 0 hg.1
    have := (J_inf_ON Δ hδq).le ⟨hJ, Ps_zero_le_ON Δ hg.2⟩
    exact this
  rw [← zero_add_fin i, ← conjSub_a_pow_Q Δ, ← conjSub_a_pow_Ps Δ, ← conjSub_inf, h0,
    conjSub_bot]

theorem Qs_inf_Ps (i : Fin 3) : Δ.Qs i ⊓ σ.Ps r i = ⊥ := by
  have h0 : Δ.Qs 0 ⊓ σ.Ps r 0 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hJ : g ∈ Δ.J := by simpa [conjSub_one] using Qs_le_J_conj Δ 0 hg.1
    have := (J_inf_ON Δ hδq).le ⟨hJ, Ps_zero_le_ON Δ hg.2⟩
    exact this
  rw [← zero_add_fin i, ← conjSub_a_pow_Qs Δ, ← conjSub_a_pow_Ps Δ, ← conjSub_inf, h0,
    conjSub_bot]

end Q

omit [Finite G] in
theorem normalizer_T_le_M : Subgroup.normalizer (σ.T : Set G) ≤ σ.M := by
  intro g hg
  rw [Setting.M, ← conjSub_eq_self_iff]
  ext y
  rw [mem_conjSub_iff, Setting.C, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have hgT := conjSub_eq_self_iff.mpr hg
  constructor
  · intro h t ht
    have ht' : g⁻¹ * t * g ∈ σ.T := by
      rw [← mem_conjSub_iff, hgT]
      exact ht
    have := h _ ht'
    calc t * y = g * (g⁻¹ * t * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * t * g)) * g⁻¹ := by rw [this]
      _ = y * t := by group
  · intro h t ht
    have ht' : g * t * g⁻¹ ∈ σ.T := by
      rw [← hgT]
      exact conj_mem_conjSub ht
    have := h _ ht'
    calc t * (g⁻¹ * y * g) = g⁻¹ * (g * t * g⁻¹ * y) * g := by group
      _ = g⁻¹ * (y * (g * t * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * t := by group

omit [Finite G] in
theorem conjSub_conjSub_conj (z a : G) (Y : Subgroup G) :
    conjSub z (conjSub a Y) = conjSub (z * a * z⁻¹) (conjSub z Y) := by
  rw [conjSub_conjSub, conjSub_conjSub]
  group

structure IsSwap (Δ : Data σ r) (z : G) : Prop where
  mem_D : z ∈ σ.D
  conj_Q : conjSub z (Δ.Q 0) = Δ.Qs 0

theorem exists_isSwap (Δ : Data σ r) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q) :
    ∃ z, IsSwap Δ z := by
  obtain ⟨z, hz, hzQ⟩ := (Δ.Q_cases hδq 0).2.2.2.2.1
  exact ⟨z, ⟨by simpa [conjSub_one] using hz, hzQ⟩⟩

namespace IsSwap

variable {Δ : Data σ r} {z : G} (hz : IsSwap Δ z) (hσ : σ.IsValid)
  (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
include hz

theorem mem_N (hσ : σ.IsValid) : z ∈ σ.N := σ.D_le_N hσ hz.mem_D

theorem mem_normalizer_T : z ∈ Subgroup.normalizer (σ.T : Set G) := hz.mem_D.2

theorem mem_M : z ∈ σ.M := normalizer_T_le_M hz.mem_normalizer_T

theorem conj_x (hσ : σ.IsValid) : z * σ.x * z⁻¹ = σ.x := by
  rw [Subgroup.mem_centralizer_singleton_iff.mp (hz.mem_N hσ), mul_inv_cancel_right]

include hδq in
theorem not_mem_C (hzC : z ∈ σ.C) : False := by
  apply Q_ne_Qs Δ hδq 0
  rw [← hz.conj_Q, conjSub_eq_self_iff.mpr (C_le_normalizer_Q Δ 0 hzC)]

include hδq in
theorem conj_x₂ (hσ : σ.IsValid) : z * σ.x₂ * z⁻¹ = σ.xs 2 := by
  obtain ⟨j, hj⟩ := exists_conj_xs_eq hσ hz.mem_normalizer_T 1
  have hj' : z * σ.x₂ * z⁻¹ = σ.xs j := hj
  match j, hj' with
  | 0, hj' =>
    exfalso
    have h1 : z * σ.x₂ * z⁻¹ = z * σ.x * z⁻¹ := by rw [hj', hz.conj_x hσ]; rfl
    exact hσ.x_ne_x₂ (by simpa using h1.symm)
  | 1, hj' => exact absurd (mem_C_of_conj z (hz.conj_x hσ) hj') (hz.not_mem_C hδq)
  | 2, hj' => exact hj'

include hδq in
theorem conj_x₃ (hσ : σ.IsValid) : z * σ.xs 2 * z⁻¹ = σ.x₂ := by
  change z * (σ.x * σ.x₂) * z⁻¹ = σ.x₂
  calc z * (σ.x * σ.x₂) * z⁻¹ = (z * σ.x * z⁻¹) * (z * σ.x₂ * z⁻¹) := by group
    _ = σ.x * (σ.x * σ.x₂) := by rw [hz.conj_x hσ, hz.conj_x₂ hδq hσ]; rfl
    _ = σ.x₂ := by rw [← mul_assoc, x_mul_x hσ, one_mul]

include hδq in
theorem sq_mem_C (hσ : σ.IsValid) : z * z ∈ σ.C := by
  apply mem_C_of_conj
  · calc z * z * σ.x * (z * z)⁻¹ = z * (z * σ.x * z⁻¹) * z⁻¹ := by group
      _ = σ.x := by rw [hz.conj_x hσ, hz.conj_x hσ]
  · calc z * z * σ.x₂ * (z * z)⁻¹ = z * (z * σ.x₂ * z⁻¹) * z⁻¹ := by group
      _ = σ.x₂ := by rw [hz.conj_x₂ hδq hσ, hz.conj_x₃ hδq hσ]

include hδq in
theorem conj_Qs (hσ : σ.IsValid) : conjSub z (Δ.Qs 0) = Δ.Q 0 := by
  rw [← hz.conj_Q, conjSub_conjSub,
    conjSub_eq_self_iff.mpr (C_le_normalizer_Q Δ 0 (hz.sq_mem_C hδq hσ))]

theorem conj_a_mem (hσ : σ.IsValid) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q) :
    (Δ.a ^ 2)⁻¹ * (z * Δ.a * z⁻¹) ∈ σ.C := by
  have ha0 := Δ.a_cycle 0
  have ha1 := Δ.a_cycle 1
  have ha2 := Δ.a_cycle 2
  change Δ.a * σ.x * Δ.a⁻¹ = σ.x₂ at ha0
  change Δ.a * σ.x₂ * Δ.a⁻¹ = σ.xs 2 at ha1
  change Δ.a * σ.xs 2 * Δ.a⁻¹ = σ.x at ha2
  have hzx := hz.conj_x hσ
  have hzx₂ := hz.conj_x₂ hδq hσ
  have hzx₃ := hz.conj_x₃ hδq hσ
  have inv_conj : ∀ {g u v : G}, g * u * g⁻¹ = v → g⁻¹ * v * g = u := by
    intro g u v h
    rw [← h]
    group
  rw [pow_two]
  apply mem_C_of_conj
  · calc (Δ.a * Δ.a)⁻¹ * (z * Δ.a * z⁻¹) * σ.x * ((Δ.a * Δ.a)⁻¹ * (z * Δ.a * z⁻¹))⁻¹ =
          Δ.a⁻¹ * (Δ.a⁻¹ * (z * (Δ.a * (z⁻¹ * σ.x * z) * Δ.a⁻¹) * z⁻¹) * Δ.a) * Δ.a := by
          simp only [mul_inv_rev, inv_inv, mul_assoc]
      _ = σ.x := by
          rw [inv_conj hzx, ha0, hzx₂, inv_conj ha1, inv_conj ha0]
  · calc (Δ.a * Δ.a)⁻¹ * (z * Δ.a * z⁻¹) * σ.x₂ * ((Δ.a * Δ.a)⁻¹ * (z * Δ.a * z⁻¹))⁻¹ =
          Δ.a⁻¹ * (Δ.a⁻¹ * (z * (Δ.a * (z⁻¹ * σ.x₂ * z) * Δ.a⁻¹) * z⁻¹) * Δ.a) * Δ.a := by
          simp only [mul_inv_rev, inv_inv, mul_assoc]
      _ = σ.x₂ := by
          rw [inv_conj hzx₃, ha2, hzx, inv_conj ha2, inv_conj ha1]

theorem conjSub_zaz (hσ : σ.IsValid) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q) {Y : Subgroup G}
    (hY : σ.C ≤ Subgroup.normalizer (Y : Set G)) :
    conjSub (z * Δ.a * z⁻¹) Y = conjSub (Δ.a ^ 2) Y := by
  have e : z * Δ.a * z⁻¹ = Δ.a ^ 2 * ((Δ.a ^ 2)⁻¹ * (z * Δ.a * z⁻¹)) := by group
  rw [e, ← conjSub_conjSub, conjSub_eq_self_iff.mpr (hY (hz.conj_a_mem hσ hδq))]

theorem conjSub_family (hσ : σ.IsValid) (hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q)
    {X Y : Fin 3 → Subgroup G} (hX : ∀ i, conjSub Δ.a (X i) = X (i + 1))
    (hY : ∀ i, conjSub Δ.a (Y i) = Y (i + 1))
    (hYC : ∀ i, σ.C ≤ Subgroup.normalizer (Y i : Set G)) (h0 : conjSub z (X 0) = Y 0) :
    conjSub z (X 1) = Y 2 ∧ conjSub z (X 2) = Y 1 := by
  have ha2 : ∀ i, conjSub (Δ.a ^ 2) (Y i) = Y (i + 2) := by
    intro i
    rw [pow_two, ← conjSub_conjSub, hY, hY, add_assoc]
    rfl
  have h1 : conjSub z (X 1) = Y 2 := by
    rw [show X 1 = conjSub Δ.a (X 0) from (hX 0).symm, conjSub_conjSub_conj, h0,
      hz.conjSub_zaz hσ hδq (hYC 0), ha2]
    rfl
  refine ⟨h1, ?_⟩
  rw [show X 2 = conjSub Δ.a (X 1) from (hX 1).symm, conjSub_conjSub_conj, h1,
    hz.conjSub_zaz hσ hδq (hYC 2), ha2]
  rfl

theorem conj_Ps_zero (hσ : σ.IsValid) : conjSub z (σ.Ps r 0) = σ.Ps r 0 :=
  conjSub_eq_self_iff.mpr (le_normalizer_pCoreIn r σ.N (hz.mem_N hσ))

theorem conj_R_zero (hσ : σ.IsValid) : conjSub z (R Δ 0) = Rs Δ 0 := by
  rw [R, Rs, conjSub_sup, hz.conj_Q, hz.conj_Ps_zero hσ]

include hδq in
theorem conj_Rs_zero (hσ : σ.IsValid) : conjSub z (Rs Δ 0) = R Δ 0 := by
  rw [R, Rs, conjSub_sup, hz.conj_Qs hδq hσ, hz.conj_Ps_zero hσ]

include hδq in
theorem conj_R (hσ : σ.IsValid) : conjSub z (R Δ 1) = Rs Δ 2 ∧ conjSub z (R Δ 2) = Rs Δ 1 :=
  hz.conjSub_family hσ hδq (conjSub_R Δ) (conjSub_Rs Δ) (C_le_normalizer_Rs Δ)
    (hz.conj_R_zero hσ)

include hδq in
theorem conj_Rs (hσ : σ.IsValid) : conjSub z (Rs Δ 1) = R Δ 2 ∧ conjSub z (Rs Δ 2) = R Δ 1 :=
  hz.conjSub_family hσ hδq (conjSub_Rs Δ) (conjSub_R Δ) (C_le_normalizer_R Δ)
    (hz.conj_Rs_zero hδq hσ)

include hδq in
theorem conj_Q12 (hσ : σ.IsValid) :
    conjSub z (Δ.Q 1) = Δ.Qs 2 ∧ conjSub z (Δ.Q 2) = Δ.Qs 1 :=
  hz.conjSub_family hσ hδq (fun i => (Δ.Q_conj i).1) (fun i => (Δ.Q_conj i).2)
    (C_le_normalizer_Qs Δ) hz.conj_Q

include hδq in
theorem conj_Qs12 (hσ : σ.IsValid) :
    conjSub z (Δ.Qs 1) = Δ.Q 2 ∧ conjSub z (Δ.Qs 2) = Δ.Q 1 :=
  hz.conjSub_family hσ hδq (fun i => (Δ.Q_conj i).2) (fun i => (Δ.Q_conj i).1)
    (C_le_normalizer_Q Δ) (hz.conj_Qs hδq hσ)

include hδq in
theorem conj_Ps12 (hσ : σ.IsValid) :
    conjSub z (σ.Ps r 1) = σ.Ps r 2 ∧ conjSub z (σ.Ps r 2) = σ.Ps r 1 :=
  hz.conjSub_family hσ hδq Δ.P_conj Δ.P_conj (C_le_normalizer_Ps r) (hz.conj_Ps_zero hσ)

end IsSwap

theorem pGroupR_of_Rs01 (hσ : σ.IsValid) (Δ : Data σ r)
    (h : IsPGroup r (Rs Δ 0 ⊔ Rs Δ 1 : Subgroup G)) : PGroupR Δ := by
  by_cases hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · obtain ⟨z, hz⟩ := exists_isSwap Δ hδq
    have h' := isPGroup_conjSub h z
    rwa [conjSub_sup, hz.conj_Rs_zero hδq hσ, (hz.conj_Rs hδq hσ).1] at h'
  · have hRR : ∀ i, Rs Δ i = R Δ i := fun i => by
      rw [R, Rs, (Δ.Q_trivial hδq i).1, (Δ.Q_trivial hδq i).2]
    rw [hRR, hRR] at h
    exact pGroupR_of_R01 Δ h

theorem pGroupR_of_Rs02 (hσ : σ.IsValid) (Δ : Data σ r)
    (h : IsPGroup r (Rs Δ 0 ⊔ Rs Δ 2 : Subgroup G)) : PGroupR Δ := by
  by_cases hδq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · obtain ⟨z, hz⟩ := exists_isSwap Δ hδq
    have h' := isPGroup_conjSub h z
    rw [conjSub_sup, hz.conj_Rs_zero hδq hσ, (hz.conj_Rs hδq hσ).2] at h'
    exact pGroupR_of_R01 Δ h'
  · have hRR : ∀ i, Rs Δ i = R Δ i := fun i => by
      rw [R, Rs, (Δ.Q_trivial hδq i).1, (Δ.Q_trivial hδq i).2]
    rw [hRR, hRR] at h
    exact h

end CFSG.ABGTheoremB.TotallyInverted.Sec11
