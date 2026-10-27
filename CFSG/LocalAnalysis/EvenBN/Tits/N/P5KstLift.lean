module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P5KstMod

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst

open Subgroup CFSG.Open CFSG.LocalAnalysis.EvenBN.Tits.N.P4 Equiv
open scoped commutatorElement

section Comm

variable {Γ : Type*} [Group Γ] {U : Subgroup Γ} {y : Γ}

@[expose] def commHom (U : Subgroup Γ) (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (y : Γ)
    (hy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) : ↥U →* ↥U where
  toFun u := ⟨u * (y * u * y⁻¹), mul_mem u.2 (hy u u.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := by
    apply Subtype.ext
    have hba : (b : Γ) * (y * a * y⁻¹) = (y * a * y⁻¹) * b := hc _ b.2 _ (hy a a.2)
    show (a : Γ) * b * (y * (a * b) * y⁻¹) = (a * (y * a * y⁻¹)) * (b * (y * b * y⁻¹))
    calc (a : Γ) * b * (y * (a * b) * y⁻¹) = a * (b * (y * a * y⁻¹)) * (y * b * y⁻¹) := by group
      _ = a * ((y * a * y⁻¹) * b) * (y * b * y⁻¹) := by rw [hba]
      _ = (a * (y * a * y⁻¹)) * (b * (y * b * y⁻¹)) := by group

theorem commHom_ker (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hsq : ∀ a ∈ U, a * a = 1)
    (hy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    (commHom U hc y hy).ker = (U ⊓ centralizer ({y} : Set Γ)).subgroupOf U := by
  ext u
  rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
  have hu2 : (u : Γ) * u = 1 := hsq u u.2
  constructor
  · intro h1
    have h2 : (u : Γ) * (y * u * y⁻¹) = 1 := congrArg Subtype.val h1
    refine ⟨u.2, ?_⟩
    have h3 : y * u * y⁻¹ = (u : Γ) := by
      have := mul_left_cancel (h2.trans hu2.symm)
      exact this
    calc (u : Γ) * y = y * u * y⁻¹ * y := by rw [h3]
      _ = y * u := by group
  · rintro ⟨-, h1⟩
    apply Subtype.ext
    show (u : Γ) * (y * u * y⁻¹) = 1
    have : y * u * y⁻¹ = (u : Γ) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h1.symm
    rw [this]
    exact hu2

theorem commutator_eq (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hsq : ∀ a ∈ U, a * a = 1)
    (hy2 : y * y = 1) (hy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    ⁅U, zpowers y⁆ = (commHom U hc y hy).range.map U.subtype := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    rcases eq_one_or_eq_of_mem_zpowers_invol hy2 hg₂ with rfl | rfl
    · simp only [commutatorElement_def, mul_one, one_mul, inv_one, mul_inv_cancel]
      exact one_mem _
    · refine ⟨commHom U hc g₂ hy ⟨g₁, hg₁⟩, ⟨⟨g₁, hg₁⟩, rfl⟩, ?_⟩
      show g₁ * (g₂ * g₁ * g₂⁻¹) = ⁅g₁, g₂⁆
      have h1 : g₁⁻¹ = g₁ := inv_eq_of_mul_eq_one_right (hsq g₁ hg₁)
      rw [commutatorElement_def, h1]
      group
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    show (u : Γ) * (y * u * y⁻¹) ∈ _
    have h1 : (u : Γ)⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u u.2)
    have : (u : Γ) * (y * u * y⁻¹) = ⁅(u : Γ), y⁆ := by
      rw [commutatorElement_def, h1]
      group
    rw [this]
    exact Subgroup.commutator_mem_commutator u.2 (mem_zpowers y)

theorem mem_commutator_iff (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hsq : ∀ a ∈ U, a * a = 1)
    (hy2 : y * y = 1) (hy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) {u : Γ} :
    u ∈ ⁅U, zpowers y⁆ ↔ ∃ c ∈ U, u = c * (y * c * y⁻¹) := by
  rw [commutator_eq hc hsq hy2 hy]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, c.2, rfl⟩
  · rintro ⟨c, hcU, rfl⟩
    exact ⟨_, ⟨⟨c, hcU⟩, rfl⟩, rfl⟩

theorem card_commutator_mul [Finite Γ] (hc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hsq : ∀ a ∈ U, a * a = 1) (hy2 : y * y = 1) (hy : ∀ u ∈ U, y * u * y⁻¹ ∈ U) :
    Nat.card ↥⁅U, zpowers y⁆ * Nat.card ↥(U ⊓ centralizer ({y} : Set Γ)) = Nat.card U := by
  have h1 := Subgroup.card_ker_mul_card_range (commHom U hc y hy)
  rw [commHom_ker hc hsq hy,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : U ⊓ centralizer ({y} : Set Γ) ≤ U)).toEquiv] at h1
  have h2 : Nat.card ↥⁅U, zpowers y⁆ = Nat.card (commHom U hc y hy).range := by
    rw [commutator_eq hc hsq hy2 hy]
    exact Nat.card_congr ((commHom U hc y hy).range.equivMapOfInjective _ U.subtype_injective).toEquiv.symm
  rw [h2, mul_comm]
  exact h1

end Comm

namespace KSetup

variable {Γ : Type*} [Group Γ] [Finite Γ] {U K : Subgroup Γ} {x v t : Γ}

theorem sq_conj_mem (h : KSetup U K x v t) {u : Γ} (hu : u ∈ U) : v ^ 2 * u * (v ^ 2)⁻¹ ∈ U :=
  (mem_normalizer_iff.1 h.hF.sq_norm u).1 hu

theorem t_comm_sq (h : KSetup U K x v t) : t * v ^ 2 = v ^ 2 * t := by
  rw [pow_two, ← mul_assoc, h.htv, mul_assoc, h.htv, mul_assoc]

theorem lift_invol (h : KSetup U K x v t) {y' : Γ} (hy2 : y' * y' = 1)
    (hw : (v ^ 2)⁻¹ * y' ∈ U ⊔ zpowers t)
    (hcard : Nat.card ↥(U ⊓ centralizer ({v ^ 2} : Set Γ)) = 4) :
    ∃ c ∈ U, c * y' * c⁻¹ = v ^ 2 ∨ c * y' * c⁻¹ = t * v ^ 2 := by
  have hw2 : v ^ 2 * v ^ 2 = 1 := h.hF.sq_mul_self
  have hwinv : (v ^ 2)⁻¹ = v ^ 2 := inv_eq_of_mul_eq_one_right hw2
  have hc := h.hF.comm
  have hsq := h.hF.sq
  have hU16 := h.hF.card
  obtain ⟨u₀, hu₀, hy'⟩ : ∃ u₀ ∈ U ⊔ zpowers t, y' = v ^ 2 * u₀ :=
    ⟨(v ^ 2)⁻¹ * y', hw, by group⟩
  have hu₀2 : u₀ * u₀ = 1 := h.U0_sq hu₀
  have hwu : v ^ 2 * u₀ = u₀ * v ^ 2 := by
    have h1 : v ^ 2 * u₀ * (v ^ 2 * u₀) = 1 := hy' ▸ hy2
    have h2 : v ^ 2 * u₀ * v ^ 2 = u₀ := by
      calc v ^ 2 * u₀ * v ^ 2 = v ^ 2 * u₀ * v ^ 2 * (u₀ * u₀) := by rw [hu₀2, mul_one]
        _ = (v ^ 2 * u₀ * (v ^ 2 * u₀)) * u₀ := by group
        _ = u₀ := by rw [h1, one_mul]
    calc v ^ 2 * u₀ = v ^ 2 * u₀ * (v ^ 2 * v ^ 2) := by rw [hw2, mul_one]
      _ = (v ^ 2 * u₀ * v ^ 2) * v ^ 2 := by group
      _ = u₀ * v ^ 2 := by rw [h2]
  have hnorm : ∀ u ∈ U, v ^ 2 * u * (v ^ 2)⁻¹ ∈ U := fun u hu => h.sq_conj_mem hu
  have hcardc := card_commutator_mul hc hsq hw2 hnorm
  rw [hcard, hU16] at hcardc
  have hle : ⁅U, zpowers (v ^ 2)⁆ ≤ U ⊓ centralizer ({v ^ 2} : Set Γ) := by
    intro u hu
    obtain ⟨c, hcU, rfl⟩ := (mem_commutator_iff hc hsq hw2 hnorm).1 hu
    have hcw : v ^ 2 * c * (v ^ 2)⁻¹ ∈ U := hnorm c hcU
    refine mem_inf.2 ⟨mul_mem hcU hcw, mem_centralizer_singleton_iff.2 ?_⟩
    have hcomm := hc _ hcU _ hcw
    rw [hwinv] at hcomm ⊢
    calc c * (v ^ 2 * c * v ^ 2) * v ^ 2 = ((v ^ 2 * c * v ^ 2) * c) * v ^ 2 := by rw [hcomm]
      _ = v ^ 2 * (c * (v ^ 2 * c * v ^ 2)) := by group
  have heq : ⁅U, zpowers (v ^ 2)⁆ = U ⊓ centralizer ({v ^ 2} : Set Γ) := by
    apply Subgroup.eq_of_le_of_card_ge hle
    omega
  have key : ∃ u ∈ U, v ^ 2 * u = u * v ^ 2 ∧ (y' = v ^ 2 * u ∨ y' = v ^ 2 * (t * u)) := by
    rcases (mem_sup_zpowers_iff_of_comm_invol h.htt h.htU).1 hu₀ with hu | hu
    · exact ⟨u₀, hu, hwu, Or.inl hy'⟩
    · refine ⟨t * u₀, hu, ?_, Or.inr ?_⟩
      · calc v ^ 2 * (t * u₀) = (v ^ 2 * t) * u₀ := by group
          _ = (t * v ^ 2) * u₀ := by rw [h.t_comm_sq]
          _ = t * (v ^ 2 * u₀) := by group
          _ = t * (u₀ * v ^ 2) := by rw [hwu]
          _ = (t * u₀) * v ^ 2 := by group
      · rw [hy']
        congr 2
        calc u₀ = (t * t) * u₀ := by rw [h.htt, one_mul]
          _ = t * (t * u₀) := by group
  obtain ⟨u, huU, huw, hy'u⟩ := key
  have huC : u ∈ ⁅U, zpowers (v ^ 2)⁆ := by
    rw [heq]
    exact mem_inf.2 ⟨huU, mem_centralizer_singleton_iff.2 huw.symm⟩
  obtain ⟨c, hcU, hcu⟩ := (mem_commutator_iff hc hsq hw2 hnorm).1 huC
  have hcc : c * c = 1 := hsq c hcU
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have huu : u * u = 1 := hsq u huU
  rw [hwinv] at hcu
  have hcwc : c * v ^ 2 * c = u * v ^ 2 := by
    calc c * v ^ 2 * c = c * v ^ 2 * c * (v ^ 2 * v ^ 2) := by rw [hw2, mul_one]
      _ = (c * (v ^ 2 * c * v ^ 2)) * v ^ 2 := by group
      _ = u * v ^ 2 := by rw [← hcu]
  have huc : u * c = c * u := hc u huU c hcU
  have hwu' : v ^ 2 * u = u * v ^ 2 := huw
  have hct : c * t = t * c := (h.htU c hcU).symm
  have hut : u * t = t * u := (h.htU u huU).symm
  refine ⟨c, hcU, ?_⟩
  rcases hy'u with e | e
  · left
    rw [e]
    calc c * (v ^ 2 * u) * c⁻¹ = c * (v ^ 2 * u) * c := by rw [hcinv]
      _ = c * v ^ 2 * (u * c) := by group
      _ = c * v ^ 2 * (c * u) := by rw [huc]
      _ = (c * v ^ 2 * c) * u := by group
      _ = (u * v ^ 2) * u := by rw [hcwc]
      _ = u * (v ^ 2 * u) := by group
      _ = u * (u * v ^ 2) := by rw [hwu']
      _ = (u * u) * v ^ 2 := by group
      _ = v ^ 2 := by rw [huu, one_mul]
  · right
    rw [e]
    have h_tuc : t * u * c = c * (t * u) := by
      calc t * u * c = t * (u * c) := by group
        _ = t * (c * u) := by rw [huc]
        _ = (t * c) * u := by group
        _ = (c * t) * u := by rw [hct.symm]
        _ = c * (t * u) := by group
    have hwt : v ^ 2 * t = t * v ^ 2 := h.t_comm_sq.symm
    calc c * (v ^ 2 * (t * u)) * c⁻¹ = c * (v ^ 2 * (t * u)) * c := by rw [hcinv]
      _ = c * v ^ 2 * ((t * u) * c) := by group
      _ = c * v ^ 2 * (c * (t * u)) := by rw [h_tuc]
      _ = (c * v ^ 2 * c) * (t * u) := by group
      _ = (u * v ^ 2) * (t * u) := by rw [hcwc]
      _ = u * (v ^ 2 * t) * u := by group
      _ = u * (t * v ^ 2) * u := by rw [hwt]
      _ = (u * t) * v ^ 2 * u := by group
      _ = (t * u) * v ^ 2 * u := by rw [hut]
      _ = t * (u * (v ^ 2 * u)) := by group
      _ = t * (u * (u * v ^ 2)) := by rw [hwu']
      _ = t * ((u * u) * v ^ 2) := by group
      _ = t * v ^ 2 := by rw [huu, one_mul]

end KSetup

end CFSG.LocalAnalysis.EvenBN.Tits.N.P5.Kst
