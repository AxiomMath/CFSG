module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Sec4S6U

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem exists_centralizer_elemAb {G : Type*} [Group G] [Finite G] {B : Subgroup G} {n : ℕ}
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hs : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 2 ^ (2 * n)) {x : G} (hx2 : x * x = 1)
    (hxN : ∀ b ∈ B, x * b * x⁻¹ ∈ B) :
    2 ^ n ≤ Nat.card ↥(B ⊓ centralizer ({x} : Set G)) := by
  have hf : ∀ b : B, x * (b : G) * x⁻¹ * (b : G)⁻¹ ∈ B := fun b =>
    B.mul_mem (hxN b b.2) (B.inv_mem b.2)
  let f : B →* B := MonoidHom.mk' (fun b => ⟨x * (b : G) * x⁻¹ * (b : G)⁻¹, hf b⟩) (by
    intro a b
    apply Subtype.ext
    have hw : (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        (a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹) := hc _ (hf b) _ (B.inv_mem a.2)
    show x * ((a : G) * (b : G)) * x⁻¹ * ((a : G) * (b : G))⁻¹ =
      (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)
    calc x * ((a : G) * (b : G)) * x⁻¹ * ((a : G) * (b : G))⁻¹
        = (x * (a : G) * x⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (x * (a : G) * x⁻¹) * ((a : G)⁻¹ * (x * (b : G) * x⁻¹ * (b : G)⁻¹)) := by
        rw [mul_assoc _ _ ((a : G)⁻¹), hw]
      _ = (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹) := by group)
  have hker : ∀ b : B, b ∈ f.ker ↔ x * (b : G) = (b : G) * x := fun b => by
    rw [MonoidHom.mem_ker]
    show (⟨x * (b : G) * x⁻¹ * (b : G)⁻¹, hf b⟩ : B) = 1 ↔ _
    rw [Subtype.ext_iff]
    show x * (b : G) * x⁻¹ * (b : G)⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  have hrange : f.range ≤ f.ker := by
    rintro _ ⟨b, rfl⟩
    rw [hker]
    show x * (x * (b : G) * x⁻¹ * (b : G)⁻¹) = (x * (b : G) * x⁻¹ * (b : G)⁻¹) * x
    have hsq := hs _ (hf b)
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = x * (b : G) * x⁻¹ * (b : G)⁻¹ := ⟨_, rfl⟩
    rw [← hcdef] at hsq ⊢
    have key : x * c * x⁻¹ = c⁻¹ := by
      have e1 : x * c * x⁻¹ = (x * x) * (b : G) * x⁻¹ * (b : G)⁻¹ * x⁻¹ := by rw [hcdef]; group
      have e2 : c⁻¹ = (b : G) * x * (b : G)⁻¹ * x⁻¹ := by rw [hcdef]; group
      rw [e1, e2, hx2, one_mul, hxinv]
    calc x * c = (x * c * x⁻¹) * x := by group
      _ = c⁻¹ * x := by rw [key]
      _ = c * x := by rw [inv_eq_of_mul_eq_one_right hsq]
  have hcardk : Nat.card f.ker * Nat.card f.range = Nat.card B := Subgroup.card_ker_mul_card_range f
  have hle : Nat.card f.range ≤ Nat.card f.ker := Subgroup.card_le_of_le hrange
  have hkerE : f.ker.map B.subtype = B ⊓ centralizer ({x} : Set G) := by
    ext g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, mem_centralizer_singleton_iff.2 ((hker b).1 hb).symm⟩
    · rintro ⟨hgB, hgC⟩
      exact ⟨⟨g, hgB⟩, (hker ⟨g, hgB⟩).2 (mem_centralizer_singleton_iff.1 hgC).symm, rfl⟩
  rw [← hkerE, Subgroup.card_map_of_injective B.subtype_injective]
  have h1 : (2 ^ n) * (2 ^ n) ≤ Nat.card f.ker * Nat.card f.ker := by
    calc (2 ^ n) * (2 ^ n) = Nat.card B := by rw [hcard, two_mul, pow_add]
      _ = Nat.card f.ker * Nat.card f.range := hcardk.symm
      _ ≤ Nat.card f.ker * Nat.card f.ker := Nat.mul_le_mul_left _ hle
  exact Nat.mul_self_le_mul_self_iff.1 h1

section C7


namespace Data.Hyp

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem comm_mul_left_Y {z a b : G} (hz : z ∈ d.Y) (ha : a ∈ d.D₂) (hb : b ∈ d.D₂) :
    (z * a) * b * (z * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : z * (a * b * a⁻¹) = (a * b * a⁻¹) * z :=
    (Data.Hyp.D₂_comm_Y' (d.D₂.mul_mem (d.D₂.mul_mem ha hb) (d.D₂.inv_mem ha)) hz).symm
  calc (z * a) * b * (z * a)⁻¹ * b⁻¹ = (z * (a * b * a⁻¹)) * z⁻¹ * b⁻¹ := by group
    _ = ((a * b * a⁻¹) * z) * z⁻¹ * b⁻¹ := by rw [hc]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem comm_mul_right_Y {z a b : G} (hz : z ∈ d.Y) (ha : a ∈ d.D₂) (hb : b ∈ d.D₂) :
    a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have haz : a * z = z * a := Data.Hyp.D₂_comm_Y' ha hz
  have hc : (a * b * a⁻¹ * b⁻¹) * z = z * (a * b * a⁻¹ * b⁻¹) :=
    Data.Hyp.D₂_comm_Y' (d.D₂.mul_mem (d.D₂.mul_mem (d.D₂.mul_mem ha hb) (d.D₂.inv_mem ha))
      (d.D₂.inv_mem hb)) hz
  calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = (a * z) * b * a⁻¹ * b⁻¹ * z⁻¹ := by group
    _ = (z * a) * b * a⁻¹ * b⁻¹ * z⁻¹ := by rw [haz]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = ((a * b * a⁻¹ * b⁻¹) * z) * z⁻¹ := by rw [hc]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem B_elemAb (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {Γ : Subgroup G} {η : G} (hη : η ∈ Γ) (hΓ : Γ ≤ ModSplit.normDY d.D₂ d.Y)
    (hηfix : ∀ y ∈ d.Y, η * y * η⁻¹ = y → y = 1) :
    (∀ x ∈ ModSplit.liftFixG d.D₂ d.Y Γ, ∀ y ∈ ModSplit.liftFixG d.D₂ d.Y Γ, x * y = y * x) ∧
      ∀ x ∈ ModSplit.liftFixG d.D₂ d.Y Γ, x * x = 1 := by
  have hmem : ∀ {x : G}, x ∈ ModSplit.liftFixG d.D₂ d.Y Γ →
      x ∈ d.D₂ ∧ η * x * η⁻¹ * x⁻¹ ∈ d.Y := fun {x} hx => by
    obtain ⟨h1, h2⟩ := (ModSplit.mem_liftFixG_iff _ _ hΓ).1 hx
    exact ⟨h1, h2 η hη⟩
  constructor
  · intro x₁ hx₁ x₂ hx₂
    obtain ⟨hD₁, hz₁⟩ := hmem hx₁
    obtain ⟨hD₂', hz₂⟩ := hmem hx₂
    obtain ⟨z₁, hz₁def⟩ : ∃ z₁ : G, z₁ = η * x₁ * η⁻¹ * x₁⁻¹ := ⟨_, rfl⟩
    obtain ⟨z₂, hz₂def⟩ : ∃ z₂ : G, z₂ = η * x₂ * η⁻¹ * x₂⁻¹ := ⟨_, rfl⟩
    rw [← hz₁def] at hz₁
    rw [← hz₂def] at hz₂
    have e1 : η * x₁ * η⁻¹ = z₁ * x₁ := by rw [hz₁def]; group
    have e2 : η * x₂ * η⁻¹ = z₂ * x₂ := by rw [hz₂def]; group
    have hc : x₁ * x₂ * x₁⁻¹ * x₂⁻¹ ∈ d.Y := h.D₂_commutator_mem_Y hK hD₁ hD₂'
    have hfixc : η * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * η⁻¹ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ := by
      have e : η * (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * η⁻¹ =
          (η * x₁ * η⁻¹) * (η * x₂ * η⁻¹) * (η * x₁ * η⁻¹)⁻¹ * (η * x₂ * η⁻¹)⁻¹ := by group
      rw [e, e1, e2, comm_mul_left_Y hz₁ hD₁ (d.D₂.mul_mem (h.Y_le_D₂ hz₂) hD₂'),
        comm_mul_right_Y hz₂ hD₁ hD₂']
    have h1 := hηfix _ hc hfixc
    calc x₁ * x₂ = (x₁ * x₂ * x₁⁻¹ * x₂⁻¹) * (x₂ * x₁) := by group
      _ = x₂ * x₁ := by rw [h1, one_mul]
  · intro x hx
    obtain ⟨hD, hz⟩ := hmem hx
    obtain ⟨z, hzdef⟩ : ∃ z : G, z = η * x * η⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hzdef] at hz
    have e1 : η * x * η⁻¹ = z * x := by rw [hzdef]; group
    have hxz : x * z = z * x := Data.Hyp.D₂_comm_Y' hD hz
    have hs : x * x ∈ d.Y := h.D₂_mul_self_mem_Y hK hD
    have hfix2 : η * (x * x) * η⁻¹ = x * x := by
      have e : η * (x * x) * η⁻¹ = (η * x * η⁻¹) * (η * x * η⁻¹) := by group
      rw [e, e1]
      calc (z * x) * (z * x) = z * (x * z) * x := by group
        _ = z * (z * x) * x := by rw [hxz]
        _ = (z * z) * (x * x) := by group
        _ = x * x := by rw [h.Y_sq hz, one_mul]
    exact hηfix _ hs hfix2

theorem Y_le_liftFixG (h : d.Hyp) {Γ : Subgroup G} (hΓ : Γ ≤ ModSplit.normDY d.D₂ d.Y) :
    d.Y ≤ ModSplit.liftFixG d.D₂ d.Y Γ := fun y hy => by
  refine (ModSplit.mem_liftFixG_iff _ _ hΓ).2 ⟨h.Y_le_D₂ hy, fun g hg => ?_⟩
  have hgY : g ∈ normalizer (d.Y : Set G) := ((ModSplit.mem_normDY _ _).1 (hΓ hg)).2
  have := (mem_normalizer_iff.1 hgY y).1 hy
  exact d.Y.mul_mem this (d.Y.inv_mem hy)

theorem D₂_le_normalizer_B (h : d.Hyp) (hK : ∀ v ∈ d.V₂, ∀ m ∈ d.M, m * v * m⁻¹ * v⁻¹ ∈ d.W)
    {Γ : Subgroup G} (hΓ : Γ ≤ ModSplit.normDY d.D₂ d.Y) :
    d.D₂ ≤ normalizer (ModSplit.liftFixG d.D₂ d.Y Γ : Set G) := fun z hz =>
  mem_normalizer_fintype fun b hb => by
    have hbD := ((ModSplit.mem_liftFixG_iff _ _ hΓ).1 hb).1
    have hc : z * b * z⁻¹ * b⁻¹ ∈ d.Y := h.D₂_commutator_mem_Y hK hz hbD
    have e : z * b * z⁻¹ = (z * b * z⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact mul_mem (h.Y_le_liftFixG hΓ hc) hb

theorem le_normalizer_liftFixG (h : d.Hyp) {Γ : Subgroup G}
    (hΓ : Γ ≤ ModSplit.normDY d.D₂ d.Y) :
    Γ ≤ normalizer (ModSplit.liftFixG d.D₂ d.Y Γ : Set G) := fun g hg =>
  mem_normalizer_fintype fun b hb => by
    obtain ⟨hbD, hbf⟩ := (ModSplit.mem_liftFixG_iff _ _ hΓ).1 hb
    have hc := hbf g hg
    have e : g * b * g⁻¹ = (g * b * g⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact mul_mem (h.Y_le_liftFixG hΓ hc) hb

theorem Γ_le_normalizer_liftFixG_of_comm (h : d.Hyp) {Γ₁ Γ₂ : Subgroup G}
    (hΓ₁ : Γ₁ ≤ ModSplit.normDY d.D₂ d.Y) (hΓ₂ : Γ₂ ≤ ModSplit.normDY d.D₂ d.Y)
    (hcomm : ∀ a ∈ Γ₁, ∀ b ∈ Γ₂, a * b = b * a) :
    Γ₁ ≤ normalizer (ModSplit.liftFixG d.D₂ d.Y Γ₂ : Set G) := fun g hg =>
  mem_normalizer_fintype fun b hb => by
    obtain ⟨hbD, hbf⟩ := (ModSplit.mem_liftFixG_iff _ _ hΓ₂).1 hb
    have hgN := (ModSplit.mem_normDY _ _).1 (hΓ₁ hg)
    refine (ModSplit.mem_liftFixG_iff _ _ hΓ₂).2 ⟨?_, fun γ hγ => ?_⟩
    · exact (mem_normalizer_iff.1 hgN.1 b).1 hbD
    · have hγg : γ * g = g * γ := (hcomm g hg γ hγ).symm
      have hc2 : g⁻¹ * γ⁻¹ * g = γ⁻¹ := by
        have : g⁻¹ * γ * g = γ := by rw [mul_assoc, hγg]; group
        calc g⁻¹ * γ⁻¹ * g = (g⁻¹ * γ * g)⁻¹ := by group
          _ = γ⁻¹ := by rw [this]
      have e : γ * (g * b * g⁻¹) * γ⁻¹ * (g * b * g⁻¹)⁻¹ =
          g * (γ * b * γ⁻¹ * b⁻¹) * g⁻¹ := by
        calc γ * (g * b * g⁻¹) * γ⁻¹ * (g * b * g⁻¹)⁻¹
            = (γ * g) * b * (g⁻¹ * γ⁻¹ * g) * b⁻¹ * g⁻¹ := by group
          _ = (g * γ) * b * γ⁻¹ * b⁻¹ * g⁻¹ := by rw [hγg, hc2]
          _ = g * (γ * b * γ⁻¹ * b⁻¹) * g⁻¹ := by group
      rw [e]
      exact (mem_normalizer_iff.1 hgN.2 _).1 (hbf γ hγ)

end Data.Hyp

end C7

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
