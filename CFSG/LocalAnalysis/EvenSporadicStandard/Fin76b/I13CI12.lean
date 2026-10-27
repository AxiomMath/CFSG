module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13CI11

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

@[expose] def E64Statement : Prop :=
  ∀ {b₁ b₂ : G}, b₁ ∈ B → b₂ ∈ B → b₁ * b₁ = 1 → b₂ * b₂ = 1 → b₁ * b₂ = b₂ * b₁ → b₁ ≠ 1 →
    b₂ ≠ 1 → b₁ ≠ b₂ → ∀ {q b : G}, q ∈ c.Qs → (b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) →
      (q * b) * (q * b) = 1 →
      ∃ A : Subgroup G, A ≤ centralizer ({q * b} : Set G) ∧ (∀ a ∈ A, a * a = 1) ∧
        64 ≤ Nat.card A

@[expose] def RankStatement (z : G) : Prop :=
  ∀ {u : G}, (∃ g : G, u = g * z * g⁻¹) → ∀ {A : Subgroup G}, A ≤ centralizer ({u} : Set G) →
    (∀ a ∈ A, a * a = 1) → Nat.card A ≤ 32

variable {c} {π : MulAut ↥E →* Equiv.Perm (Fin 5)} {Rs : Subgroup G}

namespace IsRs

variable (hR : c.IsRs Rs) (hπ : EPi E π)
  (hI : ∀ a b : MulAut ↥E, (a, b) ∈ c.rho.range ↔
    π a ∈ alternatingGroup (Fin 5) ∧ π b = π a)

include hR

theorem card_pgroup_N1_le {P : Subgroup G} (hP : IsPGroup 2 P) (hPN : P ≤ c.N1) :
    Nat.card P ≤ Nat.card ↥(Rs ⊓ c.N1) := by
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card c.N1 := Subgroup.card_dvd_of_le hPN
  have h1 := Subgroup.relIndex_mul_card (H := Rs ⊓ c.N1) (K := c.N1)
  rw [inf_eq_left.2 (inf_le_right : Rs ⊓ c.N1 ≤ c.N1)] at h1
  have hodd : Odd ((Rs ⊓ c.N1).relIndex c.N1) := Nat.odd_iff.2 (by
    have := hR.R_odd
    omega)
  have hcop : Nat.Coprime (2 ^ a) ((Rs ⊓ c.N1).relIndex c.N1) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hodd)
  rw [ha, ← h1] at hdvd
  have := hcop.dvd_of_dvd_mul_left hdvd
  rw [ha]
  exact Nat.le_of_dvd Nat.card_pos this

include hπ hI in
theorem not_conj_z_of_mem_R0 (hE64 : c.E64Statement) (hrank : RankStatement z) {y : G}
    (hy : y ∈ Rs ⊓ c.N1) (hyz : ∃ g : G, y = g * z * g⁻¹) : False := by
  by_cases hyQ : y ∈ c.Qs
  · exact c.not_conj_z_of_mem_Qs hyQ hyz
  obtain ⟨b₁, hb₁, b₂, hb₂, h11, h22, h12, h1, h2, h3⟩ := c.exists_klein_B
  have hQB_p := c.QB1_pgroup hb₁ hb₂ h11 h22 h12
  have hQB_N := c.QB1_le_N1 hb₁ hb₂
  have hQB_card := c.card_QB1_ge hb₁ hb₂ h22 h1 h2 h3
  have hR0max := max_of_odd_relIndex hR.R_pgroup hR.R_odd
  have hQBmax : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ c.N1 → c.QB1 b₁ b₂ ≤ P →
      P ≤ c.QB1 b₁ b₂ := by
    intro P hP hPN hle
    have e1 := hR.card_pgroup_N1_le hP hPN
    have e2 := hR.card_R0_le hπ hI
    have heq : c.QB1 b₁ b₂ = P := Subgroup.eq_of_le_of_card_ge hle (by omega)
    rw [heq]
  obtain ⟨g, hgN, hg⟩ := sylow_conj hQB_N (inf_le_right : Rs ⊓ c.N1 ≤ c.N1) hQB_p
    hR.R_pgroup hQBmax hR0max
  have hy' : g⁻¹ * y * g ∈ c.QB1 b₁ b₂ := (hg y).1 hy
  obtain ⟨h, hh⟩ := hyz
  have hconj : ∃ k : G, g⁻¹ * y * g = k * z * k⁻¹ := ⟨g⁻¹ * h, by rw [hh]; group⟩
  have hsq : (g⁻¹ * y * g) * (g⁻¹ * y * g) = 1 := by
    obtain ⟨k, hk⟩ := hconj
    rw [hk]
    calc k * z * k⁻¹ * (k * z * k⁻¹) = k * (z * z) * k⁻¹ := by group
      _ = 1 := by rw [c.h.z_sq]; group
  have hnotQ : g⁻¹ * y * g ∉ c.Qs := by
    intro hq
    apply hyQ
    have := (c.mem_Nc.1 (c.N1_le_Nc hgN) _).1 hq
    have e : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
    rwa [e] at this
  obtain ⟨q, hq, b, hb, hx'⟩ := c.mem_QB1 hb₁ hb₂ h11 h22 h12 hy'
  have hb1 : b ≠ 1 := by
    intro hb1
    apply hnotQ
    rw [hx', hb1, mul_one]
    exact hq
  have hb' : b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂ := by
    rcases hb with h | h | h | h
    · exact absurd h hb1
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hsq' : (q * b) * (q * b) = 1 := by rw [← hx']; exact hsq
  obtain ⟨A, hAc, hA2, hA64⟩ := hE64 hb₁ hb₂ h11 h22 h12 h1 h2 h3 hq hb' hsq'
  have hconj' : ∃ k : G, q * b = k * z * k⁻¹ := by rw [← hx']; exact hconj
  have := hrank hconj' hAc hA2
  omega

end IsRs

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
