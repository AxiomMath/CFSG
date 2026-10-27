module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbP16a

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {Q Y 𝒬 : Subgroup G} {τ ω : G}

theorem card_subgroupOf_of_le (hQ : Q ≤ 𝒬) : Nat.card ↥(Q.subgroupOf 𝒬) = Nat.card Q := by
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ).toEquiv

theorem map_subtype_closure_pair (hτ : τ ∈ 𝒬) (hω : ω ∈ 𝒬) :
    (closure ({(⟨τ, hτ⟩ : ↥𝒬), ⟨ω, hω⟩} : Set ↥𝒬)).map 𝒬.subtype = closure ({τ, ω} : Set G) := by
  rw [MonoidHom.map_closure]
  simp

theorem gen_subgroupOf (hQ : Q ≤ 𝒬) (h𝒬 : 𝒬 = Q ⊔ closure ({τ, ω} : Set G)) (hτ : τ ∈ 𝒬)
    (hω : ω ∈ 𝒬) :
    Q.subgroupOf 𝒬 ⊔ closure ({(⟨τ, hτ⟩ : ↥𝒬), ⟨ω, hω⟩} : Set ↥𝒬) = ⊤ := by
  apply Subgroup.map_injective 𝒬.subtype_injective
  rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hQ,
    map_subtype_closure_pair hτ hω, Subgroup.map_top, Subgroup.range_subtype]
  exact h𝒬.symm

theorem Setting16.of_subgroupOf (h𝒬 : 𝒬 = Q ⊔ closure ({τ, ω} : Set G)) (hτ : τ ∈ 𝒬)
    (hω : ω ∈ 𝒬) (hnorm : ∀ g ∈ 𝒬, ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
    (hY : ∀ a, a ∈ Y ↔ a ∈ Q ∧ a ^ 2 = 1) (hQ64 : Nat.card Q = 64) (hY16 : Nat.card Y = 16)
    (hsq : ∃ a ∈ Q, a ^ 2 ≠ 1) (hτ2 : τ ^ 2 = 1) (hω2 : ω ^ 2 = 1) (hτω : τ * ω = ω * τ)
    (hinv : ∀ a ∈ Q, τ * a * τ⁻¹ = a⁻¹) (homY : ∀ a ∈ Y, ω * a = a * ω)
    (hcomm_om : ∀ q ∈ Q, ω * q * ω⁻¹ * q⁻¹ ∈ Y)
    (hcent_om : ∀ a ∈ Q, ω * a = a * ω → a ∈ Y)
    (hcent_omtau : ∀ a ∈ Q, (ω * τ) * a = a * (ω * τ) → a ∈ Y)
    (hinvol_om : ∀ q ∈ Q, (ω * q) ^ 2 = 1 → q ∈ Y)
    (hinvol_omtau : ∀ q ∈ Q, (ω * τ * q) ^ 2 = 1 → q ∈ Y) :
    Setting16 (Q.subgroupOf 𝒬) (Y.subgroupOf 𝒬) (⟨τ, hτ⟩ : ↥𝒬) ⟨ω, hω⟩ := by
  have hQ : Q ≤ 𝒬 := by rw [h𝒬]; exact le_sup_left
  have hYQ : Y ≤ Q := fun a ha => (hY a).mp ha |>.1
  have hY𝒬 : Y ≤ 𝒬 := hYQ.trans hQ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun n hn g => by
      show ((g : ↥𝒬) * n * (g : ↥𝒬)⁻¹ : G) ∈ Q
      simpa using hnorm (g : G) g.2 (n : G) hn⟩
  · intro a ha b hb
    apply Subtype.ext
    exact hcomm (a : G) ha (b : G) hb
  · intro a
    have := hY (a : G)
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, this]
    constructor
    · rintro ⟨h, h2⟩
      refine ⟨h, ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h2
    · rintro ⟨h, h2⟩
      refine ⟨h, ?_⟩
      have h2' := congrArg Subtype.val h2
      simpa [Subgroup.coe_pow] using h2'
  · rw [card_subgroupOf_of_le hQ, hQ64]
  · rw [card_subgroupOf_of_le hY𝒬, hY16]
  · obtain ⟨a, ha, h2⟩ := hsq
    refine ⟨⟨a, hQ ha⟩, ha, ?_⟩
    intro h
    exact h2 (by simpa [Subgroup.coe_pow] using congrArg Subtype.val h)
  · exact Subtype.ext (by simpa using hτ2)
  · exact Subtype.ext (by simpa using hω2)
  · exact Subtype.ext (by simpa using hτω)
  · intro a ha
    apply Subtype.ext
    simpa using hinv (a : G) ha
  · intro a ha
    apply Subtype.ext
    simpa using homY (a : G) ha
  · intro q hq
    show (((⟨ω, hω⟩ : ↥𝒬) * q * (⟨ω, hω⟩ : ↥𝒬)⁻¹ * q⁻¹ : ↥𝒬) : G) ∈ Y
    simpa using hcomm_om (q : G) hq
  · intro a ha h
    show (a : G) ∈ Y
    exact hcent_om (a : G) ha (by simpa using congrArg Subtype.val h)
  · intro a ha h
    show (a : G) ∈ Y
    exact hcent_omtau (a : G) ha (by simpa using congrArg Subtype.val h)
  · intro q hq h
    show (q : G) ∈ Y
    exact hinvol_om (q : G) hq (by simpa using congrArg Subtype.val h)
  · intro q hq h
    show (q : G) ∈ Y
    exact hinvol_omtau (q : G) hq (by simpa using congrArg Subtype.val h)
  · exact gen_subgroupOf hQ h𝒬 hτ hω

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
