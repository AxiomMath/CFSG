module

public import CFSG.ClassicalInvolution.Asc77.WP3Hyp51
public import CFSG.ClassicalInvolution.Asc77.AscT8Layer

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S8

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance

section Components

variable {G : Type} [Group G] [Finite G]

theorem modOdd_normal {c : G} {Y : Subgroup G} (hYn : ∀ n ∈ Subgroup.centralizer ({c} : Set G),
    conjSub n Y = Y) : (modOdd c Y).Normal := by
  have h1 : (Y.subgroupOf (Subgroup.centralizer ({c} : Set G))).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    have h2 : (g : G) * (m : G) * (g : G)⁻¹ ∈ conjSub (g : G) Y := conj_mem_conjSub hm
    rw [hYn g g.2] at h2
    exact h2
  exact h1.map (oddQuotMk c) (QuotientGroup.mk'_surjective _)

theorem oddQuotMk_not_mem_modOdd_zpowers {B : Subgroup G} {c b : G} (hB : ∀ x ∈ B, x * x = 1)
    (hcB : c ∈ B) (hbB : b ∈ B) (hbc : b ∉ Subgroup.zpowers c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨b, hbC⟩ ∉ modOdd c (Subgroup.zpowers c) := by
  rintro ⟨k, hk, hkeq⟩
  have hkB : (k : G) ∈ B := (Subgroup.zpowers_le.mpr hcB) hk
  have h1 : oddQuotMk c (⟨b, hbC⟩⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, hkeq, inv_mul_cancel]
  have h2 : (⟨b, hbC⟩⁻¹ * k : ↥(Subgroup.centralizer ({c} : Set G))) *
      (⟨b, hbC⟩⁻¹ * k) = 1 := by
    apply Subtype.ext
    have hbk : b⁻¹ * (k : G) ∈ B := B.mul_mem (B.inv_mem hbB) hkB
    simpa using hB _ hbk
  have h3 := eq_one_of_oddQuotMk_eq_one h2 h1
  apply hbc
  have h4 : b⁻¹ * (k : G) = 1 := congrArg Subtype.val h3
  have h5 : (k : G) = b := by
    calc (k : G) = b * (b⁻¹ * (k : G)) := by group
      _ = b := by rw [h4, mul_one]
  rw [← h5]
  exact hk

theorem commute_of_isComponent_of_zStar {c b : G} {Y : Subgroup G}
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hYn : ∀ n ∈ Subgroup.centralizer ({c} : Set G), conjSub n Y = Y) (hbY : b ∈ Y)
    (hZ : ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Y) {L : Subgroup (OddQuot c)}
    (hL : CFSG.IsComponent L) {y : OddQuot c} (hy : y ∈ L) :
    oddQuotMk c ⟨b, hbC⟩ * y = y * oddQuotMk c ⟨b, hbC⟩ := by
  have hN := modOdd_normal hYn
  have hbN : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c Y := oddQuotMk_mem_modOdd hbY hbC
  rcases CFSG.LocalCores.component_normal_subgroup hL hN with hle | hcomm
  · obtain ⟨k, hkY, rfl⟩ := hle hy
    have hmem : b * (k : G) * b⁻¹ * (k : G)⁻¹ ∈ oddCoreOf (Subgroup.centralizer ({c} : Set G)) :=
      T8.oddCoreOf_le_oddCoreOf_of_normalized hYC hYn (hZ _ hkY)
    obtain ⟨hmemC, hmemO⟩ := mem_oddCoreOf_iff.mp hmem
    have h1 : oddQuotMk c (⟨b, hbC⟩ * k * ⟨b, hbC⟩⁻¹ * k⁻¹) = 1 :=
      oddQuotMk_eq_one_iff.mpr hmemO
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp (by
      rw [commutatorElement_def]
      exact h1))
  · have h1 := Subgroup.commutator_mem_commutator hy hbN
    rw [hcomm, Subgroup.mem_bot] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm

theorem not_movedByAll_of_zStar {B Y : Subgroup G} {c b : G} (hB : ∀ x ∈ B, x * x = 1)
    (hcB : c ∈ B) (hbB : b ∈ B) (hbc : b ∉ Subgroup.zpowers c)
    (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hYn : ∀ n ∈ Subgroup.centralizer ({c} : Set G), conjSub n Y = Y) (hbY : b ∈ Y)
    (hZ : ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Y) {L : Subgroup (OddQuot c)}
    (hL : CFSG.IsComponent L) : ¬ MovedByAll B c L := by
  intro hmov
  obtain ⟨y, hy, hne⟩ := hmov (oddQuotMk c ⟨b, hbC⟩)
    (oddQuotMk_mem_modOdd hbB hbC) (oddQuotMk_not_mem_modOdd_zpowers hB hcB hbB hbc hbC)
  exact hne (commute_of_isComponent_of_zStar hbC hYC hYn hbY hZ hL hy)

theorem hyp51At_of_zStar {B Y : Subgroup G} {c b : G} (hB : ∀ x ∈ B, x * x = 1) (hcB : c ∈ B)
    (hbB : b ∈ B) (hbc : b ∉ Subgroup.zpowers c) (hbC : b ∈ Subgroup.centralizer ({c} : Set G))
    (hYC : Y ≤ Subgroup.centralizer ({c} : Set G))
    (hYn : ∀ n ∈ Subgroup.centralizer ({c} : Set G), conjSub n Y = Y) (hbY : b ∈ Y)
    (hZ : ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Y) : Hyp51At B c := by
  have hno : ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → ¬ MovedByAll B c L := fun L hL =>
    not_movedByAll_of_zStar hB hcB hbB hbc hbC hYC hYn hbY hZ hL
  exact ⟨fun L₁ _ h₁ _ m₁ _ => absurd m₁ (hno L₁ h₁), fun L hL hm => absurd hm (hno L hL)⟩

theorem hyp51_of_zStar {B : Subgroup G} (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    (h : ∀ c ∈ B, c ≠ 1 → ∃ b ∈ B, b ∉ Subgroup.zpowers c ∧ ∃ Y : Subgroup G, b ∈ Y ∧
      Y ≤ Subgroup.centralizer ({c} : Set G) ∧
      (∀ n ∈ Subgroup.centralizer ({c} : Set G), conjSub n Y = Y) ∧
      ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ oddCoreOf Y) : Hyp51 B := by
  have hB2 : ∀ x ∈ B, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hB.2 x hx
  refine ⟨hB, hB8, fun c hcB hc1 => ?_⟩
  obtain ⟨b, hbB, hbc, Y, hbY, hYC, hYn, hZ⟩ := h c hcB hc1
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact DeltaClosure.comm_of_mem_elemAbelian hB hbB hcB
  exact hyp51At_of_zStar hB2 hcB hbB hbc hbC hYC hYn hbY hZ

end Components

end CFSG.ClassicalInvolution.Hat2A7S8
