module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.Interfaces

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

section Abstract

variable {X : Type*} [Group X] {O : Subgroup X} [O.Normal]

theorem card_map_centralizer {ρ τ : X} (hρ3 : orderOf ρ = 3) (hρO : ρ ∈ O)
    (hρτ : ρ * τ = τ * ρ) (hτ : ∀ x ∈ O, x * τ = τ * x → x ∈ zpowers ρ) {n : ℕ}
    (hn : Nat.card (centralizer ({τ} : Set X)) = 3 * n) :
    Nat.card ((centralizer ({τ} : Set X)).map (QuotientGroup.mk' O)) = n := by
  have h1 := card_map_mk_mul_card_inf O (centralizer ({τ} : Set X))
  have h2 : O ⊓ centralizer ({τ} : Set X) = zpowers ρ := by
    apply le_antisymm
    · intro x hx
      exact hτ x hx.1 (mem_centralizer_singleton_iff.1 hx.2)
    · intro x hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      refine ⟨zpow_mem hρO k, mem_centralizer_singleton_iff.2 ?_⟩
      exact (Commute.zpow_left (show Commute ρ τ from hρτ) k).eq
  rw [h2, Nat.card_zpowers, hρ3, hn] at h1
  omega

theorem map_centralizer_eq_top {τ : X} (hτ : τ * τ = 1) (hodd : ∀ x ∈ O, Odd (orderOf x))
    (hc : (QuotientGroup.mk τ : X ⧸ O) ∈ center (X ⧸ O)) :
    (centralizer ({τ} : Set X)).map (QuotientGroup.mk' O) = ⊤ := by
  rw [eq_top_iff]
  intro q _
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
  have hcomm : (c : X ⧸ O) * (τ : X ⧸ O) = (τ : X ⧸ O) * c := mem_center_iff.1 hc c
  have hn : c * τ * c⁻¹ * τ⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    calc (c : X ⧸ O) * (τ : X ⧸ O) * (c : X ⧸ O)⁻¹ * (τ : X ⧸ O)⁻¹
        = ((τ : X ⧸ O) * c) * (c : X ⧸ O)⁻¹ * (τ : X ⧸ O)⁻¹ := by rw [hcomm]
      _ = 1 := by group
  obtain ⟨s, hsO, hs⟩ := exists_lift hτ hodd hn
  refine ⟨s⁻¹ * c, hs, ?_⟩
  have hs1 : (QuotientGroup.mk s : X ⧸ O) = 1 := (QuotientGroup.eq_one_iff s).2 hsO
  simp [hs1]

theorem noncentral_aux [Finite X] {ρ τ₁ τ₂ : X} (hodd : ∀ x ∈ O, Odd (orderOf x))
    (hρ3 : orderOf ρ = 3) (hρO : ρ ∈ O) (hρ₁ : ρ * τ₁ = τ₁ * ρ) (hρ₂ : ρ * τ₂ = τ₂ * ρ)
    (hτ₁ : τ₁ * τ₁ = 1)
    (hO₁ : ∀ x ∈ O, x * τ₁ = τ₁ * x → x ∈ zpowers ρ)
    (hO₂ : ∀ x ∈ O, x * τ₂ = τ₂ * x → x ∈ zpowers ρ) {n : ℕ}
    (hn₁ : Nat.card (centralizer ({τ₁} : Set X)) = 3 * n)
    (hn₂ : Nat.card (centralizer ({τ₂} : Set X)) = 3 * n)
    (hc : (QuotientGroup.mk τ₁ : X ⧸ O) ∈ center (X ⧸ O)) :
    (QuotientGroup.mk τ₂ : X ⧸ O) ∈ center (X ⧸ O) := by
  have h1 := card_map_centralizer hρ3 hρO hρ₁ hO₁ hn₁
  have h2 := card_map_centralizer hρ3 hρO hρ₂ hO₂ hn₂
  rw [map_centralizer_eq_top hτ₁ hodd hc, Subgroup.card_top] at h1
  have h3 : (centralizer ({τ₂} : Set X)).map (QuotientGroup.mk' O) = ⊤ :=
    Subgroup.eq_top_of_card_eq _ (by rw [h2, h1])
  rw [mem_center_iff]
  intro q
  have hq : q ∈ (centralizer ({τ₂} : Set X)).map (QuotientGroup.mk' O) := by
    rw [h3]; trivial
  obtain ⟨x, hx, rfl⟩ := hq
  have hx' : x * τ₂ = τ₂ * x := mem_centralizer_singleton_iff.1 hx
  show (x : X ⧸ O) * (τ₂ : X ⧸ O) = (τ₂ : X ⧸ O) * x
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx']

end Abstract

theorem false_of_central_mod {Y : Type} [Group Y] (h3 : RuThreeFacts Y) (hZ : center M10 = ⊥)
    {r : Y} (hr3 : orderOf r = 3) (v : ↥(centralizer ({r} : Set Y))) (hv2 : orderOf (v : Y) = 2)
    (hcomm : ∀ m : ↥(centralizer ({r} : Set Y)),
      ((v * m * v⁻¹ * m⁻¹ : ↥(centralizer ({r} : Set Y))) : Y) ∈ zpowers r) : False := by
  obtain ⟨φ, hφs, hφk⟩ := h3.quot r hr3
  have hv1 : φ v = 1 := by
    have hcen : φ v ∈ center M10 := by
      rw [mem_center_iff]
      intro q
      obtain ⟨m, rfl⟩ := hφs q
      have h1 : v * m * v⁻¹ * m⁻¹ ∈ φ.ker := by
        rw [hφk]
        exact Subgroup.mem_subgroupOf.2 (hcomm m)
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : φ v * φ m = φ m * φ v := by
        calc φ v * φ m = (φ v * φ m * (φ v)⁻¹ * (φ m)⁻¹) * (φ m * φ v) := by group
          _ = φ m * φ v := by rw [h1, one_mul]
      exact h2.symm
    rw [hZ] at hcen
    exact hcen
  have hvk : v ∈ φ.ker := hv1
  rw [hφk] at hvk
  have h2 : orderOf (v : Y) ∣ orderOf r :=
    orderOf_dvd_of_mem_zpowers (Subgroup.mem_subgroupOf.1 hvk)
  rw [hv2, hr3] at h2
  omega

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
