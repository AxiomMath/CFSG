module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CSetup

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup

variable {C : Type} [Group C] [Finite C] {c : CInv C} {R : Subgroup C}

theorem bar_R_sq (hR : RData c R) : ∀ x ∈ c.bar R, x ^ 2 = 1 := by
  intro x hx
  change x ∈ R.map c.qmap at hx
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
  rw [← map_pow]
  exact c.qmap_eq_one_iff.mpr (hR.sq r hr)

theorem bar_R_comm (hR : RData c R) : ∀ a ∈ c.bar R, ∀ b ∈ c.bar R, a * b = b * a := by
  intro a ha b hb
  change a ∈ R.map c.qmap at ha
  change b ∈ R.map c.qmap at hb
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hb
  have h1 : c.qmap (r * s) * (c.qmap (s * r))⁻¹ = 1 := by
    rw [← map_inv, ← map_mul]
    rw [show r * s * (s * r)⁻¹ = r * s * r⁻¹ * s⁻¹ by group]
    exact c.qmap_eq_one_iff.mpr (hR.comm r hr s hs)
  have h2 : c.qmap (r * s) = c.qmap (s * r) := mul_inv_eq_one.mp h1
  calc c.qmap r * c.qmap s = c.qmap (r * s) := (map_mul c.qmap r s).symm
    _ = c.qmap (s * r) := h2
    _ = c.qmap s * c.qmap r := map_mul c.qmap s r

theorem bar_R_card (hR : RData c R) : Nat.card ↥(c.bar R) = 2 ^ 12 := by
  have hle : zpowers c.z ≤ R := Subgroup.zpowers_le.mpr hR.z_mem
  have h := c.card_bar hle
  rw [hR.card] at h
  norm_num at h ⊢
  omega

theorem bar_R_ne_bot (hR : RData c R) : c.bar R ≠ ⊥ := by
  intro h
  have hc := bar_R_card hR
  rw [h, Subgroup.card_bot] at hc
  norm_num at hc

theorem bar_R_cent (hR : RData c R) : centralizer (c.bar R : Set c.Qt) ≤ c.bar R := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff] at hb
  obtain ⟨g, rfl⟩ := c.qmap_surjective b
  change c.qmap g ∈ R.map c.qmap
  refine Subgroup.mem_map.mpr ⟨g, ?_, rfl⟩
  apply hR.self
  intro r hr
  apply c.qmap_eq_one_iff.mp
  have hcomm : c.qmap r * c.qmap g = c.qmap g * c.qmap r :=
    hb (c.qmap r) (Subgroup.mem_map.mpr ⟨r, hr, rfl⟩)
  have h1 : c.qmap (g * r * g⁻¹ * r⁻¹) = 1 := by
    rw [show c.qmap (g * r * g⁻¹ * r⁻¹) =
      c.qmap g * c.qmap r * (c.qmap g)⁻¹ * (c.qmap r)⁻¹ by simp only [map_mul, map_inv]]
    rw [← hcomm]
    group
  exact h1

theorem bar_R_irr (hR : RData c R) (U : Subgroup c.Qt) (hU : U ≤ c.bar R)
    (hn : ∀ x ∈ normalizer (c.bar R : Set c.Qt), ∀ u ∈ U, x * u * x⁻¹ ∈ U) :
    U = ⊥ ∨ U = c.bar R := by
  have hle : zpowers c.z ≤ R := Subgroup.zpowers_le.mpr hR.z_mem
  have hz : zpowers c.z ≤ U.comap c.qmap := by
    rw [Subgroup.zpowers_le, Subgroup.mem_comap]
    rw [c.qmap_eq_one_iff.mpr (Subgroup.mem_zpowers c.z)]
    exact U.one_mem
  have hU'le : U.comap c.qmap ≤ R := by
    intro u hu
    exact (c.qmap_mem_bar_iff hle).mp (hU (Subgroup.mem_comap.mp hu))
  have hInv : ∀ x ∈ normalizer (R : Set C), ∀ u ∈ U.comap c.qmap, x * u * x⁻¹ ∈ U.comap c.qmap := by
    intro x hx u hu
    rw [Subgroup.mem_comap] at hu ⊢
    have hxN : c.qmap x ∈ normalizer (c.bar R : Set c.Qt) := by
      rw [Subgroup.mem_set_normalizer_iff]
      intro y
      constructor
      · intro hy
        change y ∈ R.map c.qmap at hy
        obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
        exact Subgroup.mem_map.mpr ⟨x * r * x⁻¹,
          (Subgroup.mem_set_normalizer_iff.mp hx r).mp hr, by simp only [map_mul, map_inv]⟩
      · intro hy
        change c.qmap x * y * (c.qmap x)⁻¹ ∈ R.map c.qmap at hy
        obtain ⟨s, hs, hs_eq⟩ := Subgroup.mem_map.mp hy
        refine Subgroup.mem_map.mpr ⟨x⁻¹ * s * x, ?_, ?_⟩
        · exact (Subgroup.mem_set_normalizer_iff''.mp hx s).mp hs
        · rw [map_mul, map_mul, map_inv, hs_eq]
          group
    rw [show c.qmap (x * u * x⁻¹) = c.qmap x * c.qmap u * (c.qmap x)⁻¹ by
      simp only [map_mul, map_inv]]
    exact hn (c.qmap x) hxN (c.qmap u) hu
  rcases hR.irr (U.comap c.qmap) hz hU'le hInv with h | h
  · left
    rw [← c.bar_comap U, h]
    change (zpowers c.z).map c.qmap = ⊥
    exact (Subgroup.map_eq_bot_iff (zpowers c.z)).mpr (le_of_eq c.ker_qmap.symm)
  · right
    rw [← c.bar_comap U, h]

theorem bar_R_isPGroup (hR : RData c R) : IsPGroup 2 ↥(c.bar R) := by
  exact c.isPGroup_bar (IsPGroup.of_card (p := 2) (n := 13) hR.card)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
