module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6bData

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

open Subgroup CFSG.Sporadic.Schreier.Tits CFSG.LocalAnalysis.EvenBN.Tits CFSG.Open

section RkAbs

open commutatorElement

private theorem p6b_eq_one_or_eq_of_mem_zpowers {Γ : Type*} [Group Γ] {s : Γ} (hs : s * s = 1)
    {g : Γ} (hg : g ∈ zpowers s) : g = 1 ∨ g = s := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hs, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hs, one_zpow, one_mul]

variable {V : Type*} [CommGroup V] [Fact (∀ a : V, a * a = 1)]
variable (Z : Subgroup V) (B : Subgroup (MulAut V)) (hB : ∀ σ ∈ B, Z.map (σ : V →* V) = Z)

theorem nu_quotRep_cls (σ : ↥B) (w : V) :
    I21L.nu (quotRep Z B hB σ) (cls Z w) = cls Z ((σ : MulAut V) w * w⁻¹) := by
  show quotRep Z B hB σ (cls Z w) - cls Z w = _
  rw [quotRep_cls, cls_mul, cls_inv, sub_eq_add_neg]

variable [Finite V] {Γ : Type*} [Group Γ] (ι : V →* Γ)

theorem two_pow_rk_quotRep (hι : Function.Injective ι) (σ : ↥B) {s : Γ} (hs : s * s = 1)
    (hσ : ∀ v : V, ι ((σ : MulAut V) v) = s * ι v * s⁻¹) :
    2 ^ I21L.rk (quotRep Z B hB σ) = (Z.map ι).relIndex (⁅ι.range, zpowers s⁆ ⊔ Z.map ι) := by
  set q := quotRep Z B hB σ with hq
  set U : AddSubgroup (Additive (V ⧸ Z)) := (LinearMap.range (I21L.nu q)).toAddSubgroup with hU
  set R : Subgroup V := liftAdd Z U with hR
  have h1 : 2 ^ I21L.rk q = Z.relIndex R := by
    rw [hR, relIndex_liftAdd Z U]
    exact (card_toAddSubgroup_eq (LinearMap.range (I21L.nu q)) rfl).symm
  have hmem : ∀ w : V, (σ : MulAut V) w * w⁻¹ ∈ R := fun w =>
    ⟨cls Z w, nu_quotRep_cls Z B hB σ w⟩
  have hmem' : ∀ v ∈ R, ∃ w : V, ∃ z ∈ Z, v = (σ : MulAut V) w * w⁻¹ * z := by
    intro v hv
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hv
    obtain ⟨w, rfl⟩ := cls_surjective Z y
    rw [nu_quotRep_cls] at hy
    refine ⟨w, _, (cls_eq_iff Z _ _).1 hy, ?_⟩
    group
  have key : R.map ι = ⁅ι.range, zpowers s⁆ ⊔ Z.map ι := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      obtain ⟨w, z, hz, rfl⟩ := hmem' v hv
      rw [map_mul]
      refine mul_mem (mem_sup_left ?_) (mem_sup_right (Subgroup.mem_map_of_mem ι hz))
      have e : ι ((σ : MulAut V) w * w⁻¹) = ⁅ι w, s⁆⁻¹ := by
        rw [map_mul, map_inv, hσ, commutatorElement_def]
        group
      rw [e]
      exact inv_mem (commutator_mem_commutator ⟨w, rfl⟩ (mem_zpowers s))
    · refine sup_le ?_ (Subgroup.map_mono (le_liftAdd Z U))
      rw [commutator_le]
      rintro _ ⟨u, rfl⟩ g hg
      rcases p6b_eq_one_or_eq_of_mem_zpowers hs hg with rfl | rfl
      · simp
      · refine ⟨((σ : MulAut V) u * u⁻¹)⁻¹, inv_mem (hmem u), ?_⟩
        rw [map_inv, map_mul, map_inv, hσ, commutatorElement_def]
        group
  rw [h1, ← relIndex_map_map_of_injective Z R hι, key]

end RkAbs

section Rk

variable {G : Type} [Group G] [Finite G] {d : Data G} {z₀ : G}

variable [Fact (∀ a b : ↥d.s56V, a * b = b * a)] [Fact (∀ a : ↥d.s56V, a * a = 1)]

theorem rk_quotRep_eq_three (hZV : Zz d z₀ ≤ d.s56V)
    (hZH : ∀ g ∈ Hg d, ∀ y ∈ Zz d z₀, g * y * g⁻¹ ∈ Zz d z₀)
    {s : G} (hs : s ∈ Hg d) (hss : s * s = 1)
    (hr : (Zz d z₀).relIndex (⁅d.s56V, zpowers s⁆ ⊔ Zz d z₀) = 8) :
    CFSG.LocalAnalysis.EvenBN.Tits.I21L.rk
      (quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) (starB d s hs)) = 3 := by
  have hZ : (Zv d z₀).map d.s56V.subtype = Zz d z₀ := Subgroup.map_subgroupOf_eq_of_le hZV
  have h := two_pow_rk_quotRep (Zv d z₀) (Hs d) (map_Zv_eq hZH) d.s56V.subtype
    d.s56V.subtype_injective (starB d s hs) hss (fun v => star_apply_val hs v)
  rw [Subgroup.range_subtype, hZ, hr] at h
  exact Nat.pow_right_injective (le_refl 2) (h.trans (by norm_num : 8 = 2 ^ 3))

end Rk

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
