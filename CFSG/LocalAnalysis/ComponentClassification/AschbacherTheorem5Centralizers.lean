module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Preimages

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.ComponentClassification.AschbacherTheorem5

theorem mem_core_iff {G : Type*} [Group G] (D : Subgroup G) (d : D) :
    d.val ∈ aschbacherThm5Core D ↔ d ∈ aschbacherThm5OddCore D :=
  Subgroup.mem_map_iff_mem D.subtype_injective

theorem centralizes_of_commutes {G : Type*} [Group G] (O A : Subgroup G) (y : G)
    (hcomm : ∀ a ∈ A, y * a = a * y) : aschbacherThm5Centralizes O A y := by
  intro a ha
  have hone : y⁻¹ * a⁻¹ * y * a = 1 := by
    rw [show y⁻¹ * a⁻¹ = (a * y)⁻¹ by group, ← hcomm a ha]
    group
  rw [hone]
  exact O.one_mem

theorem centralizes_iff_quotient_commutes {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) (y : D) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D Abar) y.val ↔
      ∀ a ∈ Abar, QuotientGroup.mk' (aschbacherThm5OddCore D) y * a =
        a * QuotientGroup.mk' (aschbacherThm5OddCore D) y := by
  let quotient := QuotientGroup.mk' (aschbacherThm5OddCore D)
  have hlocal : ∀ a : D,
      y.val⁻¹ * a.val⁻¹ * y.val * a.val ∈ aschbacherThm5Core D ↔
        quotient y * quotient a = quotient a * quotient y := by
    intro a
    have hmem := mem_core_iff D (y⁻¹ * a⁻¹ * y * a)
    change y.val⁻¹ * a.val⁻¹ * y.val * a.val ∈ aschbacherThm5Core D ↔
      y⁻¹ * a⁻¹ * y * a ∈ aschbacherThm5OddCore D at hmem
    rw [hmem, ← QuotientGroup.eq_one_iff]
    change quotient (y⁻¹ * a⁻¹ * y * a) = 1 ↔ _
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hcomm : (quotient y)⁻¹ * (quotient a)⁻¹ * quotient y * quotient a =
        ⁅(quotient y)⁻¹, (quotient a)⁻¹⁆ := by
      simp only [commutatorElement_def, inv_inv]
    rw [hcomm, commutatorElement_eq_one_iff_mul_comm]
    constructor
    · intro heq
      have hinverse := congrArg Inv.inv heq
      simpa only [mul_inv_rev, inv_inv] using hinverse.symm
    · intro heq
      have hinverse := congrArg Inv.inv heq
      simpa only [mul_inv_rev] using hinverse.symm
  constructor
  · intro hcentral a ha
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherThm5OddCore D) a
    exact (hlocal lift).mp (hcentral lift.val ((mem_preimage_iff D Abar lift).mpr ha))
  · intro hcentral a ha
    let lift : D := ⟨a, preimage_le D Abar ha⟩
    exact (hlocal lift).mpr
      (hcentral (quotient lift) ((mem_preimage_iff D Abar lift).mp ha))

theorem cross_factor_centralizes {G Index : Type*} [Group G] (D : Subgroup G)
    (Abar : Index → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ Abar i, ∀ y ∈ Abar j, x * y = y * x)
    (i j : Index) (hij : i ≠ j) (y : G) (hy : y ∈ aschbacherThm5Preimage D (Abar j)) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) y := by
  let lift : D := ⟨y, preimage_le D (Abar j) hy⟩
  apply (centralizes_iff_quotient_commutes D (Abar i) lift).mpr
  intro a ha
  exact (hcomm i j hij a ha _ ((mem_preimage_iff D (Abar j) lift).mp hy)).symm

theorem centralizes_iff_central_in_factor {G : Type*} [Group G] (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D))
    (a : D) (ha : a.val ∈ aschbacherThm5Preimage D Abar) :
    aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D Abar) a.val ↔
      (⟨QuotientGroup.mk' (aschbacherThm5OddCore D) a,
        (mem_preimage_iff D Abar a).mp ha⟩ : Abar) ∈ Subgroup.center Abar := by
  rw [centralizes_iff_quotient_commutes, Subgroup.mem_center_iff]
  constructor
  · intro hcomm b
    exact Subtype.ext ((hcomm b.val b.property).symm)
  · intro hcomm b hb
    exact (congrArg Subtype.val (hcomm (⟨b, hb⟩ : Abar))).symm

theorem centralizes_transport {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (O A : Subgroup G) (y : G) (hcentral : aschbacherThm5Centralizes O A y) :
    aschbacherThm5Centralizes (O.map e.toMonoidHom) (A.map e.toMonoidHom) (e y) := by
  rintro a ⟨lift, hlift, rfl⟩
  have hmap := Subgroup.mem_map_of_mem e.toMonoidHom (hcentral lift hlift)
  simpa only [map_mul, map_inv, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] using hmap

theorem centralizer_le_normalizer_of_control {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) → g ∈ Subgroup.normalizer (D : Set G))
    (i : Fin r) (t : G) (htwo : ∃ k : ℕ, t ^ (2 ^ k) = 1) (hnoncentral : t ∉ Subgroup.center G)
    (hcentral : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) t) :
    Subgroup.centralizer {t} ≤ Subgroup.normalizer (D : Set G) := by
  intro g hg
  apply hi i i t g htwo hnoncentral hcentral
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hfixed : g⁻¹ * t * g = t := by
    rw [mul_assoc, ← hcomm]
    group
  rwa [hfixed]

theorem fusion_exclusion_of_control {G : Type*} [Group G]
    (D : Subgroup G) (r : ℕ) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (hi : ∀ (i j : Fin r) (t g : G), (∃ k : ℕ, t ^ (2 ^ k) = 1) → t ∉ Subgroup.center G →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) t →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar j))
        (g⁻¹ * t * g) → g ∈ Subgroup.normalizer (D : Set G))
    (i j : Fin r) (t g : G) (htwo : ∃ k : ℕ, t ^ (2 ^ k) = 1)
    (hnoncentral : t ∉ Subgroup.center G)
    (hcentral : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar i)) t) (hg : g ∉ Subgroup.normalizer (D : Set G)) :
    ¬ aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar j)) (g⁻¹ * t * g) :=
  fun hconjugate => hg (hi i j t g htwo hnoncentral hcentral hconjugate)

end CFSG.ComponentClassification.AschbacherTheorem5
