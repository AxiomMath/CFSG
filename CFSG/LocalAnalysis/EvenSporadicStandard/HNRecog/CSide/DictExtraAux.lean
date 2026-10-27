module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.DictFix
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelDefs

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Subgroup QuadraticMap CFSG.RankThree.Literature.FSmith CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

variable {C : Type} [Group C] {Q : Subgroup C} [hQn : Q.Normal]
  [Module (ZMod 2) (Additive (Abelianization Q))]

theorem cSide_centerOf_eq_map_center :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxQ, hxc⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hxQ⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hxc) y y.2)
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)

theorem cSide_card_centerOf [Finite Q] (hE : IsExtraspecialPGroup 2 Q) :
    Nat.card ↥(centerOf Q) = 2 := by
  rw [cSide_centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective,
    hE.2.2.2]

theorem cSide_centerOf_le_cent (hE : IsExtraspecialPGroup 2 Q) (ρ : C) :
    centerOf Q ≤ Q ⊓ Subgroup.centralizer ({ρ} : Set C) := by
  intro c hc
  obtain ⟨hcQ, _⟩ := Subgroup.mem_inf.mp hc
  refine Subgroup.mem_inf.mpr ⟨hcQ, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  by_cases hc1 : c = 1
  · rw [hc1, one_mul, mul_one]
  have hccenter : (⟨c, hcQ⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    (mem_centerOf_iff ⟨c, hcQ⟩).mp hc
  have hycenter : conjAut hQn ρ ⟨c, hcQ⟩ ∈ Subgroup.center ↥Q := by
    rw [Subgroup.mem_center_iff]
    intro z
    calc z * conjAut hQn ρ ⟨c, hcQ⟩
        = conjAut hQn ρ ((conjAut hQn ρ).symm z * ⟨c, hcQ⟩) := by
          rw [map_mul, MulEquiv.apply_symm_apply]
      _ = conjAut hQn ρ (⟨c, hcQ⟩ * (conjAut hQn ρ).symm z) := by
          rw [Subgroup.mem_center_iff.mp hccenter ((conjAut hQn ρ).symm z)]
      _ = conjAut hQn ρ ⟨c, hcQ⟩ * z := by
          rw [map_mul, MulEquiv.apply_symm_apply]
  have hcne : (⟨c, hcQ⟩ : ↥Q) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
  have hyne : conjAut hQn ρ ⟨c, hcQ⟩ ≠ 1 := fun h =>
    hcne ((conjAut hQn ρ).injective (h.trans (map_one (conjAut hQn ρ)).symm))
  have hceq : conjAut hQn ρ ⟨c, hcQ⟩ = ⟨c, hcQ⟩ :=
    eq_of_mem_center hE hycenter hccenter hyne hcne
  have hconj : ρ * c * ρ⁻¹ = c := by
    have := congrArg (fun t : ↥Q => (t : C)) hceq
    simpa [conjAut_apply] using this
  calc c * ρ = (ρ * c * ρ⁻¹) * ρ := by rw [hconj]
    _ = ρ * c := by group

theorem cSide_mem_R_iff [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ)) (x : ↥Q) :
    ((x : C) ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C) ↔
      conjLinEquiv hQn ρ (Additive.ofMul (Abelianization.of x)) =
        Additive.ofMul (Abelianization.of x)) := by
  rw [Subgroup.mem_inf, iff_true_intro x.2, true_and]
  have hiff : conjLinEquiv hQn ρ (Additive.ofMul (Abelianization.of x)) =
      Additive.ofMul (Abelianization.of x) ↔ ⁅ρ, (x : C)⁆ ∈ centerOf Q :=
    extraspecialConjOrth_apply_eq_iff hE ρ x
  have hcommiff : ⁅ρ, (x : C)⁆ ∈ centerOf Q ↔
      (x : C) ∈ Subgroup.centralizer ({ρ} : Set C) := by
    rw [← Subgroup.inv_mem_iff,
      show ⁅ρ, (x : C)⁆⁻¹ = ⁅(x : C), ρ⁆ from
        commutatorElement_inv (g₁ := ρ) (g₂ := (x : C))]
    exact cSide_comm_mem_centerOf_iff_of_odd hE hρ x.2
  rw [hiff, hcommiff]

theorem cSide_mem_centerOf_of_mem_center [Finite Q] (hE : IsExtraspecialPGroup 2 Q) {ρ : C}
    (hρ : Odd (orderOf ρ))
    (hnd : cSideFixedNondeg (extraspecialQuadForm hE) (conjLinEquiv hQn ρ)) {x : C}
    (hxR : x ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C))
    (hxcen : ∀ y ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C), x * y = y * x) :
    x ∈ centerOf Q := by
  have hxQ : x ∈ Q := (Subgroup.mem_inf.mp hxR).1
  have hxfix : conjLinEquiv hQn ρ (Additive.ofMul (Abelianization.of (⟨x, hxQ⟩ : ↥Q))) =
      Additive.ofMul (Abelianization.of (⟨x, hxQ⟩ : ↥Q)) := by
    have hconj : conjAut hQn ρ (⟨x, hxQ⟩ : ↥Q) = ⟨x, hxQ⟩ := by
      apply Subtype.ext
      rw [conjAut_apply]
      have hcomm : x * ρ = ρ * x :=
        Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hxR).2
      calc ρ * x * ρ⁻¹ = (x * ρ) * ρ⁻¹ := by rw [hcomm]
        _ = x := by group
    rw [conjLinEquiv_apply, hconj]
  apply (mem_centerOf_iff ⟨x, hxQ⟩).mpr
  apply (ofMul_of_eq_zero_iff hE ⟨x, hxQ⟩).mp
  by_contra hne
  obtain ⟨w, hwfix, hwne⟩ := hnd _ hxfix hne
  obtain ⟨y, rfl⟩ := exists_ofMul_of w
  have hyR : (y : C) ∈ Q ⊓ Subgroup.centralizer ({ρ} : Set C) :=
    (cSide_mem_R_iff hE hρ y).mpr hwfix
  have horth : polar (extraspecialQuadForm hE)
      (Additive.ofMul (Abelianization.of (⟨x, hxQ⟩ : ↥Q)))
      (Additive.ofMul (Abelianization.of y)) = 0 := by
    have hcommxy : (⟨x, hxQ⟩ : ↥Q) * y = y * ⟨x, hxQ⟩ :=
      Subtype.ext (hxcen (y : C) hyR)
    exact (polar_extraspecialQuadForm_eq_zero_iff hE (⟨x, hxQ⟩ : ↥Q) y).mpr hcommxy
  exact hwne horth

noncomputable def cSide_ofMulHom (Q : Subgroup C) :
    ↥Q →* Multiplicative (Additive (Abelianization Q)) :=
  MonoidHom.mk' (fun q => Additive.ofMul (Abelianization.of q)) (fun x y => by
    change Additive.ofMul (Abelianization.of (x * y)) =
      Additive.ofMul (Abelianization.of x) + Additive.ofMul (Abelianization.of y)
    rw [ofMul_of_mul])

theorem cSide_mul_self_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : Multiplicative V) : v * v = 1 := by
  have h : Multiplicative.toAdd v + Multiplicative.toAdd v = 0 := by
    have h2 : (2 : ZMod 2) • Multiplicative.toAdd v = 0 := by
      rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
    simpa [show (2 : ZMod 2) = (1 : ZMod 2) + 1 from by decide, add_smul, one_smul] using h2
  apply Multiplicative.toAdd.injective
  simpa using h

theorem cSide_zpow_mem_pair {α : Type*} [Group α] {a : α} (ha : a * a = 1) (m : ℤ) :
    a ^ m = 1 ∨ a ^ m = a := by
  have h2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact ha
  have hmod : a ^ m = a ^ (m % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv m 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rw [hmod]
  have hlt : m % 2 = 0 ∨ m % 2 = 1 := by
    have h1 := Int.emod_nonneg m (by norm_num : (2 : ℤ) ≠ 0)
    have h2' := Int.emod_lt_of_pos m (by norm_num : (0 : ℤ) < 2)
    omega
  rcases hlt with h | h <;> rw [h] <;> simp

theorem cSide_card_closure_pair {α : Type*} [CommGroup α] {a b : α}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) :
    Nat.card (Subgroup.closure ({a, b} : Set α)) = 4 := by
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    calc a = a * 1 := by rw [mul_one]
      _ = a * (b * b) := by rw [hb]
      _ = (a * b) * b := by group
      _ = 1 * b := by rw [h]
      _ = b := by rw [one_mul]
  have hset : (Subgroup.closure ({a, b} : Set α) : Set α) = {1, a, b, a * b} := by
    ext z
    change z ∈ Subgroup.closure ({a, b} : Set α) ↔ z ∈ ({1, a, b, a * b} : Set α)
    rw [Subgroup.mem_closure_pair]
    constructor
    · rintro ⟨m, n, rfl⟩
      rcases cSide_zpow_mem_pair ha m with h | h <;>
        rcases cSide_zpow_mem_pair hb n with h' | h' <;> rw [h, h'] <;> simp
    · intro hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact ⟨0, 0, by simp⟩
      · exact ⟨1, 0, by simp⟩
      · exact ⟨0, 1, by simp⟩
      · exact ⟨1, 1, by simp⟩
  change Nat.card (Subgroup.closure ({a, b} : Set α) : Set α) = 4
  rw [Nat.card_coe_set_eq, hset]
  exact Set.ncard_eq_four.mpr ⟨1, a, b, a * b, Ne.symm ha1, Ne.symm hb1, Ne.symm hab1, hab,
    (fun h => hb1 (by
      have h1 : a * 1 = a * b := by rw [mul_one]; exact h
      exact (mul_left_cancel h1).symm)),
    (fun h => ha1 (by
      have h1 : b * 1 = b * a := by
        rw [mul_one]
        nth_rewrite 1 [h]
        rw [mul_comm]
      exact (mul_left_cancel h1).symm)),
    rfl⟩

theorem cSide_top_eq_closure {E : Subgroup C} {x y z : C} (hx : x ∈ E) (hy : y ∈ E)
    (hz : z ∈ E) (hE : E = Subgroup.closure ({x, y, z} : Set C)) :
    (⊤ : Subgroup ↥E) = Subgroup.closure ({⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩} : Set ↥E) := by
  apply Subgroup.map_injective E.subtype_injective
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype]
  conv_lhs => rw [hE]
  congr 1
  ext t
  simp

theorem cSide_exists_two_ne_one {α : Type*} [Group α] (h : 3 ≤ Nat.card α) :
    ∃ v w : α, v ≠ 1 ∧ w ≠ 1 ∧ v ≠ w := by
  haveI : Finite α := Nat.finite_of_card_ne_zero (by omega)
  have h1 : 1 < Nat.card α := by omega
  haveI : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨v, hv⟩ : ∃ v : α, v ≠ 1 := exists_ne 1
  by_contra hcon
  have hkey : ∀ x : α, x = 1 ∨ x = v := by
    intro x
    by_cases hx : x = 1
    · exact Or.inl hx
    · by_cases hxv : x = v
      · exact Or.inr hxv
      · exact absurd ⟨x, v, hx, hv, hxv⟩ hcon
  have hsub : (Set.univ : Set α) ⊆ ({1, v} : Set α) := fun x _ => hkey x
  have h2 : Nat.card α ≤ 2 := by
    have hle := Set.ncard_le_ncard hsub
    rwa [Set.ncard_univ, Set.ncard_pair (Ne.symm hv)] at hle
  omega

theorem cSide_center_eq_one_or {z : ↥Q} (hz : z ∈ Subgroup.center ↥Q) (hz1 : z ≠ 1)
    (hzuniq : ∀ y : Subgroup.center ↥Q, y ≠ 1 → y = ⟨z, hz⟩)
    {a : ↥Q} (ha : a ∈ Subgroup.center ↥Q) : a = 1 ∨ a = z := by
  by_cases h : (⟨a, ha⟩ : Subgroup.center ↥Q) = 1
  · left; exact congrArg Subtype.val h
  · right; exact congrArg Subtype.val (hzuniq ⟨a, ha⟩ h)

end CFSG.EvenSporadicStandard.HNRecog.CSide
