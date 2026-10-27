module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Orders

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem oddCore_characteristic_of (H : Type*) [Group H] : (CFSG.oddCore H).Characteristic := by
  refine Subgroup.characteristic_iff_le_comap.2 fun φ => sSup_le fun N hN => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  refine le_sSup ⟨hN.1.map _ φ.surjective, ?_⟩
  rw [Subgroup.card_map_of_injective φ.injective]
  exact hN.2

@[expose] def autQuot (H : Type*) [Group H] (N : Subgroup H) [N.Normal] [hN : N.Characteristic] :
    MulAut H →* MulAut (H ⧸ N) where
  toFun α := QuotientGroup.congr N N α (Subgroup.characteristic_iff_map_eq.mp hN α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem autQuot_mk (H : Type*) [Group H] (N : Subgroup H) [N.Normal] [N.Characteristic]
    (α : MulAut H) (x : H) :
    autQuot H N α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := by
  rfl

theorem eq_one_of_autQuot_eq_one [Finite G] {I : Subgroup G} (hI : IsQuasisimple I)
    (hs : IsSimpleGroup (↥I ⧸ oddCore ↥I)) {α : MulAut ↥I}
    (h : (haveI := oddCore_characteristic_of ↥I; autQuot ↥I (oddCore ↥I) α) = 1) : α = 1 := by
  haveI : (oddCore ↥I).Characteristic := oddCore_characteristic_of ↥I
  have hcen : center ↥I = oddCore ↥I := center_eq_oddCore_of_simple hI hs
  have hz : ∀ x : ↥I, x⁻¹ * α x ∈ center ↥I := by
    intro x
    rw [hcen]
    have h1 : (QuotientGroup.mk x : ↥I ⧸ oddCore ↥I) = QuotientGroup.mk (α x) := by
      have h2 := autQuot_mk ↥I (oddCore ↥I) α x
      rw [h] at h2
      exact h2
    exact QuotientGroup.eq.1 h1
  have hmul : ∀ x x' : ↥I, (x * x')⁻¹ * α (x * x') = (x⁻¹ * α x) * (x'⁻¹ * α x') := by
    intro x x'
    have hc := Subgroup.mem_center_iff.1 (hz x) x'⁻¹
    calc (x * x')⁻¹ * α (x * x') = x'⁻¹ * (x⁻¹ * α x) * α x' := by
          rw [map_mul]; group
      _ = (x⁻¹ * α x) * x'⁻¹ * α x' := by rw [hc]
      _ = (x⁻¹ * α x) * (x'⁻¹ * α x') := by group
  let f : ↥I →* ↥(center ↥I) :=
    { toFun := fun x => ⟨x⁻¹ * α x, hz x⟩
      map_one' := by ext; simp
      map_mul' := fun x x' => Subtype.ext (hmul x x') }
  have hker : commutator ↥I ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.isPerfect_def.mp hI.1] at hker
  refine MulEquiv.ext fun x => ?_
  have hx : f x = 1 := hker (Subgroup.mem_top x)
  have := congrArg Subtype.val hx
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at this
  exact (inv_mul_eq_one.1 this).symm

theorem exists_aut_embedding [Finite G] {I : Subgroup G} (hI : IsQuasisimple I)
    (hs : IsSimpleGroup (↥I ⧸ oddCore ↥I)) {Y : Subgroup G}
    (hYN : Y ≤ normalizer (I : Set G)) (hYC : Y ⊓ centralizer (I : Set G) = ⊥) :
    ∃ ρ : ↥Y →* MulAut (↥I ⧸ oddCore ↥I), Function.Injective ρ := by
  haveI : (oddCore ↥I).Characteristic := oddCore_characteristic_of ↥I
  let c : ↥Y →* MulAut ↥I := I.normalizerMonoidHom.comp (Subgroup.inclusion hYN)
  refine ⟨(autQuot ↥I (oddCore ↥I)).comp c, ?_⟩
  rw [injective_iff_map_eq_one]
  intro y hy
  have h1 : c y = 1 := eq_one_of_autQuot_eq_one hI hs hy
  have hcent : (y : G) ∈ centralizer (I : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h2 := congrArg (fun a : MulAut ↥I => ((a ⟨g, hg⟩ : ↥I) : G)) h1
    simp only [c, MonoidHom.comp_apply, MulAut.one_apply] at h2
    have h3 : (y : G) * g * (y : G)⁻¹ = g := h2
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hmem : (y : G) ∈ Y ⊓ centralizer (I : Set G) := ⟨y.2, hcent⟩
  rw [hYC, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

theorem card_le_of_aut_embedding [Finite G] {I : Subgroup G} (hI : IsQuasisimple I)
    (hs : IsSimpleGroup (↥I ⧸ oddCore ↥I)) {Y : Subgroup G}
    (hYN : Y ≤ normalizer (I : Set G)) (hYC : Y ⊓ centralizer (I : Set G) = ⊥)
    (hp : IsPGroup 2 Y) (hc : IsMulCommutative Y) {n : ℕ}
    (hbound : ∀ X : Subgroup (MulAut (↥I ⧸ oddCore ↥I)), IsPGroup 2 X → IsMulCommutative X →
      Nat.card X ≤ n) : Nat.card Y ≤ n := by
  obtain ⟨ρ, hρ⟩ := exists_aut_embedding hI hs hYN hYC
  have hX2 : IsPGroup 2 ρ.range := hp.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  haveI := hc
  have hcard : Nat.card ρ.range = Nat.card Y :=
    (Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv).symm
  rw [← hcard]
  exact hbound _ hX2 (Subgroup.range_isMulCommutative ρ)

end CFSG.OddStandard.SmallF3.Omega
