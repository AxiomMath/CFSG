module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction628.ElemModule

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA628
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

structure ElemSec (f : ℕ) (Y M G : Subgroup K) (W : Type) [AddCommGroup W] [Module (ZMod f) W]
    (π : K → W) (ρ : Representation (ZMod f) ↥G W) : Prop where
  add : ∀ x ∈ Y, ∀ y ∈ Y, π (x * y) = π x + π y
  ker : ∀ x ∈ Y, π x = 0 ↔ x ∈ M
  surj : ∀ w : W, ∃ x ∈ Y, π x = w
  act : ∀ g : ↥G, ∀ x ∈ Y, ρ g (π x) = π (g * x * g⁻¹)

theorem exists_elemSec {f : ℕ} [Fact f.Prime] {Y M G : Subgroup K} (hMY : M ≤ Y)
    (hMn : ∀ x ∈ Y, ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hab : ∀ x ∈ Y, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ M) (hexp : ∀ x ∈ Y, x ^ f ∈ M)
    (hGY : G ≤ normalizer (Y : Set K)) (hGM : G ≤ normalizer (M : Set K)) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod f) W) (_ : Module.Finite (ZMod f) W)
      (π : K → W) (ρ : Representation (ZMod f) ↥G W), ElemSec f Y M G W π ρ := by
  obtain ⟨W, _, _, _, π, ρ, h1, h2, h3, h4⟩ := exists_elemSection hMY hMn hab hexp hGY hGM
  exact ⟨W, inferInstance, inferInstance, inferInstance, π, ρ, ⟨h1, h2, h3, h4⟩⟩

variable {f : ℕ} {Y M G : Subgroup K} {W : Type} [AddCommGroup W] [Module (ZMod f) W]
  {π : K → W} {ρ : Representation (ZMod f) ↥G W}

theorem ElemSec.map_one (h : ElemSec f Y M G W π ρ) : π 1 = 0 := by
  have := h.add 1 Y.one_mem 1 Y.one_mem
  simpa using this

theorem ElemSec.map_inv (h : ElemSec f Y M G W π ρ) {x : K} (hx : x ∈ Y) : π x⁻¹ = - π x := by
  have := h.add x⁻¹ (Y.inv_mem hx) x hx
  rw [inv_mul_cancel, h.map_one] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem ElemSec.eq_iff (h : ElemSec f Y M G W π ρ) {x y : K} (hx : x ∈ Y) (hy : y ∈ Y) :
    π x = π y ↔ x⁻¹ * y ∈ M := by
  rw [← h.ker _ (Y.mul_mem (Y.inv_mem hx) hy), h.add _ (Y.inv_mem hx) _ hy, h.map_inv hx]
  exact neg_add_eq_zero.symm

@[expose] def ElemSec.hom (h : ElemSec f Y M G W π ρ) : ↥Y →* Multiplicative W where
  toFun x := Multiplicative.ofAdd (π x)
  map_one' := by
    show Multiplicative.ofAdd (π ((1 : ↥Y) : K)) = 1
    rw [Subgroup.coe_one, h.map_one]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (π ((x : K) * y)) =
      Multiplicative.ofAdd (π x) * Multiplicative.ofAdd (π y)
    rw [h.add _ x.2 _ y.2]
    rfl

theorem ElemSec.card_eq (h : ElemSec f Y M G W π ρ) (hMY : M ≤ Y) :
    Nat.card Y = Nat.card M * Nat.card W := by
  have hsurj : Function.Surjective h.hom := by
    intro w
    obtain ⟨x, hx, hxw⟩ := h.surj (Multiplicative.toAdd w)
    exact ⟨⟨x, hx⟩, by simp [ElemSec.hom, hxw]⟩
  have hker : h.hom.ker = M.subgroupOf Y := by
    ext x
    simp [ElemSec.hom, Subgroup.mem_subgroupOf, h.ker _ x.2, ← ofAdd_zero]
  have h1 := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMY).toEquiv] at h1
  have h2 : Nat.card (Multiplicative W) = Nat.card W := Nat.card_congr Multiplicative.toAdd
  rw [h2] at h1
  exact h1.symm

@[expose] def ElemSec.preimage (h : ElemSec f Y M G W π ρ) (U : Submodule (ZMod f) W) :
    Subgroup K where
  carrier := {x | x ∈ Y ∧ π x ∈ U}
  mul_mem' := by
    rintro x y ⟨hx, hxU⟩ ⟨hy, hyU⟩
    exact ⟨Y.mul_mem hx hy, by rw [h.add x hx y hy]; exact U.add_mem hxU hyU⟩
  one_mem' := ⟨Y.one_mem, by rw [h.map_one]; exact U.zero_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hxU⟩
    exact ⟨Y.inv_mem hx, by rw [h.map_inv hx]; exact U.neg_mem hxU⟩

theorem ElemSec.card_preimage (h : ElemSec f Y M G W π ρ) (hMY : M ≤ Y)
    (U : Submodule (ZMod f) W) : Nat.card (h.preimage U) = Nat.card M * Nat.card U := by
  set H := h.preimage U with hH
  have hHY : H ≤ Y := fun x hx => hx.1
  let θ : ↥H →* Multiplicative W := h.hom.comp (Subgroup.inclusion hHY)
  have hker : θ.ker = M.subgroupOf H := by
    ext x
    have hxY : (x : K) ∈ Y := x.2.1
    simp only [θ, MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (π (x : K)) = 1 ↔ _
    rw [← ofAdd_zero, Multiplicative.ofAdd.apply_eq_iff_eq, h.ker _ hxY]
  have hrange : ∀ w : Multiplicative W, w ∈ θ.range ↔ Multiplicative.toAdd w ∈ U := by
    intro w
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2.2
    · intro hw
      obtain ⟨x, hx, hxw⟩ := h.surj (Multiplicative.toAdd w)
      exact ⟨⟨x, hx, by rw [hxw]; exact hw⟩, by simp [θ, ElemSec.hom, hxw]⟩
  have hMH : M ≤ H := fun m hm =>
    ⟨hMY hm, by rw [(h.ker m (hMY hm)).mpr hm]; exact U.zero_mem⟩
  have h1 := Subgroup.card_ker_mul_card_range θ
  have h2 : Nat.card θ.range = Nat.card U :=
    Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd hrange)
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv, h2] at h1
  exact h1.symm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P65N2
