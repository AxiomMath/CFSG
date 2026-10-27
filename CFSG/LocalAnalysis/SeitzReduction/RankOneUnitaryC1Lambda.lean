module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1

variable {G : Type*} [Group G] {T₁ : Subgroup G}

theorem commute_of_fixedPointFree [Finite G] {k w : G}
    (hcomm : ∀ y ∈ T₁, ∀ y' ∈ T₁, y * y' * y⁻¹ * y'⁻¹ ∈ szA₁ T₁)
    (hkT : k ∈ normalizer (T₁ : Set G)) (hkA : ∀ a ∈ szA₁ T₁, k * a * k⁻¹ = a)
    (hfpf : ∀ y ∈ T₁, y⁻¹ * (k * y * k⁻¹) ∈ szA₁ T₁ → y ∈ szA₁ T₁)
    (hwA : ∀ a ∈ szA₁ T₁, w * a * w⁻¹ = a) (hwT : ∀ y ∈ T₁, y⁻¹ * (w * y * w⁻¹) ∈ szA₁ T₁)
    (hinv : ∀ y ∈ T₁, (k * y * k⁻¹)⁻¹ * (w * (k * y * k⁻¹) * w⁻¹) = y⁻¹ * (w * y * w⁻¹)) :
    ∀ y ∈ T₁, w * y * w⁻¹ = y := by
  classical
  have hkT' : ∀ y ∈ T₁, k * y * k⁻¹ ∈ T₁ := fun y hy => (mem_normalizer_iff.mp hkT y).mp hy
  have hcen : ∀ a ∈ szA₁ T₁, ∀ y ∈ T₁, a * y = y * a := fun a ha y hy =>
    (mem_centralizer_iff.mp (mem_szA₁.mp ha).2 y hy).symm
  have hδmul : ∀ y ∈ T₁, ∀ y' ∈ T₁, (y * y')⁻¹ * (w * (y * y') * w⁻¹) =
      (y⁻¹ * (w * y * w⁻¹)) * (y'⁻¹ * (w * y' * w⁻¹)) := by
    intro y hy y' hy'
    have h1 : w * (y * y') * w⁻¹ = y * (y⁻¹ * (w * y * w⁻¹)) * (y' * (y'⁻¹ * (w * y' * w⁻¹))) := by
      group
    rw [h1, show (y * y')⁻¹ * (y * (y⁻¹ * (w * y * w⁻¹)) * (y' * (y'⁻¹ * (w * y' * w⁻¹)))) =
      y'⁻¹ * ((y⁻¹ * (w * y * w⁻¹)) * y') * (y'⁻¹ * (w * y' * w⁻¹)) by group,
      hcen _ (hwT y hy) y' hy', inv_mul_cancel_left]
  have hδψ : ∀ y ∈ T₁, (y⁻¹ * (k * y * k⁻¹))⁻¹ * (w * (y⁻¹ * (k * y * k⁻¹)) * w⁻¹) = 1 := by
    intro y hy
    rw [hδmul _ (inv_mem hy) _ (hkT' y hy), hinv y hy, ← hδmul _ (inv_mem hy) _ hy, inv_mul_cancel,
      mul_one, mul_inv_cancel, inv_one, one_mul]
  set A' := (szA₁ T₁).subgroupOf T₁ with hA'
  set ψ : T₁ → T₁ := fun y => ⟨(y : G)⁻¹ * (k * y * k⁻¹), mul_mem (inv_mem y.2) (hkT' _ y.2)⟩
    with hψ
  have hψc : ∀ (y : T₁) (a : T₁), (a : G) ∈ szA₁ T₁ → ψ (y * a) = ψ y := by
    intro y a ha
    apply Subtype.ext
    simp only [hψ, Subgroup.coe_mul]
    have hka := hkA _ ha
    calc ((y : G) * a)⁻¹ * (k * (y * a) * k⁻¹) = (a : G)⁻¹ * ((y : G)⁻¹ * (k * y * k⁻¹)) *
          (k * a * k⁻¹) := by group
      _ = (a : G)⁻¹ * ((y : G)⁻¹ * (k * y * k⁻¹)) * a := by rw [hka]
      _ = (y : G)⁻¹ * (k * y * k⁻¹) := by
          rw [mul_assoc, ← hcen _ ha _ (mul_mem (inv_mem y.2) (hkT' _ y.2)), inv_mul_cancel_left]
  let ψ' : T₁ ⧸ A' → T₁ ⧸ A' := Quotient.lift (fun y => (ψ y : T₁ ⧸ A')) fun a b hab => by
    have h1 : a⁻¹ * b ∈ A' := QuotientGroup.leftRel_apply.mp hab
    have hb : b = a * (a⁻¹ * b) := by group
    change (ψ a : T₁ ⧸ A') = (ψ b : T₁ ⧸ A')
    rw [hb, hψc a _ (mem_subgroupOf.mp h1)]
  have hinj : Function.Injective ψ' := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    change (ψ a : T₁ ⧸ A') = (ψ b : T₁ ⧸ A') at hab
    rw [QuotientGroup.eq, mem_subgroupOf] at hab ⊢
    simp only [hψ, Subgroup.coe_inv, Subgroup.coe_mul] at hab ⊢
    set x := (a : G)⁻¹ * b with hx
    have hxT : x ∈ T₁ := mul_mem (inv_mem a.2) b.2
    set p := (a : G)⁻¹ * (k * a * k⁻¹) with hp
    have hpT : p ∈ T₁ := mul_mem (inv_mem a.2) (hkT' _ a.2)
    have e : ((a : G)⁻¹ * (k * a * k⁻¹))⁻¹ * ((b : G)⁻¹ * (k * b * k⁻¹)) =
        (p⁻¹ * x⁻¹ * p⁻¹⁻¹ * x⁻¹⁻¹) * (x⁻¹ * (k * x * k⁻¹)) := by
      rw [hp, hx]; group
    rw [e] at hab
    exact hfpf x hxT (by
      have := mul_mem (inv_mem (hcomm _ (inv_mem hpT) _ (inv_mem hxT))) hab
      rwa [inv_mul_cancel_left] at this)
  have hsurj : Function.Surjective ψ' := Finite.injective_iff_surjective.mp hinj
  intro z hz
  obtain ⟨c, hc⟩ := hsurj (⟨z, hz⟩ : T₁)
  induction c using QuotientGroup.induction_on with | H y => ?_
  change (ψ y : T₁ ⧸ A') = ((⟨z, hz⟩ : T₁) : T₁ ⧸ A') at hc
  rw [QuotientGroup.eq, mem_subgroupOf] at hc
  have hc' : ((y : G)⁻¹ * (k * y * k⁻¹))⁻¹ * z ∈ szA₁ T₁ := by simpa [hψ] using hc
  set a := ((y : G)⁻¹ * (k * y * k⁻¹))⁻¹ * z with ha
  have hz' : z = ((y : G)⁻¹ * (k * y * k⁻¹)) * a := by rw [ha]; group
  have hψT : (y : G)⁻¹ * (k * y * k⁻¹) ∈ T₁ := mul_mem (inv_mem y.2) (hkT' _ y.2)
  have hδz : z⁻¹ * (w * z * w⁻¹) = 1 := by
    rw [hz', hδmul _ hψT _ (szA₁_le _ hc'), hδψ y y.2, one_mul, hwA a hc', inv_mul_cancel]
  calc w * z * w⁻¹ = z * (z⁻¹ * (w * z * w⁻¹)) := by group
    _ = z := by rw [hδz, mul_one]

end U3C1

end CFSG.SeitzReduction.RankOne
