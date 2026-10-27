module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128WrMap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem wr_mul_left_of_right_eq_one {D Q : Type} [Group D] [Group Q] (a b : D ≀ᵣ Q)
    (h : a.right = 1) : (a * b).left = a.left * b.left := by
  ext q
  simp only [RegularWreathProduct.mul_left, Pi.mul_apply, h, inv_one, one_mul]

theorem sec128_wr_triv {G : Type} [Group G] {V D B X0 : Subgroup G} (hXB : X0 ⊓ B = ⊥)
    {χ : ↥(alternatingGroup (Fin 5)) →* ↥D} (hχinj : Function.Injective χ)
    (hχX : ∀ a : ↥(alternatingGroup (Fin 5)), (χ a : G) ∈ X0)
    {ι : ↥V →* WrZ2 ↥D} (hιinj : Function.Injective ι)
    (hιform : ∀ v : ↥V, (ι v).right = 1 ∧ ∀ q, ((ι v).left q : G) ∈ B)
    (v : ↥V) (γ : WrZ2 ↥(alternatingGroup (Fin 5)))
    (h : ι v * sec128WrMap χ γ = 1) : v = 1 ∧ γ = 1 := by
  have hγ' : sec128WrMap χ γ = (ι v)⁻¹ := eq_inv_of_mul_eq_one_right h
  have hright : γ.right = 1 := by
    have h1 := congrArg RegularWreathProduct.right hγ'
    rw [sec128WrMap_right, RegularWreathProduct.inv_right, (hιform v).1] at h1
    exact h1.trans inv_one
  have hleft : ∀ q, γ.left q = 1 := by
    intro q
    have hq : χ (γ.left q) = ((ι v).left q)⁻¹ := by
      have h1 := congrFun (congrArg RegularWreathProduct.left hγ') q
      simpa only [sec128WrMap_left, RegularWreathProduct.inv_left, (hιform v).1, one_mul,
        Pi.inv_apply] using h1
    have hB : (χ (γ.left q) : G) ∈ B := by
      rw [hq]
      simpa using B.inv_mem ((hιform v).2 q)
    have hbot : (χ (γ.left q) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hXB]
      exact ⟨hχX _, hB⟩
    have hχone : χ (γ.left q) = 1 := by
      apply Subtype.ext
      simpa using hbot
    exact hχinj (by rw [hχone, map_one])
  have hγ : γ = 1 := RegularWreathProduct.ext (funext hleft) hright
  refine ⟨?_, hγ⟩
  have hv : ι v = 1 := by
    have h1 := h
    rw [hγ, map_one, mul_one] at h1
    exact h1
  exact hιinj (by rw [hv, map_one])

theorem sec128_wr_surj {G : Type} [Group G] {V D B : Subgroup G} (hBD : B ≤ D)
    {χ : ↥(alternatingGroup (Fin 5)) →* ↥D}
    (hDdec : ∀ d : ↥D, ∃ (b : G) (a : ↥(alternatingGroup (Fin 5))), b ∈ B ∧
      (d : G) = b * (χ a : G))
    {ι : ↥V →* WrZ2 ↥D}
    (hιrange : ∀ a : Multiplicative (ZMod 2) → ↥D, (∀ q, (a q : G) ∈ B) →
      ∃ v : ↥V, ι v = ⟨a, 1⟩)
    (w : WrZ2 ↥D) :
    ∃ (v : ↥V) (γ : WrZ2 ↥(alternatingGroup (Fin 5))), ι v * sec128WrMap χ γ = w := by
  choose b c hb using fun q => hDdec (w.left q)
  have hιb : ∃ v : ↥V, ι v = ⟨fun q => (⟨b q, hBD (hb q).1⟩ : ↥D), 1⟩ :=
    hιrange (fun q => (⟨b q, hBD (hb q).1⟩ : ↥D)) (fun q => (hb q).1)
  obtain ⟨v, hv⟩ := hιb
  refine ⟨v, ⟨c, w.right⟩, ?_⟩
  rw [hv]
  refine RegularWreathProduct.ext (funext fun q => ?_) ?_
  · rw [wr_mul_left_of_right_eq_one
      (a := (⟨fun q => (⟨b q, hBD (hb q).1⟩ : ↥D), 1⟩ : WrZ2 ↥D))
      (b := sec128WrMap χ ⟨c, w.right⟩) rfl]
    simp only [Pi.mul_apply, sec128WrMap_left]
    apply Subtype.ext
    simpa only [Subgroup.coe_mul, Subgroup.coe_mk] using ((hb q).2).symm
  · simp [RegularWreathProduct.mul_right]

end CFSG.OddStandard.SmallF3.Omega
