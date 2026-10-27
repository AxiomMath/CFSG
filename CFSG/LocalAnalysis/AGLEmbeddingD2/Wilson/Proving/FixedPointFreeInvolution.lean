module

public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Proving

theorem commute_odd_of_fixedPointFree_involution {Γ : Type*} [Group Γ] (M : Subgroup Γ)
    [Finite M] (t : Γ) (ht2 : t ^ 2 = 1) (htM : ∀ m ∈ M, t * m * t⁻¹ ∈ M)
    (hfix : ∀ m ∈ M, t * m = m * t → m = 1) :
    (∀ a ∈ M, ∀ b ∈ M, a * b = b * a) ∧ Odd (Nat.card M) := by
  classical
  have htt : t * t = 1 := by rw [← pow_two]; exact ht2
  have hmul : ∀ a b : Γ, t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by
    intro a b; group
  have hinv : ∀ a : Γ, t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by
    intro a; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hsq : ∀ a : Γ, t * (t * a * t⁻¹) * t⁻¹ = a := by
    intro a
    rw [htinv]
    calc t * (t * a * t) * t = (t * t) * a * (t * t) := by group
      _ = a := by rw [htt, one_mul, mul_one]
  let ψ : M → M := fun x => ⟨x⁻¹ * (t * x * t⁻¹), M.mul_mem (M.inv_mem x.2) (htM x x.2)⟩
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have h : (x : Γ)⁻¹ * (t * (x : Γ) * t⁻¹) = (y : Γ)⁻¹ * (t * (y : Γ) * t⁻¹) :=
      congrArg Subtype.val hxy
    have e1 : (y : Γ) * (x : Γ)⁻¹ = (t * (y : Γ) * t⁻¹) * (t * (x : Γ) * t⁻¹)⁻¹ := by
      have hy : (y : Γ) * ((x : Γ)⁻¹ * (t * (x : Γ) * t⁻¹)) = t * (y : Γ) * t⁻¹ := by
        rw [h, mul_inv_cancel_left]
      rw [← hy]
      simp [mul_assoc]
    have hu : t * ((y : Γ) * (x : Γ)⁻¹) * t⁻¹ = (y : Γ) * (x : Γ)⁻¹ := by
      conv_lhs => rw [e1]
      rw [hmul, hsq (y : Γ), hinv, hsq (x : Γ)]
    have hcomm : t * ((y : Γ) * (x : Γ)⁻¹) = ((y : Γ) * (x : Γ)⁻¹) * t :=
      mul_inv_eq_iff_eq_mul.mp hu
    have h1 : (y : Γ) * (x : Γ)⁻¹ = 1 :=
      hfix _ (M.mul_mem y.2 (M.inv_mem x.2)) hcomm
    have h2 : (y : Γ) = (x : Γ) := mul_inv_eq_one.mp h1
    exact Subtype.ext h2.symm
  have hψsurj : Function.Surjective ψ := Finite.injective_iff_surjective.mp hψinj
  have hkey : ∀ g ∈ M, t * g * t⁻¹ = g⁻¹ := by
    intro g hg
    obtain ⟨x, hx⟩ := hψsurj ⟨g, hg⟩
    have hg' : g = (x : Γ)⁻¹ * (t * (x : Γ) * t⁻¹) := (congrArg Subtype.val hx).symm
    rw [hg']
    rw [hmul, hsq (x : Γ), hinv (x : Γ), mul_inv_rev (x : Γ)⁻¹ (t * (x : Γ) * t⁻¹), inv_inv]
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a := by
    intro a ha b hb
    have h1 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
      rw [← hkey (a * b) (M.mul_mem ha hb), hmul, hkey a ha, hkey b hb]
    rw [mul_inv_rev a b] at h1
    have h2 := congrArg (fun z => z⁻¹) h1
    simpa using h2
  refine ⟨hcomm, ?_⟩
  let f : Function.End M := fun x => ⟨t * x * t⁻¹, htM x x.2⟩
  have hf2 : ∀ x : M, (f^[2]) x = x := by
    intro x
    apply Subtype.ext
    show t * (t * x * t⁻¹) * t⁻¹ = x
    exact hsq x
  have hf : f ^ (2 ^ 1) = 1 := by
    rw [pow_one]
    funext x
    exact hf2 x
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype M := Fintype.ofFinite M
  have hcong := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  have hfixone : ∀ y ∈ f.fixedPoints, y = 1 := by
    intro y hy
    rw [Function.mem_fixedPoints_iff] at hy
    have h' : t * (y : Γ) * t⁻¹ = (y : Γ) := congrArg Subtype.val hy
    exact Subtype.ext (hfix (y : Γ) y.2 (mul_inv_eq_iff_eq_mul.mp h'))
  have h1mem : (1 : M) ∈ f.fixedPoints := by
    rw [Function.mem_fixedPoints_iff]
    apply Subtype.ext
    show t * 1 * t⁻¹ = 1
    simp
  have hcardfix : Nat.card f.fixedPoints = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun y z => Subtype.ext ((hfixone y.1 y.2).trans (hfixone z.1 z.2).symm)⟩,
      ⟨⟨1, h1mem⟩⟩⟩
  simp only [← Nat.card_eq_fintype_card] at hcong
  rw [hcardfix] at hcong
  exact Nat.odd_iff.mpr hcong

end CFSG.AGLEmbeddingD2.Wilson.Proving

end
