module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup

variable {G : Type} [Group G]

theorem sr630a_conj_eq_inv {E : Subgroup G} [Finite E] {y : G} (hy : y ^ 2 = 1)
    (hyE : y ∈ normalizer (E : Set G)) (hfix : ∀ e ∈ E, y * e = e * y → e = 1) :
    ∀ e ∈ E, y * e * y⁻¹ = e⁻¹ := by
  have hconj : ∀ e ∈ E, y * e * y⁻¹ ∈ E := fun e he => (mem_normalizer_iff.mp hyE e).mp he
  have hyy : y * y = 1 := by rw [← pow_two]; exact hy
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyy' : y⁻¹ * y⁻¹ = 1 := by rw [hyinv]; exact hyy
  let ψ : E → E := fun e => ⟨(e : G)⁻¹ * (y * e * y⁻¹), mul_mem (inv_mem e.2) (hconj e e.2)⟩
  have hψ : Function.Injective ψ := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have h : a⁻¹ * (y * a * y⁻¹) = b⁻¹ * (y * b * y⁻¹) := congrArg Subtype.val hab
    have hcomm : y * (b * a⁻¹) = (b * a⁻¹) * y := by
      calc y * (b * a⁻¹) = b * (b⁻¹ * (y * b * y⁻¹)) * y * a⁻¹ := by group
        _ = b * (a⁻¹ * (y * a * y⁻¹)) * y * a⁻¹ := by rw [h]
        _ = (b * a⁻¹) * y := by group
    have h1 : b * a⁻¹ = 1 := hfix _ (mul_mem hb (inv_mem ha)) hcomm
    exact Subtype.ext (mul_inv_eq_one.mp h1).symm
  have hsurj : Function.Surjective ψ := Finite.surjective_of_injective hψ
  intro e he
  obtain ⟨d, hd⟩ := hsurj ⟨e, he⟩
  have hd' : (d : G)⁻¹ * (y * d * y⁻¹) = e := congrArg Subtype.val hd
  rw [← hd']
  calc y * ((d : G)⁻¹ * (y * d * y⁻¹)) * y⁻¹
      = (y * (d : G)⁻¹ * y⁻¹) * (y * y) * d * (y⁻¹ * y⁻¹) := by group
    _ = (y * (d : G)⁻¹ * y⁻¹) * 1 * d * 1 := by rw [hyy, hyy']
    _ = ((d : G)⁻¹ * (y * d * y⁻¹))⁻¹ := by group

theorem sr630a_isMulCommutative_of_conj_eq_inv {E : Subgroup G} {y : G}
    (hinv : ∀ e ∈ E, y * e * y⁻¹ = e⁻¹) : IsMulCommutative E := by
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  show a * b = b * a
  have h1 := hinv (a * b) (mul_mem ha hb)
  have h2 := hinv a ha
  have h3 := hinv b hb
  have h4 : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
    calc (a * b)⁻¹ = y * (a * b) * y⁻¹ := h1.symm
      _ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      _ = a⁻¹ * b⁻¹ := by rw [h2, h3]
  calc a * b = ((a * b)⁻¹)⁻¹ := (inv_inv _).symm
    _ = (a⁻¹ * b⁻¹)⁻¹ := by rw [h4]
    _ = b * a := by group

end CFSG.LocalAnalysis.RankThreeTheoremC
