module

public import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NcycBasic

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section GmiCore

variable {X : Type*} [Group X]

theorem gmi_isSylowOf_top [Finite X] {p : ℕ} [Fact p.Prime] (S : Sylow p X) :
    IsSylowOf p (S : Subgroup X) ⊤ := by
  rw [isSylowOf_iff]
  refine ⟨le_top, S.isPGroup', ?_⟩
  rw [Subgroup.relIndex_top_right]
  exact S.not_dvd_index

theorem gmi_top_le_normalizer {N : Subgroup X} (hN : N.Normal) :
    (⊤ : Subgroup X) ≤ normalizer (N : Set X) := by
  rw [normalizer_eq_top_iff.mpr hN]

theorem gmi_mem_normalizer_inf {S N : Subgroup X} {a : X} (haS : a ∈ S)
    (haN : a ∈ normalizer (N : Set X)) : a ∈ normalizer ((S ⊓ N : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff] at haN ⊢
  intro n
  rw [mem_inf, mem_inf, haN n]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨mul_mem (mul_mem haS h1) (inv_mem haS), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have : n = a⁻¹ * (a * n * a⁻¹) * a := by group
    rw [this]
    exact mul_mem (mul_mem (inv_mem haS) h1) haS

theorem gmi_exists_mul_of_sylow [Finite X] {p : ℕ} [hp : Fact p.Prime] {S N₁ N₂ : Subgroup X}
    (hS : IsSylowOf p S ⊤) (hN₁ : N₁.Normal) (hN₂ : N₂.Normal) (hN : N₁ ⊔ N₂ = ⊤) {x : X}
    (hx : x ∈ S) : ∃ a ∈ S ⊓ N₁, ∃ b ∈ S ⊓ N₂, a * b = x := by
  have hN₁₂ : (N₁ ⊓ N₂).Normal := Subgroup.normal_inf_normal N₁ N₂
  have h1 := hS.inf_of_le_normalizer le_top (gmi_top_le_normalizer hN₁)
  have h2 := hS.inf_of_le_normalizer le_top (gmi_top_le_normalizer hN₂)
  have h12 := hS.inf_of_le_normalizer le_top (gmi_top_le_normalizer hN₁₂)
  set A := S ⊓ N₁ with hA
  set B := S ⊓ N₂ with hB
  have hAB : A ⊓ B = S ⊓ (N₁ ⊓ N₂) := by
    ext y
    simp only [hA, hB, mem_inf]
    tauto
  have hBA : B ≤ normalizer (A : Set X) := fun b hb =>
    gmi_mem_normalizer_inf (mem_inf.mp hb).1 (gmi_top_le_normalizer hN₁ (mem_top b))
  have hAB' : A ≤ normalizer (B : Set X) := fun a ha =>
    gmi_mem_normalizer_inf (mem_inf.mp ha).1 (gmi_top_le_normalizer hN₂ (mem_top a))
  have hcAB := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hBA
  have hcN := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := N₁) (B := N₂) (fun b _ => gmi_top_le_normalizer hN₁ (mem_top b))
  rw [hN, Subgroup.card_top] at hcN
  rw [hAB, h1.card_eq, h2.card_eq, h12.card_eq] at hcAB
  have hScard := hS.card_eq
  rw [Subgroup.card_top] at hScard
  have hpos : ∀ H : Subgroup X, Nat.card H ≠ 0 := fun H => Nat.card_pos.ne'
  have hv : (Nat.card X).factorization p + (Nat.card (N₁ ⊓ N₂ : Subgroup X)).factorization p =
      (Nat.card N₁).factorization p + (Nat.card N₂).factorization p := by
    have := congrArg (fun n => n.factorization p) hcN
    simp only [Nat.factorization_mul (Nat.card_pos (α := X)).ne' (hpos _),
      Nat.factorization_mul (hpos N₁) (hpos N₂), Finsupp.add_apply] at this
    exact this
  have hcard : Nat.card (A ⊔ B : Subgroup X) = Nat.card S := by
    rw [hScard]
    have hp0 : 0 < p ^ (Nat.card (N₁ ⊓ N₂ : Subgroup X)).factorization p :=
      pow_pos hp.out.pos _
    apply Nat.eq_of_mul_eq_mul_right hp0
    rw [hcAB, ← pow_add, ← pow_add, hv]
  have hle : A ⊔ B ≤ S := sup_le inf_le_left inf_le_left
  have heq : A ⊔ B = S := Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  rw [← heq] at hx
  exact ncyc_exists_mul_of_mem_sup hAB' hx

theorem gmi_le_of_fixedPointFree [Finite X] {F N : Subgroup X} {e : X} (heN : e ∈ N)
    (hFN : ∀ x ∈ F, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (heF : ∀ x ∈ F, e * x * e⁻¹ ∈ F)
    (hfix : ∀ x ∈ F, e * x * e⁻¹ = x → x = 1) : F ≤ N := by
  classical
  let θ : F → F := fun x => ⟨e * x * e⁻¹ * (x : X)⁻¹, mul_mem (heF x x.2) (inv_mem x.2)⟩
  have hinj : Function.Injective θ := by
    intro x y hxy
    have h : e * (x : X) * e⁻¹ * (x : X)⁻¹ = e * (y : X) * e⁻¹ * (y : X)⁻¹ :=
      congrArg Subtype.val hxy
    have hz : (y : X)⁻¹ * x ∈ F := mul_mem (inv_mem y.2) x.2
    have hfx : e * ((y : X)⁻¹ * x) * e⁻¹ = (y : X)⁻¹ * x := by
      calc e * ((y : X)⁻¹ * x) * e⁻¹ =
          (e * (y : X) * e⁻¹)⁻¹ * (e * (x : X) * e⁻¹ * (x : X)⁻¹) * x := by group
        _ = (e * (y : X) * e⁻¹)⁻¹ * (e * (y : X) * e⁻¹ * (y : X)⁻¹) * x := by rw [h]
        _ = (y : X)⁻¹ * x := by group
    have h1 := hfix _ hz hfx
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hxy : e * (y : X) * e⁻¹ * (y : X)⁻¹ = x := congrArg Subtype.val hy
  rw [← hxy, show e * (y : X) * e⁻¹ * (y : X)⁻¹ = e * ((y : X) * e⁻¹ * (y : X)⁻¹) by group]
  exact mul_mem heN (hFN y y.2 _ (inv_mem heN))

end GmiCore

end CFSG.SeitzReduction.RankOne
