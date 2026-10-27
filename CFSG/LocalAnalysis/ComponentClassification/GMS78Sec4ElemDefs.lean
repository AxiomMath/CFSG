module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec4Base

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped MatrixGroups

variable {G : Type} [Group G]

structure Sec4Elem (L T U₁ : Subgroup G) (q : ℕ) : Prop extends Sec4Base L T U₁ where
  lt : gmsA L T < U₁
  elem : IsElemAbelian 2 U₁
  card : Nat.card U₁ = q ^ 2
  sylow : IsSylowOf 2 (U₁ ⊔ T) (normalizer (gmsV L T : Set G))

namespace Sec4Elem

variable {L T U₁ : Subgroup G} {q : ℕ}

theorem mul_self (hE : Sec4Elem L T U₁ q) {u : G} (hu : u ∈ U₁) : u * u = 1 := by
  rw [← sq]
  exact hE.elem.2 u hu

theorem mem_or_mem (hE : Sec4Elem L T U₁ q) (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G)))
    {x : G} (hx : x ∈ U₁ ⊔ (T ⊓ centralizer (L : Set G))) (hxx : x * x = 1) :
    x ∈ U₁ ∨ x ∈ gmsV L T := by
  obtain ⟨u, hu, t, ht, rfl⟩ := hE.exists_mul_eq hx
  by_cases ht1 : t = 1
  · left
    rw [ht1, mul_one]
    exact hu
  right
  have htt : t * t = 1 := by rw [← sq]; exact hT₀.2 t ht
  have hu' : t * u * t⁻¹ ∈ U₁ := hE.conj_mem ht hu
  have h1 : u * (t * u * t⁻¹) = 1 := by
    calc u * (t * u * t⁻¹) = u * t * u * t * (t⁻¹ * t⁻¹) := by group
      _ = 1 := by
        rw [show u * t * u * t = u * t * (u * t) by group, hxx, one_mul,
          ← mul_inv_rev, htt, inv_one]
  have h2 : t * u * t⁻¹ = u := by
    have h3 : t * u * t⁻¹ = u⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h3, inv_eq_of_mul_eq_one_right (hE.mul_self hu)]
  have huA : u ∈ gmsA L T := by
    rw [← hE.centralizer_eq t ht ht1]
    refine mem_inf.mpr ⟨hu, mem_centralizer_singleton_iff.mpr ?_⟩
    calc u * t = t * u * t⁻¹ * t := by rw [h2]
      _ = t * u := by group
  exact mul_mem (mem_sup_left huA) (mem_sup_right ht)

theorem le_or_le (hE : Sec4Elem L T U₁ q) (hT₀ : IsElemAbelian 2 (T ⊓ centralizer (L : Set G)))
    {E : Subgroup G} (hEW : E ≤ U₁ ⊔ (T ⊓ centralizer (L : Set G))) (hE2 : ∀ x ∈ E, x * x = 1) :
    E ≤ U₁ ∨ E ≤ gmsV L T := by
  by_contra hne
  push Not at hne
  obtain ⟨⟨a, haE, haU⟩, ⟨b, hbE, hbV⟩⟩ :=
    And.intro (IsConcreteLE.not_le_iff_exists.mp hne.1) (IsConcreteLE.not_le_iff_exists.mp hne.2)
  have haV : a ∈ gmsV L T := (hE.mem_or_mem hT₀ (hEW haE) (hE2 a haE)).resolve_left haU
  have hbU : b ∈ U₁ := (hE.mem_or_mem hT₀ (hEW hbE) (hE2 b hbE)).resolve_right hbV
  have hab := mul_mem haE hbE
  rcases hE.mem_or_mem hT₀ (hEW hab) (hE2 _ hab) with h | h
  · exact haU (by simpa using mul_mem h (inv_mem hbU))
  · exact hbV (by simpa using mul_mem (inv_mem haV) h)

end Sec4Elem

namespace Sec4Elem

variable [Finite G] {L T U₁ : Subgroup G} {f : ℕ}

theorem conj_not_mem
    (hE : Sec4Elem L T U₁ (2 ^ f)) (h : Sec3 G L T) (hF : Foundation) (hf : 3 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) (hX : Sec3.Facts L T (2 ^ f))
    (hlt : Nat.card (T ⊓ centralizer (L : Set G) : Subgroup G) < 2 ^ f)
    {t : G} (ht : t ∈ T ⊓ centralizer (L : Set G)) (ht1 : t ≠ 1) (g : G) :
    g * t * g⁻¹ ∉ U₁ := by
  intro hu
  have hT₀ := h.isElemAbelian_T₀ hF
  have htt : t * t = 1 := by rw [← sq]; exact hT₀.2 t ht
  set E := rightConjugate U₁ g with hEdef
  have hEC : E ≤ centralizer ({t} : Set G) := by
    intro x hx
    rw [mem_rightConjugate_iff] at hx
    have h1 := hE.comm hx hu
    refine mem_centralizer_singleton_iff.mpr ?_
    calc x * t = g⁻¹ * ((g * x * g⁻¹) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = t * x := by group
  have hEN := hEC.trans (h.centralizer_le_normalizer_of_mem (mem_inf.mp ht).2 ht1 htt)
  have hEel : IsElemAbelian 2 E := isElemAbelian_map _ hE.elem
  have h1 := h.card_le_of_le_normalizer hF hf e hEN hEel
  rw [hEdef, rightConjugate_card, hE.card, (hX.vFacts h hF).1] at h1
  have h8 : 0 < 2 ^ f := by positivity
  rw [sq] at h1
  have := Nat.le_of_mul_le_mul_left h1 h8
  omega

end Sec4Elem

end CFSG.ComponentClassification.GMS78
