module

public import CFSG.LargeExtraspecial.S8A5LB
public import CFSG.LargeExtraspecial.S8A5E

public section

namespace CFSG.LargeExtraspecial.S8

open Subgroup CFSG.CGT.Timmesfeld75

universe u

variable {Γ : Type u} [Group Γ]

namespace PairDataE

variable {M A N : Subgroup Γ} {t x : Γ} (P : PairDataE M A N t x)
include P

theorem card_le_two_mul_card_centralizer [Finite Γ] {u : Γ} (huN : u ∈ N) :
    Nat.card A ≤ 2 * Nat.card (A ⊓ centralizer ({u} : Set Γ) : Subgroup Γ) := by
  have hcomm : ∀ a ∈ A, a * u * a⁻¹ * u⁻¹ ∈ zpowers t := fun a ha => P.hNc a (P.hAN ha) u huN
  let φ : A →* Γ :=
    { toFun := fun a => (a : Γ) * u * (a : Γ)⁻¹ * u⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul]
        have hb := hcomm b b.2
        have ha := hcomm a a.2
        have e1 : (a : Γ) * (b * u * (b : Γ)⁻¹ * u⁻¹) = (b * u * (b : Γ)⁻¹ * u⁻¹) * a :=
          P.comm_zpowers_N hb (P.hAN a.2)
        calc (a : Γ) * b * u * (a * b : Γ)⁻¹ * u⁻¹ =
            a * (b * u * (b : Γ)⁻¹ * u⁻¹) * u * (a : Γ)⁻¹ * u⁻¹ := by group
          _ = (b * u * (b : Γ)⁻¹ * u⁻¹) * a * u * (a : Γ)⁻¹ * u⁻¹ := by rw [e1]
          _ = (b * u * (b : Γ)⁻¹ * u⁻¹) * (a * u * (a : Γ)⁻¹ * u⁻¹) := by group
          _ = (a * u * (a : Γ)⁻¹ * u⁻¹) * (b * u * (b : Γ)⁻¹ * u⁻¹) :=
            PairData.comm_zpowers hb ha }
  have hφ : ∀ a : A, φ a = (a : Γ) * u * (a : Γ)⁻¹ * u⁻¹ := fun a => rfl
  have hrange : φ.range ≤ zpowers t := by
    rintro _ ⟨a, rfl⟩
    rw [hφ]
    exact hcomm a a.2
  have hker : ∀ a : A, a ∈ φ.ker → (a : Γ) ∈ A ⊓ centralizer ({u} : Set Γ) := by
    intro a ha
    refine ⟨a.2, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := MonoidHom.mem_ker.mp ha
    rw [hφ] at h1
    calc (a : Γ) * u = (a : Γ) * u * (a : Γ)⁻¹ * u⁻¹ * (u * a) := by group
      _ = u * a := by rw [h1, one_mul]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
  have h2 : Nat.card φ.ker ≤ Nat.card (A ⊓ centralizer ({u} : Set Γ) : Subgroup Γ) :=
    Nat.card_le_card_of_injective (fun a => ⟨a.1.1, hker a.1 a.2⟩) (fun a b h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h))
  have h3 := card_le_two_of_le_zpowers P.htt hrange
  rw [h1]
  exact Nat.mul_le_mul h3 h2

theorem E_inf_N_le (hF₁N : conjSubgroup x A ⊓ normalizer (A : Set Γ) ⊓ N = ⊥) {e : Γ}
    (he : e ∈ Epair A x) (heN : e ∈ N) : e ∈ A ⊓ normalizer (conjSubgroup x A : Set Γ) := by
  obtain ⟨f, hf, f₁, hf₁, rfl⟩ := P.exists_mul_of_mem_E he
  have hf₁N : f₁ ∈ N := by
    have := N.mul_mem (inv_mem (P.hAN hf.1)) heN
    rwa [inv_mul_cancel_left] at this
  have h1 : f₁ ∈ conjSubgroup x A ⊓ normalizer (A : Set Γ) ⊓ N := ⟨hf₁, hf₁N⟩
  rw [hF₁N, mem_bot] at h1
  rw [h1, mul_one]
  exact hf

theorem F₁_inf_N [Finite Γ] : conjSubgroup x A ⊓ normalizer (A : Set Γ) ⊓ N = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hu, huN⟩
  rw [mem_bot]
  by_contra hu1
  have h1 := P.card_le_two_mul_card_centralizer huN
  have h4 := P.h4
  have hFpos : 0 < Nat.card (A ⊓ normalizer (conjSubgroup x A : Set Γ) : Subgroup Γ) :=
    Nat.card_pos
  obtain ⟨w, ⟨hwA, hwu⟩, hwF⟩ : ∃ w ∈ A ⊓ centralizer ({u} : Set Γ),
      w ∉ A ⊓ normalizer (conjSubgroup x A : Set Γ) := by
    by_contra hcon
    push Not at hcon
    have h5 := Subgroup.card_le_of_le (fun w hw => hcon w hw)
    omega
  have hwσ : w * (x * t * x⁻¹) ≠ x * t * x⁻¹ * w := fun h => hwF ⟨hwA, (P.hF w hwA).mpr h⟩
  have hwu' : w * u = u * w := mem_centralizer_singleton_iff.mp hwu
  have hσE : x * t * x⁻¹ ∈ Epair A x := mem_sup_right P.σ_mem_F₁
  have hwE := P.sup_le_normalizer_E (mem_sup_left hwA)
  have h2 : w * (x * t * x⁻¹) * w⁻¹ ∈ Epair A x := (mem_normalizer_iff.mp hwE _).mp hσE
  have hcomm := P.comm_E h2 hσE
  have hne : w * (x * t * x⁻¹) * w⁻¹ ≠ x * t * x⁻¹ := by
    intro h
    apply hwσ
    calc w * (x * t * x⁻¹) = w * (x * t * x⁻¹) * w⁻¹ * w := by group
      _ = x * t * x⁻¹ * w := by rw [h]
  have hbot := P.hP1σ w (P.hAM hwA) hcomm hne h2
  have hmem : u ∈ conjSubgroup x A ⊓ conjSubgroup w (conjSubgroup x A) := by
    refine ⟨hu.1, mem_conjSubgroup.mpr ?_⟩
    rw [show w⁻¹ * u * w = w⁻¹ * (u * w) by group, ← hwu', inv_mul_cancel_left]
    exact hu.1
  rw [hbot, mem_bot] at hmem
  exact hu1 hmem

theorem exists_not_mem_zpowers {K : Subgroup Γ} [Finite Γ] (hK : 2 < Nat.card K) :
    ∃ a ∈ K, a ∉ zpowers t := by
  by_contra hcon
  push Not at hcon
  have := card_le_two_of_le_zpowers P.htt (fun a ha => hcon a ha)
  omega

end PairDataE

end CFSG.LargeExtraspecial.S8
