module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic

open Subgroup

section Complement

variable {G : Type*} [Group G] [Finite G]

theorem exists_fixed_outside {E U : Subgroup G} {t z : G} (hEsq : ∀ e ∈ E, e * e = 1)
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hE : Nat.card ↥E = 16) (ht2 : t * t = 1)
    (htE : ∀ x ∈ E, t * x * t⁻¹ ∈ E)
    (hCU : ∀ x ∈ U, t * x * t⁻¹ = x → x = 1 ∨ x = z) :
    ∃ e ∈ E, e ∉ U ∧ t * e * t⁻¹ = e := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  let θ₀ : ↥E → ↥E := fun v => ⟨(v : G) * (t * (v : G) * t⁻¹), mul_mem v.2 (htE _ v.2)⟩
  have hθmul : ∀ a b : ↥E, θ₀ (a * b) = θ₀ a * θ₀ b := by
    intro a b
    apply Subtype.ext
    show (a : G) * (b : G) * (t * ((a : G) * (b : G)) * t⁻¹) =
      ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹))
    have hc : (b : G) * (t * (a : G) * t⁻¹) = (t * (a : G) * t⁻¹) * (b : G) :=
      hEc _ b.2 _ (htE _ a.2)
    calc (a : G) * (b : G) * (t * ((a : G) * (b : G)) * t⁻¹)
        = (a : G) * ((b : G) * (t * (a : G) * t⁻¹)) * (t * (b : G) * t⁻¹) := by group
      _ = (a : G) * ((t * (a : G) * t⁻¹) * (b : G)) * (t * (b : G) * t⁻¹) := by rw [hc]
      _ = ((a : G) * (t * (a : G) * t⁻¹)) * ((b : G) * (t * (b : G) * t⁻¹)) := by group
  let θ : ↥E →* ↥E := MonoidHom.mk' θ₀ hθmul
  set C : Subgroup G := E ⊓ centralizer ({t} : Set G) with hC
  have hker : ∀ v : ↥E, v ∈ θ.ker → (v : G) ∈ C := by
    intro v hv
    have h1 : (v : G) * (t * (v : G) * t⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hv)
    have h2 : t * (v : G) * t⁻¹ = (v : G) := by
      have := eq_inv_of_mul_eq_one_right h1
      rw [this]
      exact inv_eq_of_mul_eq_one_right (hEsq v v.2)
    refine Subgroup.mem_inf.2 ⟨v.2, Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    calc t * (v : G) = (t * (v : G) * t⁻¹) * t := by group
      _ = (v : G) * t := by rw [h2]
  have hrange : ∀ g ∈ θ.range, (g : G) ∈ C := by
    rintro g ⟨v, rfl⟩
    have hv := v.2
    have hw := htE _ hv
    have hcomm : (t * (v : G) * t⁻¹) * (v : G) = (v : G) * (t * (v : G) * t⁻¹) := (hEc _ hw _ hv)
    refine Subgroup.mem_inf.2 ⟨(θ v).2, Subgroup.mem_centralizer_iff.2 (fun x hx => ?_)⟩
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    show t * ((v : G) * (t * (v : G) * t⁻¹)) = ((v : G) * (t * (v : G) * t⁻¹)) * t
    calc t * ((v : G) * (t * (v : G) * t⁻¹))
        = (t * (v : G) * t⁻¹) * (t * t) * (v : G) * t⁻¹ := by group
      _ = (t * (v : G) * t⁻¹) * (v : G) * t⁻¹ := by rw [ht2, mul_one]
      _ = (v : G) * (t * (v : G) * t⁻¹) * t⁻¹ := by rw [hcomm]
      _ = ((v : G) * (t * (v : G) * t⁻¹)) * t := by rw [htinv]
  have hCcard : 4 ≤ Nat.card ↥C := by
    have h1 := Subgroup.card_mul_index θ.ker
    rw [Subgroup.index_ker, hE] at h1
    have h2 : Nat.card θ.ker ≤ Nat.card ↥C := by
      refine Nat.card_le_card_of_injective (fun v => ⟨((v : ↥E) : G), hker v v.2⟩) ?_
      intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
    have h3 : Nat.card θ.range ≤ Nat.card ↥C := by
      refine Nat.card_le_card_of_injective (fun g => ⟨((g : ↥E) : G), hrange g g.2⟩) ?_
      intro a b hab
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab))
    by_contra hlt
    push Not at hlt
    have : 16 ≤ 3 * 3 := by
      calc 16 = Nat.card θ.ker * Nat.card θ.range := h1.symm
        _ ≤ 3 * 3 := Nat.mul_le_mul (by omega) (by omega)
    omega
  by_contra hcon
  push Not at hcon
  have hsub : ∀ x ∈ C, x = 1 ∨ x = z := by
    intro x hx
    have hxE : x ∈ E := hx.1
    have hxt : t * x * t⁻¹ = x := by
      have := (Subgroup.mem_centralizer_iff.1 hx.2) t (Set.mem_singleton t)
      calc t * x * t⁻¹ = (x * t) * t⁻¹ := by rw [this]
        _ = x := by group
    by_cases hxU : x ∈ U
    · exact hCU x hxU hxt
    · exact absurd hxt (hcon x hxE hxU)
  have hle : Nat.card ↥C ≤ 2 := by
    have hsubset : (C : Set G) ⊆ {1, z} := by
      intro x hx
      rcases hsub x hx with h | h
      · exact Or.inl h
      · exact Or.inr h
    have h1 : (C : Set G).ncard ≤ ({1, z} : Set G).ncard :=
      Set.ncard_le_ncard hsubset (Set.toFinite _)
    have h2 : ({1, z} : Set G).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({z} : Set G)
      rw [Set.ncard_singleton] at this
      exact this
    have h3 : Nat.card ↥C = (C : Set G).ncard := Nat.card_coe_set_eq (C : Set G)
    omega
  omega

end Complement

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic
