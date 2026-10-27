module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenQuot

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem conj_p450_cases {β : Perm (Fin 7)} (hβ : ∀ i : Fin 7, (i : ℕ) < 4 → β i = i) :
    (β * swap 4 5 * β⁻¹) * p450 * (β * swap 4 5 * β⁻¹)⁻¹ = p450⁻¹ ∨
      (β * swap 4 5 * β⁻¹) * p450 * (β * swap 4 5 * β⁻¹)⁻¹ = p456⁻¹ * p450 ∨
        (β * swap 4 5 * β⁻¹) * p450 * (β * swap 4 5 * β⁻¹)⁻¹ = p450 * p456⁻¹ := by
  have hge : ∀ j : Fin 7, 4 ≤ (j : ℕ) → β j = 4 ∨ β j = 5 ∨ β j = 6 := by
    intro j hj
    have h4 : 4 ≤ (β j : ℕ) := by
      by_contra hlt
      have h1 := hβ (β j) (by omega)
      have h2 : β j = j := β.injective h1
      rw [h2] at hlt
      omega
    have h7 := (β j).isLt
    rcases (by omega : (β j : ℕ) = 4 ∨ (β j : ℕ) = 5 ∨ (β j : ℕ) = 6) with h | h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Or.inl (Fin.ext h))
    · exact Or.inr (Or.inr (Fin.ext h))
  have hne : β 4 ≠ β 5 := fun h => absurd (β.injective h) (by decide)
  rw [← swap_apply_apply]
  rcases hge 4 (by norm_num) with h4 | h4 | h4 <;> rcases hge 5 (by norm_num) with h5 | h5 | h5 <;>
    rw [h4, h5] at hne ⊢ <;> first | exact absurd rfl hne | decide

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}
  {ψA : A ≃* alternatingGroup (Fin 7)} {ψB : B ≃* alternatingGroup (Fin 7)}

theorem conj_symm {K : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 7))
    (a b : alternatingGroup (Fin 7)) :
    (ψ.symm a : G) * ψ.symm b * (ψ.symm a : G)⁻¹ = (ψ.symm (a * b * a⁻¹) : G) := by
  rw [map_mul, map_mul, map_inv]
  rfl

theorem conj_of_actPerm {y : normalizer (B : Set G)} {σ : Perm (Fin 7)}
    (hy : actPerm ψB (Or.inr le_rfl) y = σ) {b c : alternatingGroup (Fin 7)}
    (hbc : σ * (b : Perm (Fin 7)) * σ⁻¹ = c) :
    (y : G) * (ψB.symm b : G) * (y : G)⁻¹ = (ψB.symm c : G) := by
  have h1 := actPerm_spec ψB (Or.inr le_rfl) y (ψB.symm b)
  rw [hy, MulEquiv.apply_symm_apply, hbc] at h1
  have h2 : ψB ⟨(y : G) * (ψB.symm b : G) * (y : G)⁻¹, _⟩ = c := Subtype.ext h1
  have h3 := congrArg (fun z => ((ψB.symm z : B) : G)) h2
  simpa using h3

theorem commute_of_inv {a b : G} (h : a * b⁻¹ = b⁻¹ * a) : a * b = b * a := by
  calc a * b = b * (b⁻¹ * a) * b := by group
    _ = b * (a * b⁻¹) * b := by rw [h]
    _ = b * a := by group

theorem xa_conj_w : xa ψA * w ψA * (xa ψA)⁻¹ = (w ψA)⁻¹ := by
  rw [xa, w, conj_symm, show a4523 * a123 * a4523⁻¹ = a123⁻¹ from Subtype.ext q4523_conj.1,
    map_inv]
  rfl

theorem xa_conj_u : xa ψA * u ψA * (xa ψA)⁻¹ = (u ψA)⁻¹ := by
  rw [xa, u, conj_symm, show a4523 * a456 * a4523⁻¹ = a456⁻¹ from Subtype.ext q4523_conj.2.1,
    map_inv]
  rfl

theorem xa_conj_c1 : xa ψA * c1 ψA * (xa ψA)⁻¹ = (c1 ψA)⁻¹ := by
  rw [xa, c1, conj_symm, show a4523 * a450 * a4523⁻¹ = a450⁻¹ from Subtype.ext q4523_conj.2.2,
    map_inv]
  rfl

theorem xa_conj_of_mem_centralizer {k : G} (hk : k ∈ centralizer (A : Set G)) :
    xa ψA * k * (xa ψA)⁻¹ = k := by
  rw [xa, (mem_centralizer_iff.mp hk) _ (ψA.symm a4523).2, mul_inv_cancel_right]

theorem xa_conj_v (hco : AltCoords 7 A B ψA ψB) : xa ψA * v ψB * (xa ψA)⁻¹ = v ψB :=
  xa_conj_of_mem_centralizer (v_mem_centralizer_A hco)

theorem xa_conj_cr (hco : AltCoords 7 A B ψA ψB) : xa ψA * cr ψB * (xa ψA)⁻¹ = (cr ψB)⁻¹ := by
  obtain ⟨hN, hact⟩ := actPerm_of_stab hco (σ := a4523) (by decide) (by decide)
  rw [show ((a4523 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = q4523 from rfl,
    restrictO_q4523] at hact
  have := conj_of_actPerm (y := ⟨_, hN⟩) hact (b := a450) (c := a450⁻¹) (by decide)
  rw [map_inv] at this
  exact this

theorem y0_conj_v : y0 ψB * v ψB * (y0 ψB)⁻¹ = (v ψB)⁻¹ := by
  rw [y0, v, conj_symm, show a4523 * a123 * a4523⁻¹ = a123⁻¹ from Subtype.ext q4523_conj.1,
    map_inv]
  rfl

theorem y0_conj_cr : y0 ψB * cr ψB * (y0 ψB)⁻¹ = (cr ψB)⁻¹ := by
  rw [y0, cr, conj_symm, show a4523 * a450 * a4523⁻¹ = a450⁻¹ from Subtype.ext q4523_conj.2.2,
    map_inv]
  rfl

theorem y0_conj_u (hco : AltCoords 7 A B ψA ψB)
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))) :
    y0 ψB * u ψA * (y0 ψB)⁻¹ = (u ψA)⁻¹ := by
  rw [u, overlap hco hodd, y0, conj_symm,
    show a4523 * a456 * a4523⁻¹ = a456⁻¹ from Subtype.ext q4523_conj.2.1, map_inv]
  rfl

theorem y0_conj_of_mem_centralizer {k : G} (hk : k ∈ centralizer (B : Set G)) :
    y0 ψB * k * (y0 ψB)⁻¹ = k := by
  rw [y0, (mem_centralizer_iff.mp hk) _ (ψB.symm a4523).2, mul_inv_cancel_right]

theorem y0_conj_w (hco : AltCoords 7 A B ψA ψB) : y0 ψB * w ψA * (y0 ψB)⁻¹ = w ψA :=
  y0_conj_of_mem_centralizer (w_mem_centralizer_B hco)

theorem eq_symm_of_coe {K : Subgroup G} (ψ : K ≃* alternatingGroup (Fin 7)) {g : G} (hg : g ∈ K)
    {σ : alternatingGroup (Fin 7)} (h : (ψ ⟨g, hg⟩ : Perm (Fin 7)) = σ) :
    g = (ψ.symm σ : G) := by
  have h1 : ψ ⟨g, hg⟩ = σ := Subtype.ext h
  rw [← h1, MulEquiv.symm_apply_apply]

theorem y0_conj_c1 (hco : AltCoords 7 A B ψA ψB) :
    y0 ψB * c1 ψA * (y0 ψB)⁻¹ = (c1 ψA)⁻¹ ∨ y0 ψB * c1 ψA * (y0 ψB)⁻¹ = (u ψA)⁻¹ * c1 ψA ∨
      y0 ψB * c1 ψA * (y0 ψB)⁻¹ = c1 ψA * (u ψA)⁻¹ := by
  obtain ⟨β, hβ, hC2⟩ := hco.2.2.2.2.2.2.1
  have hstab : ∀ i : Fin 7, (i : ℕ) < 4 → ((ψB (ψB.symm a4523) : Perm (Fin 7)) i : ℕ) < 4 := by
    rw [MulEquiv.apply_symm_apply]
    decide
  obtain ⟨ha, hae⟩ := hC2 (ψB.symm a4523) hstab (ψA.symm a450)
  rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
    show ((a4523 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = q4523 from rfl, restrictO_q4523,
    show ((a450 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = p450 from rfl] at hae
  have e0 : y0 ψB * c1 ψA * (y0 ψB)⁻¹ =
      (ψB.symm a4523 : G) * (ψA.symm a450 : G) * (ψB.symm a4523 : G)⁻¹ := rfl
  rw [e0]
  rcases conj_p450_cases hβ with h | h | h <;> rw [h] at hae
  · left
    rw [eq_symm_of_coe ψA ha (σ := a450⁻¹) hae, map_inv]
    rfl
  · right; left
    rw [eq_symm_of_coe ψA ha (σ := a456⁻¹ * a450) hae, map_mul, map_inv]
    rfl
  · right; right
    rw [eq_symm_of_coe ψA ha (σ := a450 * a456⁻¹) hae, map_mul, map_inv]
    rfl

theorem conj_comm (g : G) {a b : G} (hab : a * b = b * a) :
    (g * a * g⁻¹) * (g * b * g⁻¹) = (g * b * g⁻¹) * (g * a * g⁻¹) := by
  calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
    _ = g * (b * a) * g⁻¹ := by rw [hab]
    _ = (g * b * g⁻¹) * (g * a * g⁻¹) := by group

theorem mem_normalizer_H7 [Finite G] {g : G}
    (hw : g * w ψA * g⁻¹ = w ψA ∨ g * w ψA * g⁻¹ = (w ψA)⁻¹)
    (hv : g * v ψB * g⁻¹ = v ψB ∨ g * v ψB * g⁻¹ = (v ψB)⁻¹) :
    g ∈ normalizer (H7 ψA ψB : Set G) := by
  apply mem_normalizer_of_conj_le
  intro h hh
  have key : ∀ z : G, h * z = z * h → (g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z⁻¹) →
      (g * h * g⁻¹) * z = z * (g * h * g⁻¹) := fun z hz hz' => by
    have := conj_comm g hz
    rcases hz' with e | e <;> rw [e] at this
    · exact this
    · exact commute_of_inv this
  exact ⟨mem_centralizer_singleton_iff.mpr (key _ (mem_centralizer_singleton_iff.mp
      (mem_inf.mp hh).1) hw),
    mem_centralizer_singleton_iff.mpr (key _ (mem_centralizer_singleton_iff.mp
      (mem_inf.mp hh).2) hv)⟩

theorem xa_mem_normalizer [Finite G] (hco : AltCoords 7 A B ψA ψB) :
    xa ψA ∈ normalizer (H7 ψA ψB : Set G) :=
  mem_normalizer_H7 (Or.inr xa_conj_w) (Or.inl (xa_conj_v hco))

theorem y0_mem_normalizer [Finite G] (hco : AltCoords 7 A B ψA ψB) :
    y0 ψB ∈ normalizer (H7 ψA ψB : Set G) :=
  mem_normalizer_H7 (Or.inl (y0_conj_w hco)) (Or.inr y0_conj_v)

theorem c1_pow_three : c1 ψA ^ 3 = 1 := by
  have h : a450 ^ 3 = 1 := Subtype.ext (by decide)
  show ((ψA.symm a450 : A) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

theorem cr_pow_three : cr ψB ^ 3 = 1 := by
  have h : a450 ^ 3 = 1 := Subtype.ext (by decide)
  show ((ψB.symm a450 : B) : G) ^ 3 = 1
  rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

theorem u_mul_c1_sq : (u ψA * c1 ψA) ^ 2 = 1 := by
  have h : (a456 * a450) ^ 2 = 1 := Subtype.ext (by decide)
  show ((ψA.symm a456 : A) * (ψA.symm a450 : A) : G) ^ 2 = 1
  rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, h, map_one, Subgroup.coe_one]

theorem u_mul_cr_sq (hco : AltCoords 7 A B ψA ψB)
    (hodd : Odd (Nat.card (centralizer (A : Set G) ⊓ centralizer (B : Set G) : Subgroup G))) :
    (u ψA * cr ψB) ^ 2 = 1 := by
  have h : (a456 * a450) ^ 2 = 1 := Subtype.ext (by decide)
  rw [u, overlap hco hodd]
  show ((ψB.symm a456 : B) * (ψB.symm a450 : B) : G) ^ 2 = 1
  rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, h, map_one, Subgroup.coe_one]

end Seven

end CFSG.ComponentClassification.RankTwoAlt
