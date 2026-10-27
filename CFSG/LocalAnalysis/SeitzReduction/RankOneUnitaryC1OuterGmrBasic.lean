module

import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

section Field

variable {E : Type*} [Field E] [CharP E 2]

theorem gmr_false_of_pow_five {c : E} (h1 : c ^ 5 = 1) (h2 : (1 + c) ^ 5 = 1) : False := by
  have h0 : (2 : E) = 0 := CharTwo.two_eq_zero
  have h : (1 : E) = 0 := by
    linear_combination (-(c ^ 3 + c ^ 2 + 1) - (c ^ 2 + c)) * h1 + (c ^ 3 + c ^ 2 + 1) * h2 +
      (-2 * c ^ 7 - 7 * c ^ 6 - 10 * c ^ 5 - 10 * c ^ 4 - 8 * c ^ 3 - 6 * c ^ 2 - 3 * c) * h0
  exact one_ne_zero h

theorem gmr_card_range_le [Finite E] (σ : E →+* E) {B : Type*} [Group B]
    (ψ : B →* Multiplicative E) (Z : Set E)
    (hN : ∀ b, Multiplicative.toAdd (ψ b) * σ (Multiplicative.toAdd (ψ b)) ∈ Z)
    (hT : ∀ b b', Multiplicative.toAdd (ψ b) * σ (Multiplicative.toAdd (ψ b')) +
      σ (Multiplicative.toAdd (ψ b)) * Multiplicative.toAdd (ψ b') ∈ Z) :
    Nat.card ψ.range ≤ Nat.card Z ^ 2 := by
  classical
  have h0 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hZ0 : (0 : E) ∈ Z := by
    have h := hN 1
    rwa [map_one, toAdd_one, zero_mul] at h
  have hZpos : 0 < Nat.card Z := by
    have : Nonempty Z := ⟨⟨0, hZ0⟩⟩
    exact Nat.card_pos
  by_cases hall : ∀ b, ψ b = 1
  · have hr : ψ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨b, rfl⟩
      rw [mem_bot]
      exact hall b
    rw [hr, card_bot]
    exact Nat.one_le_pow _ _ hZpos
  push Not at hall
  obtain ⟨b₀, hb₀⟩ := hall
  set a := Multiplicative.toAdd (ψ b₀) with ha
  have ha0 : a ≠ 0 := fun h => hb₀ (by rw [← ofAdd_toAdd (ψ b₀), ← ha, h, ofAdd_zero])
  let θ₀ : E →+ E :=
    { toFun := fun e => a * σ e + σ a * e
      map_zero' := by simp
      map_add' := fun e e' => by simp only [map_add]; ring }
  let θ : ψ.range →* Multiplicative E :=
    (AddMonoidHom.toMultiplicative θ₀).comp ψ.range.subtype
  have hθ : ∀ z : ψ.range, Multiplicative.toAdd (θ z) =
      a * σ (Multiplicative.toAdd (z : Multiplicative E)) +
        σ a * Multiplicative.toAdd (z : Multiplicative E) := fun z => rfl
  have hcard := Subgroup.card_mul_index θ.ker
  rw [Subgroup.index_ker] at hcard
  rw [← hcard, sq]
  refine Nat.mul_le_mul ?_ ?_
  ·
    have hker : ∀ z : θ.ker, a * σ (Multiplicative.toAdd ((z : ψ.range) : Multiplicative E)) +
        σ a * Multiplicative.toAdd ((z : ψ.range) : Multiplicative E) = 0 := by
      intro z
      rw [← hθ (z : ψ.range), MonoidHom.mem_ker.mp z.2, toAdd_one]
    let κ : θ.ker → Z := fun z =>
      ⟨Multiplicative.toAdd ((z : ψ.range) : Multiplicative E) *
        σ (Multiplicative.toAdd ((z : ψ.range) : Multiplicative E)), by
        obtain ⟨b, hb⟩ := (z : ψ.range).2
        rw [← hb]
        exact hN b⟩
    refine Nat.card_le_card_of_injective κ fun z z' hzz' => ?_
    have hn : Multiplicative.toAdd ((z : ψ.range) : Multiplicative E) *
        σ (Multiplicative.toAdd ((z : ψ.range) : Multiplicative E)) =
        Multiplicative.toAdd ((z' : ψ.range) : Multiplicative E) *
          σ (Multiplicative.toAdd ((z' : ψ.range) : Multiplicative E)) :=
      congrArg Subtype.val hzz'
    have hk := hker z
    have hk' := hker z'
    set e := Multiplicative.toAdd ((z : ψ.range) : Multiplicative E) with he
    set e' := Multiplicative.toAdd ((z' : ψ.range) : Multiplicative E) with he'
    have hprod : a * ((e + e') * σ (e + e')) = 0 := by
      rw [map_add]
      linear_combination e * hk' + e' * hk + a * hn + (a * e' * σ e' - σ a * e * e') * h0
    have hee : e + e' = 0 := by
      rcases mul_eq_zero.mp hprod with h | h
      · exact absurd h ha0
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact (map_eq_zero σ).mp h'
    have hee' : e = e' := by linear_combination hee - e' * h0
    apply Subtype.ext
    apply Subtype.ext
    exact Multiplicative.toAdd.injective hee'
  ·
    let ρ : θ.range → Z := fun z => ⟨Multiplicative.toAdd (z : Multiplicative E), by
      obtain ⟨y, hy⟩ := z.2
      rw [← hy, hθ]
      obtain ⟨b, hb⟩ := y.2
      rw [← hb]
      exact hT b₀ b⟩
    refine Nat.card_le_card_of_injective ρ fun z z' hzz' => ?_
    have h := congrArg (Subtype.val : Z → E) hzz'
    exact Subtype.ext (Multiplicative.toAdd.injective h)

omit [CharP E 2] in
theorem gmr_eq_of_card_le_two [Finite E] {Z : Set E} (hZ : Nat.card Z ≤ 2) (h0 : (0 : E) ∈ Z)
    {z₁ z₂ : E} (h1 : z₁ ∈ Z) (h2 : z₂ ∈ Z) (hz₁ : z₁ ≠ 0) (hz₂ : z₂ ≠ 0) : z₁ = z₂ := by
  by_contra h12
  have hsub : ({0, z₁, z₂} : Set E) ⊆ Z := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact h2
  have h3 : ({0, z₁, z₂} : Set E).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨0, z₁, z₂, hz₁.symm, hz₂.symm, h12, rfl⟩
  have h4 := Set.ncard_le_ncard hsub (Set.toFinite Z)
  rw [h3, ← Nat.card_coe_set_eq] at h4
  omega

theorem gmr_card_range_le_two [Finite E] (σ : E →+* E) (hσ : ∀ z, σ z = z ^ 4) {B : Type*}
    [Group B] (ψ : B →* Multiplicative E) (Z : Set E) (hZ : Nat.card Z ≤ 2)
    (hN : ∀ b, Multiplicative.toAdd (ψ b) * σ (Multiplicative.toAdd (ψ b)) ∈ Z) :
    Nat.card ψ.range ≤ 2 := by
  classical
  have h0 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hZ0 : (0 : E) ∈ Z := by
    have h := hN 1
    rwa [map_one, toAdd_one, zero_mul] at h
  have hN5 : ∀ b, Multiplicative.toAdd (ψ b) ^ 5 ∈ Z := fun b => by
    have h := hN b
    rwa [hσ, ← pow_succ'] at h
  have key : ∀ b₁ b₂, Multiplicative.toAdd (ψ b₁) ≠ 0 → Multiplicative.toAdd (ψ b₂) ≠ 0 →
      ψ b₁ = ψ b₂ := by
    intro b₁ b₂ h1 h2
    by_contra h12
    have hsum : Multiplicative.toAdd (ψ (b₁ * b₂)) =
        Multiplicative.toAdd (ψ b₁) + Multiplicative.toAdd (ψ b₂) := by
      rw [map_mul, toAdd_mul]
    have hN12 := hN5 (b₁ * b₂)
    rw [hsum] at hN12
    set a := Multiplicative.toAdd (ψ b₁) with ha
    set b := Multiplicative.toAdd (ψ b₂) with hb
    have hab : a ≠ b := fun h => h12 (by
      rw [← ofAdd_toAdd (ψ b₁), ← ofAdd_toAdd (ψ b₂), ← ha, ← hb, h])
    have hab0 : a + b ≠ 0 := fun h => hab (by linear_combination h - b * h0)
    have ha5 : a ^ 5 ≠ 0 := pow_ne_zero 5 h1
    have e1 := gmr_eq_of_card_le_two hZ hZ0 (hN5 b₁) (hN5 b₂) ha5 (pow_ne_zero 5 h2)
    have e2 := gmr_eq_of_card_le_two hZ hZ0 (hN5 b₁) hN12 ha5 (pow_ne_zero 5 hab0)
    refine gmr_false_of_pow_five (c := b / a) ?_ ?_
    · rw [div_pow, ← e1, div_self ha5]
    · rw [show 1 + b / a = (a + b) / a by rw [add_div, div_self h1], div_pow, ← e2,
        div_self ha5]
  refine (Nat.card_le_card_of_injective (fun z : ψ.range =>
    decide (Multiplicative.toAdd (z : Multiplicative E) = 0)) fun z z' hzz' => ?_).trans
    (by rw [Nat.card_eq_fintype_card, Fintype.card_bool])
  obtain ⟨b₁, hb₁⟩ := z.2
  obtain ⟨b₂, hb₂⟩ := z'.2
  apply Subtype.ext
  simp only at hzz'
  rw [← hb₁, ← hb₂] at hzz' ⊢
  by_cases h1 : Multiplicative.toAdd (ψ b₁) = 0 <;> by_cases h2 : Multiplicative.toAdd (ψ b₂) = 0
  · exact Multiplicative.toAdd.injective (h1.trans h2.symm)
  · simp [h1, h2] at hzz'
  · simp [h1, h2] at hzz'
  · exact key b₁ b₂ h1 h2

end Field

section Count

variable {G : Type*} [Group G] [Finite G]

theorem gmr_card_mul_le {U A : Subgroup G} {x : G} (hAU : A ≤ U) (hx2 : x * x = 1)
    (hxU : ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hxA : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hAc : ∀ a ∈ A, ∀ u ∈ U, a * u = u * a) (hA2 : ∀ a ∈ A, a * a = 1)
    (hcomm : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ A) (hsq : ∀ u ∈ U, u * u ∈ A) :
    Nat.card U * Nat.card A ≤
      (Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G)) ^ 2 := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hθU : ∀ u ∈ U, u⁻¹ * (x * u * x⁻¹) ∈ U := fun u hu => mul_mem (inv_mem hu) (hxU u hu)
  have hθx : ∀ u : G, x * (u⁻¹ * (x * u * x⁻¹)) * x⁻¹ = (u⁻¹ * (x * u * x⁻¹))⁻¹ := by
    intro u
    rw [hxinv]
    calc x * (u⁻¹ * (x * u * x)) * x = x * u⁻¹ * x * u * (x * x) := by group
      _ = x * u⁻¹ * x * u := by rw [hx2, mul_one]
      _ = (u⁻¹ * (x * u * x))⁻¹ := by
        rw [mul_inv_rev, mul_inv_rev, mul_inv_rev, inv_inv, hxinv]
        group
  let C : Subgroup G :=
    { carrier := {u | u ∈ U ∧ u⁻¹ * (x * u * x⁻¹) ∈ A}
      mul_mem' := by
        rintro u v ⟨hu, hua⟩ ⟨hv, hva⟩
        refine ⟨mul_mem hu hv, ?_⟩
        have e : (u * v)⁻¹ * (x * (u * v) * x⁻¹) =
            v⁻¹ * ((u⁻¹ * (x * u * x⁻¹)) * v) * (v⁻¹ * (x * v * x⁻¹)) := by group
        rw [e, hAc _ hua v hv, inv_mul_cancel_left]
        exact mul_mem hua hva
      one_mem' := ⟨one_mem _, by simp⟩
      inv_mem' := by
        rintro u ⟨hu, hua⟩
        refine ⟨inv_mem hu, ?_⟩
        have e : u⁻¹⁻¹ * (x * u⁻¹ * x⁻¹) = u * ((u⁻¹ * (x * u * x⁻¹))⁻¹ * u⁻¹) := by group
        rw [e, hAc _ (inv_mem hua) u⁻¹ (inv_mem hu), mul_inv_cancel_left]
        exact inv_mem hua }
  have hmemC : ∀ {u : G}, u ∈ C ↔ u ∈ U ∧ u⁻¹ * (x * u * x⁻¹) ∈ A := Iff.rfl
  have hCU : C ≤ U := fun u hu => (hmemC.mp hu).1
  have hAC : A ≤ C := fun a ha => hmemC.mpr ⟨hAU ha, mul_mem (inv_mem ha) (hxA a ha)⟩
  have hθC : ∀ u ∈ U, u⁻¹ * (x * u * x⁻¹) ∈ C := by
    intro u hu
    refine hmemC.mpr ⟨hθU u hu, ?_⟩
    rw [hθx u, ← mul_inv_rev]
    exact inv_mem (hsq _ (hθU u hu))
  have hkey : ∀ u ∈ U, ∀ c ∈ U, ((u⁻¹ * (x * u * x⁻¹))⁻¹ *
      ((u * c)⁻¹ * (x * (u * c) * x⁻¹)) ∈ A ↔ c⁻¹ * (x * c * x⁻¹) ∈ A) := by
    intro u hu c hc
    have h1 := hcomm _ (inv_mem (hθU u hu)) _ (inv_mem hc)
    rw [inv_inv, inv_inv] at h1
    have e : (u⁻¹ * (x * u * x⁻¹))⁻¹ * ((u * c)⁻¹ * (x * (u * c) * x⁻¹)) =
        ((u⁻¹ * (x * u * x⁻¹))⁻¹ * c⁻¹ * (u⁻¹ * (x * u * x⁻¹)) * c) *
          (c⁻¹ * (x * c * x⁻¹)) := by group
    rw [e]
    refine ⟨fun h => ?_, fun h => mul_mem h1 h⟩
    have h2 := mul_mem (inv_mem h1) h
    rwa [inv_mul_cancel_left] at h2
  set C' : Subgroup U := C.subgroupOf U with hC'
  set A' : Subgroup C := A.subgroupOf C with hA'
  let Φ : U ⧸ C' → C ⧸ A' := Quotient.lift
    (fun u : U => (QuotientGroup.mk (⟨(u : G)⁻¹ * (x * u * x⁻¹), hθC u u.2⟩ : C) : C ⧸ A'))
    (by
      intro u u' huu'
      have hmem : (u : G)⁻¹ * u' ∈ C := by
        have := QuotientGroup.leftRel_apply.mp huu'
        rw [hC', mem_subgroupOf] at this
        simpa using this
      apply QuotientGroup.eq.mpr
      rw [hA', mem_subgroupOf]
      simp only [coe_mul, coe_inv]
      have h1 := (hkey u u.2 _ (mul_mem (inv_mem u.2) u'.2)).mpr (hmemC.mp hmem).2
      rwa [mul_inv_cancel_left] at h1)
  have hΦ : Function.Injective Φ := by
    intro p p' hpp'
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective p'
    have h1 := QuotientGroup.eq.mp hpp'
    rw [hA', mem_subgroupOf] at h1
    simp only [coe_mul, coe_inv] at h1
    apply QuotientGroup.eq.mpr
    rw [hC', mem_subgroupOf]
    simp only [coe_mul, coe_inv]
    have hc : (u : G)⁻¹ * u' ∈ U := mul_mem (inv_mem u.2) u'.2
    refine hmemC.mpr ⟨hc, (hkey u u.2 _ hc).mp ?_⟩
    rwa [mul_inv_cancel_left]
  have hle : Nat.card (U ⧸ C') ≤ Nat.card (C ⧸ A') := Nat.card_le_card_of_injective Φ hΦ
  have e1 := C'.card_mul_index
  have e2 := A'.card_mul_index
  rw [Subgroup.index] at e1 e2
  rw [hC', Nat.card_congr (subgroupOfEquivOfLe hCU).toEquiv] at e1
  rw [hA', Nat.card_congr (subgroupOfEquivOfLe hAC).toEquiv] at e2
  have hUA : Nat.card U * Nat.card A ≤ Nat.card C * Nat.card C := by
    calc Nat.card U * Nat.card A = Nat.card C * (Nat.card A * Nat.card (U ⧸ C')) := by
          rw [← e1]; ring
      _ ≤ Nat.card C * (Nat.card A * Nat.card (C ⧸ A')) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hle)
      _ = Nat.card C * Nat.card C := by rw [e2]
  let δ : C →* G := MonoidHom.mk' (fun c => (c : G)⁻¹ * (x * c * x⁻¹)) (by
    intro c c'
    simp only [coe_mul]
    have hcA := (hmemC.mp c.2).2
    have hc'U := (hmemC.mp c'.2).1
    calc ((c : G) * c')⁻¹ * (x * (c * c') * x⁻¹) =
          (c' : G)⁻¹ * (((c : G)⁻¹ * (x * c * x⁻¹)) * c') * ((c' : G)⁻¹ * (x * c' * x⁻¹)) := by
            group
      _ = ((c : G)⁻¹ * (x * c * x⁻¹)) * ((c' : G)⁻¹ * (x * c' * x⁻¹)) := by
            rw [hAc _ hcA _ hc'U, inv_mul_cancel_left])
  have hδ : ∀ c : C, δ c = (c : G)⁻¹ * (x * c * x⁻¹) := fun c => rfl
  have hrange : δ.range ≤ A ⊓ centralizer ({x} : Set G) := by
    rintro _ ⟨c, rfl⟩
    rw [hδ]
    have hcA := (hmemC.mp c.2).2
    refine mem_inf.mpr ⟨hcA, mem_centralizer_singleton_iff.mpr ?_⟩
    have hinv : ((c : G)⁻¹ * (x * c * x⁻¹))⁻¹ = (c : G)⁻¹ * (x * c * x⁻¹) :=
      inv_eq_of_mul_eq_one_right (hA2 _ hcA)
    have h1 := hθx (c : G)
    rw [hinv] at h1
    calc (c : G)⁻¹ * (x * c * x⁻¹) * x = x * ((c : G)⁻¹ * (x * c * x⁻¹)) * x⁻¹ * x := by
          rw [h1]
      _ = x * ((c : G)⁻¹ * (x * c * x⁻¹)) := by group
  have hker : Nat.card δ.ker ≤ Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun c : δ.ker =>
      (⟨((c : C) : G), mem_inf.mpr ⟨(hmemC.mp (c : C).2).1,
        mem_centralizer_singleton_iff.mpr ?_⟩⟩ : (U ⊓ centralizer ({x} : Set G) : Subgroup G)))
      fun c c' hcc' => ?_
    · have h1 : δ (c : C) = 1 := MonoidHom.mem_ker.mp c.2
      rw [hδ] at h1
      have h2 : x * ((c : C) : G) * x⁻¹ = ((c : C) : G) := by
        calc x * ((c : C) : G) * x⁻¹ = ((c : C) : G) * (((c : C) : G)⁻¹ * (x * c * x⁻¹)) := by
              group
          _ = ((c : C) : G) := by rw [h1, mul_one]
      calc ((c : C) : G) * x = x * ((c : C) : G) * x⁻¹ * x := by rw [h2]
        _ = x * ((c : C) : G) := by group
    · have h := congrArg (Subtype.val : (U ⊓ centralizer ({x} : Set G) : Subgroup G) → G) hcc'
      exact Subtype.ext (Subtype.ext h)
  have hCcard : Nat.card C ≤ Nat.card (U ⊓ centralizer ({x} : Set G) : Subgroup G) *
      Nat.card (A ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have h1 := Subgroup.card_mul_index δ.ker
    rw [Subgroup.index_ker] at h1
    rw [← h1]
    exact Nat.mul_le_mul hker (card_le_of_le hrange)
  calc Nat.card U * Nat.card A ≤ Nat.card C * Nat.card C := hUA
    _ ≤ _ := by rw [sq]; exact Nat.mul_le_mul hCcard hCcard

end Count

end CFSG.SeitzReduction.RankOne
