module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16Unip
public import CFSG.LocalAnalysis.OddStandard.Seitz77Nat16SL

public section

namespace CFSG.OddStandard.Seitz77

namespace Nat16

open Matrix MatrixGroups

variable {F : Type*} [Field F]

theorem torus_inv_apply (r : SL(2, F) →* AddMonoid.End (F × F)) {ζ : F} (hz : ζ ≠ 0)
    (hh : ∀ v, r (tE ζ hz) v = (ζ * v.1, ζ⁻¹ * v.2)) (v : F × F) :
    r (tE ζ⁻¹ (inv_ne_zero hz)) v = (ζ⁻¹ * v.1, ζ * v.2) := by
  have h1 : tE ζ⁻¹ (inv_ne_zero hz) * tE ζ hz = 1 := by
    rw [tE_mul]
    have : ζ⁻¹ * ζ = 1 := inv_mul_cancel₀ hz
    rw [tE_congr _ one_ne_zero this, tE_one]
  have h2 : r (tE ζ⁻¹ (inv_ne_zero hz)) (r (tE ζ hz) (ζ⁻¹ * v.1, ζ * v.2)) =
      (ζ⁻¹ * v.1, ζ * v.2) := by
    have := congrArg (fun g => r g (ζ⁻¹ * v.1, ζ * v.2)) h1
    simpa [map_mul, map_one] using this
  have h3 : r (tE ζ hz) (ζ⁻¹ * v.1, ζ * v.2) = v := by
    rw [hh]
    ext <;> simp [hz]
  rw [h3] at h2
  exact h2

section Weyl

variable [CharP F 2] (hF : Nat.card F = 16) {ζ : F} (hζ : ζ ^ 4 = ζ + 1)
variable (r : SL(2, F) →* AddMonoid.End (F × F))

include hF hζ

theorem weyl_form (hz : ζ ≠ 0) (hh : ∀ v, r (tE ζ hz) v = (ζ * v.1, ζ⁻¹ * v.2)) {κ : F}
    (hκ : κ ≠ 0) (hU : ∀ c v, r (uE c) v = (v.1 + κ * c * v.2, v.2)) (v : F × F) :
    r wE v = (κ * v.2, κ⁻¹ * v.1) := by
  have hord : orderOf ζ = 15 := Weights16.orderOf_eq_fifteen_of_pow_four hF hζ
  have hinv14 : ζ⁻¹ = ζ ^ 14 := Weights16.inv_eq_pow_fourteen hord
  have hHi := torus_inv_apply r hz hh
  have hRR : ∀ v, r wE (r wE v) = v := by
    intro v
    have := congrArg (fun g => r g v) (wE_mul_wE (F := F))
    simpa [map_mul, map_one] using this
  have hRH : ∀ v, r wE (r (tE ζ hz) v) = r (tE ζ⁻¹ (inv_ne_zero hz)) (r wE v) := by
    intro v
    have := congrArg (fun g => r g v) (wE_mul_tE ζ hz)
    simpa [map_mul] using this
  let R := r wE
  have hRadd : ∀ v w, R (v + w) = R v + R w := fun v w => map_add _ v w
  have hRx : ∀ x, R (ζ * x, 0) = (ζ⁻¹ * (R (x, 0)).1, ζ * (R (x, 0)).2) := by
    intro x
    have h1 := hRH (x, 0)
    rw [hh, hHi] at h1
    simpa using h1
  have hRy : ∀ y, R (0, ζ⁻¹ * y) = (ζ⁻¹ * (R (0, y)).1, ζ * (R (0, y)).2) := by
    intro y
    have h1 := hRH (0, y)
    rw [hh, hHi] at h1
    simpa using h1
  have hp_add : ∀ x x', (R (x + x', 0)).1 = (R (x, 0)).1 + (R (x', 0)).1 := by
    intro x x'
    have : (x + x', (0 : F)) = (x, 0) + (x', 0) := by simp
    rw [this, hRadd]; rfl
  have hq_add : ∀ x x', (R (x + x', 0)).2 = (R (x, 0)).2 + (R (x', 0)).2 := by
    intro x x'
    have : (x + x', (0 : F)) = (x, 0) + (x', 0) := by simp
    rw [this, hRadd]; rfl
  have hs_add : ∀ y y', (R (0, y + y')).1 = (R (0, y)).1 + (R (0, y')).1 := by
    intro y y'
    have : ((0 : F), y + y') = (0, y) + (0, y') := by simp
    rw [this, hRadd]; rfl
  have ht_add : ∀ y y', (R (0, y + y')).2 = (R (0, y)).2 + (R (0, y')).2 := by
    intro y y'
    have : ((0 : F), y + y') = (0, y) + (0, y') := by simp
    rw [this, hRadd]; rfl
  have hp0 : ∀ x, (R (x, 0)).1 = 0 :=
    Weights16.additive_W0_Lambda hF hord (f := fun x => (R (x, 0)).1) hp_add (fun x => by
      have := congrArg Prod.fst (hRx x)
      simp only at this
      rw [this, hinv14])
  have ht0 : ∀ y, (R (0, y)).2 = 0 :=
    Weights16.additive_Lambda_W0 hF hord (f := fun y => (R (0, y)).2) ht_add (fun y => by
      have := congrArg Prod.snd (hRy y)
      simp only at this
      show (R (0, ζ ^ 14 * y)).2 = ζ * (R (0, y)).2
      rw [← hinv14]
      exact this)
  obtain ⟨q₁, hq⟩ := Weights16.additive_single_of_weight hF hord (a := 1) (b := 1) (i₀ := 0)
    (by decide) (f := fun x => (R (x, 0)).2) hq_add (fun x => by
      have := congrArg Prod.snd (hRx x)
      simp only at this
      show (R (ζ ^ 1 * x, 0)).2 = ζ ^ 1 * (R (x, 0)).2
      rw [pow_one]
      exact this)
  obtain ⟨s₁, hs⟩ := Weights16.additive_single_of_weight hF hord (a := 14) (b := 14) (i₀ := 0)
    (by decide) (f := fun y => (R (0, y)).1) hs_add (fun y => by
      have := congrArg Prod.fst (hRy y)
      simp only at this
      show (R (0, ζ ^ 14 * y)).1 = ζ ^ 14 * (R (0, y)).1
      rw [← hinv14]
      exact this)
  have hRv : ∀ v : F × F, R v = (s₁ * v.2, q₁ * v.1) := by
    intro v
    have h1 : R v = R (v.1, 0) + R (0, v.2) := by
      rw [← hRadd]
      congr 1
      ext <;> simp
    have h2 := hq v.1
    have h3 := hs v.2
    simp only [Fin.val_zero, pow_zero, pow_one] at h2 h3
    rw [h1]
    ext
    · simp [hp0, h3]
    · simp [ht0, h2]
  have hsq : s₁ * q₁ = 1 := by
    have h1 := hRR (1, 0)
    rw [hRv (1, 0), hRv] at h1
    have := congrArg Prod.fst h1
    simpa using this
  have hrel : uE (1 : F) * (wE * uE 1 * wE) * uE 1 = wE := by
    rw [wE_mul_uE_mul_wE, uE_mul_lE_mul_uE]
  have hU1 : ∀ v : F × F, r (uE 1) v = (v.1 + κ * v.2, v.2) := by
    intro v
    rw [hU]
    simp
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hkey := congrArg (fun g => r g (1, 0)) hrel
  simp only [map_mul] at hkey
  have hkey' : (r (uE 1)) (R ((r (uE 1)) (R ((r (uE 1)) (1, 0))))) = R (1, 0) := hkey
  rw [hU1 (1, 0), hRv, hU1, hRv, hU1, hRv] at hkey'
  have e1 := congrArg Prod.fst hkey'
  have e2 := congrArg Prod.snd hkey'
  simp only at e1 e2
  have hm : (κ * q₁ + 1) ^ 2 = 0 := by
    linear_combination e1 - hsq + (κ * q₁) * h2
  have hm1 : κ * q₁ + 1 = 0 := (pow_eq_zero_iff two_ne_zero).1 hm
  have hκq : κ * q₁ = 1 := by linear_combination hm1 - h2
  have hq₁ : q₁ = κ⁻¹ := eq_inv_of_mul_eq_one_right hκq
  have hs₁ : s₁ = κ := by
    rw [hq₁] at hsq
    field_simp at hsq
    exact hsq
  rw [hRv v, hs₁, hq₁]


theorem natural_of_torus (hz : ζ ≠ 0) (hh : ∀ v, r (tE ζ hz) v = (ζ * v.1, ζ⁻¹ * v.2))
    (hinj : Function.Injective r) :
    ∃ κ : F, κ ≠ 0 ∧ ∀ g v, (κ⁻¹ * (r g v).1, (r g v).2) = natHom g (κ⁻¹ * v.1, v.2) := by
  have h0 : ∀ v, r (uE 0) v = v := by
    intro v
    rw [uE_zero, map_one]
    rfl
  have hadd : ∀ c c' v, r (uE (c + c')) v = r (uE c) (r (uE c') v) := by
    intro c c' v
    rw [uE_add, map_mul]
    rfl
  have hequiv : ∀ c v, (ζ * (r (uE c) v).1, ζ⁻¹ * (r (uE c) v).2) =
      r (uE (ζ * ζ * c)) (ζ * v.1, ζ⁻¹ * v.2) := by
    intro c v
    rw [← hh, ← hh]
    have := congrArg (fun g => r g v) (tE_mul_uE ζ hz c)
    simpa [map_mul] using this
  have hnt : ∃ v, r (uE 1) v ≠ v := by
    by_contra hcon
    push Not at hcon
    apply uE_ne_one (one_ne_zero (α := F))
    apply hinj
    rw [map_one]
    exact AddMonoidHom.ext hcon
  obtain ⟨κ, hκ, hU0⟩ := unip_form hF hζ (fun c => r (uE c)) h0 hadd hequiv hnt
  have hU : ∀ c v, r (uE c) v = (v.1 + κ * c * v.2, v.2) := hU0
  refine ⟨κ, hκ, ?_⟩
  have hW := weyl_form hF hζ r hz hh hκ hU
  intro g
  have hg : g ∈ Subgroup.closure (Set.range (uE : F → SL(2, F)) ∪ {wE}) := by
    rw [closure_uE_wE]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | hx
    · intro v
      rw [hU, natHom_uE]
      refine Prod.ext ?_ rfl
      simp only
      field_simp
    · intro v
      rw [Set.mem_singleton_iff.1 hx, hW, natHom_wE]
      refine Prod.ext ?_ rfl
      simp only
      field_simp
  | one =>
    intro v
    rw [map_one, map_one]
    rfl
  | mul x y _ _ hx hy =>
    intro v
    rw [map_mul, map_mul]
    show (κ⁻¹ * (r x (r y v)).1, (r x (r y v)).2) = natHom x (natHom y _)
    rw [hx (r y v), hy v]
  | inv x _ hx =>
    intro v
    have h1 := hx (r x⁻¹ v)
    have h2 : r x (r x⁻¹ v) = v := by
      calc r x (r x⁻¹ v) = (r x * r x⁻¹) v := rfl
        _ = r (x * x⁻¹) v := by rw [map_mul]
        _ = v := by rw [mul_inv_cancel, map_one]; rfl
    rw [h2] at h1
    have h3 : natHom x⁻¹ (natHom x (κ⁻¹ * (r x⁻¹ v).1, (r x⁻¹ v).2)) =
        (κ⁻¹ * (r x⁻¹ v).1, (r x⁻¹ v).2) := by
      calc natHom x⁻¹ (natHom x (κ⁻¹ * (r x⁻¹ v).1, (r x⁻¹ v).2))
          = (natHom x⁻¹ * natHom x) (κ⁻¹ * (r x⁻¹ v).1, (r x⁻¹ v).2) := rfl
        _ = natHom (x⁻¹ * x) (κ⁻¹ * (r x⁻¹ v).1, (r x⁻¹ v).2) := by rw [map_mul]
        _ = _ := by rw [inv_mul_cancel, map_one]; rfl
    rw [← h3, ← h1]

end Weyl


end Nat16

end CFSG.OddStandard.Seitz77
