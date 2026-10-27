module

public import CFSG.Quasithin.Background.G6PGroup

public section

namespace CFSG.CGT.PushingUpLit.CGT6E

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

@[expose] def normHom (d : MulAut V) : V →* V where
  toFun v := v * d v * d (d v)
  map_one' := by simp
  map_mul' v w := by simp only [map_mul]; ac_rfl

theorem normHom_apply (d : MulAut V) (v : V) : normHom d v = v * d v * d (d v) := rfl

theorem apply_apply_apply_of_pow_three {d : MulAut V} (hd : d ^ 3 = 1) (v : V) :
    d (d (d v)) = v := by
  have h : (d ^ 3) v = v := by rw [hd]; rfl
  simpa [pow_succ, MulAut.mul_apply] using h

theorem apply_normHom {d : MulAut V} (hd : d ^ 3 = 1) (v : V) :
    d (normHom d v) = normHom d v := by
  rw [normHom_apply, map_mul, map_mul, apply_apply_apply_of_pow_three hd]
  ac_rfl

theorem normHom_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} {v : V} (hv : d v = v) :
    normHom d v = v := by
  rw [normHom_apply, hv, hv, mul_assoc, ← pow_two, hV, mul_one]

theorem normHom_apply_apply {d : MulAut V} (hd : d ^ 3 = 1) (v : V) :
    normHom d (d v) = normHom d v := by
  rw [normHom_apply, normHom_apply, apply_apply_apply_of_pow_three hd]
  ac_rfl

theorem normHom_of_mem_zpowers {d : MulAut V} (hd : d ^ 3 = 1) {x : MulAut V}
    (hx : x ∈ Subgroup.zpowers d) (v : V) : normHom d (x v) = normHom d v := by
  let S : Subgroup (MulAut V) :=
    { carrier := {x | ∀ v, normHom d (x v) = normHom d v}
      one_mem' := fun v => rfl
      mul_mem' := fun {a b} ha hb v => by
        show normHom d (a (b v)) = normHom d v
        rw [ha, hb]
      inv_mem' := fun {a} ha v => by
        have := ha (a⁻¹ v)
        rw [MulAut.apply_inv_self] at this
        exact this.symm }
  have hdS : d ∈ S := fun v => normHom_apply_apply hd v
  exact (Subgroup.zpowers_le.mpr hdS) hx v

theorem normHom_eq_one_of_mem_commV {d : MulAut V} (hd : d ^ 3 = 1) {w : V}
    (hw : w ∈ commV (Subgroup.zpowers d)) : normHom d w = 1 := by
  have hle : commV (Subgroup.zpowers d) ≤ (normHom d).ker := by
    rw [G6.commV_le_iff]
    intro x hx v
    rw [MonoidHom.mem_ker, map_mul, map_inv, normHom_of_mem_zpowers hd hx, mul_inv_cancel]
  exact hle hw

theorem mul_inv_normHom_mem_commV (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} (v : V) :
    v * (normHom d v)⁻¹ ∈ commV (Subgroup.zpowers d) := by
  have h1 : d v * v⁻¹ ∈ commV (Subgroup.zpowers d) :=
    G6.mem_commV_of_mem (Subgroup.mem_zpowers d) v
  have h2 : d (d v) * v⁻¹ ∈ commV (Subgroup.zpowers d) := by
    have := G6.mem_commV_of_mem (X := Subgroup.zpowers d)
      (Subgroup.mul_mem _ (Subgroup.mem_zpowers d) (Subgroup.mem_zpowers d)) v
    simpa [MulAut.mul_apply] using this
  have hvv : v * v = 1 := by rw [← pow_two]; exact hV v
  have key : ∀ x : V, v * (v * x)⁻¹ = x⁻¹ := fun x => by
    rw [mul_inv_rev, mul_comm x⁻¹ v⁻¹, mul_inv_cancel_left]
  have h3 : (d v * v⁻¹ * (d (d v) * v⁻¹))⁻¹ = (d v * d (d v))⁻¹ * (v * v) := by
    simp only [mul_inv_rev, inv_inv]; ac_rfl
  have e : v * (normHom d v)⁻¹ = ((d v * v⁻¹) * (d (d v) * v⁻¹))⁻¹ := by
    rw [h3, hvv, mul_one, normHom_apply, mul_assoc, key]
  rw [e]
  exact inv_mem (mul_mem h1 h2)

theorem eq_one_of_mem_commV_of_fixed (hV : ∀ v : V, v ^ 2 = 1) {d : MulAut V} (hd : d ^ 3 = 1)
    {v : V} (h1 : v ∈ commV (Subgroup.zpowers d)) (h2 : d v = v) : v = 1 := by
  have := normHom_eq_one_of_mem_commV hd h1
  rwa [normHom_of_fixed hV h2] at this

theorem exists_apply_mul_inv_eq [Finite V] {U : Subgroup V} {g : MulAut V}
    (hgU : ∀ u ∈ U, g u ∈ U) (hfpf : ∀ u ∈ U, g u = u → u = 1) {w : V} (hw : w ∈ U) :
    ∃ u ∈ U, g u * u⁻¹ = w := by
  let φ : U → U := fun u => ⟨g u * (u : V)⁻¹, U.mul_mem (hgU u u.2) (U.inv_mem u.2)⟩
  have hinj : Function.Injective φ := by
    intro u₁ u₂ h
    have h' : g u₁ * (u₁ : V)⁻¹ = g u₂ * (u₂ : V)⁻¹ := congrArg Subtype.val h
    have hfix : g ((u₁ : V) * (u₂ : V)⁻¹) = (u₁ : V) * (u₂ : V)⁻¹ := by
      have e : g u₁ * (g u₂)⁻¹ * ((u₁ : V) * (u₂ : V)⁻¹)⁻¹ =
          (g u₁ * (u₁ : V)⁻¹) * (g u₂ * (u₂ : V)⁻¹)⁻¹ := by
        simp only [mul_inv_rev, inv_inv, mul_assoc, mul_comm, mul_left_comm]
      have h1 : g u₁ * (g u₂)⁻¹ * ((u₁ : V) * (u₂ : V)⁻¹)⁻¹ = 1 := by
        rw [e, h']; exact mul_inv_cancel _
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.mp h1
    have := hfpf _ (U.mul_mem u₁.2 (U.inv_mem u₂.2)) hfix
    exact Subtype.ext (mul_inv_eq_one.mp this)
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  exact ⟨u, u.2, congrArg Subtype.val hu⟩

end CFSG.CGT.PushingUpLit.CGT6E
