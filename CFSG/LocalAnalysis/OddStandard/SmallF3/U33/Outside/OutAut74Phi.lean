module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Coord
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutChain

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def phi : MulAut U4 →* Equiv.Perm V4 where
  toFun α :=
    { toFun := linAdd α
      invFun := linAdd α⁻¹
      left_inv := fun v => by
        rw [← linAdd_mul, inv_mul_cancel, linAdd_one]
      right_inv := fun v => by
        rw [← linAdd_mul, mul_inv_cancel, linAdd_one] }
  map_one' := Equiv.ext fun v => linAdd_one v
  map_mul' α β := Equiv.ext fun v => linAdd_mul α β v

theorem phi_apply (α : MulAut U4) (v : V4) : phi α v = linAdd α v :=
  rfl

theorem phi_add (α : MulAut U4) (v w : V4) : phi α (v + w) = phi α v + phi α w := by
  rw [phi_apply, phi_apply, phi_apply]
  exact map_add (linAdd α) v w

private theorem fst_inv_mul (x y : U4) : (x⁻¹ * y).a = -x.a + y.a := by
  simp [UT3.mul_def, UT3.inv_def]

private theorem snd_inv_mul (x y : U4) : (x⁻¹ * y).b = -x.b + y.b := by
  simp [UT3.mul_def, UT3.inv_def]

theorem ker_phi : phi.ker = chainStab U4 := by
  ext α
  rw [MonoidHom.mem_ker]
  constructor
  · intro hα
    have hv : ∀ v : V4, linAdd α v = v := fun v => by
      have h1 : phi α v = v := by rw [hα]; rfl
      simpa [phi_apply] using h1
    refine ⟨fun x => ?_, fun z hz => ?_⟩
    · rw [mem_center_U4]
      have hx := hv (x.a, x.b)
      rw [linAdd_apply α x] at hx
      rw [Prod.mk.injEq] at hx
      exact ⟨by rw [fst_inv_mul, hx.1, neg_add_cancel],
             by rw [snd_inv_mul, hx.2, neg_add_cancel]⟩
    · have hz' : z.a = 0 ∧ z.b = 0 := (mem_center_U4 z).mp hz
      have hz_eq : z = ⟨0, 0, z.c⟩ := by
        ext <;> simp [hz'.1, hz'.2]
      have hsig : sigAdd α z.c = z.c := by
        have h1 : linAdd α (z.c, 1) = (z.c, 1) := hv (z.c, 1)
        have h2 := sqF_linAdd α (z.c, 1)
        rw [h1] at h2
        simp [sqF] at h2
        exact h2.symm
      calc α z = α ⟨0, 0, z.c⟩ := by rw [hz_eq]
        _ = ⟨0, 0, sigAdd α z.c⟩ := aut_center_eq α z.c
        _ = ⟨0, 0, z.c⟩ := by rw [hsig]
        _ = z := hz_eq.symm
  · intro hα
    have hv : ∀ v : V4, linAdd α v = v := fun v => by
      have hx : (⟨v.1, v.2, 0⟩ : U4)⁻¹ * α ⟨v.1, v.2, 0⟩ ∈ center U4 := hα.1 _
      rw [mem_center_U4] at hx
      have ha : (α ⟨v.1, v.2, 0⟩).a = v.1 := by
        have h := hx.1
        rw [fst_inv_mul] at h
        exact add_left_cancel (by rw [h, neg_add_cancel])
      have hb : (α ⟨v.1, v.2, 0⟩).b = v.2 := by
        have h := hx.2
        rw [snd_inv_mul] at h
        exact add_left_cancel (by rw [h, neg_add_cancel])
      rw [linAdd_apply α ⟨v.1, v.2, 0⟩, ha, hb]
    refine Equiv.ext fun v => ?_
    rw [phi_apply]
    simpa using hv v

theorem sigAdd_eq_id (α : MulAut U4) (h : ∀ z ∈ center U4, α z = z) (c : F4c) :
    sigAdd α c = c := by
  have hz : (⟨0, 0, c⟩ : U4) ∈ center U4 := (mem_center_U4 _).mpr ⟨rfl, rfl⟩
  have h1 : α ⟨0, 0, c⟩ = ⟨0, 0, c⟩ := h ⟨0, 0, c⟩ hz
  rw [aut_center_eq α c] at h1
  exact congrArg UT3.c h1

theorem sqF_phi_of_fix (α : MulAut U4) (h : ∀ z ∈ center U4, α z = z) (v : V4) :
    sqF (phi α v) = sqF v := by
  rw [phi_apply, sqF_linAdd]
  exact sigAdd_eq_id α h (sqF v)

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
