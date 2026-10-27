module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec12L128F4Lin

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec128_no_central_three {G : Type} [Group G] [Finite G] (V : Subgroup G)
    (hV : IsElemAb2 V 8) (Z : Subgroup (MulAut ↥V)) (hZ : _root_.commutator ↥Z = ⊤)
    (c : MulAut ↥V) (hcZ : c ∈ Z) (hcen : ∀ z ∈ Z, z * c = c * z) (hc3 : c ^ 3 = 1)
    (hc1 : c ≠ 1) (hfpf : ∀ v : ↥V, c v = v → v = 1) : False := by
  classical
  letI : CommGroup ↥V :=
    { (inferInstance : Group ↥V) with mul_comm := hV.1.1.is_comm.comm }
  letI : Module (ZMod 2) (Additive ↥V) := AddCommGroup.zmodModule (n := 2) fun x => by
    have h : x.toMul ^ 2 = 1 := by
      apply Subtype.ext
      simpa using hV.1.2 x.toMul x.toMul.2
    calc (2 : ℕ) • x = Additive.ofMul (x.toMul ^ 2) := by
          simp [ofMul_pow]
      _ = 0 := by rw [h]; rfl
  let ρ₀ : MulAut ↥V →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) :=
    { toFun := fun g => (MulEquiv.toAdditive g).toLinearEquiv
        (fun k v => ZMod.map_smul (MulEquiv.toAdditive g) k v)
      map_one' := by
        apply LinearEquiv.ext
        intro v
        apply Additive.ext
        simp
      map_mul' g h := by
        apply LinearEquiv.ext
        intro v
        apply Additive.ext
        simp [mul_assoc] }
  let ρ : ↥Z →* (Additive ↥V ≃ₗ[ZMod 2] Additive ↥V) := ρ₀.comp Z.subtype
  let c' : ↥Z := ⟨c, hcZ⟩
  refine sec128_F4_central_three (W := Additive ↥V) (hW := hV.2) (Z := ↥Z) (hZ := hZ)
    (ρ := ρ) (c := c') ?_ ?_ ?_ ?_
  ·
    intro z
    exact Subtype.ext (hcen z z.2)
  ·
    have h : (ρ c') ^ 3 = ρ (c' ^ 3) := (map_pow ρ c' 3).symm
    rw [h, show c' ^ 3 = 1 by exact Subtype.ext hc3, map_one]
  ·
    intro h
    apply hc1
    ext v
    have hv : (ρ₀ c) (Additive.ofMul v) = Additive.ofMul v := by
      have := congrArg (fun e => e (Additive.ofMul v)) h
      simpa [ρ] using this
    simpa [ρ₀] using congrArg Additive.toMul hv
  ·
    intro w hw
    have hw' : c w.toMul = w.toMul := by
      have := congrArg Additive.toMul hw
      simpa [ρ, ρ₀] using this
    have h1 : w.toMul = 1 := hfpf _ hw'
    exact Additive.ext h1

end CFSG.OddStandard.SmallF3.Omega
