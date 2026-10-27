module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.OffenderDefs

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

variable {G : Type*} [Group G] {Q : Type} [AddCommGroup Q] [Module (ZMod 2) Q]

@[expose] def nilMap (ρ : Representation (ZMod 2) G Q) (g : G) : Q →ₗ[ZMod 2] Q :=
  ρ g - LinearMap.id

theorem nilMap_apply (ρ : Representation (ZMod 2) G Q) (g : G) (v : Q) :
    nilMap ρ g v = ρ g v - v := rfl

theorem two_smul_zmod2 (v : Q) : v + v = 0 := by
  have : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) v, this, zero_smul]

theorem neg_eq_self_zmod2 (v : Q) : -v = v := by
  have := two_smul_zmod2 v
  exact neg_eq_of_add_eq_zero_left this

theorem nilMap_sq (ρ : Representation (ZMod 2) G Q) {g : G} (hg : g ^ 2 = 1) (v : Q) :
    nilMap ρ g (nilMap ρ g v) = 0 := by
  have h2 : ρ g (ρ g v) = v := by
    have := congrArg (fun x => ρ x v) hg
    simpa [pow_two, map_mul, Module.End.mul_apply] using this
  simp only [nilMap_apply, map_sub, h2]
  have a := two_smul_zmod2 v
  have b := two_smul_zmod2 (ρ g v)
  calc v - ρ g v - (ρ g v - v) = (v + v) - (ρ g v + ρ g v) := by abel
    _ = 0 := by rw [a, b, sub_zero]

theorem mem_ker_nilMap (ρ : Representation (ZMod 2) G Q) (g : G) (v : Q) :
    v ∈ LinearMap.ker (nilMap ρ g) ↔ ρ g v = v := by
  rw [LinearMap.mem_ker, nilMap_apply, sub_eq_zero]

theorem range_le_ker_nilMap (ρ : Representation (ZMod 2) G Q) {g : G} (hg : g ^ 2 = 1) :
    LinearMap.range (nilMap ρ g) ≤ LinearMap.ker (nilMap ρ g) := by
  rintro _ ⟨v, rfl⟩
  exact LinearMap.mem_ker.2 (nilMap_sq ρ hg v)

variable [Finite Q]

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
