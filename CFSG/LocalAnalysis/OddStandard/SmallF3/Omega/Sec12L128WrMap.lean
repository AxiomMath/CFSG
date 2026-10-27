module

public import Mathlib.GroupTheory.RegularWreathProduct

public section

namespace CFSG.OddStandard.SmallF3.Omega

variable {A D Q : Type} [Group A] [Group D] [Group Q]

@[expose] def sec128WrMap (χ : A →* D) : A ≀ᵣ Q →* D ≀ᵣ Q where
  toFun γ := ⟨fun q => χ (γ.left q), γ.right⟩
  map_one' := by ext <;> simp
  map_mul' a b := by ext <;> simp

@[simp] theorem sec128WrMap_left (χ : A →* D) (γ : A ≀ᵣ Q) (q : Q) :
    (sec128WrMap χ γ).left q = χ (γ.left q) := rfl

@[simp] theorem sec128WrMap_right (χ : A →* D) (γ : A ≀ᵣ Q) :
    (sec128WrMap χ γ).right = γ.right := rfl

@[expose] def sec128WrBase (b : Q → D) : D ≀ᵣ Q := ⟨b, 1⟩

theorem sec128WrBase_mul (a b : Q → D) :
    sec128WrBase a * sec128WrBase b = sec128WrBase (a * b) := by
  ext q <;> simp [sec128WrBase]

theorem sec128Wr_conj_base (ξ : Q → D) (s : Q) (b : Q → D) :
    (⟨ξ, s⟩ : D ≀ᵣ Q) * sec128WrBase b * (⟨ξ, s⟩ : D ≀ᵣ Q)⁻¹ =
      sec128WrBase (fun x => ξ x * b (s⁻¹ * x) * (ξ x)⁻¹) := by
  ext q <;> simp [sec128WrBase, mul_assoc]

end CFSG.OddStandard.SmallF3.Omega
