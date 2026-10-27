module

public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.A6NatIrr

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.QuasithinUnique.Setup.X3 CFSG.QuasithinUnique.Setup.X3E

variable {S : Type} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]

theorem a6_natural (Y A : Subgroup (Module.End (ZMod 2) S)ˣ)
    (hirr : ∀ N : Submodule (ZMod 2) S,
      (∀ d ∈ Y ⊔ A, ∀ v ∈ N, (d : Module.End (ZMod 2) S) v ∈ N) → N = ⊥ ∨ N = ⊤)
    (hAN : A ≤ Subgroup.normalizer (Y : Set (Module.End (ZMod 2) S)ˣ))
    (eY : ↥Y ≃* alternatingGroup (Fin 6)) (hdim : Module.finrank (ZMod 2) S ≤ 6) :
    Module.finrank (ZMod 2) S = 4 ∧
      ((Module.finrank (ZMod 2) ↥(LinearMap.ker
            (((eY.symm c3A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) - 1 : Module.End (ZMod 2) S)) = 2 ∧
        Module.finrank (ZMod 2) ↥(LinearMap.ker
            (((eY.symm c33A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) - 1 : Module.End (ZMod 2) S)) = 0) ∨
       (Module.finrank (ZMod 2) ↥(LinearMap.ker
            (((eY.symm c3A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) - 1 : Module.End (ZMod 2) S)) = 0 ∧
        Module.finrank (ZMod 2) ↥(LinearMap.ker
            (((eY.symm c33A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) - 1 : Module.End (ZMod 2) S)) = 2)) := by
  have hY := a6_irreducible hirr hAN eY hdim
  let σ : S6 →* (S ≃ₗ[ZMod 2] S) := unitLE.comp (Y.subtype.comp eY.symm.toMonoidHom)
  have hσ : ∀ g, (σ g : S →ₗ[ZMod 2] S) =
      (((eY.symm g : ↥Y) : (Module.End (ZMod 2) S)ˣ) : Module.End (ZMod 2) S) := fun _ => rfl
  have hsimple : IsLSimple σ ⊤ ⊤ := by
    have hnt : Nontrivial S := nontrivial_of_eY eY
    refine ⟨fun _ _ _ _ => trivial, top_ne_bot, fun W hW _ => hY W fun y hy v hv => ?_⟩
    have h := hW (eY ⟨y, hy⟩) trivial v hv
    have e : σ (eY ⟨y, hy⟩) v = (y : Module.End (ZMod 2) S) v := by
      show (((eY.symm (eY ⟨y, hy⟩) : ↥Y) : (Module.End (ZMod 2) S)ˣ) :
        Module.End (ZMod 2) S) v = _
      rw [MulEquiv.symm_apply_apply]
    rwa [e] at h
  have hnt : σ c3A6 ≠ 1 := by
    intro h
    have h1 : ((eY.symm c3A6 : ↥Y) : (Module.End (ZMod 2) S)ˣ) = 1 := by
      apply Units.ext
      rw [← hσ, h]
      rfl
    exact c3A6_ne_one (by simpa using congrArg eY (Subtype.ext h1 : eY.symm c3A6 = 1))
  have := a6_block_dims σ hsimple hdim hnt
  exact this

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
