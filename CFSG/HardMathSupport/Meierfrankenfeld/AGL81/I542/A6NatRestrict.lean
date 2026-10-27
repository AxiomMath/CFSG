module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3H13Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

open CFSG.QuasithinUnique.Setup.X3

variable {S : Type} [AddCommGroup S] [Module (ZMod 2) S] [Finite S]

@[expose] noncomputable def restrictLE (e : S ≃ₗ[ZMod 2] S) (M : Submodule (ZMod 2) S)
    (h : ∀ m ∈ M, e m ∈ M) : M ≃ₗ[ZMod 2] M :=
  e.ofSubmodules M M (by
    have : FiniteDimensional (ZMod 2) S := Module.Finite.of_finite
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rintro _ ⟨m, hm, rfl⟩
      exact h m hm
    · exact LinearEquiv.finrank_map_eq e M)

theorem restrictLE_apply (e : S ≃ₗ[ZMod 2] S) (M : Submodule (ZMod 2) S) (h : ∀ m ∈ M, e m ∈ M)
    (x : M) : ((restrictLE e M h x : M) : S) = e x := rfl

@[expose] noncomputable def restrictHom {G : Type*} [Group G] (σ : G →* (S ≃ₗ[ZMod 2] S))
    (M : Submodule (ZMod 2) S) (h : ∀ g : G, ∀ m ∈ M, σ g m ∈ M) : G →* (M ≃ₗ[ZMod 2] M) where
  toFun g := restrictLE (σ g) M (h g)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp [restrictLE_apply]
  map_mul' g g' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp [restrictLE_apply]

theorem restrictHom_apply {G : Type*} [Group G] (σ : G →* (S ≃ₗ[ZMod 2] S))
    (M : Submodule (ZMod 2) S) (h : ∀ g : G, ∀ m ∈ M, σ g m ∈ M) (g : G) (x : M) :
    ((restrictHom σ M h g x : M) : S) = σ g x := rfl

theorem isLSimple_restrictHom {G : Type*} [Group G] (σ : G →* (S ≃ₗ[ZMod 2] S))
    (M : Submodule (ZMod 2) S) (h : ∀ g : G, ∀ m ∈ M, σ g m ∈ M) (hM : M ≠ ⊥)
    (hmin : ∀ N : Submodule (ZMod 2) S, N ≠ ⊥ → (∀ g : G, ∀ n ∈ N, σ g n ∈ N) → N ≤ M → N = M) :
    IsLSimple (restrictHom σ M h) ⊤ ⊤ := by
  refine ⟨fun _ _ _ _ => trivial, ?_, fun W hW _ => ?_⟩
  · intro h0
    apply hM
    rw [eq_bot_iff]
    intro m hm
    have : (⟨m, hm⟩ : M) ∈ (⊤ : Submodule (ZMod 2) M) := trivial
    rw [h0] at this
    have h1 : (⟨m, hm⟩ : M) = 0 := this
    simpa using congrArg Subtype.val h1
  · by_cases hW0 : W = ⊥
    · exact Or.inl hW0
    · right
      have hN : W.map M.subtype = M := by
        apply hmin
        · intro h0
          apply hW0
          obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
          exfalso
          have : M.subtype w ∈ Submodule.map M.subtype W := ⟨w, hw, rfl⟩
          rw [h0, Submodule.mem_bot] at this
          exact hw0 (Subtype.ext (by simpa using this))
        · rintro g _ ⟨x, hx, rfl⟩
          exact ⟨restrictHom σ M h g x, hW g trivial x hx, rfl⟩
        · rintro _ ⟨x, _, rfl⟩
          exact x.2
      rw [eq_top_iff]
      intro x _
      have : (x : S) ∈ W.map M.subtype := by rw [hN]; exact x.2
      obtain ⟨y, hy, hxy⟩ := this
      have : y = x := Subtype.ext hxy
      rw [← this]
      exact hy

end CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
