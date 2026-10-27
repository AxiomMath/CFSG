module

public import CFSG.CharacterTheory.SteinbergBYAlternatingSixModular

public section

namespace CFSG.GF2Type.Smith1979.W4Insp

open Module Equiv Equiv.Perm Subgroup

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem invariant_of_alternating {ρ : Perm (Fin 6) →* (V ≃ₗ[ZMod 2] V)} {t : Perm (Fin 6)}
    (ht2 : t * t = 1) (hts : sign t = -1) {U : Submodule (ZMod 2) V}
    (hA : ∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ U, ρ a v ∈ U) (htU : ∀ v ∈ U, ρ t v ∈ U) :
    ∀ σ : Perm (Fin 6), ∀ v ∈ U, ρ σ v ∈ U := by
  intro σ v hv
  by_cases hσ : σ ∈ alternatingGroup (Fin 6)
  · exact hA σ hσ v hv
  · have hσs : sign σ = -1 := by
      rcases Int.units_eq_one_or (sign σ) with h | h
      · exact absurd (mem_alternatingGroup.mpr h) hσ
      · exact h
    have h1 : σ * t ∈ alternatingGroup (Fin 6) := by
      rw [mem_alternatingGroup, sign_mul, hσs, hts]
      rfl
    have e : σ = (σ * t) * t := by rw [mul_assoc, ht2, mul_one]
    have := hA _ h1 _ (htU v hv)
    rwa [← LinearEquiv.mul_apply, ← map_mul, ← e] at this

theorem false_of_alt_six_module [Module.Finite (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 8) (ρ : Perm (Fin 6) →* (V ≃ₗ[ZMod 2] V)) {t : Perm (Fin 6)}
    (ht2 : t * t = 1) (hts : sign t = -1)
    (hirr : ∀ U : Submodule (ZMod 2) V, (∀ σ : Perm (Fin 6), ∀ v ∈ U, ρ σ v ∈ U) →
      U = ⊥ ∨ U = ⊤)
    {T : Submodule (ZMod 2) V} (hT : finrank (ZMod 2) T = 2) (hcomm : ∀ v, ρ t v - v ∈ T) :
    False := by
  classical
  have hVnt : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  have hconj : ∀ {a : Perm (Fin 6)}, a ∈ alternatingGroup (Fin 6) →
      t * a * t ∈ alternatingGroup (Fin 6) := by
    intro a ha
    rw [mem_alternatingGroup] at ha ⊢
    rw [sign_mul, sign_mul, ha, hts]
    rfl
  have hρtt : ∀ v, ρ t (ρ t v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, ← map_mul, ht2, map_one]
    rfl
  by_cases hirrA : ∀ U : Submodule (ZMod 2) V,
      (∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ U, ρ a v ∈ U) → U = ⊥ ∨ U = ⊤
  ·
    let τ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V :=
      LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp
        (ρ.comp (alternatingGroup (Fin 6)).subtype)
    have hτ : τ.IsIrreducible := by
      have hbot : (⊥ : Subrepresentation τ) ≠ ⊤ := fun h =>
        bot_ne_top (congrArg Subrepresentation.toSubmodule h)
      refine (isSimpleOrder_iff _).mpr ⟨⟨⟨⊥, ⊤, hbot⟩⟩, fun U => ?_⟩
      rcases hirrA U.toSubmodule (fun a ha v hv => U.apply_mem_toSubmodule ⟨a, ha⟩ hv) with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    obtain ⟨-, i, ⟨e⟩⟩ := CFSG.CharacterTheory.SteinbergBY.a6BinaryRep_complete V τ hτ
    have h8 := e.toLinearEquiv.finrank_eq
    rw [hV, Module.finrank_fin_fun] at h8
    fin_cases i <;> simp at h8
  ·
    push Not at hirrA
    obtain ⟨U₀, hU₀, hU₀bot, hU₀top⟩ := hirrA
    obtain ⟨W, hW0, hWinv, hWmin⟩ : ∃ W : Submodule (ZMod 2) V, W ≠ ⊥ ∧
        (∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ W, ρ a v ∈ W) ∧
        ∀ U : Submodule (ZMod 2) V, U ≠ ⊥ → (∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ U, ρ a v ∈ U) →
          finrank (ZMod 2) W ≤ finrank (ZMod 2) U := by
      set s : Set (Submodule (ZMod 2) V) :=
        {U | U ≠ ⊥ ∧ ∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ U, ρ a v ∈ U}
      have hs : U₀ ∈ s := ⟨hU₀bot, hU₀⟩
      exact ⟨Function.argminOn (fun U : Submodule (ZMod 2) V => finrank (ZMod 2) U) s ⟨_, hs⟩,
        (Function.argminOn_mem _ s ⟨_, hs⟩).1, (Function.argminOn_mem _ s ⟨_, hs⟩).2,
        fun U hU hUi => Function.argminOn_le
          (fun U : Submodule (ZMod 2) V => finrank (ZMod 2) U) s ⟨hU, hUi⟩⟩
    set W' : Submodule (ZMod 2) V := W.comap (ρ t : V ≃ₗ[ZMod 2] V).toLinearMap with hW'
    have hmem : ∀ v, v ∈ W' ↔ ρ t v ∈ W := fun v => Iff.rfl
    have hW'dim : finrank (ZMod 2) W' = finrank (ZMod 2) W := by
      rw [hW', Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
    have hW'inv : ∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ W', ρ a v ∈ W' := by
      intro a ha v hv
      rw [hmem] at hv ⊢
      have e : t * a = (t * a * t) * t := by rw [mul_assoc (t * a), ht2, mul_one]
      have h1 : ρ t (ρ a v) = ρ (t * a * t) (ρ t v) := by
        calc ρ t (ρ a v) = ρ (t * a) v := by rw [map_mul]; rfl
          _ = ρ ((t * a * t) * t) v := by rw [← e]
          _ = ρ (t * a * t) (ρ t v) := by rw [map_mul]; rfl
      rw [h1]
      exact hWinv _ (hconj ha) _ hv
    have hinf : W ⊓ W' = ⊥ := by
      by_contra hne
      have hinvinf : ∀ a ∈ alternatingGroup (Fin 6), ∀ v ∈ W ⊓ W', ρ a v ∈ W ⊓ W' :=
        fun a ha v hv => ⟨hWinv a ha v hv.1, hW'inv a ha v hv.2⟩
      have h1 := hWmin _ hne hinvinf
      have h2 : W ⊓ W' = W := Submodule.eq_of_le_of_finrank_eq inf_le_left
        (le_antisymm (Submodule.finrank_mono inf_le_left) h1)
      have hWW' : W ≤ W' := h2 ▸ inf_le_right
      have hS6 := invariant_of_alternating (ρ := ρ) ht2 hts hWinv fun v hv => hWW' hv
      rcases hirr W hS6 with h | h
      · exact hW0 h
      · have h3 := hWmin U₀ hU₀bot hU₀
        rw [h, finrank_top, hV] at h3
        have h4 := Submodule.finrank_lt hU₀top
        omega
    have hsupinv : ∀ σ : Perm (Fin 6), ∀ v ∈ W ⊔ W', ρ σ v ∈ W ⊔ W' := by
      refine invariant_of_alternating ht2 hts ?_ ?_
      · intro a ha v hv
        obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        exact add_mem (Submodule.mem_sup_left (hWinv a ha w hw))
          (Submodule.mem_sup_right (hW'inv a ha w' hw'))
      · intro v hv
        obtain ⟨w, hw, w', hw', rfl⟩ := Submodule.mem_sup.mp hv
        rw [map_add]
        refine add_mem (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left hw')
        rw [hmem, hρtt]
        exact hw
    have hsup : W ⊔ W' = ⊤ := by
      rcases hirr _ hsupinv with h | h
      · exact absurd (eq_bot_iff.mpr (h ▸ le_sup_left)) hW0
      · exact h
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq W W'
    rw [hsup, hinf, finrank_top, finrank_bot, hV, hW'dim] at hdim
    set d : V →ₗ[ZMod 2] V := (ρ t : V ≃ₗ[ZMod 2] V).toLinearMap - LinearMap.id with hd
    have hmapT : ∀ w : W, d (w : V) ∈ T := fun w => by simpa [hd] using hcomm w
    let f : W →ₗ[ZMod 2] T := (d ∘ₗ W.subtype).codRestrict T hmapT
    have hfinj : Function.Injective f := by
      intro w₁ w₂ h
      have h1 : ρ t (w₁ : V) - (w₁ : V) = ρ t (w₂ : V) - (w₂ : V) := congrArg Subtype.val h
      have h2 : ρ t ((w₁ - w₂ : W) : V) = ((w₁ - w₂ : W) : V) := by
        rw [Submodule.coe_sub, map_sub]
        calc ρ t (w₁ : V) - ρ t (w₂ : V)
            = (ρ t (w₁ : V) - (w₁ : V)) - (ρ t (w₂ : V) - (w₂ : V)) + ((w₁ : V) - (w₂ : V)) := by
              abel
          _ = (w₁ : V) - (w₂ : V) := by rw [h1]; abel
      have h3 : ((w₁ - w₂ : W) : V) ∈ W ⊓ W' :=
        Submodule.mem_inf.mpr ⟨(w₁ - w₂).2, (hmem _).mpr (by rw [h2]; exact (w₁ - w₂).2)⟩
      rw [hinf, Submodule.mem_bot] at h3
      exact sub_eq_zero.mp (Subtype.ext h3)
    have hle := LinearMap.finrank_le_finrank_of_injective hfinj
    omega

end CFSG.GF2Type.Smith1979.W4Insp
