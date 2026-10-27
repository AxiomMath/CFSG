module

public import CFSG.LocalAnalysis.OddStandard.ThmCSylowPerm

public section

namespace CFSG.OddStandard.ThmC.Sylow

open CFSG.Blueprint CFSG.OddStandard.ThmC.T

theorem false_of_injective_perm {K : Type} [Group K] [Finite K] (T : Sylow 2 K)
    (hT : IsT (T : Subgroup K)) {Ω : Type} [Finite Ω] (hΩ : Nat.card Ω ≤ 15)
    (f : K →* Equiv.Perm Ω) (hf : Function.Injective f) : False :=
  hT.no_faithful_perm_le_fifteen hΩ (f.comp (T : Subgroup K).subtype)
    (hf.comp Subtype.val_injective)

theorem false_of_alternating {K : Type} [Group K] [Finite K] {n : ℕ} (hn : n ≤ 15)
    (e : K ≃* alternatingGroup (Fin n)) (T : Sylow 2 K) (hT : IsT (T : Subgroup K)) : False :=
  false_of_injective_perm T hT (Ω := Fin n) (by simpa using hn)
    ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
    (Subtype.val_injective.comp e.injective)

theorem false_of_sporadic_M12 {K : Type} [Group K] [Finite K]
    (h : NativeSporadic.IsSporadic K .M12) (T : Sylow 2 K) (hT : IsT (T : Subgroup K)) : False := by
  obtain ⟨e⟩ := h
  have e' : K ≃* ↥NativeSporadic.M12 := e
  exact false_of_injective_perm T hT (Ω := Fin 12) (by simp)
    (NativeSporadic.M12.subtype.comp e'.toMonoidHom) (Subtype.val_injective.comp e'.injective)

end CFSG.OddStandard.ThmC.Sylow
