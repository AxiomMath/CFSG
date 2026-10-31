
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsQuatBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverBase

@[expose] public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

noncomputable def psi {E : Type*} [Group E]
    (l : Cover →* E) : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) →* E :=
  l.comp (zHom.comp ((MonoidHom.id _).prodMap (MonoidHom.inl _ _)))

theorem psi_apply {E : Type*} [Group E] (l : Cover →* E)
    (d : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    psi l d = l z₁ ^ (Multiplicative.toAdd d.1).val * l z₂ ^ (Multiplicative.toAdd d.2).val := by
  simp [psi, zHom_apply]

theorem lz₁_pow {E : Type*} [Group E] (l : Cover →* E) :
    l z₁ ^ 4 = 1 := by
  rw [← map_pow, z₁_pow, map_one]

theorem lz₂_pow {E : Type*} [Group E] (l : Cover →* E) :
    l z₂ ^ 4 = 1 := by
  rw [← map_pow, z₂_pow, map_one]

theorem psi_ofAdd {E : Type*} [Group E] (l : Cover →* E)
    (i j : ℕ) : psi l (Multiplicative.ofAdd (i : ZMod 4), Multiplicative.ofAdd (j : ZMod 4)) =
      l z₁ ^ i * l z₂ ^ j := by
  rw [psi_apply, toAdd_ofAdd, toAdd_ofAdd, ZMod.val_natCast, ZMod.val_natCast,
    ← pow_eq_pow_mod i (lz₁_pow l), ← pow_eq_pow_mod j (lz₂_pow l)]

theorem psi_a {E : Type*} [Group E] (l : Cover →* E) :
    psi l (Multiplicative.ofAdd 1, 1) = l z₁ := by
  have := psi_ofAdd l 1 0
  simpa using this

theorem psi_b {E : Type*} [Group E] (l : Cover →* E) :
    psi l (1, Multiplicative.ofAdd 1) = l z₂ := by
  have := psi_ofAdd l 0 1
  simpa using this

namespace IsUSetting

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} {β : E ≃* E}

theorem r₄_comm_Q8 {t : Equiv.Perm (Fin 42)} (ht : t ∈ Q8) : r₄ * t = t * r₄ :=
  (mem_Q8.1 ht).1.symm

theorem mem_C₄ {t : Equiv.Perm (Fin 42)} : t ∈ C₄ ↔ t * r₄ = r₄ * t ∧ t ∈ S := by
  rw [C₄, mem_inf, mem_centralizer_singleton_iff]

end IsUSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
