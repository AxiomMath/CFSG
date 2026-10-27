module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Recognition
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

@[expose] def ExitNineFix : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin 9)), Function.Injective ψ →
      alternatingGroup (Fin 9) ≤ ψ.range →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender H A →
      ∀ ω : Fin 9, (∀ a : ↥H, (a : MulAut V) ∈ A → ψ a ω = ω) →
      ∀ ι : Fin 8 ↪ Fin 9, (∀ x, x ∈ Set.range ι ↔ x ≠ ω) →
        Exotic (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl) → False

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {A : Subgroup (MulAut V)}

theorem false_of_exitNineFix (hexit : ExitNineFix) (hn : n = 9) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)
    (hA : IsFFStarOffender H A) (ω : Fin n) (hω : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a ω = ω)
    (ι : Fin (n - 1) ↪ Fin n) (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ ω)
    (hex : Exotic (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl)) : False := by
  subst hn
  exact hexit V hV H ψ hψ hAlt A hA ω hω ι hι hex

theorem step_fix (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A) (hn : 9 ≤ n)
    (hT : TPerm (n - 1)) (ω : Fin n) (hω : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a ω = ω)
    (hexit : ExitNineFix) : NatVia ψ (commV H) := by
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne (show n - 1 + 1 = n by omega) ω
  have hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
    fun h _ hh => coe_mem_preSub.2 hh
  have hinj : Function.Injective
      (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl) :=
    restrictHom_injective (hK := le_rfl) hψ fun k hk =>
      eq_one_of_apply_eq_of_range_ne hι (apply_mem_permSetStab (hK := le_rfl) k) hk
  have hAK : A ≤ preSub ψ (permSetStab (Set.range ι)) := fun a ha =>
    (coe_mem_preSub (x := ⟨a, hA.1 ha⟩)).2
      (mem_permSetStab_of_apply_eq hι (hω ⟨a, hA.1 ha⟩ ha))
  rcases hT V hV _ _ hinj (alternatingGroup_le_range_restrictHom hAlt hKmem)
      ⟨A, isFFStarOffender_of_le_of_le hA hAK⟩ with hnat | ⟨h7, -⟩ | ⟨h8, hex⟩
  · exact natVia_commV_of_natShape (by omega) hψ hAlt (natShape_of_stab hV (by omega) ι
      (by omega) _ (natShape_altRho_comp_altLift hψ hAlt _ ι
        (exists_restrictHom_eq_altLift hAlt hKmem) hnat))
  · omega
  · exact (false_of_exitNineFix hexit (by omega) hV hψ hAlt hA ω hω ι hι hex).elim

theorem step_fix_of_ten_le (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A) (hn : 10 ≤ n)
    (hT : TPerm (n - 1)) (ω : Fin n) (hω : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a ω = ω) :
    NatVia ψ (commV H) := by
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne (show n - 1 + 1 = n by omega) ω
  have hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ preSub ψ (permSetStab (Set.range ι)) :=
    fun h _ hh => coe_mem_preSub.2 hh
  have hinj : Function.Injective
      (restrictHom ψ ι (preSub ψ (permSetStab (Set.range ι))) le_rfl) :=
    restrictHom_injective (hK := le_rfl) hψ fun k hk =>
      eq_one_of_apply_eq_of_range_ne hι (apply_mem_permSetStab (hK := le_rfl) k) hk
  have hAK : A ≤ preSub ψ (permSetStab (Set.range ι)) := fun a ha =>
    (coe_mem_preSub (x := ⟨a, hA.1 ha⟩)).2
      (mem_permSetStab_of_apply_eq hι (hω ⟨a, hA.1 ha⟩ ha))
  rcases hT V hV _ _ hinj (alternatingGroup_le_range_restrictHom hAlt hKmem)
      ⟨A, isFFStarOffender_of_le_of_le hA hAK⟩ with hnat | ⟨h7, -⟩ | ⟨h8, -⟩
  · exact natVia_commV_of_natShape (by omega) hψ hAlt (natShape_of_stab hV (by omega) ι
      (by omega) _ (natShape_altRho_comp_altLift hψ hAlt _ ι
        (exists_restrictHom_eq_altLift hAlt hKmem) hnat))
  · omega
  · omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
