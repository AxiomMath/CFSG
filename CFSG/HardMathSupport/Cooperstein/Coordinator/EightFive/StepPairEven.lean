module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolShape
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Recognition
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ToolRestrict

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin Equiv Equiv.Perm

@[expose] def ExitTenEven : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (H : Subgroup (MulAut V)) (ψ : ↥H →* Perm (Fin 10)), Function.Injective ψ →
      alternatingGroup (Fin 10) ≤ ψ.range →
      ∀ A : Subgroup (MulAut V), IsFFStarOffender H A → A ≤ altPre ψ →
      ∀ p q : Fin 10, p ≠ q →
      (∀ a : ↥H, (a : MulAut V) ∈ A → ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p) →
      (∀ i, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i) →
      ∀ ι : Fin 8 ↪ Fin 10, (∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q) →
        Exotic (restrictHom ψ ι
          (preSub ψ (alternatingGroup (Fin 10) ⊓ permSetStab (Set.range ι)))
          (preSub_mono inf_le_right)) → False

variable {V : Type} [CommGroup V] [Finite V] {H : Subgroup (MulAut V)} {n : ℕ}
  {ψ : ↥H →* Perm (Fin n)} {A : Subgroup (MulAut V)}

theorem false_of_exitTenEven (hexit : ExitTenEven) (hn : n = 10) (hV : ∀ v : V, v ^ 2 = 1)
    (hψ : Function.Injective ψ) (hAlt : alternatingGroup (Fin n) ≤ ψ.range)
    (hA : IsFFStarOffender H A) (hAL : A ≤ altPre ψ) (p q : Fin n) (hpq : p ≠ q)
    (horb : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p)
    (hmin : ∀ i, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i)
    (ι : Fin (n - 2) ↪ Fin n) (hι : ∀ x, x ∈ Set.range ι ↔ x ≠ p ∧ x ≠ q)
    (hex : Exotic (restrictHom ψ ι
      (preSub ψ (alternatingGroup (Fin n) ⊓ permSetStab (Set.range ι)))
      (preSub_mono inf_le_right))) : False := by
  subst hn
  exact hexit V hV H ψ hψ hAlt A hA hAL p q hpq horb hmin ι hι hex

theorem step_pair_le (hV : ∀ v : V, v ^ 2 = 1) (hψ : Function.Injective ψ)
    (hAlt : alternatingGroup (Fin n) ≤ ψ.range) (hA : IsFFStarOffender H A) (hn : 10 ≤ n)
    (hT : TPerm (n - 2)) (p q : Fin n) (hpq : p ≠ q) (hAL : A ≤ altPre ψ)
    (horb : ∀ a : ↥H, (a : MulAut V) ∈ A → ψ a p = p ∧ ψ a q = q ∨ ψ a p = q ∧ ψ a q = p)
    (hmin : ∀ i, ∃ a : ↥H, (a : MulAut V) ∈ A ∧ ψ a i ≠ i) (hexit : ExitTenEven) :
    NatVia ψ (commV H) := by
  obtain ⟨ι, hι⟩ := exists_embedding_range_ne_ne (show n - 2 + 2 = n by omega) hpq
  have hD : preSub ψ (alternatingGroup (Fin n) ⊓ permSetStab (Set.range ι)) ≤
      preSub ψ (permSetStab (Set.range ι)) :=
    preSub_mono inf_le_right
  have hKmem : ∀ h : ↥H, ψ h ∈ alternatingGroup (Fin n) → ψ h ∈ permSetStab (Set.range ι) →
      (h : MulAut V) ∈ preSub ψ (alternatingGroup (Fin n) ⊓ permSetStab (Set.range ι)) :=
    fun h h1 h2 => coe_mem_preSub.2 ⟨h1, h2⟩
  have hinj : Function.Injective (restrictHom ψ ι _ hD) :=
    restrictHom_injective (hK := hD) hψ fun k hk => by
      have hk2 := (coe_mem_preSub (ψ := ψ) (x := Subgroup.inclusion (hD.trans preSub_le) k)).1
        k.2
      exact eq_one_of_apply_eq_of_range_ne_ne hpq hι hk2.2 hk2.1 hk
  have hAD : A ≤ preSub ψ (alternatingGroup (Fin n) ⊓ permSetStab (Set.range ι)) := fun a ha =>
    (coe_mem_preSub (x := ⟨a, hA.1 ha⟩)).2
      ⟨coe_mem_altPre_iff.1 (hAL ha), mem_permSetStab_of_pair hι (horb ⟨a, hA.1 ha⟩ ha)⟩
  rcases hT V hV _ _ hinj (alternatingGroup_le_range_restrictHom hAlt hKmem)
      ⟨A, isFFStarOffender_of_le_of_le hA hAD⟩ with hnat | ⟨h7, -⟩ | ⟨h8, hex⟩
  · exact natVia_commV_of_natShape (by omega) hψ hAlt (natShape_of_stab₂ hV (by omega) ι
      (by omega) _ (natShape_altRho_comp_altLift hψ hAlt _ ι
        (exists_restrictHom_eq_altLift hAlt hKmem) hnat))
  · omega
  · exact (false_of_exitTenEven hexit (by omega) hV hψ hAlt hA hAL p q hpq horb hmin ι hι
      hex).elim

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
