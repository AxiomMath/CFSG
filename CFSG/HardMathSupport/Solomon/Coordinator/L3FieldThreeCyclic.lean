module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATModel
public import CFSG.HardMathSupport.Solomon.Coordinator.L3FATCyc

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.KFacts CFSG.HardMathSupport.Solomon.LocalBalance

theorem isCyclic_fieldAutThree_of_exponent_three {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Open.IsQuasisimple Y) (E : Subgroup (MulAut Y))
    (hf : ∀ ε ∈ E, IsFieldAutThree ε) (h3 : ∀ ε ∈ E, ε ^ 3 = 1) : IsCyclic ↥E := by
  classical
  by_cases hE : E = ⊥
  · subst E
    infer_instance
  obtain ⟨ε, hε1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
  have hε1' : (ε : MulAut Y) ≠ 1 := fun h => hε1 (Subtype.ext h)
  have hε : IsFieldAutPSL3 (ε : MulAut Y) ∨ IsFieldAutPSU3 (ε : MulAut Y) := by
    rcases hf ε ε.2 with h | h | h
    · exact (hε1' h).elim
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨M, _, e, P, hP, C, _, _, fld, hmodel, -, hker⟩ := exists_autModel hY hε
  have hmem : ∀ α ∈ E, ∃ d ∈ P.inndiag, ∃ c : C,
      MulAut.congr e (centerDescend Y α) = d * fld c := by
    intro α hα
    by_cases hα0 : centerDescend Y α = 1
    · exact ⟨1, one_mem _, 1, by rw [hα0, map_one, map_one, one_mul]⟩
    have hpow : MulAut.congr e (centerDescend Y α) ^ 3 = 1 := by
      rw [← map_pow, ← map_pow, h3 α hα, map_one, map_one]
    have hne : MulAut.congr e (centerDescend Y α) ≠ 1 := fun h =>
      hα0 ((MulAut.congr e).injective (h.trans (map_one _).symm))
    apply hmodel _ 1
    rw [pow_one]
    exact orderOf_eq_prime hpow hne
  haveI : IsCyclic ↥(E.map (centerDescend Y)) :=
    isCyclic_descend_of_members e P hP fld E hmem (fun α hα hin => hker α (hf α hα) hin)
  have hinj : Function.Injective (centerDescend Y) := by
    rw [injective_iff_map_eq_one]
    exact fun α hα => eq_one_of_centerDescend_eq_one hY hα
  let eE := Subgroup.equivMapOfInjective E (centerDescend Y) hinj
  exact isCyclic_of_injective eE.toMonoidHom eE.injective

end CFSG.HardMathSupport.Solomon.Coordinator
