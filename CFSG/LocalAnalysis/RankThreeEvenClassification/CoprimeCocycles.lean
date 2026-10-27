module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.LocalCore

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem coprime_cocycle_has_fixed_point {actor : Type u} {acted : Type v}
    [Group actor] [Finite actor] [CommGroup acted] [Finite acted]
    [MulDistribMulAction actor acted]
    (cocycle : actor → acted)
    (hcocycle : ∀ first second : actor,
      cocycle (first * second) = cocycle first * (first • cocycle second))
    (hcoprime : (Nat.card acted).Coprime (Nat.card actor)) :
    ∃ fixed : acted, ∀ member : actor, cocycle member * (member • fixed) = fixed := by
  classical
  let : Fintype actor := Fintype.ofFinite _
  let total : acted := ∏ member : actor, cocycle member
  have hproduct : ∀ member : actor,
      total = cocycle member ^ Nat.card actor * (member • total) := by
    intro member
    have hpermute : (∏ other : actor, cocycle (member * other)) = total := by
      exact Fintype.prod_equiv (Equiv.mulLeft member) _ _ (fun _ => rfl)
    calc
      total = ∏ other : actor, cocycle (member * other) := hpermute.symm
      _ = cocycle member ^ Nat.card actor * (member • total) := by
        simp only [hcocycle, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        rw [← Nat.card_eq_fintype_card, ← Finset.smul_prod']
  obtain ⟨fixed, hfixed⟩ := hcoprime.pow_left_bijective.surjective total
  refine ⟨fixed, ?_⟩
  intro member
  apply hcoprime.pow_left_bijective.injective
  change (cocycle member * (member • fixed)) ^ Nat.card actor = fixed ^ Nat.card actor
  change fixed ^ Nat.card actor = total at hfixed
  rw [mul_pow, ← smul_pow', hfixed]
  exact (hproduct member).symm

end CFSG.RankThreeEvenClassification.Helpers
