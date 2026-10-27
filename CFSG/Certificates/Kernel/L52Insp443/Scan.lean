module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.PermFano

public section

namespace CFSG.KC.L52I

open Equiv CFSG.Certificates CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Quasithin.KGC31 CFSG.SectionRank.QTK.Insp443.PermKit

variable {n : ℕ}

theorem countProducts_le_countP {f : Table → Bool} {P : Perm (Fin n) → Prop} [DecidablePred P]
    (hfP : ∀ T g, Rep n T g → f T = true → P g) :
    ∀ {Tss : List (List Table)} {Gss : List (List (Perm (Fin n)))},
      List.Forall₂ (List.Forall₂ (Rep n)) Tss Gss → ∀ {gT : Table} {g : Perm (Fin n)},
        Rep n gT g →
          countProducts n f Tss gT ≤ ((products Gss).map (g * ·)).countP fun h => decide (P h)
  | [], [], .nil, gT, g, hg => by
    simp only [countProducts, products, List.map_cons, List.map_nil, mul_one]
    by_cases hf : f gT = true
    · simp [hf, hfP gT g hg hf]
    · simp [hf]
  | T :: Ts, Gs :: Gss, .cons hT hTs, gT, g, hg => by
    rw [countProducts, foldl_add_eq_sum, zero_add, products_map_mul, List.countP_flatMap]
    exact sum_map_le_of_forall₂ hT.flip fun x t htx =>
      countProducts_le_countP hfP hTs (Rep.compT hg htx)

theorem countProducts_eq_zero_of (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) (hQ : ValidSchreier Q)
    {f : Table → Bool}
    (hX : ∀ x : Q.originalSubgroup, ∀ T, Rep n T (x : Perm (Fin n)) → f T = false) :
    countProducts n f (levelTables Q) (idT n) = 0 := by
  classical
  have h1 := countProducts_le_countP (P := fun g => ∃ T, Rep n T g ∧ f T = true)
    (fun T g hT hf => ⟨T, hT, hf⟩) (forall₂_levelTables hn Q) (Rep.idT hn)
  have h2 : ((products ((List.finRange Q.baseCount).map (levelTransversals Q))).map
      ((1 : Perm (Fin n)) * ·)).countP (fun h => decide (∃ T, Rep n T h ∧ f T = true)) = 0 := by
    rw [List.countP_eq_zero]
    intro h hh hP
    simp only [one_mul, List.map_id'] at hh
    have hX' := (mem_enumeration_iff Q hQ h).mp hh
    obtain ⟨T, hT, hfT⟩ := of_decide_eq_true hP
    rw [hX ⟨h, hX'⟩ T hT] at hfT
    exact Bool.false_ne_true hfT
  omega

end CFSG.KC.L52I

end
