module

public import CFSG.LieType.SeitzGeneration.ExcAnisotropicClasses
public import CFSG.LieType.SeitzGeneration.ExcTorusCatTw

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2

theorem seitzExcAnisotropicForAt_geFive_of_counts {c : PrimePower → LieTypeIndex}
    {X : PrimePower → Prop} {F : LieTypeIndex → Prop} {a : ℕ → ℕ} {S : ℕ → Prop}
    (hchar : ∀ q, (c q).characteristic = q.p)
    (hinj : ∀ (q : PrimePower) (hv : (c q).Valid),
      Function.Injective (MulAut.conj : Cat ⟨c q, hv⟩ →* MulAut (Cat ⟨c q, hv⟩)))
    (h1 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → p ≠ q.p →
      a (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 → RankLE1 p (Cat ⟨c q, hv⟩))
    (h3 : ∀ (q : PrimePower) (hv : (c q).Valid) (p : ℕ), p.Prime → 3 < p → p ≠ q.p →
      3 ≤ a (orderOf ((q.card : ℕ) : ZMod p)) → ¬ RankLE2 p (Cat ⟨c q, hv⟩))
    (h2 : ∀ e, a e = 2 → S e)
    (hS : ∀ e, S e → SeitzExcAnisotropicForAt F (ClassRange c X e)) :
    SeitzExcAnisotropicForAt F fun d p => 5 ≤ p ∧ ∃ q, d = c q ∧ X q := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hp5, q, hdq, hX⟩, hr, hn⟩
  obtain rfl : d = c q := hdq
  have hpq : p ≠ q.p := fun h => hpd (h.trans (hchar q).symm)
  rcases Nat.lt_or_ge (a (orderOf ((q.card : ℕ) : ZMod p))) 3 with hlt | hge
  · rcases (by omega : a (orderOf ((q.card : ℕ) : ZMod p)) ≤ 1 ∨
        a (orderOf ((q.card : ℕ) : ZMod p)) = 2) with hle | heq
    · exact (false_of_inner_plane_of_rankLE1 hp (hinj q hv) (h1 q hv p hp hpq hle) hE hc hin).elim
    · exact hS _ (h2 _ heq) ⟨c q, hv⟩ p hp hp2 hpd hex E hE hc
        ⟨hin, hF, ⟨hp5, q, rfl, hX, rfl⟩, hr, hn⟩
  · exact absurd hr (h3 q hv p hp (by omega) hpq hge)

theorem degCountTw_eq_two {e : ℕ} (h : degCountTw e = 2) : e = 3 ∨ e = 4 := by
  have h60 := le_sixty_of_degCountTw_pos (e := e) (by omega)
  have key : ∀ e ≤ 60, degCountTw e = 2 → e = 3 ∨ e = 4 := by decide
  exact key e h60 h

section Proved


theorem conj_injective_cat_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid) :
    Function.Injective
      (MulAut.conj : Cat ⟨.twistedE6 q, hv⟩ →* MulAut (Cat ⟨.twistedE6 q, hv⟩)) := by
  obtain ⟨K, _, σ, -, -, ⟨e⟩⟩ := exists_catEquiv_twistedE6 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot
    (exceptional_fixed_center_trivial TwistTag.E6 K σ))

end Proved

@[expose] def SeitzExcAnisotropicTwistedE6Class (e : ℕ) : Prop :=
  SeitzExcAnisotropicForAt IsTwistedE6Index
    (ClassRange LieTypeIndex.twistedE6 (fun _ => True) e)

@[expose] def SeitzExcAnisotropicTwistedE6Three : Prop :=
  SeitzExcAnisotropicForAt IsTwistedE6Index PrimeRange.three

section Assembly


theorem seitzExcAnisotropicTwistedE6_geFive_of_classes (h3 : SeitzExcAnisotropicTwistedE6Class 3)
    (h4 : SeitzExcAnisotropicTwistedE6Class 4) :
    SeitzExcAnisotropicForAt IsTwistedE6Index PrimeRange.geFive :=
  SeitzExcAnisotropicForAt.mono_on
    (fun d p _ _ hd hp5 => by
      obtain ⟨q, rfl⟩ := hd
      exact ⟨hp5, q, rfl, trivial⟩)
    (seitzExcAnisotropicForAt_geFive_of_counts (c := LieTypeIndex.twistedE6) (X := fun _ => True)
      (F := IsTwistedE6Index) (a := degCountTw) (S := fun e => e = 3 ∨ e = 4)
      LieTypeIndex.characteristic_twistedE6 conj_injective_cat_twistedE6
      (fun q hv p hp hpq h => rankLE1_cat_twistedE6 q hv hp hpq h)
      (fun q hv p hp hp3 hpq h => not_rankLE2_cat_twistedE6 q hv hp hp3 hpq h)
      (fun _ h => degCountTw_eq_two h)
      (fun e he => by
        rcases he with rfl | rfl
        exacts [h3, h4]))

theorem seitzExcAnisotropicTwistedE6_of_classes (h3 : SeitzExcAnisotropicTwistedE6Class 3)
    (h4 : SeitzExcAnisotropicTwistedE6Class 4) (hthree : SeitzExcAnisotropicTwistedE6Three) :
    SeitzExcAnisotropicTwistedE6 :=
  SeitzExcAnisotropicFor.of_three_geFive hthree
    (seitzExcAnisotropicTwistedE6_geFive_of_classes h3 h4)

end Assembly

theorem seitzExcAnisotropicTwistedE6Class_of_twistedE6 (h : SeitzExcAnisotropicTwistedE6)
    (e : ℕ) : SeitzExcAnisotropicTwistedE6Class e :=
  SeitzExcAnisotropicFor.toAt h _

theorem seitzExcAnisotropicTwistedE6Three_of_twistedE6 (h : SeitzExcAnisotropicTwistedE6) :
    SeitzExcAnisotropicTwistedE6Three :=
  SeitzExcAnisotropicFor.toAt h _

end CFSG.LieType.SeitzGeneration
