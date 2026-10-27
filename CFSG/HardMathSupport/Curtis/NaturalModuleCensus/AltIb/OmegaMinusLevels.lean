module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Sp
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusDefs

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.SpCell
  (cnt cnt_le_card cnt_mono exists_cut_of_cnt_lt cnt_lt_of_cut exists_cut_of_cnt_lt_card StepCoord
    topN topEmb cnt_topEmb exists_topEmb_eq topEmb_injective)

variable {r : ℕ}

@[expose] def omLev (r : ℕ) (S : Finset ℕ) : Idx r → ℕ
  | Sum.inl a => cnt S a
  | Sum.inr (Sum.inl a) => 2 * S.card - cnt S a
  | Sum.inr (Sum.inr _) => S.card

@[expose] noncomputable def topσ (r : ℕ) (S : Finset ℕ) : Idx (topN r S) → Idx r :=
  Sum.map (topEmb r S) (Sum.map (topEmb r S) id)

variable {S : Finset ℕ}

theorem step_injective (ℓ : ℕ) :
    Function.Injective (fun a : StepCoord r S ℓ => (Sum.inl a.1 : Idx r)) :=
  fun _ _ h => Subtype.ext (Sum.inl_injective h)

theorem step_range {ℓ : ℕ} (hℓ : ℓ < S.card) (u : Idx r) :
    omLev r S u = ℓ ↔ u ∈ Set.range (fun a : StepCoord r S ℓ => (Sum.inl a.1 : Idx r)) := by
  rcases u with a | a | k
  · constructor
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
    · rintro ⟨b, hb⟩
      have := Sum.inl_injective hb
      subst this
      exact b.2
  · constructor
    · intro h
      have : 2 * S.card - cnt S a = ℓ := h
      have := cnt_le_card S a
      omega
    · rintro ⟨b, hb⟩
      exact absurd hb (by simp)
  · constructor
    · intro h
      have : S.card = ℓ := h
      omega
    · rintro ⟨b, hb⟩
      exact absurd hb (by simp)

theorem topσ_injective : Function.Injective (topσ r S) :=
  Sum.map_injective.2 ⟨topEmb_injective, Sum.map_injective.2 ⟨topEmb_injective, Function.injective_id⟩⟩

theorem top_range (u : Idx r) :
    omLev r S u = S.card ↔ u ∈ Set.range (topσ r S) := by
  rcases u with a | a | k
  · constructor
    · intro h
      obtain ⟨j, hj⟩ := exists_topEmb_eq (S := S) (a := a) h
      exact ⟨Sum.inl j, by simp [topσ, hj]⟩
    · rintro ⟨v, hv⟩
      rcases v with j | j | k
      · have : topEmb r S j = a := by simpa [topσ] using hv
        subst this
        exact cnt_topEmb j
      · simp [topσ] at hv
      · simp [topσ] at hv
  · constructor
    · intro h
      have h' : 2 * S.card - cnt S a = S.card := h
      have := cnt_le_card S a
      obtain ⟨j, hj⟩ := exists_topEmb_eq (S := S) (a := a) (by omega)
      exact ⟨Sum.inr (Sum.inl j), by simp [topσ, hj]⟩
    · rintro ⟨v, hv⟩
      rcases v with j | j | k
      · simp [topσ] at hv
      · have : topEmb r S j = a := by simpa [topσ] using hv
        subst this
        show 2 * S.card - cnt S (topEmb r S j) = S.card
        rw [cnt_topEmb j]
        omega
      · simp [topσ] at hv
  · exact ⟨fun _ => ⟨Sum.inr (Sum.inr k), rfl⟩, fun _ => rfl⟩

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
