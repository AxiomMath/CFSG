module

public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Mathieu.Native

theorem m12_fix_base (g : NativeSporadic.M12)
    (h : ∀ i : Fin 12, i.val < 5 → g.1 i = i) : g = 1 := by
  have hC := chain m12_hyp
  have hsize : m12Data.base.size = 5 := rfl
  have step : ∀ i < 5, g ∈ lvl m12Data m12a m12b i → g ∈ lvl m12Data m12a m12b (i + 1) := by
    intro i hi hg
    refine (hC.2.1 i (by omega) g hg).1 ?_
    have hb : m12Data.base[i]! = i := by
      interval_cases i <;> rfl
    rw [hb, CFSG.Sporadic.Th.idx_of_lt g (show i < 12 by omega)]
    exact congrArg Fin.val (h ⟨i, by omega⟩ hi)
  have h0 : g ∈ lvl m12Data m12a m12b 0 := by
    rw [lvl_zero m12_hyp]
    trivial
  have h5 : g ∈ lvl m12Data m12a m12b 5 :=
    step 4 (by norm_num) (step 3 (by norm_num) (step 2 (by norm_num)
      (step 1 (by norm_num) (step 0 (by norm_num) h0))))
  have hcard : Nat.card (lvl m12Data m12a m12b 5) = 1 := by
    rw [(hC.2.2 5 (by omega)), hsize]
    simp
  rw [Subgroup.eq_bot_of_card_eq _ hcard] at h5
  simpa using h5

private def fiveImages (g : NativeSporadic.M12) : Fin 5 ↪ Fin 12 :=
  (Fin.castLEEmb (show 5 ≤ 12 by norm_num)).trans g.1.toEmbedding

private theorem fiveImages_injective :
    Function.Injective fiveImages := by
  intro g g' hgg
  have hfix : g⁻¹ * g' = 1 := by
    refine m12_fix_base _ fun i hi => ?_
    have h1 : g.1 i = g'.1 i := congrArg (fun f : Fin 5 ↪ Fin 12 => f ⟨i.val, hi⟩) hgg
    show (g.1)⁻¹ (g'.1 i) = i
    rw [← h1]
    simp
  exact inv_mul_eq_one.1 hfix

private theorem fiveImages_bijective :
    Function.Bijective fiveImages := by
  refine fiveImages_injective.bijective_of_nat_card_le ?_
  rw [card_M12, Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp [Nat.descFactorial]

theorem m12_five_transitive (p : Fin 5 ↪ Fin 12) :
    ∃ g ∈ NativeSporadic.M12, ∀ i : Fin 5, g (Fin.castLE (show 5 ≤ 12 by norm_num) i) = p i := by
  obtain ⟨g, hg⟩ := fiveImages_bijective.2 p
  exact ⟨g.1, g.2, fun i => congrArg (fun f : Fin 5 ↪ Fin 12 => f i) hg⟩

theorem m12_fix_five (g : Equiv.Perm (Fin 12))
    (hg : g ∈ NativeSporadic.M12) (p : Fin 5 ↪ Fin 12) (hp : ∀ i, g (p i) = p i) : g = 1 := by
  obtain ⟨h, hh, hhp⟩ := m12_five_transitive p
  have hk : (⟨h⁻¹ * g * h, NativeSporadic.M12.mul_mem
      (NativeSporadic.M12.mul_mem (NativeSporadic.M12.inv_mem hh) hg) hh⟩ : NativeSporadic.M12) =
        1 := by
    refine m12_fix_base _ fun i hi => ?_
    have h1 : h i = p ⟨i.val, hi⟩ := hhp ⟨i.val, hi⟩
    show (h⁻¹ * g * h) i = i
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hp, ← h1]
    simp
  have hk1 : h⁻¹ * g * h = 1 := congrArg Subtype.val hk
  calc g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    _ = 1 := by rw [hk1]; group

theorem m12_fix_eight :
    ∀ g ∈ NativeSporadic.M12, g * g = 1 →
      (∃ O : Finset (Fin 12), O.card = 8 ∧ ∀ ω ∈ O, g ω = ω) → g = 1 := by
  rintro g hg - ⟨O, hO, hfix⟩
  let q : Fin 5 → Fin 12 := fun i => O.orderEmbOfFin hO (Fin.castLE (show 5 ≤ 8 by norm_num) i)
  have hq : Function.Injective q := fun i j hij =>
    Fin.castLE_injective _ ((O.orderEmbOfFin hO).injective hij)
  exact m12_fix_five g hg ⟨q, hq⟩ fun i => hfix _ (Finset.orderEmbOfFin_mem O hO _)

end CFSG.GH74.Generic.S1.Exo
