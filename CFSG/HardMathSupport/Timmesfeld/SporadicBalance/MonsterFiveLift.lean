module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFiveRel
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.AGLEmbedding.Norton
  CFSG.AGLEmbedding.Norton.MON5_7 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcRegular
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PcSylow

section Sound


theorem lift_wordF_gen (g : Fin 9 → Gmat) (v : Array ℕ) :
    FreeGroup.lift g (wordF 9 v) =
      ((List.range 9).map fun k => if h : k < 9 then g ⟨k, h⟩ ^ v[k]! else 1).prod := by
  unfold wordF
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k hk
  have hk' := List.mem_range.1 hk
  simp only [Function.comp_apply, dite_eq_left hk', map_pow, FreeGroup.lift_apply_of]

theorem lift_wordF_eq_rhsW (hpow : agreeAll powEqs = true) (v : Array ℕ) :
    FreeGroup.lift (fun i : Fin 9 => gw fiveGens[i.val]!) (wordF 9 v) = gw (rhsW v) := by
  rw [lift_wordF_gen, gw_rhsW hpow]
  refine congrArg List.prod (List.map_congr_left fun k hk => ?_)
  have hk' := List.mem_range.1 hk
  simp only [hk', dite_true]

theorem powEqs_of_relEqs (h : agreeAll relEqs = true) : agreeAll powEqs = true := by
  unfold relEqs at h
  unfold agreeAll at h ⊢
  simp only [List.all_append, Bool.and_eq_true] at h ⊢
  exact h.1.1

theorem fiveRels (h : agreeAll relEqs = true) :
    ∀ r ∈ relSet 5 (pwF 9 fivePw) (cwF 9 fiveCw),
      FreeGroup.lift (fun i : Fin 9 => gw fiveGens[i.val]!) r = 1 := by
  have hall := agreeAll_sound h
  have hpow := powEqs_of_relEqs h
  have hR := lift_wordF_eq_rhsW hpow
  intro r hr
  rcases hr with ⟨i, rfl⟩ | ⟨i, j, hij, rfl⟩
  · have hmem : (repW 5 fiveGens[i.val]!, rhsW fivePw[i.val]!) ∈ relEqs := by
      unfold relEqs pwEqs
      simp only [List.mem_append]
      left; right
      exact List.mem_map.2 ⟨i.val, List.mem_range.2 i.isLt, rfl⟩
    have := hall _ hmem
    simp only at this
    rw [gw_repW] at this
    simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of, pwF]
    rw [hR, ← this, mul_inv_cancel]
  · have hmem : (fiveGens[j.val]! ++ fiveGens[i.val]!,
        fiveGens[i.val]! ++ rhsW fiveCw[i.val * 9 + j.val]!) ∈ relEqs := by
      unfold relEqs cwEqs
      simp only [List.mem_append]
      right
      rw [List.mem_flatMap]
      refine ⟨i.val, List.mem_range.2 i.isLt, ?_⟩
      rw [List.mem_map]
      exact ⟨j.val, List.mem_filter.2 ⟨List.mem_range.2 j.isLt, by simpa using hij⟩, rfl⟩
    have := hall _ hmem
    simp only [gw_append] at this
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, cwF]
    rw [hR, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact this

theorem agreeAll_append {l₁ l₂ : List (List Native.Gen × List Native.Gen)}
    (h₁ : agreeAll l₁ = true) (h₂ : agreeAll l₂ = true) : agreeAll (l₁ ++ l₂) = true := by
  unfold agreeAll at *
  rw [List.all_append, h₁, h₂]
  rfl

theorem agreeAll_drop_split (l : List (List Native.Gen × List Native.Gen)) (a n : ℕ)
    (h₁ : agreeAll ((l.drop a).take n) = true) (h₂ : agreeAll (l.drop (a + n)) = true) :
    agreeAll (l.drop a) = true := by
  have e : l.drop a = (l.drop a).take n ++ (l.drop a).drop n := (List.take_append_drop n _).symm
  rw [e]
  refine agreeAll_append h₁ ?_
  rw [List.drop_drop]
  exact h₂

theorem fiveNorm (hpow : agreeAll powEqs = true) (h : agreeAll normEqs = true) :
    ∀ j < 3, ∀ i < 9, gw fiveNW[j]! * gw fiveGens[i]! * (gw fiveNW[j]!)⁻¹ =
      FreeGroup.lift (fun i : Fin 9 => gw fiveGens[i.val]!) (wordF 9 (fiveNImg[j]!)[i]!) := by
  intro j hj i hi
  have hmem : (fiveGens[i]! ++ fiveNW[j]!, fiveNW[j]! ++ rhsW (fiveNImg[j]!)[i]!) ∈ normEqs := by
    unfold normEqs
    rw [List.mem_flatMap]
    refine ⟨j, List.mem_range.2 hj, ?_⟩
    exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have := agreeAll_sound h _ hmem
  simp only [gw_append] at this
  rw [lift_wordF_eq_rhsW hpow, mul_inv_eq_iff_eq_mul]
  exact this

end Sound

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.MonsterFive
