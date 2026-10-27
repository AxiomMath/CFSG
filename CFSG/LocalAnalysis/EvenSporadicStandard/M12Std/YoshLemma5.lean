module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Alpha
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Mem

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b

section Words

theorem actRel_s_words : ∀ i : Fin 6,
    swN ([-8, ((i.val + 1 : ℕ) : ℤ), 8] ++ invL (Ws.getD i.val [])) =
      [((7 : Fin 9), false)] ++ [(Fin.castLE (by norm_num : 6 ≤ 9) i, true)] ++
        [((7 : Fin 9), true)] ++
        invW ((actE Ws i).map (fun l => (Fin.castLE (by norm_num : 6 ≤ 9) l.1, l.2))) := by
  decide

theorem swN_sss : swN [8, 8, 8] = [((7 : Fin 9), true)] ++ [((7 : Fin 9), true)] ++
    [((7 : Fin 9), true)] := by decide

theorem swN_stst : swN [8, 9, 8, 9] = [((7 : Fin 9), true)] ++ [((8 : Fin 9), true)] ++
    [((7 : Fin 9), true)] ++ [((8 : Fin 9), true)] := by decide

theorem swN_sxsxsx_zero : swN ([8, 7, 8, 7, 8, 7] ++ (List.replicate 0 (invL cL)).flatten) =
    [((7 : Fin 9), true)] ++ [((6 : Fin 9), true)] ++ [((7 : Fin 9), true)] ++
      [((6 : Fin 9), true)] ++ [((7 : Fin 9), true)] ++ [((6 : Fin 9), true)] := by decide

theorem swN_sxsxsx_one : swN ([8, 7, 8, 7, 8, 7] ++ (List.replicate 1 (invL cL)).flatten) =
    [((7 : Fin 9), true)] ++ [((6 : Fin 9), true)] ++ [((7 : Fin 9), true)] ++
      [((6 : Fin 9), true)] ++ [((7 : Fin 9), true)] ++ [((6 : Fin 9), true)] ++
      [((0 : Fin 9), false)] ++ [((0 : Fin 9), false)] := by decide

end Words

section Assembly

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

variable {d : G} {α β : ℕ}

theorem gen5_relN (hα : α < 2) (hd : CentralSwap e₀ α d)
    (hrel : ∀ r ∈ rel4 α α, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1) {k : ℕ} (hk : k < 2)
    (hy : sG e₀ * gen5 e₀ d α α 6 * sG e₀ * gen5 e₀ d α α 6 * sG e₀ * gen5 e₀ d α α 6 =
      cG e₀ ^ k) :
    ∀ r ∈ relN α α k, FreeGroup.lift (gen5 e₀ d α α) (FreeGroup.mk r) = 1 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := sAct_facts e₀
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
  rcases List.mem_append.1 hr' with h | h
  · exact gen5_relNQL e₀ hα hα hrel r' h
  rw [relNSL] at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    have hi6 : i < 6 := List.mem_range.1 hi
    have key := actRel_s_words ⟨i, hi6⟩
    simp only [Fin.val_mk] at key
    rw [key, lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_invW, lift_gen5_map,
      lift_mk_single_inv, lift_mk_single, lift_mk_single, gen5_s]
    have := gE_s e₀ hd ⟨i, hi6⟩ (β := α)
    rw [← this]
    exact mul_inv_cancel _
  · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · rw [swN_sss, lift_mk_append, lift_mk_append, lift_mk_single, gen5_s]
      exact f6
    · rw [swN_stst, lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_single,
        lift_mk_single, gen5_s, gen5_t]
      exact f7
    · rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · rw [swN_sxsxsx_zero]
        simp only [lift_mk_append, lift_mk_single]
        rw [gen5_s]
        simpa [mul_assoc] using hy
      · rw [swN_sxsxsx_one]
        simp only [lift_mk_append, lift_mk_single, lift_mk_single_inv]
        rw [gen5_s, gen5_a1]
        rw [hy, pow_one, ← f8]
        group

theorem nGens_size (hα : α < 2) {k : ℕ} (hk : k < 2) : (nGens α k).size = 9 := by
  interval_cases α <;> interval_cases k <;> rfl

theorem mem_modelGroup_gen (n k : ℕ) (g : Array Table) (i : Fin k) :
    modelGens n k g i ∈ modelGroup n k g :=
  Subgroup.subset_closure (Set.mem_range_self i)

theorem lift_gen5_mem_Nn (he2 : orderOf e = 2) (hd : CentralSwap e₀ α d) (x : FreeGroup (Fin 9)) :
    FreeGroup.lift (gen5 e₀ d α β) x ∈ Nn e₀ := by
  have hgen : ∀ i, gen5 e₀ d α β i ∈ Nn e₀ := by
    intro i
    fin_cases i
    · exact gen5_a1_mem e₀
    · exact gen5_a2_mem e₀
    · exact gen5_b1_mem e₀
    · exact gen5_b2_mem e₀
    · exact gen5_d_mem e₀ he2 hd
    · exact gen5_e_mem e₀
    · show gen5 e₀ d α β 6 ∈ Nn e₀
      rw [gen5_x]
      exact mul_mem (dW_μS_mem e₀ he2 hd) (pow_mem (mul_mem (mul_mem (mul_mem (mul_mem
        (mul_mem (gen5_t_mem e₀) (gen5_a1_mem e₀)) (gen5_a2_mem e₀)) (gen5_b2_mem e₀))
        (gen5_d_mem e₀ he2 hd)) (pow_mem (gen5_e_mem e₀) β)) α)
    · exact gen5_s_mem e₀
    · exact gen5_t_mem e₀
  have h : (FreeGroup.lift (gen5 e₀ d α β)).range ≤ Nn e₀ :=
    FreeGroup.range_lift_le (by rintro _ ⟨i, rfl⟩; exact hgen i)
  exact h ⟨x, rfl⟩

theorem yosh5 (he2 : orderOf e = 2) (hα : α < 2) (hd : CentralSwap e₀ α d) :
    ∃ (k : ℕ) (_ : k < 2) (Ψ : ↥(modelGroup 16 9 (nGens α k)) →* G),
      Function.Injective Ψ ∧ Ψ.range = Nn e₀ ∧
      (∀ i : Fin 9, Ψ ⟨modelGens 16 9 (nGens α k) i, mem_modelGroup_gen _ _ _ i⟩ =
        gen5 e₀ d α α i) ∧
      ∀ r ∈ rel4 α α, FreeGroup.lift (gen4 e₀ d) (FreeGroup.mk r) = 1 := by
  obtain ⟨β, hβ, hrel⟩ := yosh4 e₀ he2 hd (by omega)
  obtain ⟨hαβ, k, hk, hy⟩ := lemma5_alpha_eq e₀ he2 hα (by omega) hd hrel
  subst hαβ
  have hn : (16 : ℕ) < 2 ^ 32 := by norm_num
  have hnC : ModelOK 16 16 9 (nGens α k) (relN α α k) 3072 := nModelOK α k hα hk
  have hsz : (nGens α k).size = 9 := nGens_size hα hk
  have hrelN := gen5_relN e₀ hα hd hrel hk hy
  have hinj : Function.Injective (modelHomOf hn hsz hnC (gen5 e₀ d α α) hrelN) := by
    refine modelHomOf_injective hn hsz hnC (lemma5_model_parts.2 α k hα hk) (j := 7)
      (by norm_num) (gen5 e₀ d α α) hrelN [(0, true), (0, true)]
      ((tblEq_iff_eq (rep_modelT hn hsz hnC _) (rep_modelT hn hsz hnC _)).2 rfl) ?_
    have h8 := (sAct_facts e₀).2.2.2.2.2.2.2
    have : FreeGroup.lift (gen5 e₀ d α α)
        (FreeGroup.mk [((0 : Fin 9), true), ((0 : Fin 9), true)]) =
        valG e₀ wA1 * valG e₀ wA1 := by
      rw [show ([((0 : Fin 9), true), ((0 : Fin 9), true)] : List (Fin 9 × Bool)) =
        [(0, true)] ++ [(0, true)] from rfl, lift_mk_append, lift_mk_single, gen5_a1]
    rw [this, h8]
    exact cG_ne_one e₀
  refine ⟨k, hk, modelHomOf hn hsz hnC (gen5 e₀ d α α) hrelN, hinj, ?_, ?_, hrel⟩
  · have hle : (modelHomOf hn hsz hnC (gen5 e₀ d α α) hrelN).range ≤ Nn e₀ := by
      rintro _ ⟨m, rfl⟩
      obtain ⟨x, hx⟩ : ∃ x : FreeGroup (Fin 9),
          FreeGroup.lift (modelGens 16 9 (nGens α k)) x = (m : Equiv.Perm (Fin 16)) := by
        have h : (m : Equiv.Perm (Fin 16)) ∈
            Subgroup.closure (Set.range (modelGens 16 9 (nGens α k))) := m.2
        rw [← FreeGroup.range_lift_eq_closure] at h
        exact h
      have hm : m = ⟨FreeGroup.lift (modelGens 16 9 (nGens α k)) (FreeGroup.mk x.toWord),
          lift_mem_modelGroup _ _ _ _⟩ := by
        apply Subtype.ext
        show (m : Equiv.Perm (Fin 16)) =
          FreeGroup.lift (modelGens 16 9 (nGens α k)) (FreeGroup.mk x.toWord)
        rw [FreeGroup.mk_toWord]
        exact hx.symm
      rw [hm, modelHomOf_lift]
      exact lift_gen5_mem_Nn e₀ he2 hd _
    have hcardN : Nat.card (Nn e₀) = 3072 := card_Nn e₀ he2 hd
    haveI : Finite (Nn e₀) := Nat.finite_of_card_ne_zero (by rw [hcardN]; norm_num)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, hcardN]
    exact (modelCheck_spec hn hsz hnC).1.card_group.ge
  · intro i
    have h1 := modelHomOf_lift hn hsz hnC (gen5 e₀ d α α) hrelN [(i, true)]
    have h2 : (⟨modelGens 16 9 (nGens α k) i, mem_modelGroup_gen _ _ _ i⟩ :
        ↥(modelGroup 16 9 (nGens α k))) =
        ⟨FreeGroup.lift (modelGens 16 9 (nGens α k)) (FreeGroup.mk [(i, true)]),
          lift_mem_modelGroup _ _ _ _⟩ :=
      Subtype.ext (lift_mk_single (modelGens 16 9 (nGens α k)) i).symm
    rw [h2, h1, lift_mk_single]

end Assembly

end CFSG.EvenSporadicStandard.M12Std.Yosh
