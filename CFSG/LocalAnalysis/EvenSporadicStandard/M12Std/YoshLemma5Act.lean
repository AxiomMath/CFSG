module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Gen
public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.YoshLemma5Alg

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.CosetTable
open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.GH74.M12 CFSG.GH74.M12.Hyp
open CFSG.EvenSporadicStandard.Fin76b

section Words

theorem lift_mk_single_inv {H : Type*} [Group H] {m : ℕ} (g : Fin m → H) (i : Fin m) :
    FreeGroup.lift g (FreeGroup.mk [(i, false)]) = (g i)⁻¹ := by
  have := lift_mk_invW g [(i, true)]
  rw [lift_mk_single] at this
  exact this

theorem relEL_map : ∀ r ∈ relEL,
    (swE r).map (fun l => (Fin.castLE (by norm_num : 6 ≤ 9) l.1, l.2)) = swN r := by decide

theorem actRel_x_words : ∀ α < 2, ∀ β < 2, ∀ i : Fin 6,
    swN ([-7, ((i.val + 1 : ℕ) : ℤ), 7] ++ invL ((Wx α β).getD i.val [])) =
      [((6 : Fin 9), false)] ++ [(Fin.castLE (by norm_num : 6 ≤ 9) i, true)] ++
        [((6 : Fin 9), true)] ++
        invW ((actE (Wx α β) i).map (fun l => (Fin.castLE (by norm_num : 6 ≤ 9) l.1, l.2))) := by
  decide

end Words

section Act

variable {G : Type} [Group G] {e : G}
variable (e₀ : centralizer ({e} : Set G) ≃* Multiplicative (ZMod 2) × G12)


set_option linter.unusedSectionVars false

@[expose] noncomputable def gE (d : G) (α β : ℕ) : Fin 6 → G := fun i =>
  gen5 e₀ d α β (Fin.castLE (by norm_num) i)

variable {d : G} {α β : ℕ}

theorem lift_gen5_map (w : List (Fin 6 × Bool)) :
    FreeGroup.lift (gen5 e₀ d α β)
        (FreeGroup.mk (w.map fun l => (Fin.castLE (by norm_num : 6 ≤ 9) l.1, l.2))) =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk w) :=
  (lift_mk_map (Fin.castLE (by norm_num : 6 ≤ 9)) (gen5 e₀ d α β) w).symm

theorem gE_rel
    (hrel5 : ∀ r ∈ relNQL α β, FreeGroup.lift (gen5 e₀ d α β) (FreeGroup.mk (swN r)) = 1) :
    ∀ r ∈ relE, FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk r) = 1 := by
  intro r hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hr
  have h1 := hrel5 r' (by
    simp only [relNQL, List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl hr'))))
  rw [← lift_gen5_map, relEL_map r' hr']
  exact h1

theorem gE_x (hα : α < 2) (hβ : β < 2)
    (hrel5 : ∀ r ∈ relNQL α β, FreeGroup.lift (gen5 e₀ d α β) (FreeGroup.mk (swN r)) = 1)
    (i : Fin 6) :
    (gen5 e₀ d α β 6)⁻¹ * gE e₀ d α β i * gen5 e₀ d α β 6 =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE (Wx α β) i)) := by
  have hmem : ([-7, ((i.val + 1 : ℕ) : ℤ), 7] ++ invL ((Wx α β).getD i.val [])) ∈
      relNQL α β := by
    simp only [relNQL, List.mem_append]
    refine Or.inl (Or.inr ?_)
    simp only [actRel, List.mem_map, List.mem_range]
    exact ⟨i.val, i.2, rfl⟩
  have h1 := hrel5 _ hmem
  rw [actRel_x_words α hα β hβ i, lift_mk_append, lift_mk_append, lift_mk_append, lift_mk_invW,
    lift_gen5_map, lift_mk_single_inv, lift_mk_single, lift_mk_single] at h1
  exact mul_inv_eq_one.1 h1

theorem sAct_facts :
    (sG e₀)⁻¹ * valG e₀ wA1 * sG e₀ = valG e₀ wA2 ∧
    (sG e₀)⁻¹ * valG e₀ wA2 * sG e₀ = valG e₀ wA1 * valG e₀ wA2 ∧
    (sG e₀)⁻¹ * valG e₀ wB1 * sG e₀ = valG e₀ wB2 ∧
    (sG e₀)⁻¹ * valG e₀ wB2 * sG e₀ = valG e₀ wB1 * valG e₀ wB2 ∧
    (sG e₀)⁻¹ * valG e₀ wE * sG e₀ = valG e₀ wE ∧
    sG e₀ * sG e₀ * sG e₀ = 1 ∧
    sG e₀ * valG e₀ wT * sG e₀ * valG e₀ wT = 1 ∧
    valG e₀ wA1 * valG e₀ wA1 = cG e₀ := by
  have h : sActOK = true := lemma5_parts.1
  simp only [sActOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [valG_append, valG_invW, valG_wSP] using valG_eq_of_tblEq e₀ h1
  · simpa only [valG_append, valG_invW, valG_wSP] using valG_eq_of_tblEq e₀ h2
  · simpa only [valG_append, valG_invW, valG_wSP] using valG_eq_of_tblEq e₀ h3
  · simpa only [valG_append, valG_invW, valG_wSP] using valG_eq_of_tblEq e₀ h4
  · simpa only [valG_append, valG_invW, valG_wSP] using valG_eq_of_tblEq e₀ h5
  · simpa only [valG_append, valG_wSP] using valG_eq_one_of_tblEq e₀ h6
  · simpa only [valG_append, valG_wSP] using valG_eq_one_of_tblEq e₀ h7
  · simpa only [valG_append, valG_wJ] using valG_eq_of_tblEq e₀ h8

theorem sG_inv_conj_d (hd : CentralSwap e₀ α d) : (sG e₀)⁻¹ * d * sG e₀ = d := by
  have h := hd.conj_s
  have h1 : d * sG e₀ = sG e₀ * d := by
    calc d * sG e₀ = (d * sG e₀ * d⁻¹) * d := by group
      _ = sG e₀ * d := by rw [h]
  calc (sG e₀)⁻¹ * d * sG e₀ = (sG e₀)⁻¹ * (d * sG e₀) := by group
    _ = (sG e₀)⁻¹ * (sG e₀ * d) := by rw [h1]
    _ = d := by group

theorem gE_s (hd : CentralSwap e₀ α d) (i : Fin 6) :
    (sG e₀)⁻¹ * gE e₀ d α β i * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws i)) := by
  obtain ⟨f1, f2, f3, f4, f5, -, -, -⟩ := sAct_facts e₀
  fin_cases i
  · show (sG e₀)⁻¹ * gE e₀ d α β 0 * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws 0))
    have hw : actE Ws 0 = [(1, true)] := by decide
    rw [hw, lift_mk_single]
    show (sG e₀)⁻¹ * gen5 e₀ d α β 0 * sG e₀ = gen5 e₀ d α β 1
    rw [gen5_a1, gen5_a2]
    exact f1
  · show (sG e₀)⁻¹ * gE e₀ d α β 1 * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws 1))
    have hw : actE Ws 1 = [(0, true)] ++ [(1, true)] := by decide
    rw [hw, lift_mk_append, lift_mk_single, lift_mk_single]
    show (sG e₀)⁻¹ * gen5 e₀ d α β 1 * sG e₀ = gen5 e₀ d α β 0 * gen5 e₀ d α β 1
    rw [gen5_a1, gen5_a2]
    exact f2
  · show (sG e₀)⁻¹ * gE e₀ d α β 2 * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws 2))
    have hw : actE Ws 2 = [(3, true)] := by decide
    rw [hw, lift_mk_single]
    show (sG e₀)⁻¹ * gen5 e₀ d α β 2 * sG e₀ = gen5 e₀ d α β 3
    rw [gen5_b1, gen5_b2]
    exact f3
  · show (sG e₀)⁻¹ * gE e₀ d α β 3 * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws 3))
    have hw : actE Ws 3 = [(2, true)] ++ [(3, true)] := by decide
    rw [hw, lift_mk_append, lift_mk_single, lift_mk_single]
    show (sG e₀)⁻¹ * gen5 e₀ d α β 3 * sG e₀ = gen5 e₀ d α β 2 * gen5 e₀ d α β 3
    rw [gen5_b1, gen5_b2]
    exact f4
  · show (sG e₀)⁻¹ * gE e₀ d α β 4 * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws 4))
    have hw : actE Ws 4 = [(4, true)] := by decide
    rw [hw, lift_mk_single]
    show (sG e₀)⁻¹ * gen5 e₀ d α β 4 * sG e₀ = gen5 e₀ d α β 4
    rw [gen5_d]
    exact sG_inv_conj_d e₀ hd
  · show (sG e₀)⁻¹ * gE e₀ d α β 5 * sG e₀ =
      FreeGroup.lift (gE e₀ d α β) (FreeGroup.mk (actE Ws 5))
    have hw : actE Ws 5 = [(5, true)] := by decide
    rw [hw, lift_mk_single]
    show (sG e₀)⁻¹ * gen5 e₀ d α β 5 * sG e₀ = gen5 e₀ d α β 5
    rw [gen5_e]
    exact f5

end Act

section Comp

variable {H : Type*} [Group H]

theorem comp_conj {α β : ℕ} {x s : H} {g : Fin 6 → H}
    (hx : ∀ i, x⁻¹ * g i * x = FreeGroup.lift g (FreeGroup.mk (actE (Wx α β) i)))
    (hs : ∀ i, s⁻¹ * g i * s = FreeGroup.lift g (FreeGroup.mk (actE Ws i))) (i : Fin 6) :
    (s * x * s * x * s * x)⁻¹ * g i * (s * x * s * x * s * x) =
      FreeGroup.lift g (FreeGroup.mk (compF α β i)) := by
  have e1 := hs i
  have e2 := conj_lift_substW x g (actE (Wx α β)) hx (actE Ws i)
  have e3 := conj_lift_substW s g (actE Ws) hs (substW (actE (Wx α β)) (actE Ws i))
  have e4 := conj_lift_substW x g (actE (Wx α β)) hx
    (substW (actE Ws) (substW (actE (Wx α β)) (actE Ws i)))
  have e5 := conj_lift_substW s g (actE Ws) hs
    (substW (actE (Wx α β)) (substW (actE Ws) (substW (actE (Wx α β)) (actE Ws i))))
  have e6 := conj_lift_substW x g (actE (Wx α β)) hx
    (substW (actE Ws) (substW (actE (Wx α β)) (substW (actE Ws) (substW (actE (Wx α β))
      (actE Ws i)))))
  unfold compF
  rw [← e6, ← e5, ← e4, ← e3, ← e2, ← e1]
  group

end Comp

end CFSG.EvenSporadicStandard.M12Std.Yosh
