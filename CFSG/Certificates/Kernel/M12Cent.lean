
module

public import Certificates.Data.Kernel.M12Cent
public import CFSG.Certificates.Kernel.ConjKeys
public import CFSG.RankThree.PartTwo.Toolkit.M12LocalGroups

public section

namespace CFSG.KC.M12Cent

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12 Subgroup

@[expose] def letE : ℕ → G12
  | 0 => CFSG.Sporadic.Mathieu.m12a
  | 1 => CFSG.Sporadic.Mathieu.m12a
  | 2 => CFSG.Sporadic.Mathieu.m12b
  | _ => CFSG.Sporadic.Mathieu.m12b⁻¹

@[expose] def wG : List ℕ → G12
  | [] => 1
  | l :: w => letE l * wG w

theorem tinv_tA : tinv tAk = tAk := by decide +kernel

theorem tinv_tB : tinv tBk = tBi := by decide +kernel

theorem tbl_letE (l : ℕ) : tbl (letE l).1 = letN l ∧ tbl (letE l)⁻¹.1 = letInv l := by
  have ha : tbl (CFSG.Sporadic.Mathieu.m12a : G12).1 = tAk := tbl_m12gA
  have hb : tbl (CFSG.Sporadic.Mathieu.m12b : G12).1 = tBk := tbl_m12gB
  match l with
  | 0 => exact ⟨ha, by rw [letE, tblG_inv, ha, tinv_tA]; rfl⟩
  | 1 => exact ⟨ha, by rw [letE, tblG_inv, ha, tinv_tA]; rfl⟩
  | 2 => exact ⟨hb, by rw [letE, tblG_inv, hb, tinv_tB]; rfl⟩
  | l + 3 =>
    have e : letE (l + 3) = CFSG.Sporadic.Mathieu.m12b⁻¹ := rfl
    exact ⟨by rw [e, tblG_inv, hb, tinv_tB]; rfl, by rw [e, inv_inv, hb]; rfl⟩

theorem tbl_wG (w : List ℕ) : tbl (wG w).1 = wordN w := by
  induction w with
  | nil => exact tblG_one
  | cons l w ih => rw [wG, tblG_mul, ih, (tbl_letE l).1]; rfl

theorem tbl_wG_conj (w : List ℕ) (g : G12) :
    tbl (wG w * g * (wG w)⁻¹).1 = conjN w (tbl g.1) := by
  induction w with
  | nil =>
    rw [wG, one_mul, inv_one, mul_one]
    rfl
  | cons l w ih =>
    have e : wG (l :: w) * g * (wG (l :: w))⁻¹ =
        letE l * (wG w * g * (wG w)⁻¹) * (letE l)⁻¹ := by
      rw [wG]
      group
    rw [e, tblG_mul, tblG_mul, ih, (tbl_letE l).1, (tbl_letE l).2]
    rfl

theorem pairwise_of_incr : ∀ {l : List ℕ}, incr l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: r, h => by
    rw [incr, Bool.and_eq_true, Nat.blt_eq] at h
    have hr := pairwise_of_incr h.2
    refine List.Pairwise.cons (fun c hc => ?_) hr
    rcases List.mem_cons.1 hc with rfl | hc
    · exact h.1
    · exact h.1.trans (List.rel_of_pairwise_cons hr hc)

theorem idx_eq_of_incr {l : List ℕ} (h : incr l = true) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (he : l[i] = l[j]) : i = j :=
  ((pairwise_of_incr h).nodup.getElem_inj_iff).1 he

theorem card_centralizer_conj {X : Type*} [Group X] (c g : X) :
    Nat.card (centralizer ({c * g * c⁻¹} : Set X)) = Nat.card (centralizer ({g} : Set X)) := by
  refine Nat.card_congr
    { toFun := fun u => ⟨c⁻¹ * u * c, mem_centralizer_singleton_iff.2 ?_⟩
      invFun := fun u => ⟨c * u * c⁻¹, mem_centralizer_singleton_iff.2 ?_⟩
      left_inv := fun u => Subtype.ext (by simp only; group)
      right_inv := fun u => Subtype.ext (by simp only; group) }
  · have hu := mem_centralizer_singleton_iff.1 u.2
    calc c⁻¹ * u * c * g = c⁻¹ * (u * (c * g * c⁻¹)) * c := by group
      _ = c⁻¹ * (c * g * c⁻¹ * u) * c := by rw [hu]
      _ = g * (c⁻¹ * u * c) := by group
  · have hu := mem_centralizer_singleton_iff.1 u.2
    calc c * u * c⁻¹ * (c * g * c⁻¹) = c * (u * g) * c⁻¹ := by group
      _ = c * (g * u) * c⁻¹ := by rw [hu]
      _ = c * g * c⁻¹ * (c * u * c⁻¹) := by group

variable {g : G12} {S W C R : List (List ℕ)}

theorem card_centralizer_self
    (h : centCheck (tbl g.1) S W C R = true) :
    Nat.card (centralizer ({g} : Set G12)) = 54 := by
  unfold centCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hW, hC⟩, hWk⟩, hCc⟩, hCk⟩, -⟩ := h
  have hle := CFSG.KC.ConjKeys.card_mul_le_of_conj_keys (⊤ : Subgroup G12) g
    (N := 1760) (fun j => wG (W.getD j [])) (fun _ _ => mem_top _)
    (fun u : G12 => keyT (tbl u.1)) (fun i hi j hj he => by
      rw [tbl_wG_conj, tbl_wG_conj] at he
      have hi' : i < (W.map fun w => keyT (conjN w (tbl g.1))).length := by
        rw [List.length_map, hW]
        exact hi
      have hj' : j < (W.map fun w => keyT (conjN w (tbl g.1))).length := by
        rw [List.length_map, hW]
        exact hj
      refine idx_eq_of_incr hWk hi' hj' ?_
      rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ [],
        ← List.getD_eq_getElem _ []]
      exact he)
  rw [top_inf_eq, card_top, CFSG.Sporadic.Mathieu.card_M12] at hle
  have hge : 54 ≤ Nat.card (centralizer ({g} : Set G12)) := by
    have hmem : ∀ i : Fin 54, wG (C.getD i []) ∈ centralizer ({g} : Set G12) := fun i => by
      rw [mem_centralizer_singleton_iff, eq_iff_tbl, tblG_mul, tblG_mul, tbl_wG]
      have hi : (i : ℕ) < C.length := by rw [hC]; exact i.2
      have := List.all_eq_true.1 hCc _ (List.getElem_mem hi)
      rw [beq_iff_eq] at this
      rw [List.getD_eq_getElem _ _ hi]
      exact this
    have hinj : Function.Injective fun i : Fin 54 =>
        (⟨wG (C.getD i []), hmem i⟩ : centralizer ({g} : Set G12)) := by
      intro i j he
      have he' := congrArg (fun u : centralizer ({g} : Set G12) => keyT (tbl u.1.1)) he
      simp only [tbl_wG] at he'
      have hi : (i : ℕ) < (C.map fun w => keyT (wordN w)).length := by
        rw [List.length_map, hC]
        exact i.2
      have hj : (j : ℕ) < (C.map fun w => keyT (wordN w)).length := by
        rw [List.length_map, hC]
        exact j.2
      refine Fin.ext (idx_eq_of_incr hCk hi hj ?_)
      rw [List.getElem_map, List.getElem_map, ← List.getD_eq_getElem _ [],
        ← List.getD_eq_getElem _ []]
      exact he'
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card (α := Fin 54), Fintype.card_fin] at this
  omega

theorem card_centralizer_of_centCheck
    (h : centCheck (tbl g.1) S W C R = true) {v : G12} (hv : tbl v.1 ∈ S) (hv1 : v ≠ 1) :
    Nat.card (centralizer ({v} : Set G12)) = 54 := by
  have h' := h
  unfold centCheck at h'
  simp only [Bool.and_eq_true] at h'
  have hS := List.all_eq_true.1 h'.2 _ hv
  rw [Bool.or_eq_true, beq_iff_eq] at hS
  rcases hS with h1 | hR
  · exact absurd (eq_iff_tbl.2 (h1.trans tblG_one.symm)) hv1
  · obtain ⟨w, -, hw⟩ := List.any_eq_true.1 hR
    rw [beq_iff_eq, ← tbl_wG_conj] at hw
    rw [← eq_iff_tbl.2 hw, card_centralizer_conj]
    exact card_centralizer_self h

end CFSG.KC.M12Cent

end
