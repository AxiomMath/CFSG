module

public import CFSG.GH74.GLS.C3.Prop121.FinPosCheck

public section

namespace CFSG.GH74.GLS.C3.Layer2.Model

open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Layer2

namespace Tab

variable {n : ℕ} [NeZero n]

theorem claimPos_apply (t : Tab n) (hc : t.claimPosB = true) {h0 h1 h2 h3 : Fin 64}
    (o0 : t.ok0 h0 = true) (o1 : t.ok1 h0 h1 = true) (o2 : t.ok2 h0 h1 h2 = true)
    (o3 : t.ok3 h0 h1 h2 h3 = true) (ha : t.isAutB (t.ofImages ![h0, h1, h2, h3]) = true) :
    t.finalPosB (t.ofImages ![h0, h1, h2, h3]) = true := by
  simp only [claimPosB, List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true] at hc
  exact hc h0 o0 h1 o1 h2 o2 h3 o3 ha

theorem finalPos_unpack (t : Tab n) {a : Tbl} (h : t.finalPosB a = true)
    (hx : a.get t.x0i ≠ t.x0i) (u : Fin 64) (hu : a.get u = u)
    (hsq : ∀ i, a.get (a.get i) = t.mulT (t.mulT u i) (t.inv.get u))
    (hdisj : ∀ i, (t.reach a t.x0i).get i = true →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = true → False)
    (hQ : ∀ i, t.isQ.get i = true → i ≠ t.one →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = false)
    (hW : t.wB a = true) :
    ∀ i, t.isQ.get i = true → (t.el.get (a.get i)).2 = 1 := by
  unfold finalPosB at h
  have e1 : (a.get t.x0i != t.x0i) = true := bne_iff_ne.2 hx
  have h1 := (imp_eq_true.1 h) e1
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at h1
  have e2 : (a.get u == u && (List.finRange 64).all fun i =>
      a.get (a.get i) == t.mulT (t.mulT u i) (t.inv.get u)) = true := by
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_finRange, true_implies]
    exact ⟨hu, hsq⟩
  have h2 := (imp_eq_true.1 (h1 u)) e2
  have e3 := all_not_and hdisj
  have h3 := (imp_eq_true.1 h2) e3
  have e4 : ((List.finRange 64).all fun i => imp (t.isQ.get i && i != t.one)
      (!(t.reach a (t.mulT t.x0i (a.get t.x0i))).get i)) = true := by
    apply all_imp
    intro i hi
    simp only [Bool.and_eq_true, bne_iff_ne] at hi
    simp [hQ i hi.1 hi.2]
  have h4 := (imp_eq_true.1 h3) e4
  have h5 := (imp_eq_true.1 h4) hW
  simpa only [List.all_eq_true, List.mem_finRange, true_implies, imp_eq_true,
    decide_eq_true_eq] using h5

end Tab

theorem fin_pos_data
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7) (t : Tab n) (hv : t.Valid)
    (hc : t.claimPosB = true)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ x, α (α x) = u * x * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (x : T0 n) (hx : (x : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(x : Amb n), hx⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α x : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V) :
    ∀ q : T0 n, (q : Amb n).1 = 1 → ((α q : T0 n) : Amb n).2 = 1 := by
  set a : Tbl := t.tabOf hn hv α with ha_def
  have haut : t.IsAutT a := t.tabOf_isAut hn hv α
  have ha_spec : ∀ i, t.iT hn hv (a.get i) = α (t.iT hn hv i) := t.iT_tabOf hn hv α
  have hfun : (fun k : Fin 4 => a.get (t.gens.get k)) =
      ![a.get (t.gens.get 0), a.get (t.gens.get 1), a.get (t.gens.get 2),
        a.get (t.gens.get 3)] := by
    funext k
    fin_cases k <;> rfl
  have hgen : t.ofImages ![a.get (t.gens.get 0), a.get (t.gens.get 1), a.get (t.gens.get 2),
      a.get (t.gens.get 3)] = a := by
    rw [← hfun]
    exact (haut.eq_ofImages hv).symm
  have o0 : t.ok0 (a.get (t.gens.get 0)) = true := by
    simp only [Tab.ok0, beq_iff_eq]
    exact haut.cls3_eq _
  have o1 : t.ok1 (a.get (t.gens.get 0)) (a.get (t.gens.get 1)) = true := by
    simp only [Tab.ok1, Bool.and_eq_true, beq_iff_eq]
    exact ⟨haut.cls3_eq _, haut.pairOK _ _⟩
  have o2 : t.ok2 (a.get (t.gens.get 0)) (a.get (t.gens.get 1)) (a.get (t.gens.get 2)) = true := by
    simp only [Tab.ok2, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨haut.cls3_eq _, haut.pairOK _ _⟩, haut.pairOK _ _⟩
  have o3 : t.ok3 (a.get (t.gens.get 0)) (a.get (t.gens.get 1)) (a.get (t.gens.get 2))
      (a.get (t.gens.get 3)) = true := by
    simp only [Tab.ok3, Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨⟨haut.cls3_eq _, haut.pairOK _ _⟩, haut.pairOK _ _⟩, haut.pairOK _ _⟩
  have hfin : t.finalPosB a = true := by
    have := Tab.claimPos_apply t hc o0 o1 o2 o3 (by rw [hgen]; exact (Tab.isAutB_iff t a).2 haut)
    rwa [hgen] at this
  have hx' : a.get t.x0i ≠ t.x0i := by
    intro h
    apply hx
    have := congrArg (t.iT hn hv) h
    rw [ha_spec, Tab.iT_x0] at this
    exact this
  set ui : Fin 64 := (t.eT hn hv).symm u with hui
  have hiTui : t.iT hn hv ui = u := (t.eT hn hv).apply_symm_apply u
  have hu' : a.get ui = ui := by
    apply t.iT_injective hn hv
    rw [ha_spec, hiTui, hu]
  have hsq' : ∀ i, a.get (a.get i) = t.mulT (t.mulT ui i) (t.inv.get ui) := by
    intro i
    apply t.iT_injective hn hv
    rw [ha_spec, ha_spec, hsq, Tab.iT_mul, Tab.iT_mul, Tab.iT_inv, hiTui]
  have hclX' := Tab.edge_closed t hn hv α X hclX
  have hclV' := Tab.edge_closed t hn hv α V hclV
  have hX0 := Tab.reach_sound t hn hv a X hclX' t.x0i (by rw [Tab.iT_x0]; exact hX)
  have hV0 := Tab.reach_sound t hn hv a V hclV' (t.mulT t.x0i (a.get t.x0i))
    (by rw [Tab.iT_mul, ha_spec, Tab.iT_x0]; exact hV)
  have hdisj' : ∀ i, (t.reach a t.x0i).get i = true →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = true → False := by
    intro i h1 h2
    exact Set.disjoint_left.1 hdisj (hX0 i h1) (hV0 i h2)
  have hQ' : ∀ i, t.isQ.get i = true → i ≠ t.one →
      (t.reach a (t.mulT t.x0i (a.get t.x0i))).get i = false := by
    intro i hi hi1
    by_contra hne
    have hV' : t.iT hn hv i ∈ V := hV0 i (by simpa using hne)
    refine hQ (t.iT hn hv i) ((hv.isQ_spec i).1 hi) ?_ hV'
    intro h
    apply hi1
    apply t.iT_injective hn hv
    rw [Tab.iT_one]
    exact h
  have hW := Tab.wB_of_ext t hn hv α hext
  have hpos := Tab.finalPos_unpack t hfin hx' ui hu' hsq' hdisj' hQ' hW
  intro q hq1
  set i : Fin 64 := (t.eT hn hv).symm q with hi
  have hiTq : t.iT hn hv i = q := (t.eT hn hv).apply_symm_apply q
  have hel : t.el.get i = (q : Amb n) := congrArg Subtype.val hiTq
  have hqQ : t.isQ.get i = true := (hv.isQ_spec i).2 (by rw [hel]; exact hq1)
  have h1 := hpos i hqQ
  have h2 : t.el.get (a.get i) = ((α q : T0 n) : Amb n) := by
    have := congrArg Subtype.val (ha_spec i)
    rw [hiTq] at this
    exact this
  rw [h2] at h1
  exact h1

theorem fin_pos
    (n : ℕ) [NeZero n] (hn : n = 6 ∨ n = 7)
    (α : T0 n ≃* T0 n) (u : T0 n) (X V : Set (T0 n))
    (hx : α (x0T n) ≠ x0T n) (hu : α u = u) (hsq : ∀ t, α (α t) = u * t * u⁻¹)
    (hext : n = 7 →
      ∃ β : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)) ≃* ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n)),
        ∀ (t : T0 n) (ht : (t : Amb n) ∈ Hgrp n ((α (x0T n) : T0 n) : Amb n)),
          ((β ⟨(t : Amb n), ht⟩ : ↥(Hgrp n ((α (x0T n) : T0 n) : Amb n))) : Amb n) =
            ((α t : T0 n) : Amb n))
    (hX : x0T n ∈ X) (hV : x0T n * α (x0T n) ∈ V) (hdisj : Disjoint X V)
    (hclX : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ X → t ∈ X)
    (hclV : ∀ s t : T0 n, orderOf s = 2 →
      ((∃ g ∈ Fgrp n, g * (s : Amb n) * g⁻¹ = (t : Amb n)) ∨ t = α s) → s ∈ V → t ∈ V)
    (hQ : ∀ q : T0 n, (q : Amb n).1 = 1 → q ≠ 1 → q ∉ V) :
    ∀ q : T0 n, (q : Amb n).1 = 1 → ((α q : T0 n) : Amb n).2 = 1 := by
  have hvB : (mkTab n).validB = true := by
    rcases hn with rfl | rfl
    · exact validB6
    · exact validB7
  have hcB : (mkTab n).claimPosB = true := by
    rcases hn with rfl | rfl
    · exact claimPosB6
    · exact claimPosB7
  exact fin_pos_data n hn (mkTab n) (Tab.valid_of_validB _ hvB) hcB α u X V hx hu hsq hext hX hV
    hdisj hclX hclV hQ

end CFSG.GH74.GLS.C3.Layer2.Model
