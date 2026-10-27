module

public import CFSG.GF2Type.SmithTypeE.E8.FactsCoord

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public section

namespace CFSG.GF2Type.SmithTypeE.E8.F

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.SeitzReduction
  CFSG.SeitzReduction.EPilot

@[expose] def quadPair {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop) [DecidablePred D]
    (P : ι → ι) (v : ι → ZMod 2) : ZMod 2 :=
  ∑ a, if D a ∧ a < P a then v a * v (P a) else 0

private theorem quadPair_aux_expand {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop)
    [DecidablePred D] (P : ι → ι) (v e : ι → ZMod 2) :
    quadPair D P (fun b => v b + e b)
      = quadPair D P v + quadPair D P e
        + ∑ a, if D a ∧ a < P a then v a * e (P a) + e a * v (P a) else 0 := by
  simp only [quadPair]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  try dsimp only
  split_ifs <;> ring

private theorem quadPair_aux_shift_zero {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop)
    [DecidablePred D] (P : ι → ι) (Sh : ι → ι → Prop) [DecidableRel Sh]
    (hsup : ∀ a, D a → ¬ ((∃ a', Sh a' a) ∧ (∃ a', Sh a' (P a))))
    (v : ι → ZMod 2) :
    quadPair D P (fun b => ∑ a, if Sh a b then v a else 0) = 0 := by
  simp only [quadPair]
  refine Finset.sum_eq_zero (fun a _ => ?_)
  by_cases hd : D a ∧ a < P a
  · have key := hsup a hd.1
    by_cases h1 : ∃ a', Sh a' a
    · have h2 : ¬ ∃ a', Sh a' (P a) := fun h2 => key ⟨h1, h2⟩
      have hz : (∑ x, if Sh x (P a) then v x else 0) = 0 :=
        Finset.sum_eq_zero (fun x _ => if_neg (show ¬ Sh x (P a) from fun hx => h2 ⟨x, hx⟩))
      rw [if_pos hd, hz, mul_zero]
    · have hz : (∑ x, if Sh x a then v x else 0) = 0 :=
        Finset.sum_eq_zero (fun x _ => if_neg (show ¬ Sh x a from fun hx => h1 ⟨x, hx⟩))
      rw [if_pos hd, hz, zero_mul]
  · rw [if_neg hd]

private theorem quadPair_aux_cross {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop)
    [DecidablePred D] (P : ι → ι) (hD : ∀ a, D a → D (P a)) (hPP : ∀ a, D a → P (P a) = a)
    (hPne : ∀ a, D a → P a ≠ a) (v e : ι → ZMod 2) :
    (∑ a, if D a ∧ a < P a then v a * e (P a) + e a * v (P a) else 0)
      = ∑ a, if D a then v a * e (P a) else 0 := by
  have hpt : ∀ a, (if D a ∧ a < P a then v a * e (P a) + e a * v (P a) else 0)
      = (if D a ∧ a < P a then (if D a then v a * e (P a) else 0) else 0)
        + (if D a ∧ a < P a then (if D (P a) then v (P a) * e (P (P a)) else 0) else 0) := by
    intro a
    by_cases h : D a ∧ a < P a
    · have hdp : D (P a) := hD a h.1
      simp only [if_pos h, if_pos h.1, if_pos hdp, hPP a h.1]
      ring
    · simp only [if_neg h, add_zero]
  have hsplit : ∀ a, (if D a then v a * e (P a) else 0)
      = (if D a ∧ a < P a then (if D a then v a * e (P a) else 0) else 0)
        + (if D a ∧ P a < a then (if D a then v a * e (P a) else 0) else 0) := by
    intro a
    by_cases hd : D a
    · rcases lt_or_gt_of_ne (hPne a hd) with hlt | hlt
      · have hn : ¬ (a < P a) := not_lt.mpr hlt.le
        rw [if_pos hd, if_neg (show ¬ (D a ∧ a < P a) from fun h => hn h.2),
          if_pos (show D a ∧ P a < a from ⟨hd, hlt⟩), zero_add]
      · have hn : ¬ (P a < a) := not_lt.mpr hlt.le
        rw [if_pos hd, if_pos (show D a ∧ a < P a from ⟨hd, hlt⟩),
          if_neg (show ¬ (D a ∧ P a < a) from fun h => hn h.2), add_zero]
    · rw [if_neg hd, if_neg (show ¬ (D a ∧ a < P a) from fun h => hd h.1),
        if_neg (show ¬ (D a ∧ P a < a) from fun h => hd h.1), add_zero]
  have hB1f : ∑ a ∈ Finset.univ.filter (fun a => D a ∧ a < P a),
        (if D (P a) then v (P a) * e (P (P a)) else 0)
      = ∑ b ∈ Finset.univ.filter (fun b => D b ∧ P b < b), (if D b then v b * e (P b) else 0) := by
    refine Finset.sum_nbij' P P ?_ ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      exact ⟨hD a ha.1, by rw [hPP a ha.1]; exact ha.2⟩
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      exact ⟨hD b hb.1, by rw [hPP b hb.1]; exact hb.2⟩
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact hPP a ha.1
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
      exact hPP b hb.1
    · intro a _
      rfl
  have hB1 : (∑ a, if D a ∧ a < P a then (if D (P a) then v (P a) * e (P (P a)) else 0) else 0)
      = ∑ b, if D b ∧ P b < b then (if D b then v b * e (P b) else 0) else 0 := by
    rw [Finset.sum_filter, Finset.sum_filter] at hB1f
    exact hB1f
  calc (∑ a, if D a ∧ a < P a then v a * e (P a) + e a * v (P a) else 0)
      = ∑ a, ((if D a ∧ a < P a then (if D a then v a * e (P a) else 0) else 0)
          + (if D a ∧ a < P a then (if D (P a) then v (P a) * e (P (P a)) else 0) else 0)) :=
        Finset.sum_congr rfl (fun a _ => hpt a)
    _ = (∑ a, if D a ∧ a < P a then (if D a then v a * e (P a) else 0) else 0)
          + ∑ b, if D b ∧ P b < b then (if D b then v b * e (P b) else 0) else 0 := by
        rw [Finset.sum_add_distrib, hB1]
    _ = ∑ a, (if D a then v a * e (P a) else 0) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun a _ => (hsplit a).symm)

private theorem quadPair_aux_T2 {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop)
    [DecidablePred D] (P : ι → ι) (Sh : ι → ι → Prop) [DecidableRel Sh]
    (hsym : ∀ a a', D a → Sh a' (P a) → D a' ∧ Sh a (P a'))
    (hirr : ∀ a, D a → ¬ Sh a (P a)) (v : ι → ZMod 2) :
    (∑ a, if D a then v a * (∑ a', if Sh a' (P a) then v a' else 0) else 0) = 0 := by
  have h1 : ∀ a, (if D a then v a * (∑ a', if Sh a' (P a) then v a' else 0) else 0)
      = ∑ a', if D a ∧ Sh a' (P a) then v a * v a' else 0 := by
    intro a
    by_cases hd : D a
    · rw [if_pos hd, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun a' _ => ?_)
      by_cases hs : Sh a' (P a)
      · rw [if_pos hs, if_pos (show D a ∧ Sh a' (P a) from ⟨hd, hs⟩)]
      · rw [if_neg hs, if_neg (show ¬ (D a ∧ Sh a' (P a)) from fun h => hs h.2), mul_zero]
    · rw [if_neg hd]
      symm
      refine Finset.sum_eq_zero (fun a' _ => ?_)
      rw [if_neg (show ¬ (D a ∧ Sh a' (P a)) from fun h => hd h.1)]
  have hz2 : ∀ x : ZMod 2, x + x = 0 := fun x => CharTwo.add_self_eq_zero x
  simp only [h1]
  rw [← Fintype.sum_prod_type']
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    by_cases hc : D p.1 ∧ Sh p.2 (P p.1)
    · obtain ⟨hA, hB⟩ := hsym p.1 p.2 hc.1 hc.2
      have hc' : D p.2 ∧ Sh p.1 (P p.2) := ⟨hA, hB⟩
      rw [if_pos hc, if_pos hc', mul_comm (v p.1) (v p.2)]
      exact hz2 _
    · have hc' : ¬ (D p.2 ∧ Sh p.1 (P p.2)) := fun h => hc (hsym p.2 p.1 h.1 h.2)
      rw [if_neg hc, if_neg hc', add_zero]
  · intro p _ hfp heq
    apply hfp
    have hp : p.2 = p.1 := congrArg Prod.fst heq
    by_cases hc : D p.1 ∧ Sh p.2 (P p.1)
    · exfalso
      rw [hp] at hc
      exact hirr p.1 hc.1 hc.2
    · rw [if_neg hc]
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact Prod.swap_swap p

theorem quadPair_add_shift {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop)
    [DecidablePred D] (P : ι → ι) (Sh : ι → ι → Prop) [DecidableRel Sh]
    (hD : ∀ a, D a → D (P a)) (hPP : ∀ a, D a → P (P a) = a) (hPne : ∀ a, D a → P a ≠ a)
    (hsym : ∀ a a', D a → Sh a' (P a) → D a' ∧ Sh a (P a'))
    (hirr : ∀ a, D a → ¬ Sh a (P a))
    (hsup : ∀ a, D a → ¬ ((∃ a', Sh a' a) ∧ (∃ a', Sh a' (P a))))
    (v : ι → ZMod 2) :
    quadPair D P (fun b => v b + ∑ a, if Sh a b then v a else 0) = quadPair D P v := by
  rw [quadPair_aux_expand D P v (fun b => ∑ a, if Sh a b then v a else 0),
    quadPair_aux_shift_zero D P Sh hsup v,
    quadPair_aux_cross D P hD hPP hPne v (fun b => ∑ a, if Sh a b then v a else 0),
    quadPair_aux_T2 D P Sh hsym hirr v, add_zero, add_zero]

noncomputable def opI (a : Fin e7Data.d) : Fin e7Data.d := e8fIdx (-e7Data.wt a)

theorem wt_opI (a : Fin e7Data.d) : e7Data.wt (opI a) = -e7Data.wt a := by
  unfold opI
  exact wt_idx (exists_op a)

theorem opI_opI (a : Fin e7Data.d) : opI (opI a) = a := by
  show e8fIdx (-e7Data.wt (opI a)) = a
  rw [wt_opI, neg_neg]
  exact idx_wt a

theorem opI_ne (a : Fin e7Data.d) : opI a ≠ a := by
  intro h
  have h1 := wt_opI a
  rw [h] at h1
  exact wt_ne_neg a h1

noncomputable def qf (v : Fin e7Data.d →₀ ZMod 2) : ZMod 2 :=
  quadPair (fun _ : Fin e7Data.d => True) opI (fun a => v a)

theorem opI_sym {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (a a' : Fin e7Data.d)
    (h : e7Data.wt a' ⬝ᵥ β = -1 ∧ e7Data.wt (opI a) = e7Data.wt a' + MinData.toWeight β) :
    e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt (opI a') = e7Data.wt a + MinData.toWeight β := by
  obtain ⟨h1, h2⟩ := h
  rw [wt_opI] at h2
  have hA : e7Data.wt a = -(e7Data.wt a' + MinData.toWeight β) := by
    rw [← h2, neg_neg]
  refine ⟨?_, ?_⟩
  · have e1 : e7Data.wt a ⬝ᵥ β = -(e7Data.wt a' ⬝ᵥ β + MinData.toWeight β ⬝ᵥ β) := by
      rw [hA, neg_dotProduct, add_dotProduct]
    have e2 := tw_dot_self hβ
    omega
  · rw [wt_opI, hA]
    abel

theorem opI_irr {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (a : Fin e7Data.d)
    (h : e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt (opI a) = e7Data.wt a + MinData.toWeight β) : False := by
  have h2 := h.2
  rw [wt_opI] at h2
  apply two_wt_ne hβ a
  calc e7Data.wt a + e7Data.wt a + MinData.toWeight β
      = -e7Data.wt a + e7Data.wt a := by rw [h2]; abel
    _ = 0 := by abel

theorem opI_supp {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (a : Fin e7Data.d)
    (h : (∃ p : Fin e7Data.d, e7Data.wt p ⬝ᵥ β = -1 ∧
        e7Data.wt a = e7Data.wt p + MinData.toWeight β) ∧
      (∃ q : Fin e7Data.d, e7Data.wt q ⬝ᵥ β = -1 ∧
        e7Data.wt (opI a) = e7Data.wt q + MinData.toWeight β)) : False := by
  obtain ⟨⟨p, hp1, hp2⟩, ⟨q, hq1, hq2⟩⟩ := h
  have h1 := wt_dot_shift hβ hp1 hp2
  have h2 := wt_dot_shift hβ hq1 hq2
  rw [wt_opI, neg_dotProduct] at h2
  omega

theorem qf_rho {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (v : Fin e7Data.d →₀ ZMod 2) :
    qf (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v) = qf v := by
  have hfun : (fun a : Fin e7Data.d => (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v) a) =
      (fun b : Fin e7Data.d => v b + ∑ a : Fin e7Data.d,
        if (e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt b = e7Data.wt a + MinData.toWeight β) then v a
        else 0) :=
    funext fun b => coord_rho hβ v b
  have key := quadPair_add_shift (fun _ : Fin e7Data.d => True) opI
    (fun a' b => e7Data.wt a' ⬝ᵥ β = -1 ∧ e7Data.wt b = e7Data.wt a' + MinData.toWeight β)
    (fun _ _ => trivial) (fun a _ => opI_opI a) (fun a _ => opI_ne a)
    (fun a a' _ h => ⟨trivial, opI_sym hβ a a' h⟩)
    (fun a _ h => opI_irr hβ a h) (fun a _ h => opI_supp hβ a h) (fun a => v a)
  unfold qf
  exact (congrArg (quadPair (fun _ : Fin e7Data.d => True) opI) hfun).trans key

noncomputable def starI (a : Fin e7Data.d) : Fin e7Data.d := e8fIdx (e8fTh - e7Data.wt a)

theorem wt_starI {a : Fin e7Data.d} (ha : e7Data.wt a ⬝ᵥ highRoot .E7 = 1) :
    e7Data.wt (starI a) = e8fTh - e7Data.wt a := by
  unfold starI
  exact wt_idx (star_exists a ha)

theorem dot_starI {a : Fin e7Data.d} (ha : e7Data.wt a ⬝ᵥ highRoot .E7 = 1) :
    e7Data.wt (starI a) ⬝ᵥ highRoot .E7 = 1 := by
  rw [wt_starI ha, sub_dotProduct, th_dot_th, ha] <;> norm_num

theorem starI_starI {a : Fin e7Data.d} (ha : e7Data.wt a ⬝ᵥ highRoot .E7 = 1) :
    starI (starI a) = a := by
  have h1 : e8fTh - e7Data.wt (starI a) = e7Data.wt a := by
    rw [wt_starI ha, sub_sub_cancel]
  calc starI (starI a) = e8fIdx (e8fTh - e7Data.wt (starI a)) := rfl
    _ = e8fIdx (e7Data.wt a) := by rw [h1]
    _ = a := idx_wt a

theorem starI_ne {a : Fin e7Data.d} (ha : e7Data.wt a ⬝ᵥ highRoot .E7 = 1) : starI a ≠ a := by
  intro h
  have h1 := wt_starI ha
  rw [h] at h1
  exact star_ne a ha h1

@[expose] def IsDSupp (v : Fin e7Data.d →₀ ZMod 2) : Prop :=
  ∀ b : Fin e7Data.d, e7Data.wt b ⬝ᵥ highRoot .E7 ≠ 1 → v b = 0

noncomputable def qD (v : Fin e7Data.d →₀ ZMod 2) : ZMod 2 :=
  quadPair (fun a : Fin e7Data.d => e7Data.wt a ⬝ᵥ highRoot .E7 = 1) starI (fun a => v a)

theorem qD_rho_siegel {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (h0 : e8fTh ⬝ᵥ β = 0)
    (v : Fin e7Data.d →₀ ZMod 2) :
    qD (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v) = qD v := by
  have hsym : ∀ a a' : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
      (e7Data.wt a' ⬝ᵥ β = -1 ∧ e7Data.wt (starI a) = e7Data.wt a' + MinData.toWeight β) →
      e7Data.wt a' ⬝ᵥ highRoot .E7 = 1 ∧
        (e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt (starI a') = e7Data.wt a + MinData.toWeight β) := by
    rintro a a' ha ⟨hk, hsh⟩
    have h1 : e7Data.wt a' + MinData.toWeight β = e8fTh - e7Data.wt a :=
      hsh.symm.trans (wt_starI ha)
    have e1 : e7Data.wt a' = e8fTh - e7Data.wt a - MinData.toWeight β := eq_sub_of_add_eq h1
    have hD' : e7Data.wt a' ⬝ᵥ highRoot .E7 = 1 := by
      rw [e1, sub_dotProduct, sub_dotProduct, th_dot_th, ha, tw_dot_th hβ, h0] <;> norm_num
    refine ⟨hD', ?_, ?_⟩
    · have h2 : (e7Data.wt a' + MinData.toWeight β) ⬝ᵥ β = (e8fTh - e7Data.wt a) ⬝ᵥ β := by
        rw [h1]
      rw [add_dotProduct, sub_dotProduct, hk, tw_dot_self hβ, h0] at h2
      omega
    · rw [wt_starI hD', e1]
      abel
  have hirr : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
      ¬ (e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt (starI a) = e7Data.wt a + MinData.toWeight β) := by
    rintro a ha ⟨-, hq⟩
    have h1 : e7Data.wt a + MinData.toWeight β = e8fTh - e7Data.wt a :=
      hq.symm.trans (wt_starI ha)
    apply siegel_irr hβ h0 a
    rw [add_assoc, h1]
    abel
  have hsup : ∀ a : Fin e7Data.d, e7Data.wt a ⬝ᵥ highRoot .E7 = 1 →
      ¬ ((∃ a' : Fin e7Data.d, e7Data.wt a' ⬝ᵥ β = -1 ∧
            e7Data.wt a = e7Data.wt a' + MinData.toWeight β) ∧
         (∃ a' : Fin e7Data.d, e7Data.wt a' ⬝ᵥ β = -1 ∧
            e7Data.wt (starI a) = e7Data.wt a' + MinData.toWeight β)) := by
    rintro a ha ⟨⟨a1, h1a1, h1a2⟩, ⟨a2, h2a1, h2a2⟩⟩
    have e_a : e7Data.wt a ⬝ᵥ β = 1 := wt_dot_shift hβ h1a1 h1a2
    have e_sa : e7Data.wt (starI a) ⬝ᵥ β = 1 := wt_dot_shift hβ h2a1 h2a2
    rw [wt_starI ha, sub_dotProduct, e_a, h0] at e_sa
    norm_num at e_sa
  have key := quadPair_add_shift (fun a : Fin e7Data.d => e7Data.wt a ⬝ᵥ highRoot .E7 = 1)
    starI
    (fun a' b : Fin e7Data.d => e7Data.wt a' ⬝ᵥ β = -1 ∧
      e7Data.wt b = e7Data.wt a' + MinData.toWeight β)
    (fun a ha => dot_starI ha) (fun a ha => starI_starI ha) (fun a ha => starI_ne ha)
    (fun a a' ha hsh => hsym a a' ha hsh) (fun a ha => hirr a ha) (fun a ha => hsup a ha)
    (fun a => v a)
  unfold qD
  refine Eq.trans ?_ key
  refine congrArg (quadPair (fun a : Fin e7Data.d => e7Data.wt a ⬝ᵥ highRoot .E7 = 1) starI) ?_
  funext b
  exact coord_rho hβ v b

theorem dsupp_rho_siegel {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (h0 : e8fTh ⬝ᵥ β = 0)
    {v : Fin e7Data.d →₀ ZMod 2} (hv : IsDSupp v) :
    IsDSupp (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v) := by
  intro b hb
  rw [coord_rho hβ v b]
  have hs : ∑ a : Fin e7Data.d, (if (e7Data.wt a ⬝ᵥ β = -1 ∧
      e7Data.wt b = e7Data.wt a + MinData.toWeight β) then v a else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases hab : e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt b = e7Data.wt a + MinData.toWeight β
    · rw [if_pos hab]
      refine hv a ?_
      intro h1
      have hwb : e7Data.wt b ⬝ᵥ highRoot .E7 = 1 := by
        rw [hab.2, add_dotProduct, tw_dot_th hβ, h0, add_zero, h1]
      exact hb hwb
    · rw [if_neg hab]
  rw [hs, hv b hb, add_zero]

theorem rho_triv {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) (h : 1 ≤ e8fTh ⬝ᵥ β)
    {v : Fin e7Data.d →₀ ZMod 2} (hv : IsDSupp v) :
    e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) v = v := by
  refine Finsupp.ext fun b => ?_
  rw [coord_rho hβ v b]
  have hs : ∑ a : Fin e7Data.d, (if (e7Data.wt a ⬝ᵥ β = -1 ∧
      e7Data.wt b = e7Data.wt a + MinData.toWeight β) then v a else 0) = 0 := by
    refine Finset.sum_eq_zero fun a _ => ?_
    by_cases hab : e7Data.wt a ⬝ᵥ β = -1 ∧ e7Data.wt b = e7Data.wt a + MinData.toWeight β
    · rw [if_pos hab]
      by_cases ha1 : e7Data.wt a ⬝ᵥ highRoot .E7 = 1
      · exact absurd hab.1 (triv hβ h a ha1)
      · exact hv a ha1
    · rw [if_neg hab]
  rw [hs, add_zero]

theorem qf_single (a : Fin e7Data.d) : qf (Finsupp.single a 1) = 0 := by
  unfold qf quadPair
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : b = a
  · rw [hb]
    simp [Finsupp.single_apply, (opI_ne a).symm]
  · simp [Finsupp.single_apply, Ne.symm hb]

theorem qD_single (a : Fin e7Data.d) : qD (Finsupp.single a 1) = 0 := by
  unfold qD quadPair
  apply Finset.sum_eq_zero
  intro b _
  by_cases hb : b = a
  · rw [hb]
    by_cases hD : e7Data.wt a ⬝ᵥ highRoot .E7 = 1
    · simp [Finsupp.single_apply, (starI_ne hD).symm, hD]
    · simp [hD]
  · simp [Finsupp.single_apply, Ne.symm hb]

theorem qf_posUnipotent {u : ↥(adjointGroup .E7 (ZMod 2))}
    (hu : (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2)) (v : Fin e7Data.d →₀ ZMod 2) :
    qf (e7Rep56 (ZMod 2) u v) = qf v := by
  refine posUnipotent_induction (P := fun g : ↥(adjointGroup .E7 (ZMod 2)) =>
      ∀ w : Fin e7Data.d →₀ ZMod 2, qf (e7Rep56 (ZMod 2) g w) = qf w) ?_ ?_ ?_ ?_ hu v
  · intro w
    rw [rep_one_apply]
  · intro g h hg hh w
    rw [rep_mul_apply, hg, hh]
  · intro g hg w
    have h := hg (e7Rep56 (ZMod 2) g⁻¹ w)
    rw [rep_inv_apply] at h
    exact h.symm
  · intro β hβ hpos w
    exact qf_rho hβ w

theorem posUnipotent_dsupp_qD {u : ↥(adjointGroup .E7 (ZMod 2))}
    (hu : (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2)) :
    (∀ v, IsDSupp (e7Rep56 (ZMod 2) u v) ↔ IsDSupp v) ∧
      (∀ v, IsDSupp v → qD (e7Rep56 (ZMod 2) u v) = qD v) := by
  refine posUnipotent_induction (P := fun g : ↥(adjointGroup .E7 (ZMod 2)) =>
      (∀ w, IsDSupp (e7Rep56 (ZMod 2) g w) ↔ IsDSupp w) ∧
        (∀ w, IsDSupp w → qD (e7Rep56 (ZMod 2) g w) = qD w)) ?_ ?_ ?_ ?_ hu
  · refine ⟨fun w => ?_, fun w _ => ?_⟩
    · rw [rep_one_apply]
    · rw [rep_one_apply]
  · intro g h hg hh
    obtain ⟨hg1, hg2⟩ := hg
    obtain ⟨hh1, hh2⟩ := hh
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · rw [rep_mul_apply]
      exact (hg1 (e7Rep56 (ZMod 2) h w)).trans (hh1 w)
    · rw [rep_mul_apply]
      exact (hg2 (e7Rep56 (ZMod 2) h w) ((hh1 w).mpr hw)).trans (hh2 w hw)
  · intro g hg
    obtain ⟨hg1, hg2⟩ := hg
    refine ⟨fun w => ?_, fun w hw => ?_⟩
    · have h := hg1 (e7Rep56 (ZMod 2) g⁻¹ w)
      rw [rep_inv_apply] at h
      exact h.symm
    · have h := hg1 (e7Rep56 (ZMod 2) g⁻¹ w)
      rw [rep_inv_apply] at h
      have h2 := hg2 (e7Rep56 (ZMod 2) g⁻¹ w) (h.mp hw)
      rw [rep_inv_apply] at h2
      exact h2.symm
  · intro β hβ hpos
    have hinv2 : ∀ w : Fin e7Data.d →₀ ZMod 2,
        e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2))
          (e7Rep56 (ZMod 2) (pinnedElt .E7 β (1 : ZMod 2)) w) = w := by
      intro w
      rw [← rep_mul_apply, pinnedElt_mul_self β, rep_one_apply]
    by_cases h0 : e8fTh ⬝ᵥ β = 0
    · refine ⟨fun w => ⟨fun hw => ?_, fun hw => dsupp_rho_siegel hβ h0 hw⟩,
        fun w _ => qD_rho_siegel hβ h0 w⟩
      have h' := dsupp_rho_siegel hβ h0 hw
      rw [hinv2 w] at h'
      exact h'
    · have hle : 1 ≤ e8fTh ⬝ᵥ β := by
        rcases th_cases hβ hpos with h | h | h
        · exact absurd h h0
        · omega
        · omega
      refine ⟨fun w => ⟨fun hw => ?_, fun hw => ?_⟩, fun w hw => ?_⟩
      · have e := rho_triv hβ hle hw
        rw [hinv2 w] at e
        rw [e]
        exact hw
      · rw [rho_triv hβ hle hw]
        exact hw
      · rw [rho_triv hβ hle hw]

theorem exists_posUnipotent_basis' {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) :
    ∃ u : ↥(adjointGroup .E7 (ZMod 2)),
      (u : ModGL .E7 (ZMod 2)) ∈ posUnipotent .E7 (ZMod 2) ∧
        ∃ a : Fin e7Data.d, w = e7Rep56 (ZMod 2) u (Finsupp.single a 1) := by
  obtain ⟨g, hg⟩ := hw
  exact exists_posUnipotent_basis ⟨g, hg.symm⟩

theorem qf_weightVec {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) : qf w = 0 := by
  obtain ⟨u, hu, a, rfl⟩ := exists_posUnipotent_basis' hw
  rw [qf_posUnipotent hu, qf_single]

theorem qD_weightVec {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec) (hD : IsDSupp w) :
    qD w = 0 := by
  obtain ⟨u, hu, a, rfl⟩ := exists_posUnipotent_basis' hw
  have hs : IsDSupp (Finsupp.single a 1) :=
    ((posUnipotent_dsupp_qD hu).1 (Finsupp.single a 1)).mp hD
  rw [(posUnipotent_dsupp_qD hu).2 (Finsupp.single a 1) hs, qD_single]

theorem grade_neg_three_eq_opI {b : Fin e7Data.d} (hb : e8fGrade b = -3) :
    b = opI ⟨0, by decide⟩ := by
  have h : e7Data.wt b = -e7Data.wt 0 := grade_eq_neg_three b hb
  exact (idx_wt b).symm.trans (congrArg e8fIdx h)

theorem qf_zero_add_single {b : Fin e7Data.d} (hb : e8fGrade b = -3) :
    qf (Finsupp.single ⟨0, by decide⟩ 1 + Finsupp.single b 1) = 1 := by
  have hbc : b = opI ⟨0, by decide⟩ := grade_neg_three_eq_opI hb
  subst hbc
  have hc0 : opI (⟨0, by decide⟩ : Fin e7Data.d) ≠ ⟨0, by decide⟩ := opI_ne _
  have hpos : (0 : ℕ) < (opI (⟨0, by decide⟩ : Fin e7Data.d)).val :=
    Nat.pos_of_ne_zero (fun h => hc0 (Fin.ext h))
  have hlt : (⟨0, by decide⟩ : Fin e7Data.d) < opI ⟨0, by decide⟩ := Fin.lt_def.mpr hpos
  have hnlt : ¬ opI (⟨0, by decide⟩ : Fin e7Data.d) < ⟨0, by decide⟩ :=
    fun h => Nat.not_lt_zero _ (Fin.lt_def.mp h)
  unfold qf quadPair
  rw [Finset.sum_eq_single (⟨0, by decide⟩ : Fin e7Data.d)]
  · simp [hlt, hc0, hc0.symm, Finsupp.add_apply, Finsupp.single_apply]
  · intro b _ hbz
    by_cases hbc : b = opI ⟨0, by decide⟩
    · subst hbc
      simp [opI_opI, hnlt]
    · simp [Finsupp.add_apply, Finsupp.single_apply, hbz, hbc, Ne.symm hbz, Ne.symm hbc]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem starI_zero : starI ⟨0, by decide⟩ = ⟨e8fMu, e8fMu_lt⟩ := by
  apply wt_injective
  exact (wt_starI (a := ⟨0, by decide⟩) wt_zero_th).trans wt_e8fMu.symm

theorem wt_mu_th : e7Data.wt (⟨e8fMu, e8fMu_lt⟩ : Fin e7Data.d) ⬝ᵥ highRoot .E7 = 1 := by
  rw [← starI_zero]
  exact dot_starI (a := ⟨0, by decide⟩) wt_zero_th

theorem isDSupp_zero_add_mu :
    IsDSupp (Finsupp.single ⟨0, by decide⟩ 1 + Finsupp.single ⟨e8fMu, e8fMu_lt⟩ 1) := by
  unfold IsDSupp
  intro b hb
  by_cases h0 : b = ⟨0, by decide⟩
  · subst h0
    exact absurd wt_zero_th hb
  · by_cases hμ : b = ⟨e8fMu, e8fMu_lt⟩
    · subst hμ
      exact absurd wt_mu_th hb
    · simp [Finsupp.add_apply, Finsupp.single_apply, h0, hμ, Ne.symm h0, Ne.symm hμ]

theorem qD_zero_add_mu :
    qD (Finsupp.single ⟨0, by decide⟩ 1 + Finsupp.single ⟨e8fMu, e8fMu_lt⟩ 1) = 1 := by
  have hD0 : e7Data.wt (⟨0, by decide⟩ : Fin e7Data.d) ⬝ᵥ highRoot .E7 = 1 := wt_zero_th
  have hμz : (⟨e8fMu, e8fMu_lt⟩ : Fin e7Data.d) ≠ ⟨0, by decide⟩ := by
    have h := starI_ne (a := ⟨0, by decide⟩) wt_zero_th
    rw [starI_zero] at h
    exact h
  have hμ0 : e8fMu ≠ 0 := fun h => hμz (Fin.ext h)
  have hpos : 0 < e8fMu := Nat.pos_of_ne_zero hμ0
  have hstar : starI (⟨e8fMu, e8fMu_lt⟩ : Fin e7Data.d) = ⟨0, by decide⟩ := by
    have h := starI_starI (a := ⟨0, by decide⟩) wt_zero_th
    rw [starI_zero] at h
    exact h
  have hlt : (⟨0, by decide⟩ : Fin e7Data.d) < ⟨e8fMu, e8fMu_lt⟩ := Fin.lt_def.mpr hpos
  have hnlt : ¬ (⟨e8fMu, e8fMu_lt⟩ : Fin e7Data.d) < ⟨0, by decide⟩ :=
    fun h => Nat.not_lt_zero _ (Fin.lt_def.mp h)
  unfold qD quadPair
  rw [Finset.sum_eq_single (⟨0, by decide⟩ : Fin e7Data.d)]
  · simp [hD0, starI_zero, hlt, hμz, hμz.symm, hμ0, hμ0.symm, Finsupp.add_apply,
      Finsupp.single_apply]
  · intro b _ hbz
    by_cases hbμ : b = ⟨e8fMu, e8fMu_lt⟩
    · subst hbμ
      simp [hstar, hnlt]
    · simp [Finsupp.add_apply, Finsupp.single_apply, hbz, hbμ, Ne.symm hbz, Ne.symm hbμ]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem foldr_fix_zero (l : List (Fin (Tag.rank .E7))) :
    (∀ i ∈ l, i ≠ e7n6) →
      l.foldr (fun i c => e7Data_valid.sRefl i c) ⟨0, by decide⟩ = ⟨0, by decide⟩ := by
  induction l with
  | nil => intro _; rfl
  | cons i l ih =>
    intro hl
    have h1 : ∀ j ∈ l, j ≠ e7n6 := fun j hj => hl j (by simp [hj])
    have h2 : i ≠ e7n6 := hl i (by simp)
    show e7Data_valid.sRefl i (l.foldr (fun i c => e7Data_valid.sRefl i c) ⟨0, by decide⟩) =
      ⟨0, by decide⟩
    rw [ih h1]
    exact (e7Data_weyl_zero i).2 h2

theorem exists_word_grade_neg_one {b : Fin e7Data.d} (hb : e8fGrade b = -1) :
    ∃ g : ↥(adjointGroup .E7 (ZMod 2)),
      e7Rep56 (ZMod 2) g (Finsupp.single ⟨0, by decide⟩ 1 + Finsupp.single b 1) =
        Finsupp.single ⟨0, by decide⟩ 1 + Finsupp.single ⟨e8fMu, e8fMu_lt⟩ 1 := by
  obtain ⟨l, hlJ, hl⟩ := reach_sound ((List.finRange (Tag.rank .E7)).take 6) b 16
    ⟨e8fMu, e8fMu_lt⟩ (reach_grade_neg_one b hb)
  have hT : ∀ i ∈ (List.finRange (Tag.rank .E7)).take 6, i ≠ e7n6 := by decide +kernel
  refine ⟨(l.map (nC .E7 (ZMod 2))).prod, ?_⟩
  rw [map_add, e7Rep56_prod_nC_single, e7Rep56_prod_nC_single,
    foldr_fix_zero l (fun i hi => hT i (hlJ i hi)), hl]

theorem exists_word_th {a a' : Fin e7Data.d} (ha : e7Data.wt a ⬝ᵥ highRoot .E7 = 1)
    (ha' : e7Data.wt a' ⬝ᵥ highRoot .E7 = 1) :
    ∃ l : List (Fin (Tag.rank .E7)), (∀ i ∈ l, i ≠ ⟨0, by decide⟩) ∧
      e7Rep56 (ZMod 2) ((l.map (nC .E7 (ZMod 2))).prod) (Finsupp.single a 1) =
        Finsupp.single a' 1 := by
  obtain ⟨l, hlJ, hl⟩ := reach_sound ((List.finRange (Tag.rank .E7)).drop 1) a 10 a'
    (reach_th a a' ha ha')
  have hT : ∀ i ∈ (List.finRange (Tag.rank .E7)).drop 1, i ≠ ⟨0, by decide⟩ := by
    decide +kernel
  refine ⟨l, fun i hi => hT i (hlJ i hi), ?_⟩
  rw [e7Rep56_prod_nC_single, hl]

theorem not_mem_add_grade_neg_three {b : Fin e7Data.d} (hb : e8fGrade b = -3) :
    (Finsupp.single (⟨0, by decide⟩ : Fin e7Data.d) 1 + Finsupp.single b 1 :
      Fin e7Data.d →₀ ZMod 2) ∉ weightVec := fun h => by
  have h0 := qf_weightVec h
  rw [qf_zero_add_single hb] at h0
  exact one_ne_zero h0

theorem not_mem_add_mu :
    (Finsupp.single (⟨0, by decide⟩ : Fin e7Data.d) 1 + Finsupp.single ⟨e8fMu, e8fMu_lt⟩ 1 :
      Fin e7Data.d →₀ ZMod 2) ∉ weightVec := fun h => by
  have h0 := qD_weightVec h isDSupp_zero_add_mu
  rw [qD_zero_add_mu] at h0
  exact one_ne_zero h0

theorem not_mem_add_grade_neg_one {b : Fin e7Data.d} (hb : e8fGrade b = -1) :
    (Finsupp.single (⟨0, by decide⟩ : Fin e7Data.d) 1 + Finsupp.single b 1 :
      Fin e7Data.d →₀ ZMod 2) ∉ weightVec := fun h => by
  obtain ⟨g, hg⟩ := exists_word_grade_neg_one hb
  exact not_mem_add_mu (hg ▸ rep_mem_weightVec h g)

theorem wt_ne_add_core {w : Fin e7Data.d →₀ ZMod 2} (hw : w ∈ weightVec)
    {w' : Fin e7Data.d →₀ ZMod 2} (hw' : w' ∈ weightVec) (h : w' ∉ collSpace w) :
    w + w' ∉ weightVec := by
  obtain ⟨g, b, hwg, hw'g⟩ := pair_normal_form_weights (hw.imp fun g h => h.symm)
    (hw'.imp fun g h => h.symm)
  subst hwg
  subst hw'g
  by_cases hb : 0 < wgrade b
  · exact absurd ((mem_collSpace_iff g _).2 (by rw [rep_inv_apply']; exact single_mem_W0 hb)) h
  · intro hs
    rw [← map_add] at hs
    have hs' := (rep_mem_weightVec_iff g).1 hs
    have hcases := grade_cases b
    rcases hcases with h3 | h1 | hm1 | hm3
    · exact hb (by change 0 < e8fGrade b; omega)
    · exact hb (by change 0 < e8fGrade b; omega)
    · exact not_mem_add_grade_neg_one hm1 hs'
    · exact not_mem_add_grade_neg_three hm3 hs'

theorem quadPair_add {ι : Type*} [Fintype ι] [LinearOrder ι] (D : ι → Prop) [DecidablePred D]
    (P : ι → ι) (hD : ∀ a, D a → D (P a)) (hPP : ∀ a, D a → P (P a) = a)
    (hPne : ∀ a, D a → P a ≠ a) (v e : ι → ZMod 2) :
    quadPair D P (fun b => v b + e b) =
      quadPair D P v + quadPair D P e + ∑ a, if D a then v a * e (P a) else 0 := by
  rw [quadPair_aux_expand, quadPair_aux_cross D P hD hPP hPne]

theorem opI_injective : Function.Injective opI := fun a b h =>
  (opI_opI a).symm.trans ((congrArg opI h).trans (opI_opI b))

noncomputable def ff (u v : Fin e7Data.d →₀ ZMod 2) : ZMod 2 := ∑ a, u a * v (opI a)

theorem qf_add (u v : Fin e7Data.d →₀ ZMod 2) : qf (u + v) = qf u + qf v + ff u v := by
  have h := quadPair_add (fun _ : Fin e7Data.d => True) opI (fun _ _ => trivial)
    (fun a _ => opI_opI a) (fun a _ => opI_ne a) (fun a => u a) (fun a => v a)
  have e : (∑ a : Fin e7Data.d, if (fun _ : Fin e7Data.d => True) a then u a * v (opI a) else 0) =
      ff u v := Finset.sum_congr rfl fun a _ => if_pos trivial
  rw [e] at h
  exact h

theorem ff_comm (u v : Fin e7Data.d →₀ ZMod 2) : ff u v = ff v u := by
  have h1 := qf_add u v
  have h2 := qf_add v u
  rw [add_comm v u, h1] at h2
  linear_combination h2

theorem ff_add_left (u u' v : Fin e7Data.d →₀ ZMod 2) : ff (u + u') v = ff u v + ff u' v := by
  unfold ff
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [Finsupp.add_apply, add_mul]

theorem ff_add_right (u v v' : Fin e7Data.d →₀ ZMod 2) : ff u (v + v') = ff u v + ff u v' := by
  rw [ff_comm u (v + v'), ff_add_left, ff_comm v u, ff_comm v' u]

theorem ff_smul_left (c : ZMod 2) (u v : Fin e7Data.d →₀ ZMod 2) : ff (c • u) v = c * ff u v := by
  unfold ff
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [Finsupp.smul_apply, smul_eq_mul, mul_assoc]

theorem ff_smul_right (c : ZMod 2) (u v : Fin e7Data.d →₀ ZMod 2) : ff u (c • v) = c * ff u v := by
  rw [ff_comm, ff_smul_left, ff_comm]

@[expose] noncomputable def ffForm : LinearMap.BilinForm (ZMod 2) (Fin e7Data.d →₀ ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) ff ff_add_left (fun c u v => ff_smul_left c u v) ff_add_right
    (fun c u v => ff_smul_right c u v)

theorem ff_single_single (a b : Fin e7Data.d) :
    ff (Finsupp.single a 1) (Finsupp.single b 1) = if b = opI a then 1 else 0 := by
  unfold ff
  rw [Finset.sum_eq_single a]
  · simp [Finsupp.single_apply]
  · intro x _ hx
    simp [Finsupp.single_apply, Ne.symm hx]
  · intro h
    exact absurd (Finset.mem_univ a) h

theorem ff_nondeg {u : Fin e7Data.d →₀ ZMod 2} (h : ∀ v, ff u v = 0) : u = 0 := by
  ext a
  have h1 := h (Finsupp.single (opI a) 1)
  unfold ff at h1
  rw [Finset.sum_eq_single a] at h1
  · simpa [Finsupp.single_apply] using h1
  · intro x _ hx
    have hne : opI a ≠ opI x := fun h' => hx (opI_injective h').symm
    simp [Finsupp.single_apply, hne]
  · intro h'
    exact absurd (Finset.mem_univ a) h'

theorem adjointGroup_induction {P : ↥(adjointGroup .E7 (ZMod 2)) → Prop}
    (h1 : P 1) (hmul : ∀ g h, P g → P h → P (g * h)) (hinv : ∀ g, P g → P g⁻¹)
    (hgen : ∀ β, IsRoot .E7 β → P (pinnedElt .E7 β (1 : ZMod 2)))
    (g : ↥(adjointGroup .E7 (ZMod 2))) : P g := by
  obtain ⟨H, hH⟩ : ∃ H : Subgroup ↥(adjointGroup .E7 (ZMod 2)), ∀ g, g ∈ H ↔ P g :=
    ⟨{ carrier := {g | P g}
       mul_mem' := fun {a b} ha hb => hmul a b ha hb
       one_mem' := h1
       inv_mem' := fun {a} ha => hinv a ha }, fun g => Iff.rfl⟩
  have hle : rootSpan .E7 (ZMod 2) {α | IsRoot .E7 α} ≤
      H.map (adjointGroup .E7 (ZMod 2)).subtype := by
    refine iSup₂_le fun β hβ => ?_
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    have hc : c = 0 ∨ c = 1 := by
      revert c
      decide
    rcases hc with rfl | rfl
    · rw [CFSG.Blueprint.Chevalley.pinnedX_zero]
      exact one_mem _
    · exact Subgroup.mem_map.2
        ⟨pinnedElt .E7 β (1 : ZMod 2),
          (hH (pinnedElt .E7 β (1 : ZMod 2))).2 (hgen β hβ), rfl⟩
  have hg : (g : ModGL .E7 (ZMod 2)) ∈ rootSpan .E7 (ZMod 2) {α | IsRoot .E7 α} := by
    rw [← adjointGroup_eq_rootSpan]
    exact g.2
  obtain ⟨g', hg', hgg'⟩ := Subgroup.mem_map.1 (hle hg)
  have hgu' : g' = g := Subtype.ext hgg'
  rw [← hgu']
  exact (hH g').1 hg'

theorem qf_rep (g : ↥(adjointGroup .E7 (ZMod 2))) (v : Fin e7Data.d →₀ ZMod 2) :
    qf (e7Rep56 (ZMod 2) g v) = qf v := by
  refine adjointGroup_induction (P := fun g => ∀ w : Fin e7Data.d →₀ ZMod 2,
    qf (e7Rep56 (ZMod 2) g w) = qf w) ?_ ?_ ?_ ?_ g v
  · intro w
    rw [rep_one_apply]
  · intro g h hg hh w
    rw [rep_mul_apply, hg, hh]
  · intro g hg w
    have h := hg (e7Rep56 (ZMod 2) g⁻¹ w)
    rw [rep_inv_apply] at h
    exact h.symm
  · intro β hβ w
    exact qf_rho hβ w

theorem ff_rep (g : ↥(adjointGroup .E7 (ZMod 2))) (u v : Fin e7Data.d →₀ ZMod 2) :
    ff (e7Rep56 (ZMod 2) g u) (e7Rep56 (ZMod 2) g v) = ff u v := by
  have h1 := qf_add (e7Rep56 (ZMod 2) g u) (e7Rep56 (ZMod 2) g v)
  have h2 := qf_add u v
  rw [← map_add (e7Rep56 (ZMod 2) g) u v, qf_rep, qf_rep, qf_rep, h2] at h1
  exact (add_left_cancel h1).symm

end CFSG.GF2Type.SmithTypeE.E8.F
