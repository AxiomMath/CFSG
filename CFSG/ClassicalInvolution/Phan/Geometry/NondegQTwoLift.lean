module

public import CFSG.ClassicalInvolution.Phan.Geometry.NondegConnected
public import CFSG.ClassicalInvolution.Phan.Geometry.WalkLift
public import CFSG.Monster.B.GSide.HomotopyLocal

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary Module CFSG.Monster.B.Recog CFSG.Monster.B.GSide
open CFSG.ClassicalInvolution.Phan.Geometry SimpleGraph

variable {K : Type*} [Field K] {σ : K ≃+* K} {d : ℕ} {W : Submodule K (Fin d → K)}

@[expose] def ndPt (hd : 2 ≤ finrank K W) (p : ↥(nsPts σ W)) : NdVert σ W :=
  ⟨p.1, p.2.1, fun h => by
      have h1 := p.2.2.1
      rw [h, finrank_bot] at h1
      exact zero_ne_one h1,
    fun h => by
      have h1 := p.2.2.1
      rw [h] at h1
      omega,
    p.2.2.2⟩

@[expose] def ndLine (hd : 3 ≤ finrank K W) {p q : ↥(nsPts σ W)} (h : (collGraph σ W).Adj p q) :
    NdVert σ W :=
  ⟨p.1 ⊔ q.1, sup_le p.2.1 q.2.1, fun h' => by
      have h2 := finrank_sup_of_ne_pts p.2.2.1 q.2.2.1 h.1
      rw [h', finrank_bot] at h2
      omega,
    fun h' => by
      have h2 := finrank_sup_of_ne_pts p.2.2.1 q.2.2.1 h.1
      rw [h'] at h2
      omega,
    h.2⟩

theorem ndGraph_adj_ndPt_ndLine (hd : 3 ≤ finrank K W) {p q : ↥(nsPts σ W)}
    (h : (collGraph σ W).Adj p q) : (ndGraph σ W).Adj (ndPt (by omega) p) (ndLine hd h) := by
  refine Or.inl (lt_of_le_of_ne le_sup_left fun he => ?_)
  have h2 := finrank_sup_of_ne_pts p.2.2.1 q.2.2.1 h.1
  change p.1 = p.1 ⊔ q.1 at he
  rw [← he, p.2.2.1] at h2
  omega

theorem ndGraph_adj_ndLine_ndPt (hd : 3 ≤ finrank K W) {p q : ↥(nsPts σ W)}
    (h : (collGraph σ W).Adj p q) : (ndGraph σ W).Adj (ndLine hd h) (ndPt (by omega) q) := by
  refine Or.inr (lt_of_le_of_ne le_sup_right fun he => ?_)
  have h2 := finrank_sup_of_ne_pts p.2.2.1 q.2.2.1 h.1
  change q.1 = p.1 ⊔ q.1 at he
  rw [← he, q.2.2.1] at h2
  omega

@[expose] def ndExpand (hd : 3 ≤ finrank K W) {p q : ↥(nsPts σ W)}
    (h : (collGraph σ W).Adj p q) :
    (ndGraph σ W).Walk (ndPt (by omega) p) (ndPt (by omega) q) :=
  .cons (ndGraph_adj_ndPt_ndLine hd h) (.cons (ndGraph_adj_ndLine_ndPt hd h) .nil)

abbrev ndNull (hd : 3 ≤ finrank K W) : ∀ x : ↥(nsPts σ W), Set ((collGraph σ W).Walk x x) :=
  liftNull (ndPt (by omega)) (ndExpand hd)

theorem homotopic_ndExpand_append_symm (hd : 3 ≤ finrank K W) {p q : ↥(nsPts σ W)}
    (h : (collGraph σ W).Adj p q) :
    Homotopic ((ndExpand hd h).append (ndExpand hd h.symm)) .nil := by
  have hline : ndLine hd h.symm = ndLine hd h := by
    apply Subtype.ext
    exact sup_comm q.1 p.1
  refine homotopic_nil_of_forall_adj_or_eq (z := ndLine hd h) _ ?_
  intro x hx
  simp only [ndExpand, SimpleGraph.Walk.cons_append, SimpleGraph.Walk.nil_append,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (ndGraph_adj_ndPt_ndLine hd h)
  · exact Or.inl rfl
  · exact Or.inr (ndGraph_adj_ndLine_ndPt hd h).symm
  · exact Or.inl hline
  · exact Or.inr (ndGraph_adj_ndPt_ndLine hd h)

theorem ndHomotopic_nil_of_support_le {T u : NdVert σ W} (c : (ndGraph σ W).Walk u u)
    (hc : ∀ S ∈ c.support, S.1 ≤ T.1) : Homotopic c .nil := by
  refine CFSG.Monster.B.GSide.homotopic_nil_of_forall_adj_or_eq (z := T) c ?_
  intro S hS
  by_cases he : S = T
  · exact Or.inl he
  · exact Or.inr (Or.inl (lt_of_le_of_ne (hc S hS) (fun h => he (Subtype.ext h))))

theorem ndExpand_support_le (hd : 3 ≤ finrank K W) {T : Submodule K (Fin d → K)}
    {p q : ↥(nsPts σ W)} (c : (collGraph σ W).Walk p q)
    (hc : ∀ r ∈ c.support, r.1 ≤ T) :
    ∀ S ∈ (substituteWalk (ndPt (by omega)) (ndExpand hd) c).support, S.1 ≤ T := by
  induction c with
  | @nil p =>
    intro S hS
    simp only [substituteWalk_nil, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hS
    subst S
    exact hc p (by simp)
  | @cons p q r h c ih =>
    have hp : p.1 ≤ T := hc p (by simp)
    have hq : q.1 ≤ T := hc q (by simp)
    have ht : ∀ s ∈ c.support, s.1 ≤ T := fun s hs => hc s (by simp [hs])
    intro S hS
    simp only [substituteWalk_cons, Walk.mem_support_append_iff] at hS
    rcases hS with he | ht'
    · simp only [ndExpand, Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl
      · exact hp
      · exact sup_le hp hq
      · exact hq
    · exact ih ht S ht'

theorem triangulable_ndGraph_of_cycleTrivial (hσ : IsUnitaryInvolution σ)
    (hW : Nondeg σ W) (hd : 5 ≤ finrank K W)
    (h : CycleTrivial (ndNull (σ := σ) (W := W) (by omega))) : Triangulable (ndGraph σ W) := by
  classical
  let i : ↥(nsPts σ W) → NdVert σ W := ndPt (by omega)
  let r : NdVert σ W → ↥(nsPts σ W) := fun S =>
    ⟨Classical.choose (NdVert.exists_nsPts_le hσ S),
     (Classical.choose_spec (NdVert.exists_nsPts_le hσ S)).1⟩
  have r_le : ∀ S, (r S).1 ≤ S.1 := fun S =>
    (Classical.choose_spec (NdVert.exists_nsPts_le hσ S)).2
  let connector : ∀ S, (ndGraph σ W).Walk S (i (r S)) := fun S =>
    if he : S = i (r S) then (.nil : (ndGraph σ W).Walk S S).copy rfl he
    else .cons (Or.inr (lt_of_le_of_ne (r_le S) (fun e => he (Subtype.ext e.symm)))) .nil
  have connector_support : ∀ S {Y : Submodule K (Fin d → K)}, S.1 ≤ Y →
      ∀ U ∈ (connector S).support, U.1 ≤ Y := by
    intro S Y hSY U hU
    dsimp [connector] at hU
    split_ifs at hU with he
    · simp only [Walk.support_copy, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hU
      subst U
      exact hSY
    · change U ∈ [S, i (r S)] at hU
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hU
      rcases hU with rfl | rfl
      · exact hSY
      · exact (r_le S).trans hSY
  have find_Y : ∀ T : NdVert σ W, ∃ Y : Submodule K (Fin d → K),
      T.1 ≤ Y ∧ Y ≤ W ∧ Y ≠ W ∧ Nondeg σ Y ∧ finrank K Y = finrank K W - 1 := by
    intro T
    let C := W ⊓ perp σ T.1
    have hCnd : Nondeg σ C := Nondeg.inf_perp hσ hW T.2.2.2.2 T.2.1
    have hCne : C ≠ ⊥ := by
      intro hC
      have hdim : finrank K W = finrank K T.1 + finrank K C := by
        simpa only [C] using finrank_eq_add_finrank_inf_perp hσ T.2.2.2.2 T.2.1
      rw [hC, finrank_bot] at hdim
      have hlt : finrank K T.1 < finrank K W :=
        Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne T.2.1 T.2.2.2.1)
      omega
    obtain ⟨v, hvC, hv⟩ := exists_aniso_of_nondeg hσ hCnd hCne
    have hvW : v ∈ W := hvC.1
    have hvperp : v ∈ perp σ T.1 := hvC.2
    let Y := W ⊓ perp σ (K ∙ v)
    have hYnd : Nondeg σ Y := Nondeg.inf_perp_span_singleton hσ hvW hv hW
    have hYdim : finrank K Y = finrank K W - 1 := by
      have hthis : finrank K W = finrank K Y + 1 := by
        rw [show Y = W ⊓ perp σ (K ∙ v) from rfl]
        exact finrank_eq_inf_perp_add_one hσ hvW hv
      omega
    have hYleW : Y ≤ W := inf_le_left
    have hYneW : Y ≠ W := by
      intro hYW
      rw [hYW] at hYdim
      omega
    have hTY : T.1 ≤ Y := by
      refine le_inf T.2.1 ?_
      intro t ht
      have hvt : herm σ v t = 0 := hvperp t ht
      have htv : herm σ t v = 0 := (herm_eq_zero_iff hσ _ _).mp hvt
      exact mem_perp_span_singleton.mpr htv
    exact ⟨Y, hTY, hYleW, hYneW, hYnd, hYdim⟩
  have reduce_exists : ∀ {S T : NdVert σ W}, S.1 < T.1 →
      ∃ c : (collGraph σ W).Walk (r S) (r T), ∃ Y : NdVert σ W,
        T.1 ≤ Y.1 ∧ ∀ p ∈ c.support, p.1 ≤ Y.1 := by
    intro S T hST
    obtain ⟨Y, hTY, hYW, hYne, hYnd, hYdim⟩ := find_Y T
    have hYbot : Y ≠ ⊥ := by
      intro he
      rw [he, finrank_bot] at hYdim
      omega
    let a : ↥(nsPts σ Y) := ⟨(r S).1, (r_le S).trans ((le_of_lt hST).trans hTY), (r S).2.2⟩
    let b : ↥(nsPts σ Y) := ⟨(r T).1, (r_le T).trans hTY, (r T).2.2⟩
    obtain ⟨c⟩ := (collGraph_connected_of_four_le hσ hYnd (by omega)).1 a b
    let f : (collGraph σ Y) →g (collGraph σ W) :=
      ⟨fun p => ⟨p.1, p.2.1.trans hYW, p.2.2⟩, fun {_ _} hp => hp⟩
    refine ⟨c.map f, ⟨Y, hYW, hYbot, hYne, hYnd⟩, hTY, ?_⟩
    intro p hp
    rw [Walk.support_map] at hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
    exact q.2.1
  let reduce_aux : ∀ {S T : NdVert σ W}, S.1 < T.1 → (collGraph σ W).Walk (r S) (r T) :=
    fun {_ _} hST => Classical.choose (reduce_exists hST)
  have hedge_forward : ∀ {S T : NdVert σ W} (hST : S.1 < T.1),
      Homotopic ((connector S).append (substituteWalk i (ndExpand (by omega)) (reduce_aux hST)))
        ((Walk.cons (Or.inl hST) .nil).append (connector T)) := by
    intro S T hST
    obtain ⟨Y, hTY, hc⟩ := Classical.choose_spec (reduce_exists hST)
    have hSY : S.1 ≤ Y.1 := (le_of_lt hST).trans hTY
    apply homotopic_iff_append_reverse_nil.mpr
    apply ndHomotopic_nil_of_support_le (T := Y)
    intro U hU
    rcases (Walk.mem_support_append_iff _ _).mp hU with hp | hq
    · rcases (Walk.mem_support_append_iff _ _).mp hp with hs | hc'
      · exact connector_support S hSY U hs
      · exact ndExpand_support_le (by omega) (reduce_aux hST) hc U hc'
    · have hq' : U ∈ ((Walk.cons (Or.inl hST) .nil).append (connector T)).support := by
        simpa only [Walk.support_reverse, List.mem_reverse] using hq
      rcases (Walk.mem_support_append_iff _ _).mp hq' with he | ht
      · change U ∈ [S, T] at he
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl
        · exact hSY
        · exact hTY
      · exact connector_support T hTY U ht
  let reduce : ∀ {S T}, (ndGraph σ W).Adj S T → (collGraph σ W).Walk (r S) (r T) :=
    fun {S T} hST => if hlt : S.1 < T.1 then reduce_aux hlt
      else (reduce_aux (hST.resolve_left hlt)).reverse
  have hedge : ∀ {S T} (hST : (ndGraph σ W).Adj S T),
      Homotopic ((connector S).append (substituteWalk i (ndExpand (by omega)) (reduce hST)))
        ((Walk.cons hST .nil).append (connector T)) := by
    intro S T hST
    rcases hST with hlt | hgt
    · simpa only [reduce, dif_pos hlt] using hedge_forward hlt
    · have hn : ¬ S.1 < T.1 := not_lt_of_gt hgt
      have hr := substituteWalk_reverse_homotopic i (ndExpand (by omega))
        (homotopic_ndExpand_append_symm (by omega)) (reduce_aux hgt)
      have hr' := hr.append_left (connector S)
      have hb := homotopic_reverse_connector (hedge_forward hgt)
      apply Homotopic.trans (by simpa only [reduce, dif_neg hn] using hr')
      exact hb
  exact triangulable_of_cycleTrivial_liftNull i r (ndExpand (by omega)) reduce connector
    (homotopic_ndExpand_append_symm (by omega)) hedge h

end CFSG.ClassicalInvolution.Phan
