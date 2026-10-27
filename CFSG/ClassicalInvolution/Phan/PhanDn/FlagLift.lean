module

public import CFSG.ClassicalInvolution.Phan.PhanDn.FlagGeom
public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.PhanDn.FlipflopPoints
public import CFSG.ClassicalInvolution.Phan.Geometry.WalkHomotopy
public import CFSG.Monster.B.Recog.GenericWalkHomotopy
import CFSG.Monster.B.Recog.GenericShortCycles
import CFSG.Monster.B.GSide.HomotopyLocal

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary
open CFSG.Monster.B.Recog CFSG.Monster.B.GSide

variable {K : Type} [Field K] {σ : K ≃+* K} {m : ℕ}

@[expose] def ptVert (hm : 3 ≤ m) (p : FlipPt σ (m + 1)) : FlagVert σ m :=
  ⟨p.1, p.2.isFlipflopSub, fun h => by
      have h1 := p.2.finrank_eq_one
      rw [h, finrank_bot] at h1
      omega,
    by rw [p.2.finrank_eq_one]; omega⟩

@[expose] def lineVert (hm : 3 ≤ m) {p p' : FlipPt σ (m + 1)}
    (h : (flipGraph σ (m + 1)).Adj p p') : FlagVert σ m :=
  have hc : p.1 ≠ p'.1 ∧ IsFlipflopSub σ (p.1 ⊔ p'.1) := h
  ⟨p.1 ⊔ p'.1, hc.2, fun hb => by
      have h2 := (FlipColl.isFlipLine (p := p.1) (p' := p'.1) h p.2 p'.2).2
      rw [hb, finrank_bot] at h2
      omega,
    by rw [(FlipColl.isFlipLine (p := p.1) (p' := p'.1) h p.2 p'.2).2]; omega⟩

private theorem lineVert_symm (hm : 3 ≤ m) {p p' : FlipPt σ (m + 1)}
    (h : (flipGraph σ (m + 1)).Adj p p') : lineVert hm h.symm = lineVert hm h :=
  Subtype.ext (sup_comm _ _)

theorem ptVert_adj_lineVert (hm : 3 ≤ m) {p p' : FlipPt σ (m + 1)}
    (h : (flipGraph σ (m + 1)).Adj p p') : (flagGraph σ m).Adj (ptVert hm p) (lineVert hm h) := by
  have hlt : p.1 < p.1 ⊔ p'.1 :=
    Submodule.lt_of_le_of_finrank_lt_finrank le_sup_left (by
      rw [p.2.finrank_eq_one,
        (FlipColl.isFlipLine (p := p.1) (p' := p'.1) h p.2 p'.2).2]
      omega)
  exact Or.inl (show (ptVert hm p).1 < (lineVert hm h).1 from hlt)

theorem lineVert_adj_ptVert (hm : 3 ≤ m) {p p' : FlipPt σ (m + 1)}
    (h : (flipGraph σ (m + 1)).Adj p p') : (flagGraph σ m).Adj (lineVert hm h) (ptVert hm p') := by
  have hlt : p'.1 < p.1 ⊔ p'.1 :=
    Submodule.lt_of_le_of_finrank_lt_finrank le_sup_right (by
      rw [p'.2.finrank_eq_one,
        (FlipColl.isFlipLine (p := p.1) (p' := p'.1) h p.2 p'.2).2]
      omega)
  exact Or.inr (Or.inl (show (ptVert hm p').1 < (lineVert hm h).1 from hlt))

@[expose] def liftWalk (hm : 3 ≤ m) :
    ∀ {p q : FlipPt σ (m + 1)}, (flipGraph σ (m + 1)).Walk p q →
      (flagGraph σ m).Walk (ptVert hm p) (ptVert hm q)
  | _, _, .nil => .nil
  | _, _, .cons h w =>
    .cons (ptVert_adj_lineVert hm h) (.cons (lineVert_adj_ptVert hm h) (liftWalk hm w))

variable (σ) in
@[expose] def flagNullWalks (hm : 3 ≤ m) (x : FlipPt σ (m + 1)) :
    Set ((flipGraph σ (m + 1)).Walk x x) :=
  {c | CFSG.Monster.B.Recog.Homotopic (liftWalk hm c) .nil}

theorem liftWalk_append (hm : 3 ≤ m) {p q r : FlipPt σ (m + 1)}
    (w : (flipGraph σ (m + 1)).Walk p q) (w' : (flipGraph σ (m + 1)).Walk q r) :
    liftWalk hm (w.append w') = (liftWalk hm w).append (liftWalk hm w') := by
  induction w with
  | nil => rfl
  | cons h w ih => simp [liftWalk, ih]

private theorem cons_cons_eq_of_eq {V : Type} {G : SimpleGraph V} {u w z : V} {v v' : V}
    (a : G.Adj u v) (b : G.Adj v w) (a' : G.Adj u v') (b' : G.Adj v' w) (r : G.Walk w z)
    (h : v = v') : (SimpleGraph.Walk.cons a (SimpleGraph.Walk.cons b r) : G.Walk u z) =
      SimpleGraph.Walk.cons a' (SimpleGraph.Walk.cons b' r) := by
  subst h
  rfl

private theorem liftWalk_cons_nil_symm (hm : 3 ≤ m) {p p' : FlipPt σ (m + 1)}
    (h : (flipGraph σ (m + 1)).Adj p p') :
    liftWalk hm (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil) =
      SimpleGraph.Walk.cons (lineVert_adj_ptVert hm h).symm
        (SimpleGraph.Walk.cons (ptVert_adj_lineVert hm h).symm SimpleGraph.Walk.nil) := by
  rw [show liftWalk hm (SimpleGraph.Walk.cons h.symm SimpleGraph.Walk.nil) =
    SimpleGraph.Walk.cons (ptVert_adj_lineVert hm h.symm)
      (SimpleGraph.Walk.cons (lineVert_adj_ptVert hm h.symm) SimpleGraph.Walk.nil) from rfl]
  exact cons_cons_eq_of_eq (ptVert_adj_lineVert hm h.symm) (lineVert_adj_ptVert hm h.symm)
    (lineVert_adj_ptVert hm h).symm (ptVert_adj_lineVert hm h).symm SimpleGraph.Walk.nil
    (lineVert_symm hm h)

theorem liftWalk_reverse (hm : 3 ≤ m) {p q : FlipPt σ (m + 1)}
    (w : (flipGraph σ (m + 1)).Walk p q) : liftWalk hm w.reverse = (liftWalk hm w).reverse := by
  induction w with
  | nil => rfl
  | @cons p q r h w ih =>
      rw [SimpleGraph.Walk.reverse_cons, liftWalk_append, ih, liftWalk_cons_nil_symm]
      rw [show liftWalk hm (SimpleGraph.Walk.cons h w) =
        SimpleGraph.Walk.cons (ptVert_adj_lineVert hm h)
          (SimpleGraph.Walk.cons (lineVert_adj_ptVert hm h) (liftWalk hm w)) from rfl]
      rw [SimpleGraph.Walk.reverse_cons, SimpleGraph.Walk.reverse_cons]
      simpa using SimpleGraph.Walk.append_assoc (liftWalk hm w).reverse
        (SimpleGraph.Walk.cons (lineVert_adj_ptVert hm h).symm SimpleGraph.Walk.nil)
        (SimpleGraph.Walk.cons (ptVert_adj_lineVert hm h).symm SimpleGraph.Walk.nil)

theorem le_of_mem_support_liftWalk (hm : 3 ≤ m) {p q : FlipPt σ (m + 1)}
    (w : (flipGraph σ (m + 1)).Walk p q) {U : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hU : ∀ x ∈ w.support, x.1 ≤ U) {y : FlagVert σ m} (hy : y ∈ (liftWalk hm w).support) :
    y.1 ≤ U := by
  induction w with
  | nil =>
      simp only [liftWalk, SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      subst hy
      simpa [ptVert] using hU _ (SimpleGraph.Walk.start_mem_support _)
  | @cons p q r h w ih =>
      simp only [liftWalk, SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hU p List.mem_cons_self
      rcases hy with rfl | hy
      · exact sup_le (hU p List.mem_cons_self)
          (hU q (List.mem_cons_of_mem p (SimpleGraph.Walk.start_mem_support w)))
      · exact ih (fun x hx => hU x (List.mem_cons_of_mem p hx)) hy

theorem finrank_le_two_of_mem_support_liftWalk (hm : 3 ≤ m) {p q : FlipPt σ (m + 1)}
    (w : (flipGraph σ (m + 1)).Walk p q) {y : FlagVert σ m}
    (hy : y ∈ (liftWalk hm w).support) : Module.finrank K y.1 ≤ 2 := by
  induction w with
  | nil =>
      simp only [liftWalk, SimpleGraph.Walk.support_nil, List.mem_singleton] at hy
      rename_i u
      subst hy
      have h := u.2.finrank_eq_one
      simp only [ptVert] at h ⊢
      exact h.le.trans (by norm_num)
  | @cons p q r h w ih =>
      simp only [liftWalk, SimpleGraph.Walk.support_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · have h := p.2.finrank_eq_one
        simp only [ptVert] at h ⊢
        exact h.le.trans (by norm_num)
      rcases hy with rfl | hy
      · have h := (FlipColl.isFlipLine (p := p.1) (p' := q.1) h p.2 q.2).2
        simp only [lineVert] at h ⊢
        exact le_of_eq h
      · exact ih hy

private theorem homotopic_cons_cons {V : Type} {G : SimpleGraph V} {x y z : V}
    (a : G.Adj x y) (b : G.Adj y x) (r : G.Walk x z) :
    CFSG.Monster.B.Recog.Homotopic (SimpleGraph.Walk.cons a (SimpleGraph.Walk.cons b r)) r := by
  have h := (homotopic_cons_cons_nil a).append_right r
  simpa using h

private theorem homotopic_cons_cons_cons_cons {V : Type} {G : SimpleGraph V} {u w z : V}
    {v v' : V} (a : G.Adj u v) (b : G.Adj v w) (c : G.Adj w v') (d : G.Adj v' u)
    (r : G.Walk u z) (hv : v' = v) :
    CFSG.Monster.B.Recog.Homotopic (SimpleGraph.Walk.cons a (SimpleGraph.Walk.cons b
      (SimpleGraph.Walk.cons c (SimpleGraph.Walk.cons d r)))) r := by
  subst hv
  exact (Homotopic.cons a (homotopic_cons_cons b c (SimpleGraph.Walk.cons d r))).trans
    (homotopic_cons_cons a d r)

theorem homotopic_liftWalk_of_cycleHomotopic (hm : 3 ≤ m) {p q : FlipPt σ (m + 1)}
    {w w' : (flipGraph σ (m + 1)).Walk p q} (h : CycleHomotopic (flagNullWalks σ hm) w w') :
    CFSG.Monster.B.Recog.Homotopic (liftWalk hm w) (liftWalk hm w') := by
  refine CycleHomotopic.induction h
    (R := fun w w' => CFSG.Monster.B.Recog.Homotopic (liftWalk hm w) (liftWalk hm w'))
    ?_ ?_ ?_ ?_
  · intro a b hab
    cases hab with
    | backtrack p q hy =>
        rw [liftWalk_append, liftWalk_append]
        have he : lineVert hm hy.symm = lineVert hm hy := lineVert_symm hm hy
        exact (homotopic_cons_cons_cons_cons (ptVert_adj_lineVert hm hy)
          (lineVert_adj_ptVert hm hy) (ptVert_adj_lineVert hm hy.symm)
          (lineVert_adj_ptVert hm hy.symm) (liftWalk hm q) he).symm.append_left (liftWalk hm p)
    | elem p q c hc =>
        rw [liftWalk_append, liftWalk_append]
        refine Homotopic.append_left (liftWalk hm p) ?_
        have h := ((show CFSG.Monster.B.Recog.Homotopic (liftWalk hm c) .nil from hc).append
          (Homotopic.refl (liftWalk hm q))).symm
        simpa [liftWalk_append] using h
  · intro a
    exact Homotopic.refl _
  · intro a b ih
    exact ih.symm
  · intro a b c ih₁ ih₂
    exact ih₁.trans ih₂

theorem solidWalks_subset_flagNullWalks (hm : 3 ≤ m) (x : FlipPt σ (m + 1)) :
    solidWalks σ (m + 1) x ⊆ flagNullWalks σ hm x := by
  intro c hc
  rw [mem_solidWalks_iff] at hc
  obtain ⟨M, hM, hsupp⟩ := hc
  let S : FlagVert σ m := ⟨M, hM.1, by
      rintro rfl
      have h := hM.2
      rw [finrank_bot] at h
      omega, by rw [hM.2]; omega⟩
  refine homotopic_nil_of_forall_adj_or_eq (z := S) (liftWalk hm c) ?_
  intro y hy
  have hyM : y.1 ≤ M := le_of_mem_support_liftWalk hm c hsupp hy
  by_cases hEq : y = S
  · exact Or.inl hEq
  · refine Or.inr (Or.inl ?_)
    exact lt_of_le_of_ne hyM (fun h => hEq (Subtype.ext h))

private theorem exists_walk_ptVert (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (U : FlagVert σ m) :
    ∃ p : FlipPt σ (m + 1), ∃ _w : (flagGraph σ m).Walk U (ptVert hm p), (ptVert hm p).1 ≤ U.1 := by
  obtain ⟨p, hp, hpU⟩ := IsFlipflopSub.exists_isFlipflopPt_le hσ U.2.1 U.2.2.1
  refine ⟨⟨p, hp⟩, ?_, hpU⟩
  by_cases h : p = U.1
  · exact SimpleGraph.Walk.nil.copy rfl (Subtype.ext h.symm)
  · exact SimpleGraph.Walk.cons (Or.inr (Or.inl (lt_of_le_of_ne hpU h)))
      SimpleGraph.Walk.nil

theorem connected_flagGraph (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (hconn : (flipGraph σ (m + 1)).Connected) : (flagGraph σ m).Connected := by
  have : Nonempty (FlagVert σ m) := hconn.nonempty.map (ptVert hm)
  refine ⟨fun U W => ?_⟩
  obtain ⟨p, wU, -⟩ := exists_walk_ptVert hσ hm U
  obtain ⟨q, wW, -⟩ := exists_walk_ptVert hσ hm W
  exact ⟨wU.append ((liftWalk hm (Classical.choice (hconn p q))).append wW.reverse)⟩

private noncomputable def flagBase (hconn : (flipGraph σ (m + 1)).Connected) :
    FlipPt σ (m + 1) :=
  Classical.choice hconn.nonempty

private noncomputable def flagPt (hσ : IsUnitaryInvolution σ) (x : FlagVert σ m) :
    FlipPt σ (m + 1) :=
  ⟨Classical.choose (IsFlipflopSub.exists_isFlipflopPt_le hσ x.2.1 x.2.2.1),
    (Classical.choose_spec (IsFlipflopSub.exists_isFlipflopPt_le hσ x.2.1 x.2.2.1)).1⟩

private theorem flagPt_le (hσ : IsUnitaryInvolution σ) (x : FlagVert σ m) :
    (flagPt hσ x).1 ≤ x.1 :=
  show (flagPt hσ x).1 ≤ x.1 from
    (Classical.choose_spec (IsFlipflopSub.exists_isFlipflopPt_le hσ x.2.1 x.2.2.1)).2

private noncomputable def flagDelta (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (x : FlagVert σ m) :
    (flagGraph σ m).Walk (ptVert hm (flagPt hσ x)) x :=
  if h : (flagPt hσ x).1 = x.1 then
    SimpleGraph.Walk.nil.copy rfl
      (show ptVert hm (flagPt hσ x) = x from Subtype.ext h)
  else
    SimpleGraph.Walk.cons
      (show (flagGraph σ m).Adj (ptVert hm (flagPt hσ x)) x from
        Or.inl (lt_of_le_of_ne (flagPt_le hσ x) h)) SimpleGraph.Walk.nil

private theorem flagDelta_length_le_one (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (x : FlagVert σ m) : (flagDelta hσ hm x).length ≤ 1 := by
  unfold flagDelta
  split_ifs with h
  · rw [SimpleGraph.Walk.length_copy]
    simp
  · simp

private theorem forall_mem_support_of_length_le_one {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.length ≤ 1) (P : V → Prop) (hu : P u) (hv : P v) :
    ∀ x ∈ p.support, P x := by
  cases p with
  | nil => simpa using hu
  | @cons u w v h q =>
      have hp' : q.length + 1 ≤ 1 := by simpa using hp
      have hq : q.length = 0 := by omega
      obtain rfl : w = v := SimpleGraph.Walk.eq_of_length_eq_zero hq
      have hqnil : q = .nil := SimpleGraph.Walk.eq_of_length_le_one (by omega) (by simp)
      intro x hx
      rw [hqnil] at hx
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact hu
      · exact hv

private theorem le_of_mem_support_flagDelta (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (x : FlagVert σ m) {M : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)} (hxM : x.1 ≤ M)
    {a : FlagVert σ m} (ha : a ∈ (flagDelta hσ hm x).support) : a.1 ≤ M :=
  forall_mem_support_of_length_le_one (flagDelta hσ hm x) (flagDelta_length_le_one hσ hm x)
    (fun a => a.1 ≤ M) (le_trans (flagPt_le hσ x) hxM) hxM a ha

private theorem exists_solid_le_flagVert (hσ : IsUnitaryInvolution σ)
    (U : FlagVert σ m) : ∃ M, IsSolid σ M ∧ U.1 ≤ M := by
  by_cases h : Module.finrank K U.1 = m + 1
  · exact ⟨U.1, ⟨U.2.1, h⟩, le_rfl⟩
  · obtain ⟨M, -, hM, -, hUM, -, -, -⟩ :=
      IsFlipflopSub.exists_solid_le hσ U.2.1 (by
        have hle := U.2.1.finrank_le
        omega)
    exact ⟨M, hM, hUM⟩

private theorem exists_homotopic_flagDelta_append_cons_reverse_of_le_solid
    (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m) {x y : FlagVert σ m}
    (e : (flagGraph σ m).Adj x y) {M : Submodule K (Fin (m + 1) ⊕ Fin (m + 1) → K)}
    (hM : IsSolid σ M) (hxM : x.1 ≤ M) (hyM : y.1 ≤ M) :
    ∃ c : (flipGraph σ (m + 1)).Walk (flagPt hσ x) (flagPt hσ y),
      Homotopic ((flagDelta hσ hm x).append (.cons e (flagDelta hσ hm y).reverse))
        (liftWalk hm c) := by
  obtain ⟨z, hz, hzM, hxz, hzy⟩ :=
    IsFlipflopSub.exists_flipColl_flipColl hσ hM.1 (by rw [hM.2]; omega)
      (flagPt hσ x).2 (flagPt hσ y).2 (le_trans (flagPt_le hσ x) hxM)
      (le_trans (flagPt_le hσ y) hyM)
  let c : (flipGraph σ (m + 1)).Walk (flagPt hσ x) (flagPt hσ y) :=
    .cons (show (flipGraph σ (m + 1)).Adj (flagPt hσ x) ⟨z, hz⟩ from hxz)
      (.cons (show (flipGraph σ (m + 1)).Adj ⟨z, hz⟩ (flagPt hσ y) from hzy) .nil)
  refine ⟨c, (homotopic_iff_append_reverse_nil).mpr ?_⟩
  have hsupp : ∀ a ∈ c.support, a.1 ≤ M := by
    intro a ha
    simp only [c, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact le_trans (flagPt_le hσ x) hxM
    · exact hzM
    · exact le_trans (flagPt_le hσ y) hyM
  let S : FlagVert σ m := ⟨M, hM.1, by
      rintro rfl
      have h := hM.2
      rw [finrank_bot] at h
      omega, by rw [hM.2]; omega⟩
  have hleft : ∀ a ∈ ((flagDelta hσ hm x).append
      (.cons e (flagDelta hσ hm y).reverse)).support, a.1 ≤ M := by
    intro a ha
    rw [SimpleGraph.Walk.mem_support_append_iff] at ha
    rcases ha with ha | ha
    · exact le_of_mem_support_flagDelta hσ hm x hxM ha
    · rw [SimpleGraph.Walk.support_cons, List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hxM
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ha
        exact le_of_mem_support_flagDelta hσ hm y hyM ha
  have hright : ∀ a ∈ (liftWalk hm c).support, a.1 ≤ M :=
    fun a ha => le_of_mem_support_liftWalk (U := M) hm c hsupp ha
  have hclosed : ∀ a ∈ (((flagDelta hσ hm x).append
      (.cons e (flagDelta hσ hm y).reverse)).append (liftWalk hm c).reverse).support,
      a = S ∨ (flagGraph σ m).Adj a S := by
    intro a ha
    rw [SimpleGraph.Walk.mem_support_append_iff] at ha
    have haM : a.1 ≤ M := by
      rcases ha with ha | ha
      · exact hleft a ha
      · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at ha
        exact hright a ha
    by_cases hEq : a = S
    · exact Or.inl hEq
    · refine Or.inr (Or.inl ?_)
      exact lt_of_le_of_ne haM (fun h => hEq (Subtype.ext h))
  exact homotopic_nil_of_forall_adj_or_eq (z := S) _ hclosed

private theorem exists_homotopic_flagDelta_append_cons_reverse_of_solids
    (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m) {x y : FlagVert σ m}
    (e : (flagGraph σ m).Adj x y) (hxfin : Module.finrank K x.1 = m + 1)
    (hyfin : Module.finrank K y.1 = m + 1)
    (hinf : Module.finrank K ↥(x.1 ⊓ y.1) = m) :
    ∃ c : (flipGraph σ (m + 1)).Walk (flagPt hσ x) (flagPt hσ y),
      Homotopic ((flagDelta hσ hm x).append (.cons e (flagDelta hσ hm y).reverse))
        (liftWalk hm c) := by
  have hxS : IsSolid σ x.1 := ⟨x.2.1, hxfin⟩
  have hyS : IsSolid σ y.1 := ⟨y.2.1, hyfin⟩
  obtain ⟨p₀, hp₀, hp₀le⟩ :=
    IsFlipflopSub.exists_isFlipflopPt_le_of_le hσ hxS.1 inf_le_left (by
      rw [hxfin, hinf]
      omega)
  let v : FlagVert σ m := ptVert hm ⟨p₀, hp₀⟩
  have hvx : v.1 ≤ x.1 := le_trans hp₀le inf_le_left
  have hvy : v.1 ≤ y.1 := le_trans hp₀le inf_le_right
  have hxv : (flagGraph σ m).Adj x v := by
    refine Or.inr (Or.inl (Submodule.lt_of_le_of_finrank_lt_finrank hvx ?_))
    have h1 : Module.finrank K v.1 = 1 := by
      simp only [v, ptVert]
      exact hp₀.finrank_eq_one
    rw [h1, hxfin]
    omega
  have hvy' : (flagGraph σ m).Adj v y := by
    refine Or.inl (Submodule.lt_of_le_of_finrank_lt_finrank hvy ?_)
    have h1 : Module.finrank K v.1 = 1 := by
      simp only [v, ptVert]
      exact hp₀.finrank_eq_one
    rw [h1, hyfin]
    omega
  obtain ⟨c0, hc0⟩ :=
    exists_homotopic_flagDelta_append_cons_reverse_of_le_solid hσ hm hxv hxS le_rfl hvx
  obtain ⟨c1, hc1⟩ :=
    exists_homotopic_flagDelta_append_cons_reverse_of_le_solid hσ hm hvy' hyS hvy le_rfl
  let dx := flagDelta hσ hm x
  let dv := flagDelta hσ hm v
  let dy := flagDelta hσ hm y
  let P : (flagGraph σ m).Walk x v := .cons hxv .nil
  let Q : (flagGraph σ m).Walk v (ptVert hm (flagPt hσ y)) := .cons hvy' dy.reverse
  have htri : Homotopic (dx.append (.cons e dy.reverse)) ((dx.append P).append Q) := by
    have h' : Homotopic (.cons e dy.reverse) (P.append Q) := by
      simpa [P, Q] using (homotopic_edge_triangle hxv hvy' e).append_right dy.reverse
    simpa [SimpleGraph.Walk.append_assoc] using h'.append_left dx
  have hloop : Homotopic Q ((dv.reverse.append dv).append Q) := by
    simpa using (homotopic_reverse_append dv).symm.append (Homotopic.refl Q)
  have hins : Homotopic ((dx.append P).append Q)
      ((dx.append P).append ((dv.reverse.append dv).append Q)) :=
    hloop.append_left (dx.append P)
  have h01 : Homotopic ((dx.append (P.append dv.reverse)).append (dv.append Q))
      ((liftWalk hm c0).append (liftWalk hm c1)) := hc0.append hc1
  have hassoc : ((dx.append P).append ((dv.reverse.append dv).append Q))
      = (dx.append (P.append dv.reverse)).append (dv.append Q) := by
    simp only [← SimpleGraph.Walk.append_assoc]
  refine ⟨c0.append c1, htri.trans (hins.trans ?_)⟩
  rw [hassoc, liftWalk_append]
  exact h01

private theorem exists_homotopic_flagDelta_append_cons_reverse
    (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m) {x y : FlagVert σ m}
    (e : (flagGraph σ m).Adj x y) :
    ∃ c : (flipGraph σ (m + 1)).Walk (flagPt hσ x) (flagPt hσ y),
      Homotopic ((flagDelta hσ hm x).append (.cons e (flagDelta hσ hm y).reverse))
        (liftWalk hm c) := by
  rcases e with hlt | hlt | ⟨hxfin, hyfin, hinf⟩
  · obtain ⟨M, hM, hyM⟩ := exists_solid_le_flagVert hσ y
    exact exists_homotopic_flagDelta_append_cons_reverse_of_le_solid hσ hm
      (Or.inl hlt) hM (le_trans hlt.le hyM) hyM
  · obtain ⟨M, hM, hxM⟩ := exists_solid_le_flagVert hσ x
    exact exists_homotopic_flagDelta_append_cons_reverse_of_le_solid hσ hm
      (Or.inr (Or.inl hlt)) hM hxM (le_trans hlt.le hxM)
  · exact exists_homotopic_flagDelta_append_cons_reverse_of_solids hσ hm
      (Or.inr (Or.inr ⟨hxfin, hyfin, hinf⟩)) hxfin hyfin hinf

private noncomputable def flagPi (hconn : (flipGraph σ (m + 1)).Connected)
    (p : FlipPt σ (m + 1)) : (flipGraph σ (m + 1)).Walk (flagBase hconn) p :=
  Classical.choice (hconn (flagBase hconn) p)

private noncomputable def flagGamma (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (hconn : (flipGraph σ (m + 1)).Connected) (x : FlagVert σ m) :
    (flagGraph σ m).Walk (ptVert hm (flagBase hconn)) x :=
  (liftWalk hm (flagPi hconn (flagPt hσ x))).append (flagDelta hσ hm x)

private theorem homotopic_lasso_flagGamma (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (hconn : (flipGraph σ (m + 1)).Connected) (htriv : CycleTrivial (flagNullWalks σ hm))
    {x y : FlagVert σ m} (e : (flagGraph σ m).Adj x y) :
    Homotopic (lasso (flagGamma hσ hm hconn) e) .nil := by
  obtain ⟨c, hc⟩ := exists_homotopic_flagDelta_append_cons_reverse hσ hm e
  have hlass : lasso (flagGamma hσ hm hconn) e =
      (liftWalk hm (flagPi hconn (flagPt hσ x))).append
        (((flagDelta hσ hm x).append (.cons e (flagDelta hσ hm y).reverse)).append
          (liftWalk hm (flagPi hconn (flagPt hσ y))).reverse) := by
    rw [lasso, flagGamma, flagGamma, SimpleGraph.Walk.reverse_append]
    let A := liftWalk hm (flagPi hconn (flagPt hσ x))
    let dx := flagDelta hσ hm x
    let C : (flagGraph σ m).Walk x (ptVert hm (flagPt hσ y)) :=
      .cons e (flagDelta hσ hm y).reverse
    let L := (liftWalk hm (flagPi hconn (flagPt hσ y))).reverse
    calc
      (A.append dx).append (C.append L) = ((A.append dx).append C).append L :=
        SimpleGraph.Walk.append_assoc _ _ _
      _ = (A.append (dx.append C)).append L :=
        congrArg (fun t => t.append L) (SimpleGraph.Walk.append_assoc A dx C).symm
      _ = A.append ((dx.append C).append L) :=
        (SimpleGraph.Walk.append_assoc A (dx.append C) L).symm
  have h1 : Homotopic (lasso (flagGamma hσ hm hconn) e)
      ((liftWalk hm (flagPi hconn (flagPt hσ x))).append
        ((liftWalk hm c).append (liftWalk hm (flagPi hconn (flagPt hσ y))).reverse)) := by
    rw [hlass]
    exact (hc.append_right (liftWalk hm (flagPi hconn (flagPt hσ y))).reverse).append_left
      (liftWalk hm (flagPi hconn (flagPt hσ x)))
  have h2 : Homotopic
      ((liftWalk hm (flagPi hconn (flagPt hσ x))).append
        ((liftWalk hm c).append (liftWalk hm (flagPi hconn (flagPt hσ y))).reverse))
      (liftWalk hm ((flagPi hconn (flagPt hσ x)).append
        (c.append (flagPi hconn (flagPt hσ y)).reverse))) := by
    rw [liftWalk_append, liftWalk_append, liftWalk_reverse]
  have h3 : Homotopic (liftWalk hm ((flagPi hconn (flagPt hσ x)).append
        (c.append (flagPi hconn (flagPt hσ y)).reverse))) .nil := by
    have h := homotopic_liftWalk_of_cycleHomotopic hm
      (htriv (flagBase hconn) ((flagPi hconn (flagPt hσ x)).append
        (c.append (flagPi hconn (flagPt hσ y)).reverse)))
    simpa [liftWalk] using h
  exact h1.trans (h2.trans h3)

theorem triangulable_flagGraph (hσ : IsUnitaryInvolution σ) (hm : 3 ≤ m)
    (hconn : (flipGraph σ (m + 1)).Connected) (htriv : CycleTrivial (flagNullWalks σ hm)) :
    CFSG.Monster.B.Recog.Triangulable (flagGraph σ m) := by
  intro u p
  let γ := flagGamma hσ hm hconn
  obtain ⟨L, hL, hp⟩ := homotopic_foldr_lasso γ p
  have hnull : Homotopic ((γ u).append (p.append (γ u).reverse)) .nil :=
    hp.trans (homotopic_walkProd_nil fun q hq => by
      obtain ⟨x, y, h, rfl⟩ := hL q hq
      exact homotopic_lasso_flagGamma hσ hm hconn htriv h)
  have h₁ : Homotopic p (((γ u).reverse.append (γ u)).append
      (p.append ((γ u).reverse.append (γ u)))) := by
    have := (homotopic_reverse_append (γ u)).symm.append
      ((homotopic_reverse_append (γ u)).symm.append_left p)
    rwa [SimpleGraph.Walk.append_nil, SimpleGraph.Walk.nil_append] at this
  have h₂ : Homotopic (((γ u).reverse.append (γ u)).append
      (p.append ((γ u).reverse.append (γ u))))
      ((γ u).reverse.append (γ u)) := by
    have := (hnull.append_right (γ u)).append_left (γ u).reverse
    simpa [SimpleGraph.Walk.append_assoc] using this
  exact h₁.trans (h₂.trans (homotopic_reverse_append (γ u)))

end CFSG.ClassicalInvolution.PhanDn
