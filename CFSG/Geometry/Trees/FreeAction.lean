module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.GroupTheory.FreeGroup.ResiduallyP

public section

namespace CFSG.Geometry.Trees

noncomputable section

open SimpleGraph

universe u v

variable {F : Type u} [Group F] {V : Type v} {T : SimpleGraph V} [MulAction F V]

private def orbitSet (Y : Finset V) : Set V :=
  {v | ∃ f : F, ∃ y ∈ Y, f • y = v}

private lemma mem_orbitSet {Y : Finset V} {v : V} :
    v ∈ orbitSet (F := F) Y ↔ ∃ f : F, ∃ y ∈ Y, f • y = v := Iff.rfl

private def SameOrbit (v w : V) : Prop :=
  (Quotient.mk'' v : MulAction.orbitRel.Quotient F V) = Quotient.mk'' w

private lemma sameOrbit_iff_orbitRel {v w : V} :
    SameOrbit (F := F) v w ↔ MulAction.orbitRel F V v w := Quotient.eq''

private lemma sameOrbit_comm {v w : V} : SameOrbit (F := F) v w ↔ SameOrbit (F := F) w v :=
  eq_comm

private structure IsRepSet (Y : Finset V) : Prop where
  eq_of_mem_orbit : ∀ ⦃y z : V⦄, y ∈ Y → z ∈ Y → SameOrbit (F := F) y z → y = z
  connected : ∀ u ∈ Y, ∀ v ∈ Y, ∃ p : T.Walk u v, ∀ w ∈ p.support, w ∈ (Y : Set V)

private def Covers (Y : Finset V) : Prop :=
  ∀ v : V, ∃ y ∈ Y, SameOrbit (F := F) v y

private structure IsTreeOfReps (Y : Finset V) : Prop extends IsRepSet (F := F) (T := T) Y where
  covers : Covers (F := F) Y

private lemma IsTreeOfReps.nonempty {Y : Finset V} (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hV : Nonempty V) : Y.Nonempty := by
  obtain ⟨y, hy, -⟩ := hY.covers (Classical.choice hV)
  exact ⟨y, hy⟩

private lemma eq_one_of_smul_mem_treeOfReps {Y : Finset V} (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    {f : F} {y z : V} (hy : y ∈ Y) (hz : z ∈ Y) (h : f • y = z) : f = 1 := by
  have horb : SameOrbit (F := F) y z := by
    rw [sameOrbit_iff_orbitRel]
    exact MulAction.mem_orbit_iff.mpr ⟨f⁻¹, by rw [← h, inv_smul_smul]⟩
  have hyz : y = z := hY.eq_of_mem_orbit hy hz horb
  exact hfree f y (by simpa [hyz] using h)

private def MeetsOrbit (Y : Finset V) (q : MulAction.orbitRel.Quotient F V) : Prop :=
  ∃ y ∈ Y, (Quotient.mk'' y : MulAction.orbitRel.Quotient F V) = q

private lemma exists_treeOfReps_extension {Y : Finset V} [DecidableEq V] (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsRepSet (F := F) (T := T) Y) (hYne : Y.Nonempty)
    (hnot : ∃ q : MulAction.orbitRel.Quotient F V,
      ¬ MeetsOrbit (F := F) Y q) :
    ∃ z : V, z ∉ Y ∧ IsRepSet (F := F) (T := T) (insert z Y) ∧
      (insert z Y).card = Y.card + 1 := by
  classical
  obtain ⟨q, hq⟩ := hnot
  let b : V := q.out
  have hbq : (Quotient.mk'' b : MulAction.orbitRel.Quotient F V) = q := Quotient.out_eq' q
  have hbA : b ∉ orbitSet (F := F) Y := by
    intro hb
    obtain ⟨f, y, hy, hfy⟩ := mem_orbitSet.mp hb
    apply hq
    refine ⟨y, hy, ?_⟩
    have hyb : SameOrbit (F := F) y b := by
      rw [sameOrbit_iff_orbitRel]
      exact MulAction.mem_orbit_iff.mpr
        ⟨f⁻¹, by rw [← hfy, inv_smul_smul]⟩
    exact hyb.trans hbq
  obtain ⟨y0, hy0⟩ := hYne
  have hy0A : y0 ∈ orbitSet (F := F) Y :=
    mem_orbitSet.mpr ⟨1, y0, hy0, one_smul F y0⟩
  obtain ⟨p⟩ := hT.connected y0 b
  obtain ⟨d, -, hdA, hdB⟩ :=
    p.exists_boundary_dart (orbitSet (F := F) Y) hy0A hbA
  obtain ⟨f, y, hy, hfy⟩ := mem_orbitSet.mp hdA
  let z : V := f⁻¹ • d.snd
  have hzY : z ∉ Y := by
    intro hz
    apply hdB
    refine mem_orbitSet.mpr ⟨f, z, hz, ?_⟩
    simp only [z, smul_inv_smul]
  have hzNew : ∀ w ∈ Y, ¬ SameOrbit (F := F) w z := by
    intro w hw hwz
    apply hdB
    rw [sameOrbit_iff_orbitRel] at hwz
    obtain ⟨g, hgz⟩ := MulAction.mem_orbit_iff.mp hwz
    refine mem_orbitSet.mpr ⟨f * g⁻¹, w, hw, ?_⟩
    calc
      (f * g⁻¹) • w = f • (g⁻¹ • w) := mul_smul f g⁻¹ w
      _ = f • (g⁻¹ • (g • z)) := by rw [hgz]
      _ = f • z := by rw [inv_smul_smul]
      _ = d.snd := by simp only [z, smul_inv_smul]
  have hyz : T.Adj y z := by
    have := (hadj f⁻¹ d.fst d.snd).mpr d.adj
    simpa only [z, ← hfy, inv_smul_smul] using this
  refine ⟨z, hzY, ?_, Finset.card_insert_of_notMem hzY⟩
  refine ⟨?_, ?_⟩
  · intro a b ha hb hab
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact (hzNew b hb (sameOrbit_comm.mpr hab)).elim
    · rcases hb with rfl | hb
      · exact (hzNew a ha hab).elim
      · exact hY.eq_of_mem_orbit ha hb hab
  · intro u hu v hv
    rw [Finset.mem_insert] at hu hv
    rcases hu with rfl | hu
    · rcases hv with rfl | hv
      · exact ⟨SimpleGraph.Walk.nil, by simp⟩
      · obtain ⟨p, hp⟩ := hY.connected v hv y hy
        refine ⟨p.reverse.cons hyz.symm, ?_⟩
        intro w hw
        simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact Finset.mem_insert_self z Y
        · exact Finset.mem_insert_of_mem (hp w (by simpa using hw))
    · rcases hv with rfl | hv
      · obtain ⟨p, hp⟩ := hY.connected u hu y hy
        refine ⟨p.concat hyz, ?_⟩
        intro w hw
        simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · exact Finset.mem_insert_of_mem (hp w hw)
        · exact Finset.mem_insert_self z Y
      · obtain ⟨p, hp⟩ := hY.connected u hu v hv
        exact ⟨p, fun w hw => Finset.mem_insert_of_mem (hp w hw)⟩

private lemma card_le_card_orbits [Fintype (MulAction.orbitRel.Quotient F V)] {Y : Finset V}
    (hY : IsRepSet (F := F) (T := T) Y) :
    Y.card ≤ Fintype.card (MulAction.orbitRel.Quotient F V) := by
  classical
  let f : V → MulAction.orbitRel.Quotient F V := fun v => Quotient.mk'' v
  have hinj : Set.InjOn f (Y : Set V) := by
    intro y hy z hz h
    exact hY.eq_of_mem_orbit hy hz h
  calc
    Y.card = (Y.image f).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ Fintype.card (MulAction.orbitRel.Quotient F V) := Finset.card_le_univ _

private lemma card_lt_card_orbits_of_not_covers [Fintype (MulAction.orbitRel.Quotient F V)]
    {Y : Finset V} (hY : IsRepSet (F := F) (T := T) Y) (hnot : ¬ Covers (F := F) Y) :
    Y.card < Fintype.card (MulAction.orbitRel.Quotient F V) := by
  classical
  by_contra hlt
  have hle := card_le_card_orbits hY
  have hge : Fintype.card (MulAction.orbitRel.Quotient F V) ≤ Y.card := le_of_not_gt hlt
  have hcard : Y.card = Fintype.card (MulAction.orbitRel.Quotient F V) :=
    le_antisymm hle hge
  let f : V → MulAction.orbitRel.Quotient F V := fun v => Quotient.mk'' v
  have hinj : Set.InjOn f (Y : Set V) := by
    intro y hy z hz h
    exact hY.eq_of_mem_orbit hy hz h
  have himage : (Y.image f).card = Fintype.card (MulAction.orbitRel.Quotient F V) := by
    rw [Finset.card_image_of_injOn hinj, hcard]
  have heq : Y.image f = Finset.univ := by
    refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
    rw [Finset.card_univ, himage]
  apply hnot
  intro v
  have hv : f v ∈ Y.image f := by rw [heq]; exact Finset.mem_univ (f v)
  obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
  exact ⟨y, hy, hyv.symm⟩

private lemma exists_not_meetsOrbit_of_not_covers {Y : Finset V}
    (h : ¬ Covers (F := F) Y) :
    ∃ q : MulAction.orbitRel.Quotient F V, ¬ MeetsOrbit (F := F) Y q := by
  classical
  by_contra h'
  push Not at h'
  apply h
  intro v
  obtain ⟨y, hy, hyv⟩ := h' (Quotient.mk'' v)
  exact ⟨y, hy, hyv.symm⟩

private lemma exists_treeOfReps (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    [Finite (MulAction.orbitRel.Quotient F V)] :
    ∃ Y : Finset V, IsTreeOfReps (F := F) (T := T) Y := by
  classical
  haveI : Fintype (MulAction.orbitRel.Quotient F V) :=
    Fintype.ofFinite (MulAction.orbitRel.Quotient F V)
  let v0 : V := Classical.choice hT.connected.nonempty
  let Y0 : Finset V := {v0}
  have hY0 : IsRepSet (F := F) (T := T) Y0 := by
    refine ⟨?_, ?_⟩
    · intro y z hy hz _
      rw [Finset.mem_singleton] at hy hz
      rw [hy, hz]
    · intro u hu v hv
      rw [Finset.mem_singleton] at hu hv
      subst hu
      subst hv
      exact ⟨SimpleGraph.Walk.nil, by simp [Y0]⟩
  have hY0ne : Y0.Nonempty := ⟨v0, Finset.mem_singleton_self v0⟩
  let P : ℕ → Prop := fun k =>
    ∃ Y : Finset V, IsRepSet (F := F) (T := T) Y ∧ Y.card = k
  have hP1 : P 1 := ⟨Y0, hY0, by simp [Y0]⟩
  have hQne : Nonempty (MulAction.orbitRel.Quotient F V) :=
    ⟨Quotient.mk'' v0⟩
  have hN : 1 ≤ Fintype.card (MulAction.orbitRel.Quotient F V) :=
    Fintype.card_pos
  let m : ℕ := Nat.findGreatest P (Fintype.card (MulAction.orbitRel.Quotient F V))
  have hmP : P m :=
    Nat.findGreatest_spec (P := P) hN hP1
  obtain ⟨Y, hY, hYcard⟩ := hmP
  have hm_ge : 1 ≤ m := Nat.le_findGreatest hN hP1
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hcov : Covers (F := F) Y := by
    by_contra hnot
    obtain ⟨q, hq⟩ := exists_not_meetsOrbit_of_not_covers hnot
    obtain ⟨z, hzY, hY', hcard'⟩ :=
      exists_treeOfReps_extension hT hadj hY hYne ⟨q, hq⟩
    have hlt : Y.card < Fintype.card (MulAction.orbitRel.Quotient F V) :=
      card_lt_card_orbits_of_not_covers hY hnot
    have hle : m + 1 ≤ Fintype.card (MulAction.orbitRel.Quotient F V) := by
      rw [← hYcard]
      exact hlt
    have hPsucc : P (m + 1) := ⟨insert z Y, hY', by rw [hcard', hYcard]⟩
    exact (Nat.findGreatest_is_greatest (P := P)
      (n := Fintype.card (MulAction.orbitRel.Quotient F V))
      (Nat.lt_succ_self m) hle) hPsucc
  exact ⟨Y, ⟨hY, hcov⟩⟩

private def Gen (Y : Finset V) : Set F :=
  {s | s ≠ 1 ∧ ∃ y ∈ Y, ∃ y' ∈ Y, T.Adj y (s • y')}

private lemma inv_mem_gen {Y : Finset V}
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    {s : F} (hs : s ∈ Gen (F := F) (T := T) Y) :
    s⁻¹ ∈ Gen (F := F) (T := T) Y := by
  obtain ⟨hs1, y, hy, y', hy', hedge⟩ := hs
  refine ⟨inv_ne_one.mpr hs1, y', hy', y, hy, ?_⟩
  have h : T.Adj (s⁻¹ • y) (s⁻¹ • (s • y')) :=
    (hadj s⁻¹ y (s • y')).mpr hedge
  simpa only [inv_smul_smul] using h.symm

private lemma smul_mem_treeOfReps_notMem {Y : Finset V}
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    {s : F} (hs : s ≠ 1) {y : V} (hy : y ∈ Y) : s • y ∉ Y := by
  intro hsy
  exact hs (eq_one_of_smul_mem_treeOfReps hY hfree hy hsy rfl)

private def smulGraphHom
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b) (f : F) :
    T →g T where
  toFun v := f • v
  map_rel' := fun {_ _} h => (hadj f _ _).mpr h

private lemma unique_gen_edge {Y : Finset V} (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    {s : F} (hs : s ∈ Gen (F := F) (T := T) Y) :
    ∃! p : V × V, p.1 ∈ Y ∧ p.2 ∈ Y ∧ T.Adj p.1 (s • p.2) := by
  classical
  obtain ⟨hs1, y, hy, y', hy', hedge⟩ := hs
  refine ⟨(y, y'), ⟨hy, hy', hedge⟩, ?_⟩
  rintro ⟨z, z'⟩ ⟨hz, hz', hedge2⟩
  by_contra hne
  let e1 : Sym2 V := s(y, s • y')
  let e2 : Sym2 V := s(z, s • z')
  have he2ne : e2 ≠ e1 := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨rfl, h⟩ | ⟨hzy, hyz⟩
    · apply hne
      refine Prod.ext rfl ?_
      simpa only [inv_smul_smul] using congrArg (fun v => s⁻¹ • v) h
    · exact smul_mem_treeOfReps_notMem hY hfree hs1 hy' (hzy ▸ hz)
  have hbridge : T.IsBridge e1 := by
    simpa [e1] using
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hedge
  obtain ⟨p, hp⟩ := hY.connected y hy z hz
  have hp_avoid : e1 ∉ p.edges := by
    intro he
    have hsy : s • y' ∈ p.support :=
      SimpleGraph.Walk.snd_mem_support_of_mem_edges p (by simpa [e1] using he)
    exact smul_mem_treeOfReps_notMem hY hfree hs1 hy' (hp _ hsy)
  have hreach_yz : (T.deleteEdges {e1}).Reachable y z :=
    SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, hp_avoid⟩
  let φ : T →g T := smulGraphHom (F := F) (T := T) hadj s
  obtain ⟨q, hq⟩ := hY.connected z' hz' y' hy'
  let q' := q.map φ
  have hq_support : ∀ w ∈ q'.support, ∃ w0 ∈ Y, s • w0 = w := by
    intro w hw
    rw [show q' = q.map φ from rfl, SimpleGraph.Walk.support_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := List.mem_map.mp hw
    exact ⟨w0, hq w0 hw0, rfl⟩
  have hy_not_sY : ∀ w0 ∈ Y, s • w0 ≠ y := by
    intro w0 hw0 h
    exact smul_mem_treeOfReps_notMem hY hfree hs1 hw0 (by rw [h]; exact hy)
  have hq_avoid : e1 ∉ q'.edges := by
    intro he
    have hy_support : y ∈ q'.support :=
      SimpleGraph.Walk.fst_mem_support_of_mem_edges q' (by simpa [e1] using he)
    obtain ⟨w0, hw0, hw0y⟩ := hq_support y hy_support
    exact hy_not_sY w0 hw0 hw0y
  have hreach_sz_sy : (T.deleteEdges {e1}).Reachable (s • z') (s • y') := by
    have h : (T.deleteEdges {e1}).Reachable (φ z') (φ y') :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨q', hq_avoid⟩
    change (T.deleteEdges {e1}).Reachable (s • z') (s • y')
    exact h
  have he2del : (T.deleteEdges {e1}).Adj z (s • z') := by
    refine SimpleGraph.deleteEdges_adj.mpr ⟨hedge2, ?_⟩
    intro hmem
    exact he2ne (by simpa [e2] using hmem)
  have hreach : (T.deleteEdges {e1}).Reachable y (s • y') :=
    hreach_yz.trans (he2del.reachable.trans hreach_sz_sy)
  have hb' : T.IsBridge s(y, s • y') := by simpa [e1] using hbridge
  have hnot : ¬ (T.deleteEdges {e1}).Reachable y (s • y') :=
    (SimpleGraph.isBridge_iff (G := T) (u := y) (v := s • y')).mp hb'
  exact hnot hreach

private lemma inv_ne_self_of_mem_gen {Y : Finset V} (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    (hinv : ∀ (f : F) (a b : V), T.Adj a b → f • a = b → f • b ≠ a)
    {s : F} (hs : s ∈ Gen (F := F) (T := T) Y) : s⁻¹ ≠ s := by
  classical
  intro hs_inv
  have huniq := unique_gen_edge hT hadj hY hfree hs
  obtain ⟨hs1, y, hy, y', hy', hedge⟩ := hs
  have hs2 : s * s = 1 := by
    nth_rewrite 1 [← hs_inv]
    exact inv_mul_cancel s
  have hpair : (y, y') = (y', y) := by
    refine huniq.unique ⟨hy, hy', hedge⟩ ⟨hy', hy, ?_⟩
    have hmap : T.Adj (s • y) (s • (s • y')) := (hadj s y (s • y')).mpr hedge
    have hss : s • (s • y') = y' := by
      rw [← mul_smul, hs2, one_smul]
    simpa only [hss] using hmap.symm
  have hyy' : y' = y := by
    simpa using congrArg Prod.snd hpair
  have hedge' : T.Adj y (s • y) := by simpa [hyy'] using hedge
  refine (hinv s y (s • y) hedge' rfl) ?_
  rw [← mul_smul, hs2, one_smul]

private lemma walk_endpoint_mem_of_adj_closed {A : Set V}
    (hclosed : ∀ {v w : V}, v ∈ A → T.Adj v w → w ∈ A) :
    ∀ {u v : V}, u ∈ A → (p : T.Walk u v) → v ∈ A
  | _, _, hu, .nil => hu
  | _, _, hu, .cons h p => walk_endpoint_mem_of_adj_closed hclosed (hclosed hu h) p

private lemma closure_gen_eq_top {Y : Finset V} (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1) :
    Subgroup.closure (Gen (F := F) (T := T) Y) = ⊤ := by
  classical
  let H : Subgroup F := Subgroup.closure (Gen (F := F) (T := T) Y)
  let A : Set V := {v | ∃ h : H, ∃ y ∈ Y, (h : F) • y = v}
  have hAne : A.Nonempty := by
    obtain ⟨y0, hy0⟩ := hY.nonempty hT.connected.nonempty
    exact ⟨y0, 1, y0, hy0, one_smul F y0⟩
  have hclosed : ∀ {v w : V}, v ∈ A → T.Adj v w → w ∈ A := by
    intro v w hv hadjvw
    obtain ⟨h, y, hy, hhy⟩ := hv
    let u : V := (h : F)⁻¹ • w
    have hyu : T.Adj y u := by
      have hvadj : T.Adj ((h : F) • y) w := by rwa [hhy]
      have := (hadj (h : F)⁻¹ ((h : F) • y) w).mpr hvadj
      simpa only [u, inv_smul_smul] using this
    obtain ⟨y'', hy'', hy''u⟩ := hY.covers u
    rw [sameOrbit_iff_orbitRel] at hy''u
    obtain ⟨f, hf⟩ := MulAction.mem_orbit_iff.mp hy''u
    by_cases hf1 : f = 1
    · subst hf1
      refine ⟨h, y'', hy'', ?_⟩
      calc
        (h : F) • y'' = (h : F) • u := by rw [← hf, one_smul]
        _ = w := by simp only [u, smul_inv_smul]
    · have hfGen : f ∈ Gen (F := F) (T := T) Y := by
        refine ⟨hf1, y, hy, y'', hy'', ?_⟩
        rwa [hf]
      let h' : H := h * ⟨f, Subgroup.subset_closure hfGen⟩
      refine ⟨h', y'', hy'', ?_⟩
      calc
        (h' : F) • y'' = (h : F) • (f • y'') := mul_smul (h : F) f y''
        _ = (h : F) • u := by rw [hf]
        _ = w := by simp only [u, smul_inv_smul]
  have hAuniv : A = Set.univ := by
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨p⟩ := hT.connected (Classical.choose hAne) v
    exact walk_endpoint_mem_of_adj_closed hclosed (Classical.choose_spec hAne) p
  ext f
  constructor
  · intro _
    exact Subgroup.mem_top f
  · intro _
    obtain ⟨y0, hy0⟩ := hY.nonempty hT.connected.nonempty
    have hfyA : f • y0 ∈ A := by
      rw [hAuniv]
      exact Set.mem_univ (f • y0)
    obtain ⟨h, y, hy, hhy⟩ := hfyA
    have hyy0 : y = y0 := by
      have h1 : SameOrbit (F := F) y (f • y0) := by
        rw [sameOrbit_iff_orbitRel]
        exact MulAction.mem_orbit_iff.mpr
          ⟨(h : F)⁻¹, by rw [← hhy, inv_smul_smul]⟩
      have h2 : SameOrbit (F := F) (f • y0) y0 := by
        rw [sameOrbit_iff_orbitRel]
        exact MulAction.mem_orbit_iff.mpr ⟨f, rfl⟩
      exact hY.eq_of_mem_orbit hy hy0 (h1.trans h2)
    have hhy0 : (h : F) • y0 = f • y0 := by simpa only [hyy0] using hhy
    have hfix : (h : F)⁻¹ * f = 1 := by
      apply hfree
      calc
        ((h : F)⁻¹ * f) • y0 = (h : F)⁻¹ • (f • y0) := mul_smul (h : F)⁻¹ f y0
        _ = (h : F)⁻¹ • ((h : F) • y0) := by rw [hhy0]
        _ = y0 := inv_smul_smul (h : F) y0
    have hfh : (h : F) = f := inv_mul_eq_one.mp hfix
    rw [← hfh]
    exact h.property

private lemma reachable_smul_of_not_mem {s : F} {e : Sym2 V} {a b : V}
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (h : (T.deleteEdges {e}).Reachable a b) :
    (T.deleteEdges {Sym2.map (fun v => s • v) e}).Reachable (s • a) (s • b) := by
  classical
  obtain ⟨p⟩ := h
  have hinj : Function.Injective (fun v : V => s • v) := by
    intro x y hxy
    simpa only [inv_smul_smul] using congrArg (fun v => s⁻¹ • v) hxy
  let φ : T.deleteEdges {e} →g T.deleteEdges {Sym2.map (fun v => s • v) e} :=
    { toFun := fun v => s • v
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.deleteEdges_adj] at hxy ⊢
        refine ⟨(hadj s x y).mpr hxy.1, ?_⟩
        intro hmem
        have hmem' : Sym2.map (fun v => s • v) (s(x, y)) =
            Sym2.map (fun v => s • v) e := by simpa using hmem
        exact hxy.2 (by simpa using Sym2.map.injective hinj hmem') }
  exact ⟨p.map φ⟩

private lemma component_subset_of_internal_edge (hT : T.IsTree)
    {e : Sym2 V} {z a u v : V} (he : e = s(z, a)) (hza : T.Adj z a)
    {f : Sym2 V} (hf : f = s(u, v)) (huv : T.Adj u v) (hne : f ≠ e)
    (hzu_e : (T.deleteEdges {e}).Reachable z u)
    (hzu_f : (T.deleteEdges {f}).Reachable z u) :
    ∀ x : V, (T.deleteEdges {f}).Reachable v x → (T.deleteEdges {e}).Reachable z x := by
  classical
  have hbe : T.IsBridge e := by
    simpa [he] using (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hza
  have hbf : T.IsBridge f := by
    simpa [hf] using (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) huv
  have ha_not : ¬ (T.deleteEdges {e}).Reachable z a := by
    have hb' : T.IsBridge s(z, a) := by simpa [← he] using hbe
    simpa [← he] using
      (SimpleGraph.isBridge_iff (G := T) (u := z) (v := a)).mp hb' 
  let D : Set V := {x | (T.deleteEdges {e}).Reachable z x}
  have hzD : z ∈ D := SimpleGraph.Reachable.rfl
  have huD : u ∈ D := hzu_e
  have hnotuv : ¬ (T.deleteEdges {f}).Reachable u v := by
    have hb' : T.IsBridge s(u, v) := by simpa [← hf] using hbf
    simpa [← hf] using
      (SimpleGraph.isBridge_iff (G := T) (u := u) (v := v)).mp hb' 
  have hvD : v ∈ D := by
    have huv_e : (T.deleteEdges {e}).Adj u v := by
      refine SimpleGraph.deleteEdges_adj.mpr ⟨huv, ?_⟩
      intro hmem
      exact hne (hf.trans hmem)
    exact hzu_e.trans huv_e.reachable
  have hcross : ∀ {p q : V}, p ∈ D → q ∉ D → T.Adj p q → s(p, q) = e := by
    intro p q hp hq hpq
    by_contra hpqe
    apply hq
    exact hp.trans (SimpleGraph.deleteEdges_adj.mpr ⟨hpq, by simpa using hpqe⟩).reachable
  intro x hx
  by_contra hxD
  have hx' : (T.deleteEdges {s(u, v)}).Reachable v x := by simpa [hf] using hx
  rw [SimpleGraph.reachable_deleteEdges_iff_exists_walk] at hx'
  obtain ⟨Q, hQ⟩ := hx' 
  have hnotvx : ¬ (T.deleteEdges {e}).Reachable v x := by
    intro hvx
    exact hxD (hvD.trans hvx)
  obtain ⟨d, hd, hdD, hdnotD⟩ := Q.exists_boundary_dart D hvD hxD
  have hd_edge : d.edge = e := hcross hdD hdnotD d.adj
  have hd_fst : d.fst = z := by
    have hd_edge' : s(d.fst, d.snd) = s(z, a) := by
      simpa only [SimpleGraph.Dart.edge, he] using hd_edge
    rw [Sym2.eq_iff] at hd_edge'
    rcases hd_edge' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact (ha_not (h1 ▸ hdD)).elim
  have hsupp : z ∈ Q.support := by
    simpa only [hd_fst] using Q.dart_fst_mem_support_of_mem_darts hd
  have hvz_f : (T.deleteEdges {f}).Reachable v z := by
    have h : (T.deleteEdges {s(u, v)}).Reachable v z :=
      SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
        ⟨Q.takeUntil z hsupp, fun hef => hQ (Q.edges_takeUntil_subset_edges hsupp hef)⟩
    simpa [hf] using h
  exact hnotuv ((hvz_f.trans hzu_f).symm)

private lemma treeOfReps_reachable_of_gen_edge {Y : Finset V}
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    {s : F} (hs : s ∈ Gen (F := F) (T := T) Y) {a b : V} (ha : a ∈ Y) (hb : b ∈ Y)
    (hedge : T.Adj a (s • b)) {y : V} (hy : y ∈ Y) :
    (T.deleteEdges {s(a, s • b)}).Reachable a y := by
  classical
  obtain ⟨p, hp⟩ := hY.connected a ha y hy
  refine SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr ⟨p, ?_⟩
  intro he
  have hsb : s • b ∈ p.support :=
    SimpleGraph.Walk.snd_mem_support_of_mem_edges p (by simpa using he)
  exact smul_mem_treeOfReps_notMem hY hfree hs.1 hb (hp _ hsb)

private lemma smul_treeOfReps_reachable_of_gen_edge {Y : Finset V}
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    {s : F} (hs : s ∈ Gen (F := F) (T := T) Y) {a b : V} (ha : a ∈ Y) (hb : b ∈ Y)
    (hedge : T.Adj a (s • b)) {y1 y2 : V} (hy1 : y1 ∈ Y) (hy2 : y2 ∈ Y) :
    (T.deleteEdges {s(a, s • b)}).Reachable (s • y1) (s • y2) := by
  classical
  obtain ⟨p, hp⟩ := hY.connected y1 hy1 y2 hy2
  refine SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
    ⟨p.map (smulGraphHom (F := F) (T := T) hadj s), ?_⟩
  intro he
  have ha_support : a ∈ (p.map (smulGraphHom (F := F) (T := T) hadj s)).support :=
    SimpleGraph.Walk.fst_mem_support_of_mem_edges _ he
  rw [SimpleGraph.Walk.support_map] at ha_support
  obtain ⟨w, hw, hw_eq⟩ := List.mem_map.mp ha_support
  have hw_eq' : s • w = a := hw_eq
  exact smul_mem_treeOfReps_notMem hY hfree hs.1 (hp w hw)
    (by simpa only [← hw_eq'] using ha)

private def Reduced : List F → Prop
  | [] => True
  | [_] => True
  | a :: b :: l => b ≠ a⁻¹ ∧ Reduced (b :: l)

private lemma smul_treeOfReps_reachable_avoiding {Y : Finset V}
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    {s : F} {a z0 : V} (hz0 : z0 ∉ Y) {y1 y2 : V} (hy1 : y1 ∈ Y) (hy2 : y2 ∈ Y) :
    (T.deleteEdges {s(s • a, s • z0)}).Reachable (s • y1) (s • y2) := by
  classical
  obtain ⟨p, hp⟩ := hY.connected y1 hy1 y2 hy2
  refine SimpleGraph.reachable_deleteEdges_iff_exists_walk.mpr
    ⟨p.map (smulGraphHom (F := F) (T := T) hadj s), ?_⟩
  intro he
  have hz_support : s • z0 ∈
      (p.map (smulGraphHom (F := F) (T := T) hadj s)).support :=
    SimpleGraph.Walk.snd_mem_support_of_mem_edges _ he
  rw [SimpleGraph.Walk.support_map] at hz_support
  obtain ⟨w, hw, hw_eq⟩ := List.mem_map.mp hz_support
  have hw_eq' : s • w = s • z0 := hw_eq
  have hwz : w = z0 := by
    simpa only [inv_smul_smul] using congrArg (fun v => s⁻¹ • v) hw_eq'
  exact hz0 (hwz ▸ hp w hw)

private lemma reduced_word_far {Y : Finset V} (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    (w : List F) (hw : ∀ s ∈ w, s ∈ Gen (F := F) (T := T) Y)
    (hred : Reduced w) (hne : w ≠ []) :
    ∃ a b : V, a ∈ Y ∧ b ∈ Y ∧ T.Adj a (w.head hne • b) ∧
      ∀ y ∈ Y, (T.deleteEdges {s(a, w.head hne • b)}).Reachable
        (w.head hne • b) (w.prod • y) := by
  classical
  revert hw hred hne
  induction w with
  | nil =>
      intro _ _ hne
      exact (hne rfl).elim
  | cons s rest ih =>
      intro hw hred hne
      cases rest with
      | nil =>
          have hs : s ∈ Gen (F := F) (T := T) Y := hw s (by simp)
          have hs' : s ∈ Gen (F := F) (T := T) Y := hs
          obtain ⟨hs1, a, ha, b, hb, hedge⟩ := hs
          refine ⟨a, b, ha, hb, ?_, ?_⟩
          · simpa using hedge
          · intro y hy
            simpa using
              smul_treeOfReps_reachable_of_gen_edge hadj hY hfree hs' ha hb hedge hb hy
      | cons u t =>
          have hred_rest : Reduced (u :: t) := hred.2
          have hu_ne : u ≠ s⁻¹ := hred.1
          have hw_rest : ∀ v ∈ (u :: t), v ∈ Gen (F := F) (T := T) Y := by
            intro v hv
            simp only [List.mem_cons] at hv
            exact hw v (by simp only [List.mem_cons]; exact Or.inr hv)
          have hne_rest : (u :: t) ≠ [] := by simp
          obtain ⟨a_t, b_t, ha_t, hb_t, hedge_t, hfar_t⟩ :=
            ih hw_rest hred_rest hne_rest
          let u0 : F := (u :: t).head hne_rest
          have hhead : u0 = u := by simp [u0]
          have hu0_gen : u0 ∈ Gen (F := F) (T := T) Y :=
            hw_rest u0 (by simp [u0])
          have hz0 : u0 • b_t ∉ Y :=
            smul_mem_treeOfReps_notMem hY hfree hu0_gen.1 hb_t
          have hs_gen : s ∈ Gen (F := F) (T := T) Y := hw s (by simp)
          have hs_gen' : s ∈ Gen (F := F) (T := T) Y := hs_gen
          obtain ⟨hs1, a_s, ha_s, b_s, hb_s, hedge_s⟩ := hs_gen
          let vf : V := s • (u0 • b_t)
          let f : Sym2 V := s(s • a_t, vf)
          let e_s : Sym2 V := s(a_s, s • b_s)
          have huv : T.Adj (s • a_t) vf := by
            have h := (hadj s a_t (u0 • b_t)).mpr hedge_t
            simpa only [vf] using h
          have hsu_ne : s * u0 ≠ 1 := by
            intro h
            apply hu_ne
            have : u0 = s⁻¹ := (mul_eq_one_iff_eq_inv').mp h
            exact hhead.symm.trans this
          have hne_f : f ≠ e_s := by
            intro h
            rw [Sym2.eq_iff] at h
            rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
            · exact smul_mem_treeOfReps_notMem hY hfree hs_gen'.1 ha_t (h1 ▸ ha_s)
            · apply hsu_ne
              apply eq_one_of_smul_mem_treeOfReps hY hfree hb_t ha_s
              simpa only [vf, mul_smul] using h2
          have hzu_e : (T.deleteEdges {e_s}).Reachable (s • b_s) (s • a_t) := by
            have h := smul_treeOfReps_reachable_of_gen_edge hadj hY hfree hs_gen'
              ha_s hb_s hedge_s hb_s ha_t
            simpa only [e_s] using h
          have hzu_f : (T.deleteEdges {f}).Reachable (s • b_s) (s • a_t) := by
            have h := smul_treeOfReps_reachable_avoiding hadj hY (s := s) (a := a_t)
              (z0 := u0 • b_t) hz0 hb_s ha_t
            simpa only [f, vf] using h
          refine ⟨a_s, b_s, ha_s, hb_s, ?_, ?_⟩
          · simpa using hedge_s
          · intro y hy
            have hfar := hfar_t y hy
            have hfar_map : (T.deleteEdges {f}).Reachable vf
                (s • ((u :: t).prod • y)) := by
              have h := reachable_smul_of_not_mem (s := s)
                (e := s(a_t, (u :: t).head hne_rest • b_t)) hadj hfar
              simpa only [f, vf, Sym2.map_mk] using h
            have hnest := component_subset_of_internal_edge (T := T) hT
              (e := e_s) (z := s • b_s) (a := a_s) (u := s • a_t) (v := vf) (f := f)
              (by simpa only [e_s] using (Sym2.eq_swap (a := a_s) (b := s • b_s)))
              hedge_s.symm rfl huv hne_f hzu_e hzu_f
            have := hnest (s • ((u :: t).prod • y)) hfar_map
            change (T.deleteEdges {e_s}).Reachable (s • b_s) ((s :: u :: t).prod • y)
            simpa only [List.prod_cons, mul_smul] using this

private lemma reduced_word_prod_ne_one {Y : Finset V} (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    {w : List F} (hw : ∀ s ∈ w, s ∈ Gen (F := F) (T := T) Y)
    (hred : Reduced w) (hne : w ≠ []) : w.prod ≠ 1 := by
  classical
  intro hprod
  obtain ⟨a, b, ha, hb, hedge, hfar⟩ :=
    reduced_word_far hT hadj hY hfree w hw hred hne
  have hhead_gen : w.head hne ∈ Gen (F := F) (T := T) Y :=
    hw _ (List.head_mem hne)
  let e : Sym2 V := s(a, w.head hne • b)
  have hfar_b : (T.deleteEdges {e}).Reachable (w.head hne • b) b := by
    have := hfar b hb
    rw [hprod, one_smul] at this
    simpa only [e] using this
  have ha_b : (T.deleteEdges {e}).Reachable a b := by
    have := treeOfReps_reachable_of_gen_edge hY hfree hhead_gen ha hb hedge hb
    simpa only [e] using this
  have hbridge : T.IsBridge s(a, w.head hne • b) := by
    simpa only [e] using
      (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hT.isAcyclic) hedge
  have hnot : ¬ (T.deleteEdges {e}).Reachable a (w.head hne • b) := by
    have := (SimpleGraph.isBridge_iff (G := T) (u := a) (v := w.head hne • b)).mp hbridge
    simpa only [e] using this
  exact hnot (ha_b.trans hfar_b.symm)

private def ReducedSigned {α : Type u} : List (α × Bool) → Prop
  | [] => True
  | [_] => True
  | (a, b) :: (c, d) :: l => (a ≠ c ∨ b = d) ∧ ReducedSigned ((c, d) :: l)

private lemma reducedSigned_of_no_adjacent {α : Type u} :
    ∀ (L : List (α × Bool)),
      (∀ (L₂ : List (α × Bool)) (x : α) (b : Bool) (L₃ : List (α × Bool)),
        L ≠ L₂ ++ (x, b) :: (x, !b) :: L₃) → ReducedSigned L
  | [], _ => trivial
  | [_], _ => trivial
  | a :: c :: l, h => by
      refine ⟨?_, reducedSigned_of_no_adjacent (c :: l) fun L₂ x b L₃ hEq => ?_⟩
      · by_contra hcon
        push Not at hcon
        obtain ⟨hq, hb⟩ := hcon
        have hc : c = (a.1, !a.2) := by
          rcases a with ⟨q, b⟩
          rcases c with ⟨r, d⟩
          cases b <;> cases d <;> simp_all
        exact h [] a.1 a.2 l (by simp [hc])
      · exact h (a :: L₂) x b L₃ (by simpa [hEq])

private def signedToF {α : Type u} (toF : α → F) (L : List (α × Bool)) : List F :=
  L.map fun e => cond e.2 (toF e.1) (toF e.1)⁻¹

private lemma reduced_signedToF {α : Type u} {toF : α → F}
    (hinj : Function.Injective toF) (hne : ∀ a b : α, toF a ≠ (toF b)⁻¹)
    {L : List (α × Bool)} (hL : ReducedSigned L) : Reduced (signedToF toF L) := by
  induction L with
  | nil => trivial
  | cons a L ih =>
      cases L with
      | nil => trivial
      | cons c l =>
          obtain ⟨hac, hrest⟩ := hL
          refine ⟨?_, ih hrest⟩
          rcases a with ⟨q, b⟩
          rcases c with ⟨r, d⟩
          cases b <;> cases d <;>
            simp only [signedToF, List.map_cons, cond_true, cond_false, inv_inv] at hac ⊢
          · intro h
            exact hne r q (by simpa using congrArg Inv.inv h)
          · intro h
            exact (hac.resolve_right (by simp)) (hinj h).symm
          · intro h
            exact (hac.resolve_right (by simp)) (hinj (inv_inj.mp h)).symm
          · exact hne r q

private def InvRel (S : Set F) : S → S → Prop :=
  fun a b => (b : F) = (a : F) ∨ (b : F) = (a : F)⁻¹

private lemma invRel_equivalence (S : Set F) : Equivalence (InvRel S) where
  refl a := Or.inl rfl
  symm := by
    intro a b h
    rcases h with h | h
    · exact Or.inl h.symm
    · exact Or.inr (by rw [h, inv_inv])
  trans := by
    intro a b c hab hbc
    rcases hab with hab | hab <;> rcases hbc with hbc | hbc
    · exact Or.inl (hbc.trans hab)
    · exact Or.inr (by rw [hbc, hab])
    · exact Or.inr (by rw [hbc, hab])
    · exact Or.inl (by rw [hbc, hab, inv_inv])

private def invSetoid (S : Set F) : Setoid S :=
  ⟨InvRel S, invRel_equivalence S⟩

private abbrev InvQuot (S : Set F) : Type u := Quotient (invSetoid S)

private abbrev invRep (S : Set F) (q : InvQuot S) : F := (q.out : F)

private abbrev invClass (S : Set F) (s : S) : InvQuot S := Quotient.mk'' s

private lemma invRep_mem (S : Set F) (q : InvQuot S) : invRep S q ∈ S := by
  change (q.out : F) ∈ S
  exact q.out.property

private lemma invRep_mk_eq (S : Set F) (s : S) :
    invRep S (invClass S s) = (s : F) ∨ invRep S (invClass S s) = (s : F)⁻¹ := by
  have h := Quotient.eq''.mp (Quotient.out_eq' (invClass S s))
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h, inv_inv])

private lemma invRep_injective (S : Set F) : Function.Injective (invRep S) := by
  intro q q' h
  change (q.out : F) = (q'.out : F) at h
  have hs : (q.out : S) = q'.out := Subtype.ext h
  rw [← Quotient.out_eq' q, ← Quotient.out_eq' q']
  exact congrArg (invClass S) hs

private lemma invRep_not_inv (S : Set F)
    (hne : ∀ s ∈ S, s⁻¹ ≠ s) {q q' : InvQuot S}
    (h : invRep S q = (invRep S q')⁻¹) : False := by
  have hrel : InvRel S q'.out q.out :=
    Or.inr (by simpa only [invRep] using h)
  have hq : q' = q := by
    rw [← Quotient.out_eq' q', ← Quotient.out_eq' q]
    exact Quotient.sound hrel
  have heq : invRep S q = invRep S q' := by rw [hq]
  rw [heq] at h
  refine hne (invRep S q') (invRep_mem S q') ?_
  simpa only [invRep, heq] using h.symm

private lemma freeGroup_lift_invRep_injective {Y : Finset V} (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hY : IsTreeOfReps (F := F) (T := T) Y)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    (hinv : ∀ (f : F) (a b : V), T.Adj a b → f • a = b → f • b ≠ a)
    (hinvGen : ∀ s ∈ Gen (F := F) (T := T) Y, s⁻¹ ≠ s) :
    Function.Injective
      (FreeGroup.lift (fun q : InvQuot (Gen (F := F) (T := T) Y) =>
        invRep (Gen (F := F) (T := T) Y) q)) := by
  classical
  let S := Gen (F := F) (T := T) Y
  let φ : FreeGroup (InvQuot S) →* F :=
    FreeGroup.lift (fun q => invRep S q)
  have hker : ∀ z : FreeGroup (InvQuot S), z ≠ 1 → φ z ≠ 1 := by
    intro z hz hφz
    let L : List (InvQuot S × Bool) := z.toWord
    have hLne : L ≠ [] := by
      intro h
      exact hz (FreeGroup.toWord_eq_nil_iff.mp h)
    have hno : ∀ (L₂ : List (InvQuot S × Bool)) (x : InvQuot S) (b : Bool)
        (L₃ : List (InvQuot S × Bool)), L ≠ L₂ ++ (x, b) :: (x, !b) :: L₃ := by
      intro L₂ x b L₃ hEq
      have hred : FreeGroup.reduce L = L := FreeGroup.reduce_toWord z
      exact FreeGroup.reduce.not (L₁ := L) (L₂ := L₂) (L₃ := L₃) (x := x) (b := b)
        (by rw [hred, hEq])
    have hredSigned : ReducedSigned L := reducedSigned_of_no_adjacent L hno
    have hred : Reduced (signedToF (toF := fun q => invRep S q) L) :=
      reduced_signedToF (invRep_injective S) (fun a b => invRep_not_inv S hinvGen) hredSigned
    have hall : ∀ s ∈ signedToF (toF := fun q => invRep S q) L, s ∈ S := by
      intro s hs
      rw [signedToF] at hs
      obtain ⟨e, -, rfl⟩ := List.mem_map.mp hs
      rcases e with ⟨q, b⟩
      cases b
      · exact inv_mem_gen hadj (invRep_mem S q)
      · exact invRep_mem S q
    have hmapNe : signedToF (toF := fun q => invRep S q) L ≠ [] := by
      intro h
      have hlen : L.length = 0 := by simpa [signedToF] using congrArg List.length h
      exact hLne (List.length_eq_zero_iff.mp hlen)
    have hprod : (signedToF (toF := fun q => invRep S q) L).prod = 1 := by
      rw [← FreeGroup.mk_toWord (x := z)] at hφz
      simpa [φ, FreeGroup.lift_mk, signedToF] using hφz
    exact reduced_word_prod_ne_one hT hadj hY hfree hall hred hmapNe hprod
  intro x y hxy
  by_contra hxy'
  have hne : x * y⁻¹ ≠ 1 := by
    intro h
    exact hxy' (mul_inv_eq_one.mp h)
  apply hker (x * y⁻¹) hne
  show φ (x * y⁻¹) = 1
  rw [map_mul, map_inv, hxy, mul_inv_cancel]

private lemma freeGroup_lift_invRep_surjective {Y : Finset V}
    (hgen : Subgroup.closure (Gen (F := F) (T := T) Y) = ⊤) :
    Function.Surjective
      (FreeGroup.lift (fun q : InvQuot (Gen (F := F) (T := T) Y) =>
        invRep (Gen (F := F) (T := T) Y) q)) := by
  classical
  let S := Gen (F := F) (T := T) Y
  let φ : FreeGroup (InvQuot S) →* F := FreeGroup.lift (fun q => invRep S q)
  have hle : Subgroup.closure S ≤ φ.range := by
    rw [Subgroup.closure_le]
    intro s hs
    let s' : S := ⟨s, hs⟩
    have hrep := invRep_mk_eq S s'
    rcases hrep with h | h
    · refine ⟨FreeGroup.of (invClass S s'), ?_⟩
      show φ (FreeGroup.of (invClass S s')) = s
      simpa only [φ, FreeGroup.lift_apply_of] using h
    · refine ⟨(FreeGroup.of (invClass S s'))⁻¹, ?_⟩
      show φ ((FreeGroup.of (invClass S s'))⁻¹) = s
      rw [map_inv, show φ (FreeGroup.of (invClass S s')) = invRep S (invClass S s') by
        simp only [φ, FreeGroup.lift_apply_of], h, inv_inv]
  have htop : (⊤ : Subgroup F) ≤ φ.range := by
    rw [← hgen]
    exact hle
  exact (MonoidHom.range_eq_top).mp (le_antisymm le_top htop)

theorem isFreeGroup_of_free_action (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    (hinv : ∀ (f : F) (a b : V), T.Adj a b → f • a = b → f • b ≠ a)
    [Finite (MulAction.orbitRel.Quotient F V)] : IsFreeGroup F := by
  classical
  obtain ⟨Y, hY⟩ := exists_treeOfReps (F := F) (T := T) hT hadj
  let S := Gen (F := F) (T := T) Y
  let φ : FreeGroup (InvQuot S) →* F := FreeGroup.lift (fun q => invRep S q)
  have hgen : Subgroup.closure S = ⊤ := closure_gen_eq_top hT hadj hY hfree
  have hinvGen : ∀ s ∈ S, s⁻¹ ≠ s :=
    fun s hs => inv_ne_self_of_mem_gen hT hadj hY hfree hinv hs
  have hbij : Function.Bijective φ :=
    ⟨freeGroup_lift_invRep_injective hT hadj hY hfree hinv hinvGen,
      freeGroup_lift_invRep_surjective hgen⟩
  exact (FreeGroupBasis.ofRepr (MulEquiv.ofBijective φ hbij).symm).isFreeGroup

theorem residuallyFinite_of_free_action (hT : T.IsTree)
    (hadj : ∀ (f : F) (a b : V), T.Adj (f • a) (f • b) ↔ T.Adj a b)
    (hfree : ∀ (f : F) (v : V), f • v = v → f = 1)
    (hinv : ∀ (f : F) (a b : V), T.Adj a b → f • a = b → f • b ≠ a)
    [Finite (MulAction.orbitRel.Quotient F V)] : Group.ResiduallyFinite F := by
  classical
  have hfreeGrp := isFreeGroup_of_free_action hT hadj hfree hinv
  obtain ⟨ι, ⟨b⟩⟩ := hfreeGrp.nonempty_basis
  letI : Group.ResiduallyFinite (FreeGroup ι) := FreeGroup.instResiduallyFinite
  rw [Group.residuallyFinite_iff_exists_finiteIndex]
  intro f hf
  have hfb : b.repr f ≠ 1 := by
    intro h
    exact hf (b.repr.injective (by simpa using h))
  obtain ⟨K, hK, hKb⟩ :=
    (Group.residuallyFinite_iff_exists_finiteIndex.mp inferInstance) (b.repr f) hfb
  refine ⟨K.comap b.repr.toMonoidHom, inferInstance, ?_⟩
  intro hmem
  exact hKb (by simpa using hmem)

theorem exists_normal_finiteIndex_le_of_residuallyFinite {G : Type*} [Group G]
    {F : Subgroup G} [F.FiniteIndex] [Group.ResiduallyFinite F]
    (R : Set G) (hR : R.Finite) (hRF : R ⊆ F) (h1 : (1 : G) ∉ R) :
    ∃ N : Subgroup G, N.Normal ∧ N.FiniteIndex ∧ N ≤ F ∧ ∀ r ∈ R, r ∉ N := by
  classical
  haveI : Finite R := hR.to_subtype
  have hex : ∀ r : R, ∃ H : Subgroup F, H.FiniteIndex ∧ (⟨(r : G), hRF r.2⟩ : F) ∉ H := by
    intro r
    have hr1 : (⟨(r : G), hRF r.2⟩ : F) ≠ 1 := by
      intro h
      apply h1
      have : (r : G) = 1 := by
        simpa using congrArg (fun x : F => (x : G)) h
      exact this ▸ r.2
    exact (Group.residuallyFinite_iff_exists_finiteIndex (G := F)).mp inferInstance
      ⟨(r : G), hRF r.2⟩ hr1
  let Hf : R → Subgroup F := fun r => Classical.choose (hex r)
  have hHf_fin : ∀ r : R, (Hf r).FiniteIndex := fun r =>
    (Classical.choose_spec (hex r)).1
  have hHf_not : ∀ r : R, (⟨(r : G), hRF r.2⟩ : F) ∉ Hf r := fun r =>
    (Classical.choose_spec (hex r)).2
  let N₀ : Subgroup F := ⨅ r : R, Hf r
  have hN₀_fin : N₀.FiniteIndex := Subgroup.finiteIndex_iInf fun r => hHf_fin r
  have hN₀_not : ∀ r : R, (⟨(r : G), hRF r.2⟩ : F) ∉ N₀ := by
    intro r hr
    exact hHf_not r (iInf_le Hf r hr)
  let N₁ : Subgroup G := N₀.map F.subtype
  have hN₁_le : N₁ ≤ F := Subgroup.map_subtype_le N₀
  have hN₁_rel : N₁.relIndex F ≠ 0 := by
    have hEq : N₁.relIndex F =
        (N₀.map F.subtype).relIndex ((⊤ : Subgroup F).map F.subtype) := by
      rw [show N₁ = N₀.map F.subtype from rfl, Subgroup.map_top, F.range_subtype]
    rw [hEq, Subgroup.relIndex_map_map_of_injective (f := F.subtype) N₀ ⊤
      F.subtype_injective, Subgroup.relIndex_top_right]
    exact hN₀_fin.index_ne_zero
  have hN₁_fin : N₁.FiniteIndex := by
    refine ⟨?_⟩
    have htop : N₁.relIndex (⊤ : Subgroup G) ≠ 0 :=
      Subgroup.relIndex_ne_zero_trans hN₁_rel (by
        simpa only [Subgroup.relIndex_top_right] using
          (inferInstance : F.FiniteIndex).index_ne_zero)
    simpa only [Subgroup.relIndex_top_right] using htop
  refine ⟨N₁.normalCore, Subgroup.normalCore_normal N₁, inferInstance, ?_, ?_⟩
  · exact (Subgroup.normalCore_le N₁).trans hN₁_le
  · intro r hrR hrN
    have hrN₁ : r ∈ N₁ := Subgroup.normalCore_le N₁ hrN
    rw [Subgroup.mem_map] at hrN₁
    obtain ⟨x, hxN₀, hxr⟩ := hrN₁
    have hx : x = (⟨(r : G), hRF hrR⟩ : F) := Subtype.ext (by simpa using hxr)
    exact hN₀_not ⟨r, hrR⟩ (by simpa [hx] using hxN₀)

end

end CFSG.Geometry.Trees
