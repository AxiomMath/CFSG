module

public import CFSG.GH74.BNPair.Statements
public import CFSG.GH74.BNPair.BuildingPoly
public import CFSG.GH74.BNPair.BuildingTrans

public section

namespace CFSG.GH74.BNPair

universe u

open scoped Pointwise

namespace RankTwoSystem

variable {X : Type u} [Group X] {n : ℕ} (D : RankTwoSystem X n)

open Classical in
theorem rank2 : Rank2 D.B D.N {D.w₁, D.w₂} D.w₁ D.w₂ n where
  tits := D.isTits
  gens := by simp
  dih :=
    { mul_self_a := D.isTits.mul_self_gen (by simp)
      mul_self_b := D.isTits.mul_self_gen (by simp)
      ne := D.w₁_ne_w₂
      closure_eq := by simpa using D.isTits.closure_eq
      card_eq := D.card_weyl
      three_le := D.three_le }

theorem isTypeOne_iff (v : D.Vertex) :
    D.IsTypeOne v ↔ vtype D.B D.N D.w₁ D.w₂ v = true := by
  constructor
  · rintro ⟨x, hx⟩
    have : v = vtx D.B D.N D.w₁ D.w₂ true x := Subtype.ext hx
    rw [this, D.rank2.vtype_vtx]
  · intro h
    obtain ⟨i, x, rfl⟩ := exists_vtx v
    rw [D.rank2.vtype_vtx] at h
    subst h
    exact ⟨x, rfl⟩

theorem isTypeTwo_iff (v : D.Vertex) :
    D.IsTypeTwo v ↔ vtype D.B D.N D.w₁ D.w₂ v = false := by
  constructor
  · rintro ⟨x, hx⟩
    have : v = vtx D.B D.N D.w₁ D.w₂ false x := Subtype.ext hx
    rw [this, D.rank2.vtype_vtx]
  · intro h
    obtain ⟨i, x, rfl⟩ := exists_vtx v
    rw [D.rank2.vtype_vtx] at h
    subst h
    exact ⟨x, rfl⟩

theorem polyHyp : PolyHyp D.graph n :=
  D.rank2.polyHyp

theorem lemma30_6_i : D.graph.Connected :=
  D.polyHyp.connected

theorem lemma30_6_iv : ∀ v : D.Vertex, 3 ≤ (D.graph.neighborSet v).encard :=
  D.polyHyp.valency

theorem lemma30_6_iii :
    (∀ a b a' b' : D.Vertex, D.graph.Adj a b → D.graph.Adj a' b' →
      ∃ g : X, (D.action g a = a' ∧ D.action g b = b') ∨ (D.action g a = b' ∧ D.action g b = a')) ∧
    (∀ v v' : D.Vertex, D.IsTypeOne v → D.IsTypeOne v' → ∃ g : X, D.action g v = v') ∧
    (∀ v v' : D.Vertex, D.IsTypeTwo v → D.IsTypeTwo v' → ∃ g : X, D.action g v = v') := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b a' b' h h'
    by_cases ht : vtype D.B D.N D.w₁ D.w₂ a = vtype D.B D.N D.w₁ D.w₂ a'
    · obtain ⟨g, hg1, hg2⟩ := D.rank2.exists_action_adj h h' ht
      exact ⟨g, Or.inl ⟨hg1, hg2⟩⟩
    · have h1 : vtype D.B D.N D.w₁ D.w₂ a = vtype D.B D.N D.w₁ D.w₂ b' := by
        have e := D.rank2.vtype_not_of_adj h'
        cases hx : vtype D.B D.N D.w₁ D.w₂ a <;> cases hy : vtype D.B D.N D.w₁ D.w₂ a' <;>
          simp_all
      obtain ⟨g, hg1, hg2⟩ := D.rank2.exists_action_adj h h'.symm h1
      exact ⟨g, Or.inr ⟨hg1, hg2⟩⟩
  · intro v v' hv hv'
    rw [isTypeOne_iff] at hv hv'
    exact D.rank2.exists_action_vtx (hv.trans hv'.symm)
  · intro v v' hv hv'
    rw [isTypeTwo_iff] at hv hv'
    exact D.rank2.exists_action_vtx (hv.trans hv'.symm)

end RankTwoSystem

@[expose] def Lemma30_6_ii : Prop :=
  ∀ (X : Type u) [Group X] (n : ℕ) (D : RankTwoSystem X n),
    D.graphMinusTop.IsTree ∧
      ∀ (i j : ℕ), ∀ v ∈ D.sideOne i, ∀ v' ∈ D.sideTwo j, ∀ l : List D.Vertex,
        IsGLSPath D.graph l → l.head? = some v → l.getLast? = some v' →
          (∃ a b : D.Vertex, [a, b] <:+: l ∧ (a : Set X) ∩ (b : Set X) ⊆ dc D.B D.N D.w₀) ∨
            (([D.vertex₁, D.vertex₂] <:+: l ∨ [D.vertex₂, D.vertex₁] <:+: l) ∧
              l.length = i + j + 2)

theorem lemma30_6_of_ii (h : Lemma30_6_ii.{u}) : Lemma30_6.{u} := by
  intro X _ n D
  obtain ⟨h1, h2⟩ := h X n D
  exact ⟨D.lemma30_6_i, ⟨h1, h2⟩, D.lemma30_6_iii, D.lemma30_6_iv⟩

theorem lemma30_7 : Lemma30_7.{u} := by
  intro X _ n D
  have h := D.polyHyp
  refine ⟨fun v v' => (h.reach_dist v v').2, fun v v' hd => h.exists_unique_path_of_dist_lt hd,
    ?_, fun v v' hd => h.exists_bijOn hd, ?_, ?_⟩
  · intro v v' hd v₁ hadj
    obtain ⟨l, hl, hh, hla, hlen, h1⟩ := h.exists_path_through hd hadj
    refine ⟨l, ⟨hl, hh, hla, hlen, h1⟩, ?_⟩
    rintro l' ⟨hl', hh', hla', hlen', h1'⟩
    exact h.path_through_unique hl' hl hh' hh hla' hla hlen' hlen h1' h1
  · intro v v' l hl hh hla hlen
    exact h.dist_eq_of_path hl hh hla hlen
  · intro a p hp _ v
    exact h.exists_far_cycle p hp v

theorem lemma30_8 : Lemma30_8.{u} := by
  intro X _ n D j hj l l' hl hl' hlen hlen' htype
  have hne : l ≠ [] := by rintro rfl; simp at hlen
  have hne' : l' ≠ [] := by rintro rfl; simp at hlen'
  obtain ⟨u, hu⟩ : ∃ u, l.head? = some u := ⟨l.head hne, List.head?_eq_some_head hne⟩
  obtain ⟨u', hu'⟩ : ∃ u', l'.head? = some u' := ⟨l'.head hne', List.head?_eq_some_head hne'⟩
  obtain ⟨v, hv⟩ : ∃ v, l.getLast? = some v :=
    ⟨l.getLast hne, List.getLast?_eq_some_getLast hne⟩
  obtain ⟨v', hv'⟩ : ∃ v', l'.getLast? = some v' :=
    ⟨l'.getLast hne', List.getLast?_eq_some_getLast hne'⟩
  have htp : vtype D.B D.N D.w₁ D.w₂ u = vtype D.B D.N D.w₁ D.w₂ u' := by
    have := htype u u' hu hu'
    rw [D.isTypeOne_iff, D.isTypeOne_iff] at this
    cases hx : vtype D.B D.N D.w₁ D.w₂ u <;> cases hy : vtype D.B D.N D.w₁ D.w₂ u' <;>
      simp_all
  obtain ⟨f, k, hk, hf0, hfk, hadj, hnb, hfl⟩ := hl.exists_fun hu hv
  obtain ⟨f', k', hk', hf0', hfk', hadj', hnb', hfl'⟩ := hl'.exists_fun hu' hv'
  have hkj : k = j := by omega
  have hkj' : k' = j := by omega
  rcases Nat.eq_zero_or_pos j with hj0 | hjpos
  · subst hj0
    subst hkj
    subst hkj'
    obtain ⟨g, hg⟩ := D.rank2.exists_action_vtx htp
    refine ⟨g, ?_⟩
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hlen
    obtain ⟨y, rfl⟩ := List.length_eq_one_iff.1 hlen'
    simp only [List.head?_cons, Option.some.injEq] at hu hu'
    subst hu
    subst hu'
    have hg' : D.action g x = y := hg
    simpa using hg'
  · obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    subst hkj
    subst hkj'
    obtain ⟨g, hg⟩ := D.rank2.exists_action_path (f₁ := f) (f₂ := f') hj hadj hnb hadj' hnb'
      (by rw [hf0, hf0']; exact htp)
    have hg' : ∀ i, i ≤ m + 1 → D.action g (f i) = f' i := hg
    refine ⟨g, List.ext_getElem? fun i => ?_⟩
    by_cases hi : i ≤ m + 1
    · rw [List.getElem?_map, hfl i hi, hfl' i hi, Option.map_some, hg' i hi]
    · have h1 : l[i]? = none := List.getElem?_eq_none (by omega)
      have h2 : l'[i]? = none := List.getElem?_eq_none (by omega)
      rw [List.getElem?_map, h1, h2]
      rfl

theorem lemma30_10 : Lemma30_10.{u} := by
  intro X _ n D π π' hπ hπ' hlen hlen' hpre g hg hfix hfixΓ
  exact D.polyHyp.eq_one_of_fix hπ' hlen hlen' hpre hg hfix hfixΓ

end CFSG.GH74.BNPair
