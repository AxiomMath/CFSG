module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.Phan.PhanS0Graph
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open SimpleGraph CFSG.ClassicalInvolution.Phan

section Transport

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem cycleHomotopic_map (ψ : H →g G) {E' : ∀ y : W, Set (H.Walk y y)}
    {E : ∀ x : V, Set (G.Walk x x)}
    (hE : ∀ (y : W) (c : H.Walk y y), c ∈ E' y → CycleHomotopic E (c.map ψ) .nil) {u v : W}
    {p q : H.Walk u v} (h : CycleHomotopic E' p q) :
    CycleHomotopic E (p.map ψ) (q.map ψ) := by
  refine CycleHomotopic.induction (R := fun a b => CycleHomotopic E (a.map ψ) (b.map ψ)) h
    ?_ (fun a => CycleHomotopic.refl _) (fun a b hab => hab.symm)
    (fun a b c hab hbc => hab.trans hbc)
  intro a b hab
  cases hab with
  | backtrack p q h' =>
    rw [Walk.map_append, Walk.map_append, Walk.map_cons, Walk.map_cons]
    exact cycleHomotopic_backtrack E _ _ (ψ.map_adj h')
  | elem p q c hc =>
    rw [Walk.map_append, Walk.map_append, Walk.map_append]
    exact cycleHomotopic_insert_null E _ _ (hE _ c hc)

theorem walk_map_symm_map (φ : G ≃g H) {u v : V} (p : G.Walk u v) :
    ((p.map φ.toHom).map φ.symm.toHom).copy (φ.symm_apply_apply u) (φ.symm_apply_apply v) = p := by
  apply Walk.ext_support
  rw [Walk.support_copy, Walk.support_map, Walk.support_map, List.map_map]
  have : (⇑φ.symm.toHom ∘ ⇑φ.toHom) = id := funext fun x => φ.symm_apply_apply x
  rw [this, List.map_id]

theorem cycleHomotopic_copy {E : ∀ x : V, Set (G.Walk x x)} {u v u' v' : V} (hu : u = u')
    (hv : v = v') {a b : G.Walk u v} (hab : CycleHomotopic E a b) :
    CycleHomotopic E (a.copy hu hv) (b.copy hu hv) := by
  subst hu hv
  simpa using hab

theorem cycleHomotopic_of_iso (φ : G ≃g H) {E : ∀ x : V, Set (G.Walk x x)}
    {E' : ∀ y : W, Set (H.Walk y y)}
    (hE : ∀ (y : W) (c : H.Walk y y), c ∈ E' y →
      CycleHomotopic E (c.map φ.symm.toHom) .nil) {u v : V} {p q : G.Walk u v}
    (h : CycleHomotopic E' (p.map φ.toHom) (q.map φ.toHom)) : CycleHomotopic E p q := by
  have h' := cycleHomotopic_copy (φ.symm_apply_apply u) (φ.symm_apply_apply v)
    (cycleHomotopic_map φ.symm.toHom hE h)
  rwa [walk_map_symm_map, walk_map_symm_map] at h'

theorem quadNull_of_iso (φ : G ≃g H) (h : QuadNull H) : QuadNull G := by
  intro a b c d hab hbc hcd hda
  refine cycleHomotopic_of_iso φ (E' := triWalks H) ?_ ?_
  · intro y c hc
    refine cycleHomotopic_of_mem _ ?_
    show (c.map φ.symm.toHom).length = 3
    rw [Walk.length_map]
    exact hc
  · exact h _ _ _ _ (φ.map_adj_iff.2 hab) (φ.map_adj_iff.2 hbc) (φ.map_adj_iff.2 hcd)
      (φ.map_adj_iff.2 hda)

theorem pentNull_of_iso (φ : G ≃g H) (h : PentNull H) : PentNull G := by
  intro u p hp
  refine cycleHomotopic_of_iso φ (E' := triWalks H) ?_ ?_
  · intro y c hc
    refine cycleHomotopic_of_mem _ ?_
    show (c.map φ.symm.toHom).length = 3
    rw [Walk.length_map]
    exact hc
  · exact h _ (p.map φ.toHom) (by rw [Walk.length_map]; exact hp)

theorem ediam_le_two_of_iso (φ : G ≃g H) (hc : H.Connected) (h : H.ediam ≤ 2) :
    G.ediam ≤ 2 := by
  refine ediam_le_of_edist_le fun u v => ?_
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_edist (φ u) (φ v)
  have hle : H.edist (φ u) (φ v) ≤ 2 := (edist_le_ediam).trans h
  have := edist_le (((p.map φ.symm.toHom).copy (φ.symm_apply_apply u) (φ.symm_apply_apply v)))
  refine this.trans ?_
  rw [Walk.length_copy, Walk.length_map, hp]
  exact hle

end Transport

end CFSG.ClassicalInvolution.PhanB3.S
