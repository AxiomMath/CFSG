module

public import CFSG.Fischer.Uniq.Model
public import CFSG.Fischer.Uniq.YSize

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

@[expose] def TripleProperty (E : Set X) : Prop :=
  ∀ e x : X, e ∈ E → x ∈ E → e * x ≠ x * e → ySet E e x ⊆ {e, x, e * x * e}

@[expose] def muFamily (E : Set X) (d : X) : Set (Set X) :=
  {O | ∃ c ∈ E, c * d ≠ d * c ∧ muSet E d c = O}

@[expose] def muGraph (E : Set X) (d : X) : SimpleGraph (muFamily E d) :=
  SimpleGraph.fromRel fun O Q => ∃ f ∈ LocalClass E d, f ∉ (O : Set X) ∧
    (fun s => f * s * f) '' (O : Set X) = Q

@[expose] def starMap {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d') (O : Set X) :
    Set Y :=
  {y | ∃ f : LocalClass E d, (f : X) ∈ O ∧ (φ f : Y) = y}

structure CoverRigid {V : Type*} (G : SimpleGraph V) (r : V) : Prop where
  exists_adj_adj : ∀ v, v ≠ r → ¬ G.Adj r v → ∃ x, G.Adj r x ∧ G.Adj x v
  connected : ∀ v, v ≠ r → ¬ G.Adj r v → (G.induce {x | G.Adj r x ∧ G.Adj x v}).Connected
  exists_adj_adj_adj : ∀ v w, v ≠ r → ¬ G.Adj r v → w ≠ r → ¬ G.Adj r w → G.Adj v w →
    ∃ x, G.Adj r x ∧ G.Adj x v ∧ G.Adj x w

section Rigid

variable {V W : Type*} {G : SimpleGraph V} {G' : SimpleGraph W}

@[expose] def commonNeighborsHom (e : G ≃g G') (r v : V) :
    G.induce {x | G.Adj r x ∧ G.Adj x v} →g G'.induce {x | G'.Adj (e r) x ∧ G'.Adj x (e v)} where
  toFun x := ⟨e x, e.map_adj_iff.2 x.2.1, e.map_adj_iff.2 x.2.2⟩
  map_rel' h := e.map_adj_iff.2 h

theorem commonNeighborsHom_surjective (e : G ≃g G') (r v : V) :
    Function.Surjective (commonNeighborsHom e r v) := by
  rintro ⟨y, hy1, hy2⟩
  refine ⟨⟨e.symm y, ?_, ?_⟩, Subtype.ext (e.apply_symm_apply y)⟩
  · rw [← e.map_adj_iff, e.apply_symm_apply]; exact hy1
  · rw [← e.map_adj_iff, e.apply_symm_apply]; exact hy2

theorem CoverRigid.map {r : V} (h : CoverRigid G r) (e : G ≃g G') : CoverRigid G' (e r) := by
  have hne : ∀ {v' : W}, v' ≠ e r → e.symm v' ≠ r := fun {v'} hv h' => hv (by
    rw [← h', e.apply_symm_apply])
  have hadj : ∀ {v' : W}, ¬ G'.Adj (e r) v' → ¬ G.Adj r (e.symm v') := fun {v'} hv h' => hv (by
    rw [← e.apply_symm_apply v']; exact e.map_adj_iff.2 h')
  refine ⟨fun v' h0 h1 => ?_, fun v' h0 h1 => ?_, fun v' w' hv0 hv1 hw0 hw1 hvw => ?_⟩
  · obtain ⟨x, hx1, hx2⟩ := h.exists_adj_adj _ (hne h0) (hadj h1)
    refine ⟨e x, e.map_adj_iff.2 hx1, ?_⟩
    rw [← e.apply_symm_apply v']
    exact e.map_adj_iff.2 hx2
  · have := (h.connected _ (hne h0) (hadj h1)).map _ (commonNeighborsHom_surjective e r _)
    rwa [e.apply_symm_apply] at this
  · have hvw' : G.Adj (e.symm v') (e.symm w') := by
      rw [← e.map_adj_iff, e.apply_symm_apply, e.apply_symm_apply]; exact hvw
    obtain ⟨x, hx1, hx2, hx3⟩ :=
      h.exists_adj_adj_adj _ _ (hne hv0) (hadj hv1) (hne hw0) (hadj hw1) hvw'
    refine ⟨e x, e.map_adj_iff.2 hx1, ?_, ?_⟩
    · rw [← e.apply_symm_apply v']; exact e.map_adj_iff.2 hx2
    · rw [← e.apply_symm_apply w']; exact e.map_adj_iff.2 hx3

end Rigid

section StarModel

theorem Pair.mul_mul_mem_localClass_of_mem (hP : Pair X E) {d f g : X}
    (hf : f ∈ LocalClass E d) (hg : g ∈ LocalClass E d) : f * g * f ∈ LocalClass E d := by
  refine ⟨Pair.mul_mul_mem hP hf.1 hg.1, fun h => hg.2.1 ?_, ?_⟩
  · calc g = f * (f * g * f) * f := (Pair.mul_mul_mul_mul hP hf.1 g).symm
      _ = d := by rw [h]; exact (Pair.mul_mul_eq_self_iff hP hf.1 d).2 hf.2.2
  · have h1 : Commute f d := hf.2.2
    have h2 : Commute g d := hg.2.2
    exact ((h1.mul_left h2).mul_left h1 : Commute (f * g * f) d)

@[expose] def starTau (hP : Pair X E) {d : X} (f g : LocalClass E d) : LocalClass E d :=
  ⟨f * g * f, Pair.mul_mul_mem_localClass_of_mem hP f.2 g.2⟩

@[simp]
theorem starTau_coe (hP : Pair X E) {d : X} (f g : LocalClass E d) :
    (starTau hP f g : X) = f * g * f :=
  rfl

theorem starTau_involutive (hP : Pair X E) {d : X} (f : LocalClass E d) :
    Function.Involutive (starTau hP f) :=
  fun g => Subtype.ext (Pair.mul_mul_mul_mul hP f.2.1 g)

theorem starTau_self (hP : Pair X E) {d : X} (f : LocalClass E d) : starTau hP f f = f :=
  Subtype.ext (by rw [starTau_coe, Pair.mul_self hP f.2.1, one_mul])

@[expose] def starModel (hP : Pair X E) (d : X) : LocalModel (LocalClass E d) where
  perp f g := (f : X) * g = g * f
  tv f := (starTau_involutive hP f).toPerm _
  tv_tv f := starTau_involutive hP f
  tv_self f := starTau_self hP f

theorem starModel_perp (hP : Pair X E) {d : X} (f g : LocalClass E d) :
    (starModel hP d).perp f g ↔ (f : X) * g = g * f :=
  Iff.rfl

@[simp]
theorem starModel_tv (hP : Pair X E) {d : X} (f g : LocalClass E d) :
    ((starModel hP d).tv f g : X) = f * g * f :=
  rfl

@[expose] def starPoints (hP : Pair X E) (d : X) : LocalPoints (starModel hP d) E d where
  χ := Equiv.refl _
  comm _ _ := Iff.rfl
  tau _ _ _ := rfl

@[simp]
theorem starPoints_χ (hP : Pair X E) {d : X} (f : LocalClass E d) :
    (starPoints hP d).χ f = f :=
  rfl

theorem starPoints_muImg (hP : Pair X E) (d c : X) :
    (starPoints hP d).muImg c = {p : LocalClass E d | (p : X) ∈ LocalClass E c} := by
  ext p
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hp
    exact ⟨p, hp, rfl⟩

end StarModel

section Family

theorem muSet_subset_localClass (d c : X) : muSet E d c ⊆ LocalClass E d :=
  Set.inter_subset_left

theorem subset_localClass_of_mem_muFamily {d : X} {O : Set X} (hO : O ∈ muFamily E d) :
    O ⊆ LocalClass E d := by
  obtain ⟨c, -, -, rfl⟩ := hO
  exact muSet_subset_localClass d c

theorem muSet_mem_muFamily {d c : X} (hc : c ∈ E) (hcd : c * d ≠ d * c) :
    muSet E d c ∈ muFamily E d :=
  ⟨c, hc, hcd, rfl⟩

theorem Pair.muGraph_adj (hP : Pair X E) {d : X} {O Q : muFamily E d} :
    (muGraph E d).Adj O Q ↔ O ≠ Q ∧ ∃ f ∈ LocalClass E d, f ∉ (O : Set X) ∧
      (fun s => f * s * f) '' (O : Set X) = Q := by
  rw [muGraph, SimpleGraph.fromRel_adj]
  refine and_congr_right fun _ => ⟨?_, Or.inl⟩
  rintro (h | ⟨f, hf, hfQ, hQO⟩)
  · exact h
  · refine ⟨f, hf, fun hfO => hfQ ?_, ?_⟩
    · rw [← hQO] at hfO
      obtain ⟨s, hs, hsf⟩ := hfO
      have hsf : f * s * f = f := hsf
      have : s = f := by
        rw [← Pair.mul_mul_mul_mul hP hf.1 s, hsf, Pair.mul_self hP hf.1, one_mul]
      rwa [← this]
    · rw [← hQO, Set.image_image]
      simp only [Pair.mul_mul_mul_mul hP hf.1, Set.image_id']

theorem mem_starMap_iff {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d') {O : Set X}
    (p : LocalClass E d) : (φ p : Y) ∈ starMap φ O ↔ (p : X) ∈ O := by
  constructor
  · rintro ⟨f, hf, he⟩
    rwa [← φ.injective (Subtype.ext he)]
  · intro h
    exact ⟨p, h, rfl⟩

theorem starMap_subset {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d') (O : Set X) :
    starMap φ O ⊆ LocalClass F d' := by
  rintro _ ⟨f, -, rfl⟩
  exact (φ f).2

theorem starMap_nonempty {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d') {O : Set X}
    (hO : O ⊆ LocalClass E d) (hne : O.Nonempty) : (starMap φ O).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  exact ⟨_, ⟨x, hO hx⟩, hx, rfl⟩

theorem starMap_symm_starMap {d : X} {d' : Y} (φ : LocalClass E d ≃ LocalClass F d')
    {O : Set X} (hO : O ⊆ LocalClass E d) : starMap φ.symm (starMap φ O) = O := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [← φ.apply_symm_apply g, mem_starMap_iff] at hg
    exact hg
  · intro hx
    refine ⟨φ ⟨x, hO hx⟩, ?_, by rw [φ.symm_apply_apply]⟩
    rw [mem_starMap_iff]
    exact hx

end Family

end CFSG.Fischer.Classification
