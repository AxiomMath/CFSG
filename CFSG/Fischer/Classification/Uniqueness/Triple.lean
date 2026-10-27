module

public import CFSG.Fischer.Classification.Uniqueness.Lift

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

@[expose] def LocalTriple (E : Set X) (f : X) : Prop :=
  ∀ a ∈ LocalClass E f, ∀ b ∈ LocalClass E f, a * b ≠ b * a → ∀ y ∈ LocalClass E f,
    muSet E a b ∩ LocalClass E f ⊆ LocalClass E y → y = a ∨ y = b ∨ y = a * b * a

theorem muSet_map (ψ : X ≃* Y) (E : Set X) (a b : X) :
    muSet (ψ '' E) (ψ a) (ψ b) = ψ '' muSet E a b := by
  rw [muSet, muSet, localClass_map, localClass_map, Set.image_inter ψ.injective]

theorem mem_localClass_map_iff (ψ : X ≃* Y) {e s : X} :
    ψ s ∈ LocalClass (ψ '' E) (ψ e) ↔ s ∈ LocalClass E e := by
  rw [localClass_map, ψ.injective.mem_set_image]

theorem tripleProperty_map (ψ : X ≃* Y) (hT : TripleProperty E) : TripleProperty (ψ '' E) := by
  rintro _ _ ⟨e, he, rfl⟩ ⟨x, hx, rfl⟩ hex _ ⟨⟨y, hy, rfl⟩, hsub⟩
  have hex' : e * x ≠ x * e := fun h => hex (by rw [← map_mul, ← map_mul, h])
  have hy' : y ∈ ySet E e x := ⟨hy, fun s hs => by
    have : ψ s ∈ muSet (ψ '' E) (ψ e) (ψ x) := by rw [muSet_map]; exact ⟨s, hs, rfl⟩
    exact (mem_localClass_map_iff ψ).1 (hsub this)⟩
  rcases hT e x he hx hex' hy' with h | h | h
  · exact Or.inl (by rw [h])
  · exact Or.inr (Or.inl (by rw [h]))
  · rw [Set.mem_singleton_iff] at h
    exact Or.inr (Or.inr (by rw [h, map_mul, map_mul]; exact Set.mem_singleton _))

theorem tripleProperty_congr (ψ : X ≃* Y) (h : ψ '' E = F) :
    TripleProperty E ↔ TripleProperty F := by
  refine ⟨fun hT => h ▸ tripleProperty_map ψ hT, fun hT => ?_⟩
  rw [← image_symm_image ψ E, h]
  exact tripleProperty_map ψ.symm hT

theorem localTriple_map (ψ : X ≃* Y) {f : X} (h : LocalTriple E f) :
    LocalTriple (ψ '' E) (ψ f) := by
  intro a' ha b' hb hab y' hy hsub
  rw [localClass_map] at ha hb hy
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  obtain ⟨y, hy, rfl⟩ := hy
  have hab' : a * b ≠ b * a := fun e => hab (by rw [← map_mul, ← map_mul, e])
  have hsub' : muSet E a b ∩ LocalClass E f ⊆ LocalClass E y := by
    rintro s ⟨hs, hsf⟩
    have h1 : ψ s ∈ muSet (ψ '' E) (ψ a) (ψ b) := by rw [muSet_map]; exact ⟨s, hs, rfl⟩
    exact (mem_localClass_map_iff ψ).1 (hsub ⟨h1, (mem_localClass_map_iff ψ).2 hsf⟩)
  rcases h a ha b hb hab' y hy hsub' with e | e | e
  · exact Or.inl (by rw [e])
  · exact Or.inr (Or.inl (by rw [e]))
  · exact Or.inr (Or.inr (by rw [e, map_mul, map_mul]))

theorem Pair.localTriple_of_mem (hP : Pair X E) {d f : X} (hd : d ∈ E) (hf : f ∈ E)
    (h : LocalTriple E d) : LocalTriple E f := by
  obtain ⟨ψ, hψE, hψd⟩ := Pair.exists_mulEquiv hP hd hf
  have := localTriple_map ψ h
  rwa [hψE, hψd] at this

theorem Pair.tripleProperty_of_local (hP : Pair X E) (hconn : (commGraph E).Connected)
    (hloc : ∀ f ∈ E, LocalTriple E f) : TripleProperty E := by
  intro e x he hx hex y hy
  obtain ⟨f, hfe, hfx⟩ := Pair.muSet_nonempty hP hconn he hx (fun h => hex h.symm)
  have hfy : f ∈ LocalClass E y := hy.2 ⟨hfe, hfx⟩
  exact hloc f hfe.1 e ⟨he, hfe.2.1.symm, hfe.2.2.symm⟩ x ⟨hx, hfx.2.1.symm, hfx.2.2.symm⟩ hex
    y ⟨hy.1, hfy.2.1.symm, hfy.2.2.symm⟩ fun s hs => hy.2 hs.1

theorem Pair.tripleProperty_of_localTriple (hP : Pair X E) (hconn : (commGraph E).Connected)
    {d : X} (hd : d ∈ E) (h : LocalTriple E d) : TripleProperty E :=
  Pair.tripleProperty_of_local hP hconn fun _ hf => Pair.localTriple_of_mem hP hd hf h

theorem Pair.localTriple_of_localImages (hP : Pair X E) {f : X}
    (hi : Function.Injective (starImage E f)) (hT : TripleProperty (LocalImages E f)) :
    LocalTriple E f := by
  intro a ha b hb hab y hy hsub
  set A : LocalClass E f := ⟨a, ha⟩
  set B : LocalClass E f := ⟨b, hb⟩
  set W : LocalClass E f := ⟨y, hy⟩
  have hcomm : ∀ s t : LocalClass E f, starImage E f s * starImage E f t =
      starImage E f t * starImage E f s ↔ (s : X) * t = t * s :=
    fun s t => Pair.starImage_commute_iff hP s t
  have hne : ∀ s t : LocalClass E f, starImage E f s ≠ starImage E f t ↔ (s : X) ≠ t :=
    fun s t => ⟨fun h e => h (congrArg _ (Subtype.ext e)), fun h e => h (congrArg _ (hi e))⟩
  have hab' : starImage E f A * starImage E f B ≠ starImage E f B * starImage E f A :=
    fun e => hab ((hcomm A B).1 e)
  have hyY : starImage E f W ∈ ySet (LocalImages E f) (starImage E f A) (starImage E f B) := by
    refine ⟨starImage_mem_localImages W, fun q hq => ?_⟩
    have hq' : q ∈ Set.range (starImage E f) := by rw [range_starImage]; exact hq.1.1
    obtain ⟨S, rfl⟩ := hq'
    have hsa : (S : X) ∈ LocalClass E a :=
      ⟨S.2.1, (hne S A).1 hq.1.2.1, (hcomm S A).1 hq.1.2.2⟩
    have hsb : (S : X) ∈ LocalClass E b :=
      ⟨S.2.1, (hne S B).1 hq.2.2.1, (hcomm S B).1 hq.2.2.2⟩
    have hsy : (S : X) ∈ LocalClass E y := hsub ⟨⟨hsa, hsb⟩, S.2⟩
    exact ⟨starImage_mem_localImages S, (hne S W).2 hsy.2.1, (hcomm S W).2 hsy.2.2⟩
  rcases hT _ _ (starImage_mem_localImages A) (starImage_mem_localImages B) hab' hyY with
    e | e | e
  · exact Or.inl (congrArg Subtype.val (hi e))
  · exact Or.inr (Or.inl (congrArg Subtype.val (hi e)))
  · refine Or.inr (Or.inr (congrArg Subtype.val (hi (e.trans ?_) :
      W = ⟨_, Pair.mul_mul_mem_localClass_of_mem hP ha hb⟩)))
    exact (starImage_conj A B _).symm

theorem Pair.tripleProperty_of_localImages (hP : Pair X E) (hconn : (commGraph E).Connected)
    {d : X} (hd : d ∈ E) (hi : Function.Injective (starImage E d))
    (hT : TripleProperty (LocalImages E d)) : TripleProperty E :=
  Pair.tripleProperty_of_localTriple hP hconn hd (Pair.localTriple_of_localImages hP hi hT)

end CFSG.Fischer.Classification
