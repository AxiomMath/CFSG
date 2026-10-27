module

public import CFSG.ClassicalInvolution.Phan.TitsChamber

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan.TitsChamber

section MapT

variable {I I' C D : Type*} {X : ChamberSystem I C} {Y : ChamberSystem I' D}

@[expose] def galleryMapT (τ : I → I') (f : C → D) (γ : List (I × C)) : List (I' × D) :=
  γ.map fun p => (τ p.1, f p.2)

@[simp] theorem galleryMapT_nil (τ : I → I') (f : C → D) :
    galleryMapT τ f ([] : List (I × C)) = [] := rfl

@[simp] theorem galleryMapT_cons (τ : I → I') (f : C → D) (p : I × C) (γ : List (I × C)) :
    galleryMapT τ f (p :: γ) = (τ p.1, f p.2) :: galleryMapT τ f γ := rfl

@[simp] theorem galleryMapT_append (τ : I → I') (f : C → D) (γ η : List (I × C)) :
    galleryMapT τ f (γ ++ η) = galleryMapT τ f γ ++ galleryMapT τ f η :=
  List.map_append

theorem galleryEnd_galleryMapT (τ : I → I') (f : C → D) (x : C) (γ : List (I × C)) :
    galleryEnd (f x) (galleryMapT τ f γ) = f (galleryEnd x γ) := by
  induction γ generalizing x with
  | nil => rfl
  | cons p γ ih => exact ih p.2

theorem mem_galleryType_galleryMapT (τ : I → I') (f : C → D) (γ : List (I × C)) (j : I') :
    j ∈ galleryType (galleryMapT τ f γ) ↔ ∃ i ∈ galleryType γ, τ i = j := by
  simp [galleryType, galleryMapT, List.mem_map]

@[expose] def IsTypeMorphism (X : ChamberSystem I C) (Y : ChamberSystem I' D) (τ : I → I')
    (f : C → D) : Prop :=
  ∀ i x y, X.adj i x y → Y.adj (τ i) (f x) (f y)

theorem IsTypeMorphism.isGallery {τ : I → I'} {f : C → D} (hf : IsTypeMorphism X Y τ f) :
    ∀ {x : C} {γ : List (I × C)}, X.IsGallery x γ → Y.IsGallery (f x) (galleryMapT τ f γ)
  | _, [], _ => trivial
  | _, _ :: _, h => ⟨hf _ _ _ h.1, hf.isGallery h.2⟩

theorem elemMove_mapT {τ : I → I'} {f : C → D} (hf : IsTypeMorphism X Y τ f) {x : C}
    {γ γ' : List (I × C)} (h : X.ElemMove x γ γ') :
    Y.ElemMove (f x) (galleryMapT τ f γ) (galleryMapT τ f γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  simp only [galleryMapT_append]
  refine .mk _ _ _ _ (τ '' J) ((Set.encard_image_le τ J).trans hJ) ?_ ?_ ?_ ?_ ?_
  · rw [galleryEnd_galleryMapT]; exact hf.isGallery hη
  · rw [galleryEnd_galleryMapT]; exact hf.isGallery hη'
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := (mem_galleryType_galleryMapT τ f η j).1 hj
    exact ⟨i, hηJ i hi, rfl⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := (mem_galleryType_galleryMapT τ f η' j).1 hj
    exact ⟨i, hη'J i hi, rfl⟩
  · rw [galleryEnd_galleryMapT, galleryEnd_galleryMapT, galleryEnd_galleryMapT, hend]

theorem twoHomotopic_mapT {τ : I → I'} {f : C → D} (hf : IsTypeMorphism X Y τ f) {x : C}
    {γ γ' : List (I × C)} (h : X.TwoHomotopic x γ γ') :
    Y.TwoHomotopic (f x) (galleryMapT τ f γ) (galleryMapT τ f γ') := by
  induction h with
  | rel _ _ h => exact TwoHomotopic.of_elemMove (elemMove_mapT hf h)
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

end MapT

section Cover

variable {I I' : Type*} {G H : Type*} [Group G] [Group H]

variable (e : I → I') (ψ : H →* G) (TG : Subgroup G) (QG : I' → Subgroup G)
  (hQG : ∀ j, TG ≤ QG j) (TH : Subgroup H) (QH : I → Subgroup H) (hQH : ∀ i, TH ≤ QH i)

@[expose] noncomputable def cosetMap (hT : TH.map ψ ≤ TG) : H ⧸ TH → G ⧸ TG :=
  Quotient.map' ψ fun a b hab => by
    have : a⁻¹ * b ∈ TH := QuotientGroup.leftRel_apply.mp hab
    exact QuotientGroup.leftRel_apply.mpr (by
      rw [← map_inv, ← map_mul]
      exact hT ⟨_, this, rfl⟩)

theorem cosetMap_mk (hT : TH.map ψ ≤ TG) (a : H) :
    cosetMap ψ TG TH hT (a : H ⧸ TH) = ((ψ a : G) : G ⧸ TG) := rfl

variable {e ψ TG QG hQG TH QH hQH}

theorem isTypeMorphism_cosetMap (hT : TH.map ψ ≤ TG) (h1 : ∀ i, (QH i).map ψ ≤ QG (e i)) :
    IsTypeMorphism (cosetSystem TH QH hQH) (cosetSystem TG QG hQG) e (cosetMap ψ TG TH hT) := by
  intro i x y hxy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [cosetSystem_adj_mk] at hxy
  rw [cosetMap_mk, cosetMap_mk, cosetSystem_adj_mk, ← map_inv, ← map_mul]
  exact h1 i ⟨_, hxy, rfl⟩

theorem exists_lift_gallery (hT : TH.map ψ ≤ TG)
    (h2 : ∀ i, ∀ x ∈ QG (e i), ∃ q ∈ QH i, ∃ t ∈ TG, x = ψ q * t) :
    ∀ (γ : List (I' × G ⧸ TG)) (a : H),
      (cosetSystem TG QG hQG).IsGallery ((ψ a : G) : G ⧸ TG) γ →
      (∀ j ∈ galleryType γ, j ∈ Set.range e) →
      ∃ η : List (I × H ⧸ TH), (cosetSystem TH QH hQH).IsGallery (a : H ⧸ TH) η ∧
        galleryMapT e (cosetMap ψ TG TH hT) η = γ := by
  intro γ
  induction γ with
  | nil => exact fun a _ _ => ⟨[], trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨j, y⟩ := p
    intro a hγ hJ
    obtain ⟨hadj, hγ'⟩ := hγ
    obtain ⟨i, hi⟩ := hJ j (by simp [galleryType])
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← hi, cosetSystem_adj_mk] at hadj
    obtain ⟨q, hq, t, ht, hx⟩ := h2 i _ hadj
    have hb' : ((ψ (a * q) : G) : G ⧸ TG) = (b : G ⧸ TG) := by
      have hbq : b = ψ (a * q) * t := by rw [map_mul, mul_assoc, ← hx]; simp
      exact QuotientGroup.eq.mpr (by rw [hbq, inv_mul_cancel_left]; exact ht)
    obtain ⟨η, hη, hη'⟩ := ih (a * q) (by rw [hb']; exact hγ')
      (fun j' hj' => hJ j' (List.mem_cons_of_mem _ hj'))
    refine ⟨(i, ((a * q : H) : H ⧸ TH)) :: η, ⟨?_, hη⟩, ?_⟩
    · rw [cosetSystem_adj_mk]
      simpa using hq
    · simp only [galleryMapT_cons, cosetMap_mk, hb', hi, hη']

theorem twoHomotopic_nil_of_coset_cover (hT : TH.map ψ ≤ TG)
    (h1 : ∀ i, (QH i).map ψ ≤ QG (e i))
    (h2 : ∀ i, ∀ x ∈ QG (e i), ∃ q ∈ QH i, ∃ t ∈ TG, x = ψ q * t)
    (h3 : ∀ h, ψ h ∈ TG → h ∈ TH)
    (hS : (cosetSystem TH QH hQH).SimplyTwoConnected) (a : H) (γ : List (I' × G ⧸ TG))
    (hγ : (cosetSystem TG QG hQG).IsGallery ((ψ a : G) : G ⧸ TG) γ)
    (hJ : ∀ j ∈ galleryType γ, j ∈ Set.range e)
    (hend : galleryEnd ((ψ a : G) : G ⧸ TG) γ = ((ψ a : G) : G ⧸ TG)) :
    (cosetSystem TG QG hQG).TwoHomotopic ((ψ a : G) : G ⧸ TG) γ [] := by
  obtain ⟨η, hη, hηγ⟩ := exists_lift_gallery (hQG := hQG) (hQH := hQH) hT h2 γ a hγ hJ
  have hmorph := isTypeMorphism_cosetMap (hQG := hQG) (hQH := hQH) hT h1
  have hendη : galleryEnd (a : H ⧸ TH) η = (a : H ⧸ TH) := by
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (galleryEnd (a : H ⧸ TH) η)
    have h' := galleryEnd_galleryMapT e (cosetMap ψ TG TH hT) (a : H ⧸ TH) η
    rw [hηγ, cosetMap_mk, hend, ← hc, cosetMap_mk] at h'
    have := (QuotientGroup.eq.mp h' : (ψ a)⁻¹ * ψ c ∈ TG)
    rw [← map_inv, ← map_mul] at this
    rw [← hc]
    exact (QuotientGroup.eq.mpr (h3 _ this)).symm
  have hnull := hS _ η hη hendη
  have := (twoHomotopic_mapT hmorph hnull)
  rw [hηγ] at this
  simpa [cosetMap_mk] using this

end Cover

end CFSG.ClassicalInvolution.PhanG
