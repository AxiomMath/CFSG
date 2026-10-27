module

public import CFSG.ClassicalInvolution.Phan.PhanG1Cover

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan.TitsChamber

variable {I I' C D : Type*} {X : ChamberSystem I C} {Y : ChamberSystem I' D}

@[expose] def IsPanelLift (X : ChamberSystem I C) (Y : ChamberSystem I' D) (τ : I → I')
    (f : C → D) : Prop :=
  ∀ i x d, Y.adj (τ i) (f x) d → ∃ y, X.adj i x y ∧ f y = d

theorem IsPanelLift.exists_galleryMapT_eq {τ : I → I'} {f : C → D}
    (hl : IsPanelLift X Y τ f) :
    ∀ {x : C} {γ : List (I' × D)}, Y.IsGallery (f x) γ →
      (∀ j ∈ galleryType γ, j ∈ Set.range τ) → ∃ η, X.IsGallery x η ∧ galleryMapT τ f η = γ := by
  intro x γ
  induction γ generalizing x with
  | nil => exact fun _ _ => ⟨[], trivial, rfl⟩
  | cons p γ ih =>
    obtain ⟨j, d⟩ := p
    intro hγ hτ
    obtain ⟨hadj, hγ'⟩ := hγ
    obtain ⟨i, hi⟩ := hτ j (by simp [galleryType])
    obtain ⟨y, hxy, rfl⟩ := hl i x d (by rwa [hi])
    obtain ⟨η, hη, hηγ⟩ := ih (x := y) hγ'
      (fun j' hj' => hτ j' (List.mem_cons_of_mem _ hj'))
    exact ⟨(i, y) :: η, ⟨hxy, hη⟩, by rw [galleryMapT_cons, hηγ, hi]⟩

theorem twoHomotopic_nil_of_isPanelLift {τ : I → I'} {f : C → D}
    (hf : IsTypeMorphism X Y τ f) (hl : IsPanelLift X Y τ f)
    (hinj : Function.Injective f) (hX : X.SimplyTwoConnected) {x : C} {γ : List (I' × D)}
    (hγ : Y.IsGallery (f x) γ) (hτ : ∀ j ∈ galleryType γ, j ∈ Set.range τ)
    (hend : galleryEnd (f x) γ = f x) : Y.TwoHomotopic (f x) γ [] := by
  obtain ⟨η, hη, hηγ⟩ := hl.exists_galleryMapT_eq hγ hτ
  have hendη : galleryEnd x η = x := by
    apply hinj
    rw [← galleryEnd_galleryMapT τ f x η, hηγ, hend]
  have hmove := twoHomotopic_mapT hf (hX x η hη hendη)
  rw [hηγ] at hmove
  simpa using hmove

theorem simplyTwoConnected_of_isPanelLift {τ : I → I'} {f : C → D}
    (hf : IsTypeMorphism X Y τ f) (hl : IsPanelLift X Y τ f) (hinj : Function.Injective f)
    (hX : X.SimplyTwoConnected) (hτ : Function.Surjective τ) (hfs : Function.Surjective f) :
    Y.SimplyTwoConnected := by
  intro d γ hγ hend
  obtain ⟨x, rfl⟩ := hfs d
  exact twoHomotopic_nil_of_isPanelLift hf hl hinj hX hγ (fun j _ => hτ j) hend

theorem connected_of_isTypeMorphism {τ : I → I'} {f : C → D} (hf : IsTypeMorphism X Y τ f)
    (hfs : Function.Surjective f) (hX : X.Connected) : Y.Connected := by
  intro a b
  obtain ⟨x, rfl⟩ := hfs a
  obtain ⟨y, rfl⟩ := hfs b
  obtain ⟨γ, hγ, hend⟩ := hX x y
  exact ⟨galleryMapT τ f γ, hf.isGallery hγ, by rw [galleryEnd_galleryMapT, hend]⟩

end CFSG.ClassicalInvolution.PhanG
