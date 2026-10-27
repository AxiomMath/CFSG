module

public import CFSG.ClassicalInvolution.Phan.Phan3GHom
public import CFSG.ClassicalInvolution.Phan.GalleryWalk

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan.TitsChamber

variable {I C V : Type*} {X : ChamberSystem I C} {Γ : SimpleGraph V}

variable (F : Fib X Γ) (𝒥 : Set I → Prop) in
structure RigidOn : Prop where
  two : ∀ J : Set I, J.encard ≤ 2 → 𝒥 J
  null : ∀ {e : C} {γ : List (I × C)}, F.Q e → IsJGallery X F.J' e γ → galleryEnd e γ = e →
    HomotopicOn X 𝒥 e γ []
  edge : ∀ {e e' f f' : C} {ρ ρ' : List (I × C)} {x' : V}, F.Q e → F.Q e' → F.P e = F.P e' →
    Γ.Adj (F.P e) x' → IsJGallery X F.J' e ρ → X.adj F.a (galleryEnd e ρ) f → F.P f = x' →
    IsJGallery X F.J' e' ρ' → X.adj F.a (galleryEnd e' ρ') f' → F.P f' = x' →
    ∃ τ τ' : List (I × C), IsJGallery X F.J' e τ ∧ galleryEnd e τ = e' ∧
      IsJGallery X F.J' f τ' ∧ galleryEnd f τ' = f' ∧
      X.TwoHomotopic e (τ ++ ρ' ++ [(F.a, f')]) (ρ ++ (F.a, f) :: τ')

variable {F : Fib X Γ} {𝒥 : Set I → Prop}

theorem RigidOn.fib_unique (R : RigidOn F 𝒥) {e : C} {τ₁ τ₂ : List (I × C)} (hQ : F.Q e)
    (h₁ : IsJGallery X F.J' e τ₁) (h₂ : IsJGallery X F.J' e τ₂)
    (hend : galleryEnd e τ₁ = galleryEnd e τ₂) : HomotopicOn X 𝒥 e τ₁ τ₂ := by
  have h₂' : IsJGallery X F.J' (galleryEnd e τ₁) (galleryReverse e τ₂) := by
    rw [hend]
    exact h₂.reverse
  have hc : IsJGallery X F.J' e (τ₁ ++ galleryReverse e τ₂) := h₁.append h₂'
  have hend' : galleryEnd e (τ₁ ++ galleryReverse e τ₂) = e := by
    rw [galleryEnd_append, hend, galleryEnd_galleryReverse]
  have h0 := R.null hQ hc hend'
  have hrev : HomotopicOn X 𝒥 (galleryEnd e τ₁) (galleryReverse e τ₂ ++ τ₂) [] := by
    rw [hend]
    exact HomotopicOn.of_twoHomotopic R.two (twoHomotopic_reverse_append h₂.1)
  have h1 := HomotopicOn.append_left (X := X) (x := e) τ₁ hrev
  have h2 := HomotopicOn.append_right h0 τ₂
  simp only [List.nil_append, List.append_assoc, List.append_nil] at h1 h2
  exact HomotopicOn.trans (HomotopicOn.symm h1) h2

theorem RigidOn.lift_unique (R : RigidOn F 𝒥) {x y : V} {w : Γ.Walk x y} :
    ∀ {e e₂ : C} {γ γ' τ : List (I × C)}, F.Q e → F.Q e₂ → F.Lift w e γ → F.Lift w e₂ γ' →
      IsJGallery X F.J' e τ → galleryEnd e τ = e₂ →
      ∃ τ' : List (I × C), IsJGallery X F.J' (galleryEnd e γ) τ' ∧
        galleryEnd (galleryEnd e γ) τ' = galleryEnd e₂ γ' ∧
        HomotopicOn X 𝒥 e (τ ++ γ') (γ ++ τ') := by
  induction w with
  | nil =>
    intro e e₂ γ γ' τ hQ hQ' hl hl' hτ hτe
    refine ⟨galleryReverse e γ ++ (τ ++ γ'), ?_, ?_, ?_⟩
    · refine hl.2.reverse.append ?_
      rw [galleryEnd_galleryReverse]
      refine hτ.append ?_
      rw [hτe]
      exact hl'.2
    · rw [galleryEnd_append, galleryEnd_galleryReverse, galleryEnd_append, hτe]
    · have h1 := HomotopicOn.append_right
        (HomotopicOn.of_twoHomotopic R.two (twoHomotopic_append_reverse hl.2.1)) (τ ++ γ')
      simp only [List.nil_append, List.append_assoc] at h1
      exact HomotopicOn.symm h1
  | @cons u v z hxy w ih =>
    intro e e₂ γ γ' τ hQ hQ' hl hl' hτ hτe
    obtain ⟨hPe, ρ, f, δ, rfl, hρ, hadj, hδ⟩ := hl
    obtain ⟨hPe', ρ', f', δ', rfl, hρ', hadj', hδ'⟩ := hl'
    have hQρ : F.Q (galleryEnd e ρ) := F.Q_galleryEnd hQ (hρ.mono (Set.subset_insert _ _))
    have hQρ' : F.Q (galleryEnd e₂ ρ') := F.Q_galleryEnd hQ' (hρ'.mono (Set.subset_insert _ _))
    have hQf : F.Q f := F.step_Q (Set.mem_insert _ _) hadj hQρ
    have hQf' : F.Q f' := F.step_Q (Set.mem_insert _ _) hadj' hQρ'
    obtain ⟨τ₀, τ₀', hτ₀, hτ₀e, hτ₀', hτ₀'e, hhom⟩ := R.edge hQ hQ' (hPe.trans hPe'.symm)
      (hPe ▸ hxy) hρ hadj hδ.start_eq hρ' hadj' hδ'.start_eq
    have hττ₀ : HomotopicOn X 𝒥 e τ τ₀ := R.fib_unique hQ hτ hτ₀ (by rw [hτe, hτ₀e])
    obtain ⟨τ'', hτ'', hτ''e, hhom'⟩ := ih hQf hQf' hδ hδ' hτ₀' hτ₀'e
    refine ⟨τ'', ?_, ?_, ?_⟩
    · rw [galleryEnd_append, galleryEnd_cons]
      exact hτ''
    · rw [galleryEnd_append, galleryEnd_cons, galleryEnd_append, galleryEnd_cons]
      exact hτ''e
    · have e1 : τ ++ (ρ' ++ (F.a, f') :: δ') = (τ ++ ρ' ++ [(F.a, f')]) ++ δ' := by simp
      have e2 : (ρ ++ (F.a, f) :: τ₀') ++ δ' = (ρ ++ [(F.a, f)]) ++ (τ₀' ++ δ') := by simp
      have e3 : (ρ ++ (F.a, f) :: δ) ++ τ'' = (ρ ++ [(F.a, f)]) ++ (δ ++ τ'') := by simp
      rw [e1, e3]
      have h1 : HomotopicOn X 𝒥 e ((τ ++ ρ' ++ [(F.a, f')]) ++ δ')
          ((τ₀ ++ ρ' ++ [(F.a, f')]) ++ δ') :=
        HomotopicOn.append_right
          (HomotopicOn.append_right (HomotopicOn.append_right hττ₀ ρ') [(F.a, f')]) δ'
      have h2 := HomotopicOn.append_right (HomotopicOn.of_twoHomotopic R.two hhom) δ'
      rw [e2] at h2
      have h3 : HomotopicOn X 𝒥 e ((ρ ++ [(F.a, f)]) ++ (τ₀' ++ δ'))
          ((ρ ++ [(F.a, f)]) ++ (δ ++ τ'')) := by
        refine HomotopicOn.append_left (X := X) (x := e) (ρ ++ [(F.a, f)]) ?_
        have : galleryEnd e (ρ ++ [(F.a, f)]) = f := by simp
        rw [this]
        exact hhom'
      exact HomotopicOn.trans h1 (HomotopicOn.trans h2 h3)

variable (F 𝒥) in
@[expose] def FibreNullOn {u : V} (m : Γ.Walk u u) : Prop :=
  ∀ (e : C) (γ : List (I × C)), F.Q e → F.Lift m e γ →
    ∃ τ : List (I × C), IsJGallery X F.J' e τ ∧ galleryEnd e τ = galleryEnd e γ ∧
      HomotopicOn X 𝒥 e γ τ

theorem RigidOn.lift_insert (R : RigidOn F 𝒥) {x u y : V} {p : Γ.Walk x u} {q : Γ.Walk u y}
    {m : Γ.Walk u u} (hm : FibreNullOn F 𝒥 m) {e₀ : C} {γ γ' : List (I × C)} (hQ : F.Q e₀)
    (hl : F.Lift (p.append q) e₀ γ) (hl' : F.Lift (p.append (m.append q)) e₀ γ') :
    ∃ τ : List (I × C), IsJGallery X F.J' (galleryEnd e₀ γ) τ ∧
      galleryEnd (galleryEnd e₀ γ) τ = galleryEnd e₀ γ' ∧ HomotopicOn X 𝒥 e₀ (γ ++ τ) γ' := by
  obtain ⟨γp, γq, rfl, hp, hq⟩ := hl.of_append
  obtain ⟨γp', δ', rfl, hp', hδ'⟩ := hl'.of_append
  obtain ⟨γm, γq', rfl, hm', hq'⟩ := hδ'.of_append
  have hQg' : F.Q (galleryEnd e₀ γp') := hp'.Q_galleryEnd hQ
  have hQg : F.Q (galleryEnd e₀ γp) := hp.Q_galleryEnd hQ
  obtain ⟨τ₁, hτ₁, hτ₁e, hh₁⟩ := R.lift_unique hQ hQ hp hp' IsJGallery.nil rfl
  obtain ⟨τ₂, hτ₂, hτ₂e, hh₂⟩ := hm _ _ hQg' hm'
  have hτ₁₂ : IsJGallery X F.J' (galleryEnd e₀ γp) (τ₁ ++ τ₂) := by
    refine hτ₁.append ?_
    rw [hτ₁e]
    exact hτ₂
  have hτ₁₂e : galleryEnd (galleryEnd e₀ γp) (τ₁ ++ τ₂) = galleryEnd (galleryEnd e₀ γp') γm := by
    rw [galleryEnd_append, hτ₁e, hτ₂e]
  obtain ⟨τ₃, hτ₃, hτ₃e, hh₃⟩ := R.lift_unique hQg (hm'.Q_galleryEnd hQg') hq hq' hτ₁₂ hτ₁₂e
  refine ⟨τ₃, ?_, ?_, ?_⟩
  · rw [galleryEnd_append]
    exact hτ₃
  · simp only [galleryEnd_append]
    exact hτ₃e
  · simp only [List.nil_append] at hh₁
    have hA := HomotopicOn.append_right (HomotopicOn.append hh₁ hh₂) γq'
    have hB := HomotopicOn.append_left (X := X) (x := e₀) γp hh₃
    simp only [List.append_assoc] at hA hB ⊢
    exact HomotopicOn.symm (HomotopicOn.trans hA hB)

theorem RigidOn.fibreNull_backtrack (R : RigidOn F 𝒥) {u v : V} (h : Γ.Adj u v) :
    FibreNullOn F 𝒥 (.cons h (.cons h.symm .nil)) := by
  intro e γ hQ hl
  obtain ⟨hPe, ρ₁, f₁, δ, rfl, hρ₁, hadj₁, hδ⟩ := hl
  have hQg : F.Q (galleryEnd e ρ₁) := F.Q_galleryEnd hQ (hρ₁.mono (Set.subset_insert _ _))
  have hPg : F.P (galleryEnd e ρ₁) = u := (F.P_galleryEnd hQ hρ₁).trans hPe
  have hQf₁ : F.Q f₁ := F.step_Q (Set.mem_insert _ _) hadj₁ hQg
  have hδ₀ : F.Lift (.cons h.symm .nil) f₁
      ((F.a, galleryEnd e ρ₁) :: galleryReverse e ρ₁) :=
    ⟨hδ.start_eq, [], galleryEnd e ρ₁, galleryReverse e ρ₁, rfl, IsJGallery.nil,
      adj_symm hadj₁, hPg, hρ₁.reverse⟩
  have hend₀ : galleryEnd f₁ ((F.a, galleryEnd e ρ₁) :: galleryReverse e ρ₁) = e := by
    simp
  obtain ⟨τ', hτ', hτ'e, hh⟩ := R.lift_unique hQf₁ hQf₁ hδ₀ hδ IsJGallery.nil rfl
  rw [hend₀] at hτ' hτ'e
  refine ⟨τ', hτ', ?_, ?_⟩
  · rw [hτ'e, galleryEnd_append, galleryEnd_cons]
  · simp only [List.nil_append] at hh
    have h1 : HomotopicOn X 𝒥 e ((ρ₁ ++ [(F.a, f₁)]) ++ δ)
        ((ρ₁ ++ [(F.a, f₁)]) ++ ((F.a, galleryEnd e ρ₁) :: (galleryReverse e ρ₁ ++ τ'))) := by
      refine HomotopicOn.append_left (X := X) (x := e) (ρ₁ ++ [(F.a, f₁)]) ?_
      have : galleryEnd e (ρ₁ ++ [(F.a, f₁)]) = f₁ := by simp
      rw [this]
      simpa using hh
    have h2 := HomotopicOn.of_twoHomotopic R.two
      (twoHomotopic_backtrack (X := X) (x := e) ρ₁ (galleryReverse e ρ₁ ++ τ') hadj₁)
    have h3 := HomotopicOn.append_right (HomotopicOn.of_twoHomotopic R.two
      (twoHomotopic_append_reverse (X := X) hρ₁.1)) τ'
    have e1 : ρ₁ ++ (F.a, f₁) :: δ = (ρ₁ ++ [(F.a, f₁)]) ++ δ := by simp
    have e2 : (ρ₁ ++ [(F.a, f₁)]) ++ ((F.a, galleryEnd e ρ₁) :: (galleryReverse e ρ₁ ++ τ')) =
        ρ₁ ++ [(F.a, f₁), (F.a, galleryEnd e ρ₁)] ++ (galleryReverse e ρ₁ ++ τ') := by simp
    rw [e1]
    refine HomotopicOn.trans h1 ?_
    rw [e2]
    refine HomotopicOn.trans h2 ?_
    simpa using h3

theorem RigidOn.fibreNull_of_exists (R : RigidOn F 𝒥)
    (hconn : ∀ {e e' : C}, F.Q e → F.Q e' → F.P e = F.P e' →
      ∃ τ : List (I × C), IsJGallery X F.J' e τ ∧ galleryEnd e τ = e')
    {u : V} {c : Γ.Walk u u} {e₁ : C} {γ₁ τ₁ : List (I × C)} (hQ₁ : F.Q e₁)
    (hl₁ : F.Lift c e₁ γ₁) (hτ₁ : IsJGallery X F.J' (galleryEnd e₁ γ₁) τ₁)
    (hτ₁e : galleryEnd (galleryEnd e₁ γ₁) τ₁ = e₁) (hh : HomotopicOn X 𝒥 e₁ (γ₁ ++ τ₁) []) :
    FibreNullOn F 𝒥 c := by
  intro e γ hQ hl
  obtain ⟨τ, hτ, hτe⟩ := hconn hQ₁ hQ (hl₁.start_eq.trans hl.start_eq.symm)
  obtain ⟨τ', hτ', hτ'e, hh'⟩ := R.lift_unique hQ₁ hQ hl₁ hl hτ hτe
  have hrev₁ : IsJGallery X F.J' e₁ (galleryReverse (galleryEnd e₁ γ₁) τ₁) := by
    have := hτ₁.reverse
    rwa [hτ₁e] at this
  have hrev₁e : galleryEnd e₁ (galleryReverse (galleryEnd e₁ γ₁) τ₁) = galleryEnd e₁ γ₁ := by
    have := galleryEnd_galleryReverse (galleryEnd e₁ γ₁) τ₁
    rwa [hτ₁e] at this
  have hrev : IsJGallery X F.J' e (galleryReverse e₁ τ) := by
    have := hτ.reverse
    rwa [hτe] at this
  have hreve : galleryEnd e (galleryReverse e₁ τ) = e₁ := by
    have := galleryEnd_galleryReverse e₁ τ
    rwa [hτe] at this
  have hγ₁ : HomotopicOn X 𝒥 e₁ γ₁ (galleryReverse (galleryEnd e₁ γ₁) τ₁) := by
    have h1 := HomotopicOn.append_right hh (galleryReverse (galleryEnd e₁ γ₁) τ₁)
    have h2 := HomotopicOn.append_left (X := X) (x := e₁) γ₁
      (HomotopicOn.of_twoHomotopic R.two (twoHomotopic_append_reverse (X := X) hτ₁.1))
    simp only [List.append_assoc, List.nil_append, List.append_nil] at h1 h2
    exact HomotopicOn.trans (HomotopicOn.symm h2) h1
  have hτσ : HomotopicOn X 𝒥 e₁ (τ ++ γ) (galleryReverse (galleryEnd e₁ γ₁) τ₁ ++ τ') :=
    HomotopicOn.trans hh' (HomotopicOn.append_right hγ₁ τ')
  refine ⟨galleryReverse e₁ τ ++ (galleryReverse (galleryEnd e₁ γ₁) τ₁ ++ τ'), ?_, ?_, ?_⟩
  · refine hrev.append ?_
    rw [hreve]
    refine hrev₁.append ?_
    rw [hrev₁e]
    exact hτ'
  · rw [galleryEnd_append, hreve, galleryEnd_append, hrev₁e, hτ'e]
  · have h1 : HomotopicOn X 𝒥 e (galleryReverse e₁ τ ++ τ) [] := by
      have := HomotopicOn.of_twoHomotopic R.two (twoHomotopic_reverse_append (X := X) hτ.1)
      rwa [hτe] at this
    have h2 := HomotopicOn.append_right h1 γ
    have h3 : HomotopicOn X 𝒥 e (galleryReverse e₁ τ ++ (τ ++ γ))
        (galleryReverse e₁ τ ++ (galleryReverse (galleryEnd e₁ γ₁) τ₁ ++ τ')) := by
      refine HomotopicOn.append_left (X := X) (x := e) (galleryReverse e₁ τ) ?_
      rw [hreve]
      exact hτσ
    simp only [List.append_assoc, List.nil_append] at h2 h3
    exact HomotopicOn.trans (HomotopicOn.symm h2) h3

theorem RigidOn.lift_homotopic (R : RigidOn F 𝒥) {E : ∀ x : V, Set (Γ.Walk x x)}
    (hE : ∀ (x : V) (c : Γ.Walk x x), c ∈ E x → FibreNullOn F 𝒥 c)
    (hlift : ∀ {e : C} {x' : V}, F.Q e → Γ.Adj (F.P e) x' →
      ∃ (ρ : List (I × C)) (f : C), IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
        F.P f = x' ∧ F.Q f)
    {u v : V} {w w' : Γ.Walk u v} (h : CycleHomotopic E w w') :
    ∀ {e₀ : C} {γ γ' : List (I × C)}, F.Q e₀ → F.Lift w e₀ γ → F.Lift w' e₀ γ' →
      ∃ τ : List (I × C), IsJGallery X F.J' (galleryEnd e₀ γ) τ ∧
        galleryEnd (galleryEnd e₀ γ) τ = galleryEnd e₀ γ' ∧ HomotopicOn X 𝒥 e₀ (γ ++ τ) γ' := by
  refine CycleHomotopic.induction (R := fun a b => ∀ {e₀ : C} {γ γ' : List (I × C)}, F.Q e₀ →
    F.Lift a e₀ γ → F.Lift b e₀ γ' → ∃ τ : List (I × C), IsJGallery X F.J' (galleryEnd e₀ γ) τ ∧
      galleryEnd (galleryEnd e₀ γ) τ = galleryEnd e₀ γ' ∧ HomotopicOn X 𝒥 e₀ (γ ++ τ) γ') h
    ?_ ?_ ?_ ?_
  · intro a b hab e₀ γ γ' hQ hl hl'
    cases hab with
    | backtrack p q hadj =>
      exact R.lift_insert (m := .cons hadj (.cons hadj.symm .nil)) (R.fibreNull_backtrack hadj)
        hQ hl (by simpa using hl')
    | elem p q c hc => exact R.lift_insert (hE _ c hc) hQ hl hl'
  · intro a e₀ γ γ' hQ hl hl'
    obtain ⟨τ', hτ', hτ'e, hh⟩ := R.lift_unique hQ hQ hl hl' IsJGallery.nil rfl
    exact ⟨τ', hτ', hτ'e, by simpa using HomotopicOn.symm hh⟩
  · intro a b hab e₀ γ γ' hQ hl hl'
    obtain ⟨τ, hτ, hτe, hh⟩ := hab hQ hl' hl
    refine ⟨galleryReverse (galleryEnd e₀ γ') τ, ?_, ?_, ?_⟩
    · have := hτ.reverse
      rwa [hτe] at this
    · have := galleryEnd_galleryReverse (galleryEnd e₀ γ') τ
      rwa [hτe] at this
    · have h1 := HomotopicOn.append_right (HomotopicOn.symm hh)
        (galleryReverse (galleryEnd e₀ γ') τ)
      have h2 := HomotopicOn.append_left (X := X) (x := e₀) γ'
        (HomotopicOn.of_twoHomotopic R.two (twoHomotopic_append_reverse (X := X) hτ.1))
      simp only [List.append_assoc, List.append_nil] at h1 h2
      exact HomotopicOn.trans h1 h2
  · intro a b c hab hbc e₀ γ γ'' hQ hl hl''
    obtain ⟨γ', hl'⟩ := F.exists_lift (D := fun _ => True)
      (fun {e x'} hQ _ _ hadj => hlift hQ hadj) b (fun _ _ => trivial) e₀ hQ hl.start_eq
    obtain ⟨τ₁, hτ₁, hτ₁e, hh₁⟩ := hab hQ hl hl'
    obtain ⟨τ₂, hτ₂, hτ₂e, hh₂⟩ := hbc hQ hl' hl''
    refine ⟨τ₁ ++ τ₂, ?_, ?_, ?_⟩
    · refine hτ₁.append ?_
      rw [hτ₁e]
      exact hτ₂
    · rw [galleryEnd_append, hτ₁e, hτ₂e]
    · rw [← List.append_assoc]
      exact HomotopicOn.trans (HomotopicOn.append_right hh₁ τ₂) hh₂

theorem RigidOn.homotopicOn_nil (R : RigidOn F 𝒥) {E : ∀ x : V, Set (Γ.Walk x x)}
    (hE : ∀ (x : V) (c : Γ.Walk x x), c ∈ E x → FibreNullOn F 𝒥 c)
    (hlift : ∀ {e : C} {x' : V}, F.Q e → Γ.Adj (F.P e) x' →
      ∃ (ρ : List (I × C)) (f : C), IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
        F.P f = x' ∧ F.Q f)
    (htriv : ∀ (x : V) (w : Γ.Walk x x), CycleHomotopic E w .nil)
    {e₀ : C} {γ : List (I × C)} (hQ : F.Q e₀) (hγ : IsJGallery X (insert F.a F.J') e₀ γ)
    (hend : galleryEnd e₀ γ = e₀) : HomotopicOn X 𝒥 e₀ γ [] := by
  obtain ⟨y, w, γ', hh, hl⟩ := F.exists_lift_of_gallery hQ hγ (F.P e₀) rfl
  have hend' : galleryEnd e₀ γ' = e₀ := (TwoHomotopic.galleryEnd_eq hh).symm.trans hend
  have hy : y = F.P e₀ := by
    rw [← hl.end_eq hQ, hend']
  subst hy
  obtain ⟨τ, hτ, hτe, hh'⟩ := R.lift_homotopic hE hlift (htriv _ w) hQ hl
    (show F.Lift (.nil : Γ.Walk (F.P e₀) (F.P e₀)) e₀ [] from ⟨rfl, IsJGallery.nil⟩)
  rw [hend'] at hτ hτe
  have h0 := R.null hQ hτ (by simpa using hτe)
  have h1 : HomotopicOn X 𝒥 e₀ (γ' ++ τ) (γ' ++ []) :=
    HomotopicOn.append_left (X := X) (x := e₀) γ' (by rw [hend']; exact h0)
  simp only [List.append_nil] at h1
  exact HomotopicOn.trans (HomotopicOn.of_twoHomotopic R.two hh)
    (HomotopicOn.trans (HomotopicOn.symm h1) hh')

end CFSG.ClassicalInvolution.Phan.Q3G
