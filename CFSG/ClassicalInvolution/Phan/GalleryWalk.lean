module

public import CFSG.Monster.B.Geometry.ChamberSystem
public import CFSG.ClassicalInvolution.Phan.Geometry.WalkHomotopy

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C V : Type*}

@[expose] def IsJGallery (X : ChamberSystem I C) (J : Set I) (e : C) (γ : List (I × C)) : Prop :=
  X.IsGallery e γ ∧ ∀ i ∈ galleryType γ, i ∈ J

namespace IsJGallery

variable {X : ChamberSystem I C} {J J₂ : Set I} {e f : C} {γ η : List (I × C)}

theorem nil : IsJGallery X J e [] := ⟨trivial, by simp⟩

theorem cons {i : I} (hi : i ∈ J) (hadj : X.adj i e f) (h : IsJGallery X J f γ) :
    IsJGallery X J e ((i, f) :: γ) :=
  ⟨⟨hadj, h.1⟩, by
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact hi
    · exact h.2 j hj⟩

theorem append (h : IsJGallery X J e γ) (h' : IsJGallery X J (galleryEnd e γ) η) :
    IsJGallery X J e (γ ++ η) :=
  ⟨h.1.append h'.1, by
    intro j hj
    rw [galleryType_append, List.mem_append] at hj
    exact hj.elim (h.2 j) (h'.2 j)⟩

theorem reverse (h : IsJGallery X J e γ) :
    IsJGallery X J (galleryEnd e γ) (galleryReverse e γ) :=
  ⟨h.1.reverse, by
    intro j hj
    rw [galleryType_galleryReverse, List.mem_reverse] at hj
    exact h.2 j hj⟩

theorem mono (hJ : J ⊆ J₂) (h : IsJGallery X J e γ) : IsJGallery X J₂ e γ :=
  ⟨h.1, fun j hj => hJ (h.2 j hj)⟩

theorem mem_residue (h : IsJGallery X J e γ) : galleryEnd e γ ∈ X.residue J e :=
  ⟨γ, h.1, h.2, rfl⟩

theorem of_append_left (h : IsJGallery X J e (γ ++ η)) : IsJGallery X J e γ :=
  ⟨h.1.of_append_left, fun j hj => h.2 j (by simp [galleryType_append, hj])⟩

theorem of_append_right (h : IsJGallery X J e (γ ++ η)) :
    IsJGallery X J (galleryEnd e γ) η :=
  ⟨h.1.of_append_right, fun j hj => h.2 j (by simp [galleryType_append, hj])⟩

theorem append_iff : IsJGallery X J e (γ ++ η) ↔
    IsJGallery X J e γ ∧ IsJGallery X J (galleryEnd e γ) η :=
  ⟨fun h => ⟨h.of_append_left, h.of_append_right⟩, fun h => h.1.append h.2⟩

end IsJGallery

theorem mem_residue_iff_exists_isJGallery {X : ChamberSystem I C} {J : Set I} {e f : C} :
    f ∈ X.residue J e ↔ ∃ γ, IsJGallery X J e γ ∧ galleryEnd e γ = f :=
  ⟨fun ⟨γ, h1, h2, h3⟩ => ⟨γ, ⟨h1, h2⟩, h3⟩, fun ⟨γ, h, h3⟩ => ⟨γ, h.1, h.2, h3⟩⟩

variable {X : ChamberSystem I C} {Γ : SimpleGraph V}

variable (X Γ) in
structure Fib where
  P : C → V
  a : I
  J' : Set I
  Q : C → Prop
  step_Q : ∀ {i : I} {e f : C}, i ∈ insert a J' → X.adj i e f → Q e → Q f
  step_P : ∀ {i : I} {e f : C}, i ∈ J' → X.adj i e f → Q e → P e = P f
  step_a : ∀ {e f : C}, X.adj a e f → Q e → e = f ∨ Γ.Adj (P e) (P f)

namespace Fib

variable (F : Fib X Γ)

@[expose] def Lift : ∀ {x y : V}, Γ.Walk x y → C → List (I × C) → Prop
  | x, _, .nil, e, γ => F.P e = x ∧ IsJGallery X F.J' e γ
  | x, _, .cons _ w, e, γ =>
      F.P e = x ∧ ∃ (ρ : List (I × C)) (f : C) (δ : List (I × C)),
        γ = ρ ++ (F.a, f) :: δ ∧ IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
          Lift w f δ

variable {F}

theorem lift_nil_iff {x : V} {e : C} {γ : List (I × C)} :
    F.Lift (.nil : Γ.Walk x x) e γ ↔ F.P e = x ∧ IsJGallery X F.J' e γ := Iff.rfl

theorem lift_cons_iff {x x' y : V} (h : Γ.Adj x x') (w : Γ.Walk x' y) {e : C}
    {γ : List (I × C)} :
    F.Lift (.cons h w) e γ ↔ F.P e = x ∧ ∃ (ρ : List (I × C)) (f : C) (δ : List (I × C)),
        γ = ρ ++ (F.a, f) :: δ ∧ IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
          F.Lift w f δ := Iff.rfl

theorem Lift.start_eq {x y : V} {w : Γ.Walk x y} {e : C} {γ : List (I × C)}
    (h : F.Lift w e γ) : F.P e = x := by
  cases w with
  | nil => exact h.1
  | cons _ _ => exact h.1

theorem Lift.isJGallery {x y : V} {w : Γ.Walk x y} {e : C} {γ : List (I × C)}
    (h : F.Lift w e γ) : IsJGallery X (insert F.a F.J') e γ := by
  induction w generalizing e γ with
  | nil => exact h.2.mono (Set.subset_insert _ _)
  | cons hxy w ih =>
    obtain ⟨-, ρ, f, δ, rfl, hρ, hadj, hδ⟩ := h
    refine (hρ.mono (Set.subset_insert _ _)).append ?_
    exact IsJGallery.cons (Set.mem_insert _ _) hadj (ih hδ)

theorem Q_galleryEnd {e : C} {γ : List (I × C)} (hQ : F.Q e)
    (h : IsJGallery X (insert F.a F.J') e γ) : F.Q (galleryEnd e γ) := by
  induction γ generalizing e with
  | nil => exact hQ
  | cons p γ ih =>
    obtain ⟨⟨hadj, hγ⟩, hJ⟩ := h
    exact ih (F.step_Q (hJ p.1 (by simp)) hadj hQ) ⟨hγ, fun j hj => hJ j (by simp [hj])⟩

theorem Lift.Q_galleryEnd {x y : V} {w : Γ.Walk x y} {e : C} {γ : List (I × C)}
    (hQ : F.Q e) (h : F.Lift w e γ) : F.Q (galleryEnd e γ) :=
  F.Q_galleryEnd hQ h.isJGallery

theorem P_galleryEnd {e : C} {γ : List (I × C)} (hQ : F.Q e) (h : IsJGallery X F.J' e γ) :
    F.P (galleryEnd e γ) = F.P e := by
  induction γ generalizing e with
  | nil => rfl
  | cons p γ ih =>
    obtain ⟨⟨hadj, hγ⟩, hJ⟩ := h
    have hi : p.1 ∈ F.J' := hJ p.1 (by simp)
    rw [galleryEnd_cons, ih (F.step_Q (Set.mem_insert_of_mem _ hi) hadj hQ)
      ⟨hγ, fun j hj => hJ j (by simp [hj])⟩]
    exact (F.step_P hi hadj hQ).symm

theorem Lift.end_eq {x y : V} {w : Γ.Walk x y} {e : C} {γ : List (I × C)}
    (hQ : F.Q e) (h : F.Lift w e γ) : F.P (galleryEnd e γ) = y := by
  induction w generalizing e γ with
  | nil => rw [F.P_galleryEnd hQ h.2, h.1]
  | cons hxy w ih =>
    obtain ⟨-, ρ, f, δ, rfl, hρ, hadj, hδ⟩ := h
    have hQρ : F.Q (galleryEnd e ρ) :=
      F.Q_galleryEnd hQ (hρ.mono (Set.subset_insert _ _))
    have hQf : F.Q f := F.step_Q (Set.mem_insert _ _) hadj hQρ
    rw [galleryEnd_append, galleryEnd_cons]
    exact ih hQf hδ

theorem Lift.prepend_fibre {x y : V} {q : Γ.Walk x y} {e : C} {ρ δ : List (I × C)}
    (hρ : IsJGallery X F.J' e ρ) (hPe : F.P e = x) (h : F.Lift q (galleryEnd e ρ) δ) :
    F.Lift q e (ρ ++ δ) := by
  cases q with
  | nil => exact ⟨hPe, hρ.append h.2⟩
  | cons hxy q =>
    obtain ⟨-, ρ', f, δ', rfl, hρ', hadj, hδ'⟩ := h
    refine ⟨hPe, ρ ++ ρ', f, δ', by simp, hρ.append hρ', ?_, hδ'⟩
    rw [galleryEnd_append]
    exact hadj

theorem Lift.fibre_cons {x y : V} {w : Γ.Walk x y} {i : I} {e f : C} {γ : List (I × C)}
    (hi : i ∈ F.J') (hadj : X.adj i e f) (hPe : F.P e = x) (h : F.Lift w f γ) :
    F.Lift w e ((i, f) :: γ) :=
  Lift.prepend_fibre (ρ := [(i, f)]) (IsJGallery.cons hi hadj IsJGallery.nil) hPe h

theorem Lift.append {x u y : V} {p : Γ.Walk x u} {q : Γ.Walk u y} {e : C}
    {γ₁ γ₂ : List (I × C)} (hp : F.Lift p e γ₁) (hq : F.Lift q (galleryEnd e γ₁) γ₂) :
    F.Lift (p.append q) e (γ₁ ++ γ₂) := by
  induction p generalizing e γ₁ with
  | nil => exact Lift.prepend_fibre hp.2 hp.1 hq
  | cons hxy p ih =>
    obtain ⟨hPe, ρ, f, δ, rfl, hρ, hadj, hδ⟩ := hp
    refine ⟨hPe, ρ, f, δ ++ γ₂, by simp, hρ, hadj, ih hδ ?_⟩
    rw [galleryEnd_append, galleryEnd_cons] at hq
    exact hq

theorem Lift.of_append {x u y : V} {p : Γ.Walk x u} {q : Γ.Walk u y} {e : C}
    {γ : List (I × C)} (h : F.Lift (p.append q) e γ) :
    ∃ γ₁ γ₂ : List (I × C), γ = γ₁ ++ γ₂ ∧ F.Lift p e γ₁ ∧ F.Lift q (galleryEnd e γ₁) γ₂ := by
  induction p generalizing e γ with
  | nil =>
    exact ⟨[], γ, rfl, ⟨h.start_eq, IsJGallery.nil⟩, h⟩
  | cons hxy p ih =>
    obtain ⟨hPe, ρ, f, δ, rfl, hρ, hadj, hδ⟩ := h
    obtain ⟨δ₁, δ₂, rfl, h₁, h₂⟩ := ih hδ
    refine ⟨ρ ++ (F.a, f) :: δ₁, δ₂, by simp, ⟨hPe, ρ, f, δ₁, rfl, hρ, hadj, h₁⟩, ?_⟩
    rw [galleryEnd_append, galleryEnd_cons]
    exact h₂

theorem Lift.mono {F' : Fib X Γ} (hP : F.P = F'.P) (ha : F.a = F'.a) (hJ : F.J' ⊆ F'.J')
    {x y : V} {w : Γ.Walk x y} {e : C} {γ : List (I × C)} (h : F.Lift w e γ) :
    F'.Lift w e γ := by
  induction w generalizing e γ with
  | nil => exact ⟨by rw [← hP]; exact h.1, h.2.mono hJ⟩
  | cons hxy w ih =>
    obtain ⟨hPe, ρ, f, δ, rfl, hρ, hadj, hδ⟩ := h
    exact ⟨by rw [← hP]; exact hPe, ρ, f, δ, by rw [← ha], hρ.mono hJ, by rw [← ha]; exact hadj,
      ih hδ⟩

theorem exists_lift {D : V → Prop}
    (hlift : ∀ {e : C} {x' : V}, F.Q e → D (F.P e) → D x' → Γ.Adj (F.P e) x' →
      ∃ (ρ : List (I × C)) (f : C), IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
        F.P f = x' ∧ F.Q f)
    {x y : V} (w : Γ.Walk x y) (hw : ∀ v ∈ w.support, D v) :
    ∀ e : C, F.Q e → F.P e = x → ∃ γ : List (I × C), F.Lift w e γ := by
  induction w with
  | nil => exact fun e _ he => ⟨[], he, IsJGallery.nil⟩
  | @cons u v z hxy w ih =>
    intro e hQ he
    have hx : D u := hw u (by simp)
    have hx' : D v := hw v (by simp [SimpleGraph.Walk.support_cons])
    obtain ⟨ρ, f, hρ, hadj, hPf, hQf⟩ := hlift hQ (he ▸ hx) hx' (he ▸ hxy)
    obtain ⟨δ, hδ⟩ := ih (fun v hv => hw v (by simp [hv])) f hQf hPf
    exact ⟨ρ ++ (F.a, f) :: δ, he, ρ, f, δ, rfl, hρ, hadj, hδ⟩

theorem exists_lift_of_gallery :
    ∀ {γ : List (I × C)} {e : C}, F.Q e → IsJGallery X (insert F.a F.J') e γ →
      ∀ x : V, F.P e = x → ∃ (y : V) (w : Γ.Walk x y) (γ' : List (I × C)),
        X.TwoHomotopic e γ γ' ∧ F.Lift w e γ' := by
  intro γ
  induction γ with
  | nil =>
    intro e _ _ x hx
    exact ⟨x, .nil, [], TwoHomotopic.refl _, hx, IsJGallery.nil⟩
  | cons p γ ih =>
    intro e hQ h x hx
    obtain ⟨i, f⟩ := p
    obtain ⟨⟨hadj, hγ⟩, hJ⟩ := h
    have hi : i ∈ insert F.a F.J' := hJ i (by simp)
    have hγ' : IsJGallery X (insert F.a F.J') f γ := ⟨hγ, fun j hj => hJ j (by simp [hj])⟩
    have hQf : F.Q f := F.step_Q hi hadj hQ
    by_cases hiJ : i ∈ F.J'
    · obtain ⟨y, w, γ', hh, hl⟩ := ih hQf hγ' x ((F.step_P hiJ hadj hQ).symm.trans hx)
      exact ⟨y, w, (i, f) :: γ', TwoHomotopic.append_left (X := X) (x := e) [(i, f)] hh,
        Lift.fibre_cons hiJ hadj hx hl⟩
    · have hia : i = F.a := (Set.mem_insert_iff.mp hi).resolve_right hiJ
      subst hia
      rcases F.step_a hadj hQ with rfl | hΓ
      · obtain ⟨y, w, γ', hh, hl⟩ := ih hQ hγ' x hx
        refine ⟨y, w, γ', ?_, hl⟩
        have h0 := twoHomotopic_constant (X := X) (x := e) [] γ F.a
        simp only [galleryEnd_nil, List.nil_append] at h0
        exact h0.trans hh
      · rw [hx] at hΓ
        obtain ⟨y, w, γ', hh, hl⟩ := ih hQf hγ' (F.P f) rfl
        exact ⟨y, .cons hΓ w, (F.a, f) :: γ',
          TwoHomotopic.append_left (X := X) (x := e) [(F.a, f)] hh,
          hx, [], f, γ', rfl, IsJGallery.nil, hadj, hl⟩

variable (F) in
structure Rigid : Prop where
  null : ∀ {e : C} {γ : List (I × C)}, F.Q e → IsJGallery X F.J' e γ → galleryEnd e γ = e →
    X.TwoHomotopic e γ []
  edge : ∀ {e e' f f' : C} {ρ ρ' : List (I × C)} {x' : V}, F.Q e → F.Q e' → F.P e = F.P e' →
    Γ.Adj (F.P e) x' → IsJGallery X F.J' e ρ → X.adj F.a (galleryEnd e ρ) f → F.P f = x' →
    IsJGallery X F.J' e' ρ' → X.adj F.a (galleryEnd e' ρ') f' → F.P f' = x' →
    ∃ τ τ' : List (I × C), IsJGallery X F.J' e τ ∧ galleryEnd e τ = e' ∧
      IsJGallery X F.J' f τ' ∧ galleryEnd f τ' = f' ∧
      X.TwoHomotopic e (τ ++ ρ' ++ [(F.a, f')]) (ρ ++ (F.a, f) :: τ')

theorem Rigid.fib_unique (R : F.Rigid) {e : C} {τ₁ τ₂ : List (I × C)} (hQ : F.Q e)
    (h₁ : IsJGallery X F.J' e τ₁) (h₂ : IsJGallery X F.J' e τ₂)
    (hend : galleryEnd e τ₁ = galleryEnd e τ₂) : X.TwoHomotopic e τ₁ τ₂ := by
  have h₂' : IsJGallery X F.J' (galleryEnd e τ₁) (galleryReverse e τ₂) := by
    rw [hend]
    exact h₂.reverse
  have hc : IsJGallery X F.J' e (τ₁ ++ galleryReverse e τ₂) := h₁.append h₂'
  have hend' : galleryEnd e (τ₁ ++ galleryReverse e τ₂) = e := by
    rw [galleryEnd_append, hend, galleryEnd_galleryReverse]
  have h0 := R.null hQ hc hend'
  have hrev : X.TwoHomotopic (galleryEnd e τ₁) (galleryReverse e τ₂ ++ τ₂) [] := by
    rw [hend]
    exact twoHomotopic_reverse_append h₂.1
  have h1 := TwoHomotopic.append_left (X := X) (x := e) τ₁ hrev
  have h2 := h0.append_right τ₂
  simp only [List.nil_append, List.append_assoc, List.append_nil] at h1 h2
  exact h1.symm.trans h2

theorem Rigid.lift_unique (R : F.Rigid) {x y : V} {w : Γ.Walk x y} :
    ∀ {e e₂ : C} {γ γ' τ : List (I × C)}, F.Q e → F.Q e₂ → F.Lift w e γ → F.Lift w e₂ γ' →
      IsJGallery X F.J' e τ → galleryEnd e τ = e₂ →
      ∃ τ' : List (I × C), IsJGallery X F.J' (galleryEnd e γ) τ' ∧
        galleryEnd (galleryEnd e γ) τ' = galleryEnd e₂ γ' ∧
        X.TwoHomotopic e (τ ++ γ') (γ ++ τ') := by
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
    · have h1 := (twoHomotopic_append_reverse hl.2.1).append_right (τ ++ γ')
      simp only [List.nil_append, List.append_assoc] at h1
      exact h1.symm
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
    have hττ₀ : X.TwoHomotopic e τ τ₀ := R.fib_unique hQ hτ hτ₀ (by rw [hτe, hτ₀e])
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
      have h1 : X.TwoHomotopic e ((τ ++ ρ' ++ [(F.a, f')]) ++ δ')
          ((τ₀ ++ ρ' ++ [(F.a, f')]) ++ δ') :=
        ((hττ₀.append_right ρ').append_right [(F.a, f')]).append_right δ'
      have h2 := hhom.append_right δ'
      rw [e2] at h2
      have h3 : X.TwoHomotopic e ((ρ ++ [(F.a, f)]) ++ (τ₀' ++ δ'))
          ((ρ ++ [(F.a, f)]) ++ (δ ++ τ'')) := by
        refine TwoHomotopic.append_left (X := X) (x := e) (ρ ++ [(F.a, f)]) ?_
        have : galleryEnd e (ρ ++ [(F.a, f)]) = f := by simp
        rw [this]
        exact hhom'
      exact h1.trans (h2.trans h3)

variable (F) in
@[expose] def FibreNull {u : V} (m : Γ.Walk u u) : Prop :=
  ∀ (e : C) (γ : List (I × C)), F.Q e → F.Lift m e γ →
    ∃ τ : List (I × C), IsJGallery X F.J' e τ ∧ galleryEnd e τ = galleryEnd e γ ∧
      X.TwoHomotopic e γ τ

theorem Rigid.lift_insert (R : F.Rigid) {x u y : V} {p : Γ.Walk x u} {q : Γ.Walk u y}
    {m : Γ.Walk u u} (hm : F.FibreNull m) {e₀ : C} {γ γ' : List (I × C)} (hQ : F.Q e₀)
    (hl : F.Lift (p.append q) e₀ γ) (hl' : F.Lift (p.append (m.append q)) e₀ γ') :
    ∃ τ : List (I × C), IsJGallery X F.J' (galleryEnd e₀ γ) τ ∧
      galleryEnd (galleryEnd e₀ γ) τ = galleryEnd e₀ γ' ∧ X.TwoHomotopic e₀ (γ ++ τ) γ' := by
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
    have hA := (hh₁.append hh₂).append_right γq'
    have hB := TwoHomotopic.append_left (X := X) (x := e₀) γp hh₃
    simp only [List.append_assoc] at hA hB ⊢
    exact (hA.trans hB).symm

theorem Rigid.fibreNull_backtrack (R : F.Rigid) {u v : V} (h : Γ.Adj u v) :
    F.FibreNull (.cons h (.cons h.symm .nil)) := by
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
    have h1 : X.TwoHomotopic e ((ρ₁ ++ [(F.a, f₁)]) ++ δ)
        ((ρ₁ ++ [(F.a, f₁)]) ++ ((F.a, galleryEnd e ρ₁) :: (galleryReverse e ρ₁ ++ τ'))) := by
      refine TwoHomotopic.append_left (X := X) (x := e) (ρ₁ ++ [(F.a, f₁)]) ?_
      have : galleryEnd e (ρ₁ ++ [(F.a, f₁)]) = f₁ := by simp
      rw [this]
      simpa using hh
    have h2 := twoHomotopic_backtrack (X := X) (x := e) ρ₁ (galleryReverse e ρ₁ ++ τ') hadj₁
    have h3 := (twoHomotopic_append_reverse (X := X) hρ₁.1).append_right τ'
    have e1 : ρ₁ ++ (F.a, f₁) :: δ = (ρ₁ ++ [(F.a, f₁)]) ++ δ := by simp
    have e2 : (ρ₁ ++ [(F.a, f₁)]) ++ ((F.a, galleryEnd e ρ₁) :: (galleryReverse e ρ₁ ++ τ')) =
        ρ₁ ++ [(F.a, f₁), (F.a, galleryEnd e ρ₁)] ++ (galleryReverse e ρ₁ ++ τ') := by simp
    rw [e1]
    refine h1.trans ?_
    rw [e2]
    refine h2.trans ?_
    simpa using h3

theorem Rigid.fibreNull_of_exists (R : F.Rigid)
    (hconn : ∀ {e e' : C}, F.Q e → F.Q e' → F.P e = F.P e' →
      ∃ τ : List (I × C), IsJGallery X F.J' e τ ∧ galleryEnd e τ = e')
    {u : V} {c : Γ.Walk u u} {e₁ : C} {γ₁ τ₁ : List (I × C)} (hQ₁ : F.Q e₁)
    (hl₁ : F.Lift c e₁ γ₁) (hτ₁ : IsJGallery X F.J' (galleryEnd e₁ γ₁) τ₁)
    (hτ₁e : galleryEnd (galleryEnd e₁ γ₁) τ₁ = e₁) (hh : X.TwoHomotopic e₁ (γ₁ ++ τ₁) []) :
    F.FibreNull c := by
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
  have hγ₁ : X.TwoHomotopic e₁ γ₁ (galleryReverse (galleryEnd e₁ γ₁) τ₁) := by
    have h1 := hh.append_right (galleryReverse (galleryEnd e₁ γ₁) τ₁)
    have h2 := TwoHomotopic.append_left (X := X) (x := e₁) γ₁
      (twoHomotopic_append_reverse (X := X) hτ₁.1)
    simp only [List.append_assoc, List.nil_append, List.append_nil] at h1 h2
    exact h2.symm.trans h1
  have hτσ : X.TwoHomotopic e₁ (τ ++ γ) (galleryReverse (galleryEnd e₁ γ₁) τ₁ ++ τ') :=
    hh'.trans (hγ₁.append_right τ')
  refine ⟨galleryReverse e₁ τ ++ (galleryReverse (galleryEnd e₁ γ₁) τ₁ ++ τ'), ?_, ?_, ?_⟩
  · refine hrev.append ?_
    rw [hreve]
    refine hrev₁.append ?_
    rw [hrev₁e]
    exact hτ'
  · rw [galleryEnd_append, hreve, galleryEnd_append, hrev₁e, hτ'e]
  · have h1 : X.TwoHomotopic e (galleryReverse e₁ τ ++ τ) [] := by
      have := twoHomotopic_reverse_append (X := X) hτ.1
      rwa [hτe] at this
    have h2 := h1.append_right γ
    have h3 : X.TwoHomotopic e (galleryReverse e₁ τ ++ (τ ++ γ))
        (galleryReverse e₁ τ ++ (galleryReverse (galleryEnd e₁ γ₁) τ₁ ++ τ')) := by
      refine TwoHomotopic.append_left (X := X) (x := e) (galleryReverse e₁ τ) ?_
      rw [hreve]
      exact hτσ
    simp only [List.append_assoc, List.nil_append] at h2 h3
    exact h2.symm.trans h3

theorem Rigid.lift_homotopic (R : F.Rigid) {E : ∀ x : V, Set (Γ.Walk x x)}
    (hE : ∀ (x : V) (c : Γ.Walk x x), c ∈ E x → F.FibreNull c)
    (hlift : ∀ {e : C} {x' : V}, F.Q e → Γ.Adj (F.P e) x' →
      ∃ (ρ : List (I × C)) (f : C), IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
        F.P f = x' ∧ F.Q f)
    {u v : V} {w w' : Γ.Walk u v} (h : CycleHomotopic E w w') :
    ∀ {e₀ : C} {γ γ' : List (I × C)}, F.Q e₀ → F.Lift w e₀ γ → F.Lift w' e₀ γ' →
      ∃ τ : List (I × C), IsJGallery X F.J' (galleryEnd e₀ γ) τ ∧
        galleryEnd (galleryEnd e₀ γ) τ = galleryEnd e₀ γ' ∧ X.TwoHomotopic e₀ (γ ++ τ) γ' := by
  refine CycleHomotopic.induction (R := fun a b => ∀ {e₀ : C} {γ γ' : List (I × C)}, F.Q e₀ →
    F.Lift a e₀ γ → F.Lift b e₀ γ' → ∃ τ : List (I × C), IsJGallery X F.J' (galleryEnd e₀ γ) τ ∧
      galleryEnd (galleryEnd e₀ γ) τ = galleryEnd e₀ γ' ∧ X.TwoHomotopic e₀ (γ ++ τ) γ') h
    ?_ ?_ ?_ ?_
  · intro a b hab e₀ γ γ' hQ hl hl'
    cases hab with
    | backtrack p q hadj =>
      exact R.lift_insert (m := .cons hadj (.cons hadj.symm .nil)) (R.fibreNull_backtrack hadj)
        hQ hl (by simpa using hl')
    | elem p q c hc => exact R.lift_insert (hE _ c hc) hQ hl hl'
  · intro a e₀ γ γ' hQ hl hl'
    obtain ⟨τ', hτ', hτ'e, hh⟩ := R.lift_unique hQ hQ hl hl' IsJGallery.nil rfl
    exact ⟨τ', hτ', hτ'e, by simpa using hh.symm⟩
  · intro a b hab e₀ γ γ' hQ hl hl'
    obtain ⟨τ, hτ, hτe, hh⟩ := hab hQ hl' hl
    refine ⟨galleryReverse (galleryEnd e₀ γ') τ, ?_, ?_, ?_⟩
    · have := hτ.reverse
      rwa [hτe] at this
    · have := galleryEnd_galleryReverse (galleryEnd e₀ γ') τ
      rwa [hτe] at this
    · have h1 := hh.symm.append_right (galleryReverse (galleryEnd e₀ γ') τ)
      have h2 := TwoHomotopic.append_left (X := X) (x := e₀) γ'
        (twoHomotopic_append_reverse (X := X) hτ.1)
      simp only [List.append_assoc, List.append_nil] at h1 h2
      exact h1.trans h2
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
      exact (TwoHomotopic.append_right hh₁ τ₂).trans hh₂

theorem Rigid.twoHomotopic_nil (R : F.Rigid) {E : ∀ x : V, Set (Γ.Walk x x)}
    (hE : ∀ (x : V) (c : Γ.Walk x x), c ∈ E x → F.FibreNull c)
    (hlift : ∀ {e : C} {x' : V}, F.Q e → Γ.Adj (F.P e) x' →
      ∃ (ρ : List (I × C)) (f : C), IsJGallery X F.J' e ρ ∧ X.adj F.a (galleryEnd e ρ) f ∧
        F.P f = x' ∧ F.Q f)
    (htriv : ∀ (x : V) (w : Γ.Walk x x), CycleHomotopic E w .nil)
    {e₀ : C} {γ : List (I × C)} (hQ : F.Q e₀) (hγ : IsJGallery X (insert F.a F.J') e₀ γ)
    (hend : galleryEnd e₀ γ = e₀) : X.TwoHomotopic e₀ γ [] := by
  obtain ⟨y, w, γ', hh, hl⟩ := F.exists_lift_of_gallery hQ hγ (F.P e₀) rfl
  have hend' : galleryEnd e₀ γ' = e₀ := (hh.galleryEnd_eq).symm.trans hend
  have hy : y = F.P e₀ := by
    rw [← hl.end_eq hQ, hend']
  subst hy
  obtain ⟨τ, hτ, hτe, hh'⟩ := R.lift_homotopic hE hlift (htriv _ w) hQ hl
    (show F.Lift (.nil : Γ.Walk (F.P e₀) (F.P e₀)) e₀ [] from ⟨rfl, IsJGallery.nil⟩)
  rw [hend'] at hτ hτe
  have h0 := R.null hQ hτ (by simpa using hτe)
  have h1 : X.TwoHomotopic e₀ (γ' ++ τ) (γ' ++ []) :=
    TwoHomotopic.append_left (X := X) (x := e₀) γ' (by rw [hend']; exact h0)
  simp only [List.append_nil] at h1
  exact hh.trans (h1.symm.trans hh')

end Fib

end CFSG.ClassicalInvolution.Phan
