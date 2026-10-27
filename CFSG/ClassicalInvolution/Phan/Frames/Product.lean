module

public import CFSG.Monster.B.Geometry.ChamberSystem

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {I C : Type*} {X : ChamberSystem I C}

theorem mem_residue_induction {J : Set I} {c : C} (Q : C → Prop) (h0 : Q c)
    (hstep : ∀ (d e : C) (j : I), j ∈ J → Q d → X.adj j d e → Q e) :
    ∀ e ∈ X.residue J c, Q e := by
  have key : ∀ (γ : List (I × C)) (x : C), Q x → X.IsGallery x γ → (∀ i ∈ galleryType γ, i ∈ J) →
      Q (galleryEnd x γ) := by
    intro γ
    induction γ with
    | nil => exact fun x hx _ _ => hx
    | cons p γ ih =>
      intro x hx hγ hJ
      refine ih p.2 (hstep x p.2 p.1 (hJ p.1 (by simp)) hx hγ.1) hγ.2 fun i hi => hJ i ?_
      simp [hi]
  rintro e ⟨γ, hγ, hJ, rfl⟩
  exact key γ c h0 hγ hJ

variable (X) in
@[expose] def CommuteTypes (i j : I) : Prop :=
  ∀ x y z : C, X.adj i x y → X.adj j y z → ∃ y', X.adj j x y' ∧ X.adj i y' z

theorem pair_encard_le_two (i j : I) : ({i, j} : Set I).encard ≤ 2 := by
  have := Set.encard_insert_le ({j} : Set I) i
  rw [Set.encard_singleton] at this
  exact this.trans (by norm_num)

theorem exists_push {J₁ : Set I} {j : I} (hcomm : ∀ i ∈ J₁, CommuteTypes X j i) :
    ∀ (α : List (I × C)) (c x : C), X.adj j c x → X.IsGallery x α →
      (∀ i ∈ galleryType α, i ∈ J₁) →
      ∃ α' : List (I × C), X.IsGallery c α' ∧ (∀ i ∈ galleryType α', i ∈ J₁) ∧
        X.adj j (galleryEnd c α') (galleryEnd x α) ∧
        X.TwoHomotopic c ((j, x) :: α) (α' ++ [(j, galleryEnd x α)]) := by
  intro α
  induction α with
  | nil =>
    intro c x hcx _ _
    exact ⟨[], trivial, by simp, hcx, TwoHomotopic.refl _⟩
  | cons p α ih =>
    intro c x hcx hα hJ
    obtain ⟨hxw, hα⟩ := hα
    have hpi : p.1 ∈ J₁ := hJ p.1 (by simp)
    obtain ⟨u, hcu, huw⟩ := hcomm p.1 hpi c x p.2 hcx hxw
    obtain ⟨α', hα'g, hα'J, hα'end, hα'h⟩ := ih u p.2 huw hα
      (fun i hi => hJ i (by simp [hi]))
    refine ⟨(p.1, u) :: α', ⟨hcu, hα'g⟩, ?_, hα'end, ?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hpi
      · exact hα'J i hi
    · have h1 : X.TwoHomotopic c ((j, x) :: p :: α) ((p.1, u) :: (j, p.2) :: α) := by
        have := twoHomotopic_replace (X := X) (x := c) [] [(j, x), (p.1, p.2)]
          [(p.1, u), (j, p.2)] α (J := {j, p.1}) (pair_encard_le_two j p.1)
          (by simpa using ⟨hcx, hxw⟩) (by simpa using ⟨hcu, huw⟩) (by simp) (by simp) (by simp)
        simpa using this
      have h2 := TwoHomotopic.append_left (X := X) (x := c) [(p.1, u)] hα'h
      refine h1.trans ?_
      simpa using h2

theorem exists_sort {J₁ J₂ : Set I} (hcomm : ∀ j ∈ J₂, ∀ i ∈ J₁, CommuteTypes X j i) :
    ∀ (γ : List (I × C)) (c : C), X.IsGallery c γ → (∀ i ∈ galleryType γ, i ∈ J₁ ∨ i ∈ J₂) →
      ∃ α β : List (I × C), X.IsGallery c α ∧ (∀ i ∈ galleryType α, i ∈ J₁) ∧
        X.IsGallery (galleryEnd c α) β ∧ (∀ i ∈ galleryType β, i ∈ J₂) ∧
        X.TwoHomotopic c γ (α ++ β) := by
  intro γ
  induction γ with
  | nil =>
    intro c _ _
    exact ⟨[], [], trivial, by simp, trivial, by simp, TwoHomotopic.refl _⟩
  | cons p γ ih =>
    intro c hγ hJ
    obtain ⟨hcp, hγ⟩ := hγ
    obtain ⟨α', β', hα'g, hα'J, hβ'g, hβ'J, hh⟩ := ih p.2 hγ
      (fun i hi => hJ i (by simp [hi]))
    have h0 := TwoHomotopic.append_left (X := X) (x := c) [p] hh
    by_cases hp1 : p.1 ∈ J₁
    · refine ⟨p :: α', β', ⟨hcp, hα'g⟩, ?_, hβ'g, hβ'J, by simpa using h0⟩
      intro i hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hp1
      · exact hα'J i hi
    · have hp2 : p.1 ∈ J₂ := (hJ p.1 (by simp)).resolve_left hp1
      obtain ⟨α'', hα''g, hα''J, hα''end, hα''h⟩ :=
        exists_push (fun i hi => hcomm p.1 hp2 i hi) α' c p.2 hcp hα'g hα'J
      refine ⟨α'', (p.1, galleryEnd p.2 α') :: β', hα''g, hα''J, ⟨hα''end, hβ'g⟩, ?_, ?_⟩
      · intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hp2
        · exact hβ'J i hi
      · have h1 := hα''h.append_right β'
        have h2 : X.TwoHomotopic c (p :: γ) (p :: α' ++ β') := by simpa using h0
        refine h2.trans (h1.trans ?_)
        simp only [List.cons_append, List.append_assoc, List.nil_append]
        exact TwoHomotopic.refl _

theorem mem_residue_union_iff {J₁ J₂ : Set I} (hcomm : ∀ j ∈ J₂, ∀ i ∈ J₁, CommuteTypes X j i)
    {c e : C} :
    e ∈ X.residue (J₁ ∪ J₂) c ↔ ∃ f ∈ X.residue J₁ c, e ∈ X.residue J₂ f := by
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    obtain ⟨α, β, hαg, hαJ, hβg, hβJ, hh⟩ := exists_sort hcomm γ c hγ hJ
    refine ⟨galleryEnd c α, ⟨α, hαg, hαJ, rfl⟩, β, hβg, hβJ, ?_⟩
    rw [← galleryEnd_append, hh.galleryEnd_eq]
  · rintro ⟨f, hf, he⟩
    exact mem_residue_trans (residue_mono Set.subset_union_left c hf)
      (residue_mono Set.subset_union_right f he)

theorem twoHomotopic_nil_of_union {J₁ J₂ : Set I}
    (hcomm : ∀ j ∈ J₂, ∀ i ∈ J₁, CommuteTypes X j i)
    (hinter : ∀ c d : C, d ∈ X.residue J₁ c → d ∈ X.residue J₂ c → d = c)
    (h₁ : ∀ (c : C) (γ : List (I × C)), X.IsGallery c γ → (∀ i ∈ galleryType γ, i ∈ J₁) →
      galleryEnd c γ = c → X.TwoHomotopic c γ [])
    (h₂ : ∀ (c : C) (γ : List (I × C)), X.IsGallery c γ → (∀ i ∈ galleryType γ, i ∈ J₂) →
      galleryEnd c γ = c → X.TwoHomotopic c γ [])
    (c : C) (γ : List (I × C)) (hγ : X.IsGallery c γ)
    (hJ : ∀ i ∈ galleryType γ, i ∈ J₁ ∨ i ∈ J₂) (hend : galleryEnd c γ = c) :
    X.TwoHomotopic c γ [] := by
  obtain ⟨α, β, hαg, hαJ, hβg, hβJ, hh⟩ := exists_sort hcomm γ c hγ hJ
  have hend' : galleryEnd (galleryEnd c α) β = c := by
    rw [← galleryEnd_append, ← hh.galleryEnd_eq, hend]
  have hd1 : galleryEnd c α ∈ X.residue J₁ c := ⟨α, hαg, hαJ, rfl⟩
  have hd2 : galleryEnd c α ∈ X.residue J₂ c :=
    mem_residue_symm ⟨β, hβg, hβJ, hend'⟩
  have hdc : galleryEnd c α = c := hinter c _ hd1 hd2
  have hα0 := h₁ c α hαg hαJ hdc
  rw [hdc] at hβg hend'
  have hβ0 := h₂ c β hβg hβJ hend'
  refine hh.trans ?_
  have := hα0.append (δ := β) (δ' := []) (by rw [hdc]; exact hβ0)
  simpa using this

end CFSG.ClassicalInvolution.Phan
