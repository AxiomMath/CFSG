module

public import CFSG.Geometry.GeneralizedQuadrangles.Hermitian.Tallini.Nets

public section

namespace CFSG.Geometry.GeneralizedQuadrangles

open SimpleGraph CFSG.Geometry.GeneralizedPolygons

universe u

variable {V : Type u}

section PaschF

variable {Γ : SimpleGraph V} [Fintype V] [DecidableRel Γ.Adj]

private theorem isStarPlane_of_mem_isPlaneBundle {c : Γ.Coloring (Fin 2)} {β : Set (Set V)}
    (hβ : IsPlaneBundle Γ c β) {X : Set V} (hX : X ∈ β) : IsStarPlane Γ c X := by
  rcases hβ with ⟨L, -, rfl⟩ | ⟨Y, y, -, -, rfl⟩
  · exact hX.1
  · exact hX.1

theorem inter_nonempty_of_subset_conjNet (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {W : Set V} (hW : IsStarPlane Γ c W) {β₁ β₂ : Set (Set V)} (h1 : IsPlaneBundle Γ c β₁)
    (h2 : IsPlaneBundle Γ c β₂) (hs1 : β₁ ⊆ conjNet Γ c W) (hs2 : β₂ ⊆ conjNet Γ c W) :
    (β₁ ∩ β₂).Nonempty := by
  classical
  have hs : 2 ≤ s := two_le_s hP hT c hdeg
  have hii' : TalliniCondPrime Γ c := talliniCondPrime_of_talliniCond hP hT c hdeg hreg hii
  have hWβ1 : W ∈ conjBundle Γ c β₁ := ⟨hW, fun X hX => (hs1 hX).2⟩
  have hWβ2 : W ∈ conjBundle Γ c β₂ := ⟨hW, fun X hX => (hs2 hX).2⟩
  have hb1 : IsPlaneBundle Γ c (conjBundle Γ c β₁) :=
    (conjBundle_conjBundle hP hT c hdeg hreg hst hii h1).1
  have hb2 : IsPlaneBundle Γ c (conjBundle Γ c β₂) :=
    (conjBundle_conjBundle hP hT c hdeg hreg hst hii h2).1
  by_cases heq : conjBundle Γ c β₁ = conjBundle Γ c β₂
  · have hβeq : β₁ = β₂ := by
      have h1' : conjBundle Γ c (conjBundle Γ c β₁) = β₁ :=
        (conjBundle_conjBundle hP hT c hdeg hreg hst hii h1).2
      have h2' : conjBundle Γ c (conjBundle Γ c β₂) = β₂ :=
        (conjBundle_conjBundle hP hT c hdeg hreg hst hii h2).2
      calc
        β₁ = conjBundle Γ c (conjBundle Γ c β₁) := h1'.symm
        _ = conjBundle Γ c (conjBundle Γ c β₂) := by rw [heq]
        _ = β₂ := h2'
    have hpos : 0 < β₂.ncard := by
      rw [ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii' h2]
      omega
    obtain ⟨X, hX⟩ := (Set.ncard_pos (s := β₂)).mp hpos
    rw [hβeq]
    exact ⟨X, hX, hX⟩
  · have hpos : 1 < (conjBundle Γ c β₁).ncard := by
      rw [ncard_of_isPlaneBundle hP hT c hdeg hreg hst hii' hb1]
      omega
    obtain ⟨W', hW'β1, hW'ne⟩ := Set.exists_ne_of_one_lt_ncard hpos W
    have hW'plane : IsStarPlane Γ c W' := hW'β1.1
    have hnot : W' ∉ conjBundle Γ c β₂ := by
      intro hW'β2
      obtain ⟨β, -, huniq⟩ :=
        existsUnique_isPlaneBundle hP hT c hdeg hreg hst hii' hW hW'plane (fun h => hW'ne h.symm)
      have e1 : conjBundle Γ c β₁ = β := huniq _ ⟨hb1, hWβ1, hW'β1⟩
      have e2 : conjBundle Γ c β₂ = β := huniq _ ⟨hb2, hWβ2, hW'β2⟩
      exact heq (e1.trans e2.symm)
    have he4 := ncard_inter_conjNet hP hT c hdeg hreg hst hii h2 hW'plane hnot
    obtain ⟨Z, hZ⟩ := Set.ncard_eq_one.mp he4
    have hZmem : Z ∈ β₂ ∩ conjNet Γ c W' := by rw [hZ]; exact Set.mem_singleton Z
    have hZβ2 : Z ∈ β₂ := hZmem.1
    have hZW' : Z ∈ conjNet Γ c W' := hZmem.2
    have hZW : Z ∈ conjNet Γ c W := hs2 hZβ2
    have he3 := conjNet_inter_conjNet hP hT c hdeg hreg hst hii hb1 hWβ1 hW'β1
      (fun h => hW'ne h.symm)
    have hcb : conjBundle Γ c (conjBundle Γ c β₁) = β₁ :=
      (conjBundle_conjBundle hP hT c hdeg hreg hst hii h1).2
    have hZboth : Z ∈ conjNet Γ c W ∩ conjNet Γ c W' := ⟨hZW, hZW'⟩
    rw [he3, hcb] at hZboth
    exact ⟨Z, hZboth, hZβ2⟩

theorem bundle_veblen (hP : IsGeneralizedPolygon Γ 4) (hT : IsThick Γ)
    (c : Γ.Coloring (Fin 2)) {s t : ℕ}
    (hdeg : ∀ v, Γ.degree v = if c v = 0 then t + 1 else s + 1)
    (hreg : ∀ x, c x = 0 → IsRegularVertex Γ x) (hst : s ≠ t) (hii : TalliniCond Γ c)
    {β β' γ₁ γ₂ : Set (Set V)} (hβ : IsPlaneBundle Γ c β) (hβ' : IsPlaneBundle Γ c β')
    (hγ₁ : IsPlaneBundle Γ c γ₁) (hγ₂ : IsPlaneBundle Γ c γ₂) (hββ' : (β ∩ β').Nonempty)
    {X₁ X₂ Y₁ Y₂ : Set V} (h1 : X₁ ∈ β) (h2 : X₂ ∈ β) (h1' : Y₁ ∈ β') (h2' : Y₂ ∈ β')
    (hne1 : X₁ ≠ Y₁) (hne2 : X₂ ≠ Y₂) (hγ1 : X₁ ∈ γ₁ ∧ Y₁ ∈ γ₁) (hγ2 : X₂ ∈ γ₂ ∧ Y₂ ∈ γ₂) :
    (γ₁ ∩ γ₂).Nonempty := by
  classical
  obtain ⟨X, hXβ, hXβ'⟩ := hββ'
  have hXplane : IsStarPlane Γ c X := isStarPlane_of_mem_isPlaneBundle hβ hXβ
  have hb1 : IsPlaneBundle Γ c (conjBundle Γ c β) :=
    (conjBundle_conjBundle hP hT c hdeg hreg hst hii hβ).1
  have hb2 : IsPlaneBundle Γ c (conjBundle Γ c β') :=
    (conjBundle_conjBundle hP hT c hdeg hreg hst hii hβ').1
  have hsub1 : conjBundle Γ c β ⊆ conjNet Γ c X := by
    intro Z hZ
    exact ⟨hZ.1, (isConjPlane_comm hP hT c hdeg hreg).mp (hZ.2 X hXβ)⟩
  have hsub2 : conjBundle Γ c β' ⊆ conjNet Γ c X := by
    intro Z hZ
    exact ⟨hZ.1, (isConjPlane_comm hP hT c hdeg hreg).mp (hZ.2 X hXβ')⟩
  obtain ⟨W', hW'⟩ :=
    inter_nonempty_of_subset_conjNet hP hT c hdeg hreg hst hii hXplane hb1 hb2 hsub1 hsub2
  have hW'β : W' ∈ conjBundle Γ c β := hW'.1
  have hW'β' : W' ∈ conjBundle Γ c β' := hW'.2
  have hW'plane : IsStarPlane Γ c W' := hW'β.1
  have hcX1 : IsConjPlane Γ c W' X₁ := hW'β.2 X₁ h1
  have hcX2 : IsConjPlane Γ c W' X₂ := hW'β.2 X₂ h2
  have hcY1 : IsConjPlane Γ c W' Y₁ := hW'β'.2 Y₁ h1'
  have hcY2 : IsConjPlane Γ c W' Y₂ := hW'β'.2 Y₂ h2'
  have hW'γ1 : W' ∈ conjBundle Γ c γ₁ :=
    mem_conjBundle_of_two hP hT c hdeg hreg hst hii hγ₁ hγ1.1 hγ1.2 hne1 hW'plane hcX1 hcY1
  have hW'γ2 : W' ∈ conjBundle Γ c γ₂ :=
    mem_conjBundle_of_two hP hT c hdeg hreg hst hii hγ₂ hγ2.1 hγ2.2 hne2 hW'plane hcX2 hcY2
  have hsubγ1 : γ₁ ⊆ conjNet Γ c W' := by
    intro Z hZ
    exact ⟨isStarPlane_of_mem_isPlaneBundle hγ₁ hZ, hW'γ1.2 Z hZ⟩
  have hsubγ2 : γ₂ ⊆ conjNet Γ c W' := by
    intro Z hZ
    exact ⟨isStarPlane_of_mem_isPlaneBundle hγ₂ hZ, hW'γ2.2 Z hZ⟩
  exact inter_nonempty_of_subset_conjNet hP hT c hdeg hreg hst hii hW'plane hγ₁ hγ₂
    hsubγ1 hsubγ2

end PaschF

end CFSG.Geometry.GeneralizedQuadrangles
