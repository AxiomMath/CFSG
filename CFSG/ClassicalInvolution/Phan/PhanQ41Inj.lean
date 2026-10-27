module

public import CFSG.ClassicalInvolution.Phan.PhanQ40Cent

public section

namespace CFSG.ClassicalInvolution.PhanQ


open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalGroups.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg

section Lines

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G} {e' : Fin 3 → Fin 4} {ψ : Su K p f 4 →* G}

theorem nondeg_top_four (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) :
    Nondeg (unitaryInvolution K p f) (⊤ : Submodule K (Fin 4 → K)) := by
  have := (stdFrame (unitaryInvolution K p f) 4).nondeg_spanAt hσ Finset.univ
  rwa [(stdFrame (unitaryInvolution K p f) 4).spanAt_univ] at this

omit [Finite K] [CharP K p] in
theorem finrank_top_four : Module.finrank K (⊤ : Submodule K (Fin 4 → K)) = 4 := by
  rw [finrank_top]
  simp

theorem spanAt_posInt_zero_three (hσ : IsUnitaryInvolution (unitaryInvolution K p f))
    (c : Frame (unitaryInvolution K p f) 4) {a : ℕ} (ha : a = 0) :
    c.spanAt (posInt 3 a 3) = ⊤ := by
  have : posInt 3 a 3 = Finset.univ := by
    ext k
    simp only [mem_posInt, Finset.mem_univ, iff_true]
    have := k.2
    omega
  rw [this, c.spanAt_univ hσ]

theorem ChainCtx.exists_adj_zero (C : ChainCtx S e' ψ) {f₀ : Frame (unitaryInvolution K p f) 4}
    {L' : Submodule K (Fin 4 → K)} (hL' : L' ∈ nsPts (unitaryInvolution K p f) ⊤)
    (hcol : IsCollinear (unitaryInvolution K p f) (f₀.line 0) L') :
    ∃ c₁ c₂ : Frame (unitaryInvolution K p f) 4, c₁.line 0 = f₀.line 0 ∧ c₂.line 0 = L' ∧
      (frameSystem (unitaryInvolution K p f) 3).adj 0 c₁ c₂ := by
  have hq3 : 3 ≤ p ^ f := by have := C.hq; omega
  have hx' : L' ∈ nsPts (unitaryInvolution K p f) (f₀.spanAt (posInt 3 (0 : Fin 3).val 3)) := by
    rwa [spanAt_posInt_zero_three C.hσ f₀ (a := (0 : Fin 3).val) rfl]
  obtain ⟨ρ, c₂, hρ, hadj, hline⟩ := exists_edge_lift C.hσ C.hK hq3
    (i := 0) (b := 3) (by simp) le_rfl hx' hcol
  refine ⟨galleryEnd f₀ ρ, c₂, ?_, hline, hadj⟩
  have hres : galleryEnd f₀ ρ ∈ (frameSystem (unitaryInvolution K p f) 3).residue
      (typeInt 3 ((0 : Fin 3).val + 1) 3) f₀ := mem_residue_iff_exists_isJGallery.2 ⟨ρ, hρ, rfl⟩
  refine residue_agree hres ?_
  rintro ⟨j, hj, hk⟩
  rw [mem_typeInt] at hj
  rcases hk with hk | hk
  · have := congrArg Fin.val hk
    simp at this
    omega
  · have := congrArg Fin.val hk
    simp at this

theorem ChainCtx.line_eq_of_ptMap_eq (C : ChainCtx S e' ψ) {k : Fin 4}
    (hcov : ∀ i : Fin 4, i = k ∨ ∃ j, e' j = i)
    (hc0 : ∀ A B, S.ι k A * S.ι (e' 0) B = S.ι (e' 0) B * S.ι k A)
    (hc2 : ∀ A B, S.ι k A * S.ι (e' 2) B = S.ι (e' 2) B * S.ι k A)
    (hpair : ({e' 2} : Set (Fin 4)) ∪ {k} = {2, 3})
    (hcomm : CommuteTypes (phanSystem S) k (e' 2))
    (h0 : PtStep0 S) (he : PtEdge S) {f₁ f₂ : Frame (unitaryInvolution K p f) 4}
    (h : ptMap S (C.Phi f₁) = ptMap S (C.Phi f₂)) : f₁.line 0 = f₂.line 0 := by
  by_contra hne
  have hq3 : 3 ≤ p ^ f := by have := C.hq; omega
  have hL : f₁.line 0 ∈ nsPts (unitaryInvolution K p f) ⊤ :=
    ⟨le_top, f₁.finrank_line _, f₁.nondeg_line _⟩
  have hL' : f₂.line 0 ∈ nsPts (unitaryInvolution K p f) ⊤ :=
    ⟨le_top, f₂.finrank_line _, f₂.nondeg_line _⟩
  have hdist : ∀ {c d : Frame (unitaryInvolution K p f) 4},
      (frameSystem (unitaryInvolution K p f) 3).adj 0 c d → c.line 0 ≠ d.line 0 →
      ptMap S (C.Phi c) ≠ ptMap S (C.Phi d) := by
    intro c d hcd hl hp
    have hadj : (phanSystem S).adj 0 (C.Phi c) (C.Phi d) := C.he0 ▸ C.Phi_adj hcd
    exact hl (congrArg (fun x => x.line 0) (C.Phi_inj (h0 hadj hp)))
  rcases isCollinear_or_exists_common C.hσ C.hK hq3 (nondeg_top_four C.hσ)
    (by rw [finrank_top_four]; omega) hL hL' with hcol | ⟨M, hM, hLM, hML'⟩
  · obtain ⟨c₁, c₂, h1, h2, hadj⟩ := C.exists_adj_zero hL' hcol
    refine hdist hadj (by rw [h1, h2]; exact hne) ?_
    rw [C.ptMap_Phi_eq h1, h, C.ptMap_Phi_eq h2.symm]
  · obtain ⟨c₁, d₁, h1, h1', hadj1⟩ := C.exists_adj_zero hM hLM
    obtain ⟨c₂, d₂, h2, h2', hadj2⟩ := C.exists_adj_zero hM hML'.symm
    have hpab : ptMap S (C.Phi c₁) = ptMap S (C.Phi c₂) := by
      rw [C.ptMap_Phi_eq h1, h, C.ptMap_Phi_eq h2.symm]
    have hpcd : ptMap S (C.Phi d₁) = ptMap S (C.Phi d₂) :=
      C.ptMap_Phi_eq (h1'.trans h2'.symm)
    have hne' : ptMap S (C.Phi c₁) ≠ ptMap S (C.Phi d₁) :=
      hdist hadj1 (by rw [h1, h1']; exact hLM.1)
    have hadjΦ1 : (phanSystem S).adj 0 (C.Phi c₁) (C.Phi d₁) := C.he0 ▸ C.Phi_adj hadj1
    have hadjΦ2 : (phanSystem S).adj 0 (C.Phi c₂) (C.Phi d₂) := C.he0 ▸ C.Phi_adj hadj2
    obtain ⟨-, hb⟩ := he hadjΦ1 hadjΦ2 hpab hpcd hne'
    rw [← hpair] at hb
    obtain ⟨g, hg1, hg2⟩ := (mem_residue_union_iff (J₁ := {e' 2}) (J₂ := {k})
      (fun j hj i hi => by
        rw [Set.mem_singleton_iff] at hj hi
        subst hj
        subst hi
        exact hcomm)).1 hb
    rw [mem_residue_singleton] at hg1 hg2
    obtain ⟨c₁', hadj12, rfl⟩ := C.exists_adj_Phi (i := 2) c₁ hg1
    have := C.eq_of_adj_out hcov hc0 hc2 hg2
    subst this
    have h12 := hadj12 0 (by simp) (by simp)
    exact hne (by rw [← h1, ← h2, h12])

theorem ChainCtx.exists_frame_line (C : ChainCtx S e' ψ) {L : Submodule K (Fin 4 → K)}
    (hL : L ∈ nsPts (unitaryInvolution K p f) ⊤) :
    ∃ c : Frame (unitaryInvolution K p f) 4, c.line 0 = L := by
  have hq3 : 3 ≤ p ^ f := by have := C.hq; omega
  obtain ⟨c', -, h⟩ := exists_residue_line_eq C.hσ C.hK hq3 3 0 3 rfl le_rfl
    (stdFrame (unitaryInvolution K p f) 4) L
    (by rwa [spanAt_posInt_zero_three C.hσ _ rfl])
  exact ⟨c', h⟩

@[expose] noncomputable def ChainCtx.piPt (C : ChainCtx S e' ψ)
    (L : ↥(nsPts (unitaryInvolution K p f) (⊤ : Submodule K (Fin 4 → K)))) :
    G ⧸ parab S {1, 2, 3} :=
  ptMap S (C.Phi (Classical.choose (C.exists_frame_line L.2)))

theorem ChainCtx.piPt_eq (C : ChainCtx S e' ψ)
    {L : ↥(nsPts (unitaryInvolution K p f) (⊤ : Submodule K (Fin 4 → K)))}
    {c : Frame (unitaryInvolution K p f) 4} (h : c.line 0 = L.1) :
    C.piPt L = ptMap S (C.Phi c) :=
  C.ptMap_Phi_eq ((Classical.choose_spec (C.exists_frame_line L.2)).trans h.symm)

theorem ChainCtx.adj_ptMap_of_collinear (C : ChainCtx S e' ψ) (h0 : PtStep0 S)
    {c d : Frame (unitaryInvolution K p f) 4}
    (h : IsCollinear (unitaryInvolution K p f) (c.line 0) (d.line 0)) :
    (ptGraph S).Adj (ptMap S (C.Phi c)) (ptMap S (C.Phi d)) := by
  obtain ⟨c₁, c₂, h1, h2, hadj⟩ := C.exists_adj_zero ⟨le_top, d.finrank_line _, d.nondeg_line _⟩ h
  have hadjΦ : (phanSystem S).adj 0 (C.Phi c₁) (C.Phi c₂) := C.he0 ▸ C.Phi_adj hadj
  have hne : ptMap S (C.Phi c₁) ≠ ptMap S (C.Phi c₂) := by
    intro hp
    have := congrArg (fun x : Frame (unitaryInvolution K p f) 4 => x.line 0)
      (C.Phi_inj (h0 hadjΦ hp))
    rw [h1, h2] at this
    exact h.1 this
  rw [← C.ptMap_Phi_eq h1, ← C.ptMap_Phi_eq h2]
  exact ptGraph_adj_of_adj hadjΦ hne

end Lines

end CFSG.ClassicalInvolution.PhanQ
