module

public import CFSG.ClassicalInvolution.Phan.FirstLine
public import CFSG.ClassicalInvolution.Phan.Geometry.Decomp

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  Module

variable {K : Type} [Field K] {σ : K ≃+* K}

section Geom

variable {n : ℕ} [Finite K] {q : ℕ}

theorem fibreNull_of_geomWalk (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ}
    (hib : i.val + 2 ≤ b) (hbn : b ≤ n) (c : Frame σ (n + 1))
    (hW : c.spanAt (posInt n i.val b) = W)
    (h2 : ∀ j, 1 ≤ j → i.val + j < b → NullOn σ n (typeInt n i.val (i.val + j)))
    (R : (frameFib hσ d i (by omega) c hW.le).Rigid) {x : ↥(nsPts σ W)}
    {w : (collGraph σ W).Walk x x} (hw : IsGeomWalk σ W w) :
    (frameFib hσ d i (by omega) c hW.le).FibreNull w := by
  obtain ⟨A, hAW, hAnd, hA2, hAlt, hsupp⟩ := hw
  have hWdim : finrank K W = b + 1 - i.val := by
    rw [← hW, c.finrank_spanAt, card_posInt hbn]
  obtain ⟨j, hj⟩ : ∃ j, finrank K A = j + 1 := ⟨finrank K A - 1, by omega⟩
  have hj1 : 1 ≤ j := by omega
  have hjb : i.val + j < b := by omega
  have hx : x.1 ∈ nsPts σ A := ⟨hsupp x w.start_mem_support, x.2.2.1, x.2.2.2⟩
  obtain ⟨e₁, he₁, he₁line, he₁span⟩ := exists_adapted hσ hK hq j i.val b (by omega) hbn c A
    (hAW.trans hW.ge) hAnd hj x.1 hx
  have he₁line' : e₁.line i.castSucc = x.1 := he₁line
  have hib' : i.val < i.val + j := by omega
  have hbn' : i.val + j ≤ n := by omega
  have hc' : e₁.spanAt (posInt n i.val (i.val + j)) ≤ W := by
    rw [he₁span]
    exact hAW
  have hP₁ : (frameFib hσ d i hib' e₁ hc').P e₁ = x := by
    refine Subtype.ext ?_
    change (firstPt σ d i e₁).1 = x.1
    rw [firstPt_val (line_mem_nsPts_of_mem_residue hσ hib'.le hc' (self_mem_residue _ _))]
    exact he₁line'
  obtain ⟨γ₁, hl₁⟩ := (frameFib hσ d i hib' e₁ hc').exists_lift (D := fun v => v.1 ≤ A)
    (fun {e x'} hQ _ hDx hadj => frameFib_lift hσ hK hq d i hib' hbn' e₁ hc'
      (D := fun v => v.1 ≤ A) (fun v hv => by rw [he₁span]; exact hv) hQ hDx hadj)
    w hsupp e₁ (self_mem_residue _ _) hP₁
  have hQ₂ : (frameFib hσ d i hib' e₁ hc').Q (galleryEnd e₁ γ₁) :=
    hl₁.Q_galleryEnd (self_mem_residue _ _)
  have hP₂ : (frameFib hσ d i hib' e₁ hc').P (galleryEnd e₁ γ₁) = x :=
    hl₁.end_eq (self_mem_residue _ _)
  have hline₂ : (galleryEnd e₁ γ₁).line i.castSucc = e₁.line i.castSucc := by
    have h := congrArg Subtype.val (hP₂.trans hP₁.symm)
    change (firstPt σ d i (galleryEnd e₁ γ₁)).1 = (firstPt σ d i e₁).1 at h
    rwa [firstPt_val (line_mem_nsPts_of_mem_residue hσ hib'.le hc' hQ₂),
      firstPt_val (line_mem_nsPts_of_mem_residue hσ hib'.le hc' (self_mem_residue _ _))] at h
  have hres : e₁ ∈ (frameSystem σ n).residue (typeInt n (i.val + 1) (i.val + j))
      (galleryEnd e₁ γ₁) := by
    refine (mem_residue_typeInt_iff hσ hK hq (by omega) hbn').2 fun k hk => ?_
    by_cases hka : k = i.castSucc
    · rw [hka]
      exact hline₂.symm
    · have hk' : k ∉ posInt n i.val (i.val + j) := by
        rw [mem_posInt] at hk ⊢
        have h1 : k.val ≠ i.val := fun h => hka (Fin.ext (by simpa using h))
        omega
      exact (residue_typeInt_agree hQ₂ hk').symm
  obtain ⟨τ, hτ, hτe⟩ := mem_residue_iff_exists_isJGallery.1 hres
  have hγ₁J : IsJGallery (frameSystem σ n) (typeInt n i.val (i.val + j)) e₁ γ₁ :=
    hl₁.isJGallery.mono (insert_typeInt_subset hib')
  have hτJ : IsJGallery (frameSystem σ n) (typeInt n i.val (i.val + j)) (galleryEnd e₁ γ₁) τ :=
    hτ.mono (typeInt_mono (Nat.le_succ _) le_rfl)
  have hclosed := hγ₁J.append hτJ
  have hh := h2 j hj1 hjb e₁ (γ₁ ++ τ) hclosed.1 hclosed.2 (by rw [galleryEnd_append, hτe])
  have hsub : typeInt n (i.val + 1) (i.val + j) ⊆ typeInt n (i.val + 1) b :=
    typeInt_mono le_rfl hjb.le
  have hl₁' : (frameFib hσ d i (by omega) c hW.le).Lift w e₁ γ₁ :=
    Fib.Lift.mono (F := frameFib hσ d i hib' e₁ hc')
      (F' := frameFib hσ d i (by omega) c hW.le) rfl rfl hsub hl₁
  refine R.fibreNull_of_exists
    (fun {e e'} he he' hP => frameFib_conn hσ hK hq d i (by omega) hbn c hW.le he he' hP) he₁
    hl₁' (hτ.mono hsub) hτe hh

theorem nullOn_run_step (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    (i : Fin n) {b : ℕ} (hib : i.val + 3 ≤ b) (hbn : b ≤ n)
    (h1 : NullOn σ n (typeInt n (i.val + 1) b))
    (h2 : ∀ j, 1 ≤ j → i.val + j < b → NullOn σ n (typeInt n i.val (i.val + j))) :
    NullOn σ n (typeInt n i.val b) := by
  intro c γ hγ hJ hend
  have hq3 : 3 ≤ q := by omega
  set W : Submodule K (Fin (n + 1) → K) := c.spanAt (posInt n i.val b) with hWdef
  have hW : c.spanAt (posInt n i.val b) = W := rfl
  have hnd : Nondeg σ W := c.nondeg_spanAt hσ _
  have hdim : finrank K W = b + 1 - i.val := by
    rw [hWdef, c.finrank_spanAt, card_posInt hbn]
  have hWmem : c.line i.castSucc ∈ nsPts σ W :=
    ⟨c.line_le_spanAt (mem_posInt.2 ⟨le_refl _, by simp only [Fin.val_castSucc]; omega⟩),
      c.finrank_line _, c.nondeg_line _⟩
  set d : ↥(nsPts σ W) := ⟨c.line i.castSucc, hWmem⟩ with hd
  have R := frameFib_rigid hσ hK hq3 d i (by omega : i.val + 2 ≤ b) hbn c hW.le h1
  refine R.twoHomotopic_nil (E := geomWalks σ W) ?_ ?_ ?_ (ChamberSystem.self_mem_residue _ _)
    ?_ hend
  · intro x w hw
    exact fibreNull_of_geomWalk hσ hK hq3 d i (by omega) hbn c hW h2 R hw
  · intro e x' hQ hadj
    exact frameFib_lift hσ hK hq3 d i (by omega) hbn c hW.le (D := fun _ => True)
      (fun v _ => v.2.1) hQ trivial hadj
  · intro x w
    exact collinear_decomp hσ hK hq hnd (by omega) w
  · refine ⟨hγ, fun j hj => ?_⟩
    have hj' := hJ j hj
    by_cases hji : j = i
    · exact Or.inl hji
    · refine Or.inr ⟨?_, hj'.2⟩
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      have := hj'.1
      show i.val + 1 ≤ j.val
      omega

theorem nullOn_run (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) :
    ∀ (r a : ℕ), a + r ≤ n → NullOn σ n (typeInt n a (a + r)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro a har
  by_cases hr : r ≤ 2
  · exact nullOn_typeInt_of_le_two (by omega)
  · have han : a < n := by omega
    have h1 : NullOn σ n (typeInt n (a + 1) (a + r)) := by
      have := ih (r - 1) (by omega) (a + 1) (by omega)
      rwa [show a + 1 + (r - 1) = a + r by omega] at this
    refine nullOn_run_step hσ hK hq ⟨a, han⟩ (b := a + r) (by show a + 3 ≤ a + r; omega) har h1
      fun j _ hj => ?_
    have hj' : a + j < a + r := hj
    exact ih j (by omega) a (by omega)

end Geom

theorem frameSystem_simplyTwoConnected (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) (n : ℕ) : (frameSystem σ n).SimplyTwoConnected := by
  rw [simplyTwoConnected_iff_nullOn_univ, ← typeInt_zero_self]
  simpa using nullOn_run hσ hK hq n 0 (by omega)

end CFSG.ClassicalInvolution.Phan
