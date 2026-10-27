module

public import CFSG.ClassicalInvolution.Phan.Phan3GGallery
public import CFSG.ClassicalInvolution.Phan.FirstLine
public import CFSG.ClassicalInvolution.Phan.Geometry.Decomp

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan.TitsChamber Module

variable {K : Type} [Field K] {σ : K ≃+* K}

variable (σ) (n : ℕ) in
@[expose] def NullOn3 (𝒥 : Set (Fin n) → Prop) (J : Set (Fin n)) : Prop :=
  ∀ (c : Frame σ (n + 1)) (γ : List (Fin n × Frame σ (n + 1))),
    (frameSystem σ n).IsGallery c γ → (∀ i ∈ galleryType γ, i ∈ J) → galleryEnd c γ = c →
      HomotopicOn (frameSystem σ n) 𝒥 c γ []

@[expose] def J3 (n : ℕ) (J : Set (Fin n)) : Prop :=
  J.encard ≤ 2 ∨ ∃ a : ℕ, J = typeInt n a (a + 3)

theorem J3_of_encard_le_two (n : ℕ) : ∀ J : Set (Fin n), J.encard ≤ 2 → J3 n J :=
  fun _ h => Or.inl h

theorem J3_typeInt (n a : ℕ) : J3 n (typeInt n a (a + 3)) :=
  Or.inr ⟨a, rfl⟩

section Geom

variable {n : ℕ} [Finite K] {q : ℕ}

theorem frameFib_rigidOn (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ}
    (hib : i.val + 2 ≤ b) (hbn : b ≤ n) (c : Frame σ (n + 1))
    (hc : c.spanAt (posInt n i.val b) ≤ W) {𝒥 : Set (Fin n) → Prop}
    (two : ∀ J : Set (Fin n), J.encard ≤ 2 → 𝒥 J)
    (hnull : NullOn3 σ n 𝒥 (typeInt n (i.val + 1) b)) :
    RigidOn (frameFib hσ d i (by omega) c hc) 𝒥 := by
  refine ⟨two, fun {e γ} _ hγ hend => hnull e γ hγ.1 hγ.2 hend, ?_⟩
  intro e e' f f' ρ ρ' x' he he' hP hadj hρ hf hfx hρ' hf' hf'x
  have hmem : ∀ {e : Frame σ (n + 1)}, (frameFib hσ d i (by omega) c hc).Q e →
      ((frameFib hσ d i (by omega) c hc).P e).1 = e.line i.castSucc := fun {e} he =>
    firstPt_val (line_mem_nsPts_of_mem_residue hσ (by omega) hc he)
  have hQf : (frameFib hσ d i (by omega) c hc).Q f := by
    refine (frameFib hσ d i (by omega) c hc).step_Q (Set.mem_insert _ _) hf ?_
    exact (frameFib hσ d i (by omega) c hc).Q_galleryEnd he
      (hρ.mono (Set.subset_insert _ _))
  have hQf' : (frameFib hσ d i (by omega) c hc).Q f' := by
    refine (frameFib hσ d i (by omega) c hc).step_Q (Set.mem_insert _ _) hf' ?_
    exact (frameFib hσ d i (by omega) c hc).Q_galleryEnd he'
      (hρ'.mono (Set.subset_insert _ _))
  have hee' : e.line i.castSucc = e'.line i.castSucc := by
    rw [← hmem he, ← hmem he', hP]
  have hx : e.line i.castSucc ≠ x'.1 := by
    rw [← hmem he]
    exact hadj.1
  have hfx' : f.line i.castSucc = x'.1 := by
    rw [← hmem hQf, hfx]
  have hf'x' : f'.line i.castSucc = x'.1 := by
    rw [← hmem hQf', hf'x]
  exact edge_aux hσ hK hq hib hbn he he' hee' hx hρ hf hfx' hρ' hf' hf'x'

theorem fibreNull_of_geomWalk3 (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2)
    (hq : 3 ≤ q) {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ}
    (hib : i.val + 2 ≤ b) (hbn : b ≤ n) (c : Frame σ (n + 1))
    (hW : c.spanAt (posInt n i.val b) = W) {𝒥 : Set (Fin n) → Prop}
    (h2 : ∀ j, 1 ≤ j → i.val + j < b → NullOn3 σ n 𝒥 (typeInt n i.val (i.val + j)))
    (R : RigidOn (frameFib hσ d i (by omega) c hW.le) 𝒥) {x : ↥(nsPts σ W)}
    {w : (collGraph σ W).Walk x x} (hw : IsGeomWalk σ W w) :
    FibreNullOn (frameFib hσ d i (by omega) c hW.le) 𝒥 w := by
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

theorem nullOn3_run_step (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 3 ^ 2)
    (hdec : ∀ {W : Submodule K (Fin (n + 1) → K)}, Nondeg σ W → 5 ≤ finrank K W →
      ∀ {x : ↥(nsPts σ W)} (w : (collGraph σ W).Walk x x),
        CycleHomotopic (geomWalks σ W) w .nil)
    {𝒥 : Set (Fin n) → Prop} (two : ∀ J : Set (Fin n), J.encard ≤ 2 → 𝒥 J)
    (i : Fin n) {b : ℕ} (hib : i.val + 4 ≤ b) (hbn : b ≤ n)
    (h1 : NullOn3 σ n 𝒥 (typeInt n (i.val + 1) b))
    (h2 : ∀ j, 1 ≤ j → i.val + j < b → NullOn3 σ n 𝒥 (typeInt n i.val (i.val + j))) :
    NullOn3 σ n 𝒥 (typeInt n i.val b) := by
  intro c γ hγ hJ hend
  have hq3 : 3 ≤ 3 := le_rfl
  set W : Submodule K (Fin (n + 1) → K) := c.spanAt (posInt n i.val b) with hWdef
  have hW : c.spanAt (posInt n i.val b) = W := rfl
  have hnd : Nondeg σ W := c.nondeg_spanAt hσ _
  have hdim : finrank K W = b + 1 - i.val := by
    rw [hWdef, c.finrank_spanAt, card_posInt hbn]
  have hWmem : c.line i.castSucc ∈ nsPts σ W :=
    ⟨c.line_le_spanAt (mem_posInt.2 ⟨le_refl _, by simp only [Fin.val_castSucc]; omega⟩),
      c.finrank_line _, c.nondeg_line _⟩
  set d : ↥(nsPts σ W) := ⟨c.line i.castSucc, hWmem⟩ with hd
  have R := frameFib_rigidOn hσ hK hq3 d i (by omega : i.val + 2 ≤ b) hbn c hW.le two h1
  refine R.homotopicOn_nil (E := geomWalks σ W) ?_ ?_ ?_ (ChamberSystem.self_mem_residue _ _)
    ?_ hend
  · intro x w hw
    exact fibreNull_of_geomWalk3 hσ hK hq3 d i (by omega) hbn c hW h2 R hw
  · intro e x' hQ hadj
    exact frameFib_lift hσ hK hq3 d i (by omega) hbn c hW.le (D := fun _ => True)
      (fun v _ => v.2.1) hQ trivial hadj
  · intro x w
    exact hdec hnd (by omega) w
  · refine ⟨hγ, fun j hj => ?_⟩
    have hj' := hJ j hj
    by_cases hji : j = i
    · exact Or.inl hji
    · refine Or.inr ⟨?_, hj'.2⟩
      have : j.val ≠ i.val := fun h => hji (Fin.ext h)
      have := hj'.1
      show i.val + 1 ≤ j.val
      omega

theorem nullOn3_run (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = 3 ^ 2)
    (hdec : ∀ {W : Submodule K (Fin (n + 1) → K)}, Nondeg σ W → 5 ≤ finrank K W →
      ∀ {x : ↥(nsPts σ W)} (w : (collGraph σ W).Walk x x),
        CycleHomotopic (geomWalks σ W) w .nil) :
    ∀ (r a : ℕ), a + r ≤ n → NullOn3 σ n (J3 n) (typeInt n a (a + r)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro a har
  by_cases hr : r ≤ 2
  · intro c γ hγ hJ hend
    exact HomotopicOn.of_twoHomotopic (J3_of_encard_le_two n)
      (nullOn_typeInt_of_le_two (σ := σ) (n := n) (a := a) (b := a + r) (by omega) c γ hγ hJ hend)
  · by_cases hr3 : r = 3
    · subst hr3
      intro c γ hγ hJ hend
      have := homotopicOn_replace (X := frameSystem σ n) (𝒥 := J3 n) (x := c) [] γ [] []
        (J := typeInt n a (a + 3)) (J3_typeInt n a) (by simpa using hγ) (by simp)
        (by simpa using hJ) (by simp) (by simpa using hend)
      simpa using this
    · have han : a < n := by omega
      have h1 : NullOn3 σ n (J3 n) (typeInt n (a + 1) (a + r)) := by
        have := ih (r - 1) (by omega) (a + 1) (by omega)
        rwa [show a + 1 + (r - 1) = a + r by omega] at this
      refine nullOn3_run_step hσ hK hdec (J3_of_encard_le_two n) ⟨a, han⟩ (b := a + r)
        (by show a + 4 ≤ a + r; omega) har h1 fun j _ hj => ?_
      have hj' : a + j < a + r := hj
      exact ih j (by omega) a (by omega)

end Geom

theorem frameSystem_simplyConnectedOn3 (hσ : IsUnitaryInvolution σ) [Finite K]
    (hK : Nat.card K = 3 ^ 2) (n : ℕ)
    (hdec : ∀ {W : Submodule K (Fin (n + 1) → K)}, Nondeg σ W → 5 ≤ finrank K W →
      ∀ {x : ↥(nsPts σ W)} (w : (collGraph σ W).Walk x x),
        CycleHomotopic (geomWalks σ W) w .nil) :
    SimplyConnectedOn (frameSystem σ n) (J3 n) := by
  intro c γ hγ hend
  have h := nullOn3_run hσ hK hdec n 0 (by omega)
  rw [zero_add, typeInt_zero_self] at h
  exact h c γ hγ (fun _ _ => trivial) hend

end CFSG.ClassicalInvolution.Phan.Q3G
