module

public import CFSG.ClassicalInvolution.Phan.GalleryWalk
public import CFSG.ClassicalInvolution.Phan.Residues

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  Module

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

section EdgeLift

variable [Finite K] {q : ℕ}

theorem exists_edge_lift (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {i : Fin n} {b : ℕ} (hib : i.val < b) (hbn : b ≤ n) {e : Frame σ (n + 1)}
    {x' : Submodule K (Fin (n + 1) → K)} (hx' : x' ∈ nsPts σ (e.spanAt (posInt n i.val b)))
    (hcol : IsCollinear σ (e.line i.castSucc) x') :
    ∃ (ρ : List (Fin n × Frame σ (n + 1))) (f : Frame σ (n + 1)),
      IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) e ρ ∧
      (frameSystem σ n).adj i (galleryEnd e ρ) f ∧ f.line i.castSucc = x' := by
  set a : ℕ := i.val with ha
  have hpaV : i.castSucc ∈ posInt n a b :=
    mem_posInt.2 ⟨le_refl a, by simp only [Fin.val_castSucc]; omega⟩
  set P : Submodule K (Fin (n + 1) → K) := e.line i.castSucc ⊔ x' with hP
  have hPnd : Nondeg σ P := hcol.2
  have hP2 : finrank K P = 2 := finrank_sup_of_ne_pts (e.finrank_line _) hx'.2.1 hcol.1
  have hL : e.line i.castSucc ∈ nsPts σ P := ⟨le_sup_left, e.finrank_line _, e.nondeg_line _⟩
  obtain ⟨z, hz, hzo, hzP⟩ := exists_orth_complement_in_plane hσ hP2 hPnd hL
  have hPle : P ≤ e.spanAt (posInt n a b) := sup_le (e.line_le_spanAt hpaV) hx'.1
  have hzV' : z ∈ nsPts σ (e.spanAt (posInt n (a + 1) b)) := by
    refine ⟨(e.le_spanAt_iff hσ).2 fun l hl => ?_, hz.2.1, hz.2.2⟩
    by_cases hlp : l = i.castSucc
    · rw [hlp]
      exact hzo
    · have hl' : l ∉ posInt n a b := by
        rw [mem_posInt] at hl ⊢
        have : l.val ≠ a := fun h => hlp (Fin.ext (by simpa [ha] using h))
        omega
      exact (e.orth_spanAt hl').mono le_rfl (hz.1.trans hPle)
  obtain ⟨cs, hcs, hcsz⟩ := exists_residue_line_eq hσ hK hq (b - (a + 1)) (a + 1) b (by omega) hbn
    e z hzV'
  have hcspa : cs.line i.castSucc = e.line i.castSucc :=
    residue_typeInt_agree hcs (by rw [mem_posInt]; simp [ha])
  have hcsz' : cs.line i.succ = z := hcsz
  have hplane : cs.line i.castSucc ⊔ cs.line i.succ = P := by rw [hcspa, hcsz', hzP]
  have hx'' : x' ∈ nsPts σ (cs.line i.castSucc ⊔ cs.line i.succ) := by
    rw [hplane]
    exact ⟨le_sup_right, hx'.2.1, hx'.2.2⟩
  obtain ⟨c', hadj, hc'⟩ := exists_adj_line_eq hσ cs i hx''
  obtain ⟨ρ, hρ, hρe⟩ := mem_residue_iff_exists_isJGallery.1 hcs
  exact ⟨ρ, c', hρ, by rw [hρe]; exact hadj, hc'⟩

theorem posInt_eq_insert {a b : ℕ} (hab : a ≤ b) (ha : a < n + 1) :
    posInt n a b = insert ⟨a, ha⟩ (posInt n (a + 1) b) := by
  ext k
  simp only [mem_posInt, Finset.mem_insert, Fin.ext_iff]
  omega

theorem exists_adapted (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q) :
    ∀ (j a b : ℕ) (hab : a + j ≤ b) (hbn : b ≤ n) (e : Frame σ (n + 1))
      (A : Submodule K (Fin (n + 1) → K)), A ≤ e.spanAt (posInt n a b) → Nondeg σ A →
      finrank K A = j + 1 → ∀ x ∈ nsPts σ A,
      ∃ e' ∈ (frameSystem σ n).residue (typeInt n a b) e, e'.line ⟨a, by omega⟩ = x ∧
        e'.spanAt (posInt n a (a + j)) = A := by
  intro j
  induction j with
  | zero =>
    intro a b hab hbn e A hA hAnd hdim x hx
    have hxA : x = A := Submodule.eq_of_le_of_finrank_eq hx.1 (by rw [hx.2.1, hdim])
    subst hxA
    obtain ⟨e', he', hline⟩ := exists_residue_line_eq hσ hK hq (b - a) a b (by omega) hbn e x
      ⟨hA, hx.2⟩
    refine ⟨e', he', hline, ?_⟩
    have h0 : a + 0 = a := rfl
    rw [h0, posInt_self (by omega), Frame.spanAt_singleton]
    exact hline
  | succ j ih =>
    intro a b hab hbn e A hA hAnd hdim x hx
    obtain ⟨v, hv, hvA, rfl⟩ := mem_nsPts_iff.mp hx
    set A' : Submodule K (Fin (n + 1) → K) := A ⊓ perp σ (K ∙ v) with hA'
    have hA'nd : Nondeg σ A' := Nondeg.inf_perp_span_singleton hσ hvA hv hAnd
    have hA'dim : finrank K A' = j + 1 := by
      have := finrank_eq_inf_perp_add_one hσ hvA hv
      rw [← hA'] at this
      omega
    obtain ⟨e₁, he₁, he₁line⟩ := exists_residue_line_eq hσ hK hq (b - a) a b (by omega) hbn e
      (K ∙ v) ⟨hx.1.trans hA, hx.2⟩
    have hspan₁ : e₁.spanAt (posInt n a b) = e.spanAt (posInt n a b) :=
      spanAt_posInt_of_mem_residue hσ he₁
    have hA'orth : Orth σ (K ∙ v) A' := fun u hu w hw =>
      herm_eq_zero_comm σ hσ.invol (hw.2 u hu)
    have hA'le : A' ≤ e₁.spanAt (posInt n (a + 1) b) := by
      refine (e₁.le_spanAt_iff hσ).2 fun l hl => ?_
      by_cases hla : l.val = a
      · have : e₁.line l = K ∙ v := by
          rw [← he₁line]
          exact congrArg e₁.line (Fin.ext hla)
        rw [this]
        exact hA'orth
      · have hl' : l ∉ posInt n a b := by
          rw [mem_posInt] at hl ⊢
          omega
        rw [residue_typeInt_agree he₁ hl']
        exact (e.orth_spanAt hl').mono le_rfl (inf_le_left.trans hA)
    obtain ⟨w, hwA', hww⟩ := exists_aniso_of_nondeg hσ hA'nd (fun h => by
      rw [h, finrank_bot] at hA'dim
      omega)
    obtain ⟨e'', he'', he''line, he''span⟩ := ih (a + 1) b (by omega) hbn e₁ A' hA'le hA'nd
      hA'dim (K ∙ w) (span_singleton_mem_nsPts hww hwA')
    refine ⟨e'', mem_residue_trans he₁
      (residue_mono (typeInt_mono (Nat.le_succ a) le_rfl) e₁ he''), ?_, ?_⟩
    · rw [residue_typeInt_agree he'' (by rw [mem_posInt]; simp)]
      exact he₁line
    · rw [posInt_eq_insert (by omega) (by omega), Frame.spanAt_insert,
        show a + (j + 1) = a + 1 + j by omega, he''span, residue_typeInt_agree he'' (by
          rw [mem_posInt]; simp), he₁line]
      exact span_sup_inf_perp hσ hvA hv

end EdgeLift

section FirstLine

theorem eq_of_adj_of_line_eq (hσ : IsUnitaryInvolution σ) {i : Fin n} {e f : Frame σ (n + 1)}
    (hadj : (frameSystem σ n).adj i e f) (h : e.line i.castSucc = f.line i.castSucc) : e = f := by
  refine Frame.ext (funext fun k => ?_)
  by_cases hk : k = i.succ
  · subst hk
    refine Frame.line_eq_of_agree_except hσ fun k hk => ?_
    by_cases hk' : k = i.castSucc
    · subst hk'
      exact h
    · exact hadj k hk' hk
  · by_cases hk' : k = i.castSucc
    · subst hk'
      exact h
    · exact hadj k hk' hk

variable (σ) in
@[expose] noncomputable def firstPt {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W))
    (i : Fin n) (e : Frame σ (n + 1)) : ↥(nsPts σ W) :=
  @dite _ (e.line i.castSucc ∈ nsPts σ W) (Classical.propDecidable _) (fun h => ⟨_, h⟩)
    (fun _ => d)

theorem firstPt_val {W : Submodule K (Fin (n + 1) → K)} {d : ↥(nsPts σ W)} {i : Fin n}
    {e : Frame σ (n + 1)} (h : e.line i.castSucc ∈ nsPts σ W) :
    (firstPt σ d i e).1 = e.line i.castSucc := by
  simp [firstPt, h]

theorem line_mem_nsPts_of_mem_residue (hσ : IsUnitaryInvolution σ)
    {W : Submodule K (Fin (n + 1) → K)} {i : Fin n} {b : ℕ} (hib : i.val ≤ b)
    {c e : Frame σ (n + 1)} (hc : c.spanAt (posInt n i.val b) ≤ W)
    (he : e ∈ (frameSystem σ n).residue (typeInt n i.val b) c) :
    e.line i.castSucc ∈ nsPts σ W := by
  refine ⟨?_, e.finrank_line _, e.nondeg_line _⟩
  have h1 := spanAt_posInt_of_mem_residue hσ he
  refine (e.line_le_spanAt (S := posInt n i.val b)
    (mem_posInt.2 ⟨le_refl _, by simpa using hib⟩)).trans ?_
  rw [h1]
  exact hc

theorem insert_typeInt_subset {i : Fin n} {b : ℕ} (hib : i.val < b) :
    insert i (typeInt n (i.val + 1) b) ⊆ typeInt n i.val b := by
  intro j hj
  rcases hj with rfl | hj
  · exact ⟨le_rfl, hib⟩
  · exact ⟨(Nat.le_succ _).trans hj.1, hj.2⟩

@[expose] noncomputable def frameFib (hσ : IsUnitaryInvolution σ)
    {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ} (hib : i.val < b)
    (c : Frame σ (n + 1)) (hc : c.spanAt (posInt n i.val b) ≤ W) :
    Fib (frameSystem σ n) (collGraph σ W) where
  P := firstPt σ d i
  a := i
  J' := typeInt n (i.val + 1) b
  Q e := e ∈ (frameSystem σ n).residue (typeInt n i.val b) c
  step_Q := by
    intro j e f hj hadj he
    exact mem_residue_trans he (residue_mono (Set.singleton_subset_iff.2
      (insert_typeInt_subset hib hj)) _ ((mem_residue_singleton).2 hadj))
  step_P := by
    intro j e f hj hadj he
    have hf : f ∈ (frameSystem σ n).residue (typeInt n i.val b) c :=
      mem_residue_trans he (residue_mono (Set.singleton_subset_iff.2
        (insert_typeInt_subset hib (Set.mem_insert_of_mem _ hj))) _
        ((mem_residue_singleton).2 hadj))
    refine Subtype.ext ?_
    rw [firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc he),
      firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc hf)]
    refine hadj _ ?_ ?_
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      have := hj.1
      omega
    · intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      have := hj.1
      omega
  step_a := by
    intro e f hadj he
    have hf : f ∈ (frameSystem σ n).residue (typeInt n i.val b) c :=
      mem_residue_trans he (residue_mono (Set.singleton_subset_iff.2
        (insert_typeInt_subset hib (Set.mem_insert _ _))) _ ((mem_residue_singleton).2 hadj))
    by_cases h : e.line i.castSucc = f.line i.castSucc
    · exact Or.inl (eq_of_adj_of_line_eq hσ hadj h)
    · refine Or.inr ?_
      show IsCollinear σ (firstPt σ d i e).1 (firstPt σ d i f).1
      rw [firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc he),
        firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc hf)]
      have hL2 : finrank K ↥(e.line i.castSucc ⊔ e.line i.succ) = 2 := by
        rw [← Frame.spanAt_pair, e.finrank_spanAt, Finset.card_pair (castSucc_ne_succ i)]
      have hLnd : Nondeg σ (e.line i.castSucc ⊔ e.line i.succ) := by
        rw [← Frame.spanAt_pair]
        exact e.nondeg_spanAt hσ _
      have hfL := line_mem_nsPts_of_adj hσ hadj
      exact isCollinear_of_le_plane hL2 hLnd ⟨le_sup_left, e.finrank_line _⟩
        ⟨hfL.1, hfL.2.1⟩ h

theorem eq_of_orth_of_le_sup {m : ℕ} {x L L' : Submodule K (Fin m → K)} (hx1 : finrank K x = 1)
    (hxnd : Nondeg σ x) (hL : finrank K L = 1) (hL' : finrank K L' = 1) (hxL : Orth σ x L)
    (hxL' : Orth σ x L') (hle : L ≤ x ⊔ L') : L = L' := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hL, hL'])
  intro v hv
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp (hle hv)
  have h1 : herm σ u (u + w) = 0 := hxL u hu _ hv
  rw [herm_add_right, hxL' u hu w hw, add_zero] at h1
  have hu0 : u = 0 := by
    by_contra hu0
    have hx : x = K ∙ u := (Submodule.eq_of_le_of_finrank_eq
      ((Submodule.span_singleton_le_iff_mem _ _).2 hu)
      (by rw [finrank_span_singleton hu0, hx1])).symm
    rw [hx] at hxnd
    exact herm_self_ne_zero_of_nondeg_span hu0 hxnd h1
  rw [hu0, zero_add]
  exact hw

theorem sup_line_eq_of_adj (hσ : IsUnitaryInvolution σ) {i : Fin n} {g f : Frame σ (n + 1)}
    (hadj : (frameSystem σ n).adj i g f) (hne : g.line i.castSucc ≠ f.line i.castSucc) :
    g.line i.castSucc ⊔ g.line i.succ = g.line i.castSucc ⊔ f.line i.castSucc := by
  have hfL := line_mem_nsPts_of_adj hσ hadj
  have hle : g.line i.castSucc ⊔ f.line i.castSucc ≤ g.line i.castSucc ⊔ g.line i.succ :=
    sup_le le_sup_left hfL.1
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [finrank_sup_of_ne_pts (g.finrank_line _) (f.finrank_line _) hne, ← Frame.spanAt_pair,
    g.finrank_spanAt, Finset.card_pair (castSucc_ne_succ i)]

theorem line_galleryEnd_of_separated {i : Fin n} {J₁ : Set (Fin n)}
    (hJ₁ : ∀ j ∈ J₁, Separated i j) {e : Frame σ (n + 1)} {α : List (Fin n × Frame σ (n + 1))}
    (hα : IsJGallery (frameSystem σ n) J₁ e α) :
    (galleryEnd e α).line i.castSucc = e.line i.castSucc := by
  refine residue_agree hα.mem_residue fun hk => ?_
  obtain ⟨j, hj, hkj⟩ := hk
  have hs := hJ₁ j hj
  rcases hkj with hkj | hkj
  · exact hs.castSucc_ne_castSucc hkj.symm
  · exact hs.succ_ne_castSucc hkj.symm

theorem exists_square (hσ : IsUnitaryInvolution σ) {i : Fin n} {J₁ : Set (Fin n)}
    (hJ₁ : ∀ j ∈ J₁, Separated i j) {g g' f f' : Frame σ (n + 1)}
    {μ : List (Fin n × Frame σ (n + 1))} (hμ : IsJGallery (frameSystem σ n) J₁ g μ)
    (hμe : galleryEnd g μ = g') (hf : (frameSystem σ n).adj i g f)
    (hf' : (frameSystem σ n).adj i g' f') (hline : f.line i.castSucc = f'.line i.castSucc) :
    ∃ μ' : List (Fin n × Frame σ (n + 1)), IsJGallery (frameSystem σ n) J₁ f μ' ∧
      galleryEnd f μ' = f' ∧
      (frameSystem σ n).TwoHomotopic g (μ ++ [(i, f')]) ((i, f) :: μ') := by
  have hrev : IsJGallery (frameSystem σ n) J₁ g' (galleryReverse g μ) := by
    have := hμ.reverse
    rwa [hμe] at this
  have hg : galleryEnd g' (galleryReverse g μ) = g := by
    have := galleryEnd_galleryReverse g μ
    rwa [hμe] at this
  obtain ⟨α', hα'g, hα'J, hα'end, hα'h⟩ := exists_push (X := frameSystem σ n) (J₁ := J₁)
    (j := i) (fun k hk => commuteTypes_of_separated hσ (hJ₁ k hk)) (galleryReverse g μ) f' g'
    (adj_symm hf') hrev.1 hrev.2
  rw [hg] at hα'end hα'h
  have hf₂ : galleryEnd f' α' = f := by
    refine eq_of_adj_of_line_eq hσ (adj_trans hα'end hf) ?_
    rw [line_galleryEnd_of_separated hJ₁ ⟨hα'g, hα'J⟩, hline]
  have hα' : IsJGallery (frameSystem σ n) J₁ f' α' := ⟨hα'g, hα'J⟩
  refine ⟨galleryReverse f' α', ?_, ?_, ?_⟩
  · have := hα'.reverse
    rwa [hf₂] at this
  · have := galleryEnd_galleryReverse f' α'
    rwa [hf₂] at this
  · have h1 := hα'h.reverse
    simp only [galleryEnd_cons, hg, galleryReverse_cons, galleryReverse_append,
      galleryReverse_nil, hf₂] at h1
    have h2 : galleryReverse g' (galleryReverse g μ) = μ := by
      have := galleryReverse_galleryReverse g μ
      rwa [hμe] at this
    rw [h2] at h1
    simpa using h1

section Edge

variable [Finite K] {q : ℕ}

theorem edge_aux (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {i : Fin n} {b : ℕ} (hib : i.val + 2 ≤ b) (hbn : b ≤ n) {c e e' f f' : Frame σ (n + 1)}
    {ρ ρ' : List (Fin n × Frame σ (n + 1))} {x' : Submodule K (Fin (n + 1) → K)}
    (he : e ∈ (frameSystem σ n).residue (typeInt n i.val b) c)
    (he' : e' ∈ (frameSystem σ n).residue (typeInt n i.val b) c)
    (hee' : e.line i.castSucc = e'.line i.castSucc) (hx : e.line i.castSucc ≠ x')
    (hρ : IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) e ρ)
    (hf : (frameSystem σ n).adj i (galleryEnd e ρ) f) (hfx : f.line i.castSucc = x')
    (hρ' : IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) e' ρ')
    (hf' : (frameSystem σ n).adj i (galleryEnd e' ρ') f') (hf'x : f'.line i.castSucc = x') :
    ∃ τ τ' : List (Fin n × Frame σ (n + 1)),
      IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) e τ ∧ galleryEnd e τ = e' ∧
      IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) f τ' ∧ galleryEnd f τ' = f' ∧
      (frameSystem σ n).TwoHomotopic e (τ ++ ρ' ++ [(i, f')]) (ρ ++ (i, f) :: τ') := by
  set a : ℕ := i.val with ha
  set g := galleryEnd e ρ with hg
  set g' := galleryEnd e' ρ' with hg'
  have hge : g ∈ (frameSystem σ n).residue (typeInt n (a + 1) b) e := hρ.mem_residue
  have hg'e : g' ∈ (frameSystem σ n).residue (typeInt n (a + 1) b) e' := hρ'.mem_residue
  have hgQ : g ∈ (frameSystem σ n).residue (typeInt n a b) c :=
    mem_residue_trans he (residue_mono (typeInt_mono (Nat.le_succ a) le_rfl) e hge)
  have hg'Q : g' ∈ (frameSystem σ n).residue (typeInt n a b) c :=
    mem_residue_trans he' (residue_mono (typeInt_mono (Nat.le_succ a) le_rfl) e' hg'e)
  have hnot : i.castSucc ∉ posInt n (a + 1) b := by
    rw [mem_posInt]
    simp only [Fin.val_castSucc]
    omega
  have hga : g.line i.castSucc = e.line i.castSucc := residue_typeInt_agree hge hnot
  have hg'a : g'.line i.castSucc = e'.line i.castSucc := residue_typeInt_agree hg'e hnot
  have hgg' : g'.line i.castSucc = g.line i.castSucc := by rw [hga, hg'a, hee']
  have hne : g.line i.castSucc ≠ f.line i.castSucc := by
    rw [hga, hfx]
    exact hx
  have hne' : g'.line i.castSucc ≠ f'.line i.castSucc := by
    rw [hg'a, ← hee', hf'x]
    exact hx
  have hplane := sup_line_eq_of_adj hσ hf hne
  have hplane' := sup_line_eq_of_adj hσ hf' hne'
  have hline1 : g.line i.succ = g'.line i.succ := by
    refine eq_of_orth_of_le_sup (g.finrank_line _) (g.nondeg_line _) (g.finrank_line _)
      (g'.finrank_line _) (g.orth_line _ _ (castSucc_ne_succ i)) ?_ ?_
    · rw [← hgg']
      exact g'.orth_line _ _ (castSucc_ne_succ i)
    · calc g.line i.succ ≤ g.line i.castSucc ⊔ g.line i.succ := le_sup_right
        _ = g.line i.castSucc ⊔ f.line i.castSucc := hplane
        _ = g'.line i.castSucc ⊔ f'.line i.castSucc := by rw [hgg', hfx, hf'x]
        _ = g'.line i.castSucc ⊔ g'.line i.succ := hplane'.symm
        _ = g.line i.castSucc ⊔ g'.line i.succ := by rw [hgg']
  have hres : g' ∈ (frameSystem σ n).residue (typeInt n (a + 2) b) g := by
    refine (mem_residue_typeInt_iff hσ hK hq (by omega) hbn).2 fun k hk => ?_
    by_cases hka : k = i.castSucc
    · rw [hka]
      exact hgg'
    · by_cases hks : k = i.succ
      · rw [hks]
        exact hline1.symm
      · have hk' : k ∉ posInt n a b := by
          rw [mem_posInt] at hk ⊢
          have h1 : k.val ≠ a := fun h => hka (Fin.ext (by simpa using h))
          have h2 : k.val ≠ a + 1 := fun h => hks (Fin.ext (by simpa using h))
          omega
        rw [residue_typeInt_agree hg'Q hk', residue_typeInt_agree hgQ hk']
  obtain ⟨μ, hμ, hμe⟩ := mem_residue_iff_exists_isJGallery.1 hres
  have hJsub : typeInt n (a + 2) b ⊆ typeInt n (a + 1) b := typeInt_mono (by omega) le_rfl
  obtain ⟨μ', hμ'J, hμ'e, hsq⟩ := exists_square hσ (J₁ := typeInt n (a + 2) b)
    (fun j hj => Or.inl (by have := hj.1; omega)) hμ hμe hf hf' (by rw [hfx, hf'x])
  refine ⟨ρ ++ (μ ++ galleryReverse e' ρ'), μ', ?_, ?_, hμ'J.mono hJsub, hμ'e, ?_⟩
  · refine hρ.append ((hμ.mono hJsub).append ?_)
    rw [hμe]
    exact hρ'.reverse
  · rw [galleryEnd_append, galleryEnd_append, hμe]
    exact galleryEnd_galleryReverse e' ρ'
  · have hend : galleryEnd e (ρ ++ μ) = g' := by rw [galleryEnd_append, hμe]
    have h1 : (frameSystem σ n).TwoHomotopic (galleryEnd e (ρ ++ μ))
        ((galleryReverse e' ρ' ++ ρ') ++ [(i, f')]) ([] ++ [(i, f')]) := by
      rw [hend]
      exact (twoHomotopic_reverse_append hρ'.1).append_right _
    have h2 := TwoHomotopic.append_left (X := frameSystem σ n) (x := e) (ρ ++ μ) h1
    have h3 := TwoHomotopic.append_left (X := frameSystem σ n) (x := e) ρ hsq
    have e1 : (ρ ++ (μ ++ galleryReverse e' ρ')) ++ ρ' ++ [(i, f')] =
        (ρ ++ μ) ++ ((galleryReverse e' ρ' ++ ρ') ++ [(i, f')]) := by simp
    have e2 : (ρ ++ μ) ++ ([] ++ [(i, f')]) = ρ ++ (μ ++ [(i, f')]) := by simp
    rw [e1]
    refine h2.trans ?_
    rw [e2]
    exact h3

end Edge

section Instance

variable [Finite K] {q : ℕ}

theorem frameFib_conn (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ} (hib : i.val < b)
    (hbn : b ≤ n) (c : Frame σ (n + 1)) (hc : c.spanAt (posInt n i.val b) ≤ W)
    {e e' : Frame σ (n + 1)} (he : (frameFib hσ d i hib c hc).Q e)
    (he' : (frameFib hσ d i hib c hc).Q e')
    (hP : (frameFib hσ d i hib c hc).P e = (frameFib hσ d i hib c hc).P e') :
    ∃ τ : List (Fin n × Frame σ (n + 1)),
      IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) e τ ∧ galleryEnd e τ = e' := by
  have hline : e.line i.castSucc = e'.line i.castSucc := by
    have := congrArg Subtype.val hP
    change (firstPt σ d i e).1 = (firstPt σ d i e').1 at this
    rwa [firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc he),
      firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc he')] at this
  have : e' ∈ (frameSystem σ n).residue (typeInt n (i.val + 1) b) e := by
    refine (mem_residue_typeInt_iff hσ hK hq (by omega) hbn).2 fun k hk => ?_
    by_cases hka : k = i.castSucc
    · rw [hka]
      exact hline.symm
    · have hk' : k ∉ posInt n i.val b := by
        rw [mem_posInt] at hk ⊢
        have h1 : k.val ≠ i.val := fun h => hka (Fin.ext (by simpa using h))
        omega
      rw [residue_typeInt_agree he' hk', residue_typeInt_agree he hk']
  exact mem_residue_iff_exists_isJGallery.1 this |>.imp fun τ hτ => hτ

theorem frameFib_lift (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ} (hib : i.val < b)
    (hbn : b ≤ n) (c : Frame σ (n + 1)) (hc : c.spanAt (posInt n i.val b) ≤ W)
    {D : ↥(nsPts σ W) → Prop} (hD : ∀ x, D x → x.1 ≤ c.spanAt (posInt n i.val b))
    {e : Frame σ (n + 1)} {x' : ↥(nsPts σ W)} (he : (frameFib hσ d i hib c hc).Q e) (hDx : D x')
    (hadj : (collGraph σ W).Adj ((frameFib hσ d i hib c hc).P e) x') :
    ∃ (ρ : List (Fin n × Frame σ (n + 1))) (f : Frame σ (n + 1)),
      IsJGallery (frameSystem σ n) (typeInt n (i.val + 1) b) e ρ ∧
      (frameSystem σ n).adj i (galleryEnd e ρ) f ∧
      (frameFib hσ d i hib c hc).P f = x' ∧ (frameFib hσ d i hib c hc).Q f := by
  have hPe : ((frameFib hσ d i hib c hc).P e).1 = e.line i.castSucc :=
    firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc he)
  have hx' : x'.1 ∈ nsPts σ (e.spanAt (posInt n i.val b)) := by
    refine ⟨?_, x'.2.2.1, x'.2.2.2⟩
    rw [spanAt_posInt_of_mem_residue hσ he]
    exact hD x' hDx
  have hcol : IsCollinear σ (e.line i.castSucc) x'.1 := by
    rw [← hPe]
    exact hadj
  obtain ⟨ρ, f, hρ, hf, hfx⟩ := exists_edge_lift hσ hK hq hib hbn hx' hcol
  have hQf : (frameFib hσ d i hib c hc).Q f := by
    refine (frameFib hσ d i hib c hc).step_Q (Set.mem_insert _ _) hf ?_
    exact (frameFib hσ d i hib c hc).Q_galleryEnd he (hρ.mono (Set.subset_insert _ _))
  refine ⟨ρ, f, hρ, hf, ?_, hQf⟩
  refine Subtype.ext ?_
  change (firstPt σ d i f).1 = x'.1
  rw [firstPt_val (line_mem_nsPts_of_mem_residue hσ hib.le hc hQf), hfx]

theorem frameFib_rigid (hσ : IsUnitaryInvolution σ) (hK : Nat.card K = q ^ 2) (hq : 3 ≤ q)
    {W : Submodule K (Fin (n + 1) → K)} (d : ↥(nsPts σ W)) (i : Fin n) {b : ℕ}
    (hib : i.val + 2 ≤ b) (hbn : b ≤ n) (c : Frame σ (n + 1))
    (hc : c.spanAt (posInt n i.val b) ≤ W) (hnull : NullOn σ n (typeInt n (i.val + 1) b)) :
    (frameFib hσ d i (by omega) c hc).Rigid := by
  refine ⟨fun {e γ} _ hγ hend => hnull e γ hγ.1 hγ.2 hend, ?_⟩
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

end Instance


end FirstLine

end CFSG.ClassicalInvolution.Phan
