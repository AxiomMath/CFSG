module

public import CFSG.ClassicalInvolution.Phan.PhanG8Line
public import CFSG.ClassicalInvolution.Phan.PhanG7Point

public section

namespace CFSG.ClassicalInvolution.PhanG

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalInvolution.PhanD4
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {G : Type} [Group G] {S : PhanFamilyD4 K p f G}

section Points

theorem mem_residue_mk_iff (J : Set (Fin 4)) (a b : G) :
    (b : G ⧸ torusSub S) ∈ (phanSystem S).residue J (a : G ⧸ torusSub S) ↔
      a⁻¹ * b ∈ parab S J := by
  rw [mem_parab_iff]
  constructor
  · intro h
    have h' := (phanSystem_isMorphism_smul (S := S) a⁻¹).mapsTo_residue J
      (a : G ⧸ torusSub S) h
    simp only [smul_mk, inv_mul_cancel] at h'
    exact h'
  · intro h
    have h' := (phanSystem_isMorphism_smul (S := S) a).mapsTo_residue J
      ((1 : G) : G ⧸ torusSub S) h
    simp only [smul_mk, mul_one, mul_inv_cancel_left] at h'
    exact h'

variable (S) in
@[expose] noncomputable def ptMap : G ⧸ torusSub S → G ⧸ parab S {1, 2, 3} :=
  cosetMap (MonoidHom.id G) (parab S {1, 2, 3}) (torusSub S)
    (by simpa using torusSub_le_parab (S := S) {1, 2, 3})

theorem ptMap_mk (a : G) :
    ptMap S (a : G ⧸ torusSub S) = (a : G ⧸ parab S {1, 2, 3}) := rfl

theorem ptMap_eq_iff (c d : G ⧸ torusSub S) :
    ptMap S c = ptMap S d ↔ d ∈ (phanSystem S).residue {1, 2, 3} c := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective d
  rw [ptMap_mk, ptMap_mk, QuotientGroup.eq, mem_residue_mk_iff]

variable (S) in
@[expose] def ptGraph : SimpleGraph (G ⧸ parab S {1, 2, 3}) where
  Adj x y := x ≠ y ∧ ∃ c d : G ⧸ torusSub S, ptMap S c = x ∧ ptMap S d = y ∧
    (phanSystem S).adj 0 c d
  symm := ⟨fun _ _ ⟨hne, c, d, hc, hd, h⟩ => ⟨hne.symm, d, c, hd, hc, adj_symm h⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem ptGraph_adj_of_adj {c d : G ⧸ torusSub S} (h : (phanSystem S).adj 0 c d)
    (hne : ptMap S c ≠ ptMap S d) : (ptGraph S).Adj (ptMap S c) (ptMap S d) :=
  ⟨hne, c, d, rfl, rfl, h⟩

variable (S) in
@[expose] def PtStep0 : Prop :=
  ∀ {e g : G ⧸ torusSub S}, (phanSystem S).adj 0 e g → ptMap S e = ptMap S g → e = g

variable (S) in
@[expose] def PtEdge : Prop :=
  ∀ {a b c d : G ⧸ torusSub S}, (phanSystem S).adj 0 a c → (phanSystem S).adj 0 b d →
    ptMap S a = ptMap S b → ptMap S c = ptMap S d → ptMap S a ≠ ptMap S c →
      d ∈ (phanSystem S).residue {2, 3} c ∧ b ∈ (phanSystem S).residue {2, 3} a

variable (S) in
@[expose] noncomputable def phanFib (h0 : PtStep0 S) : Fib (phanSystem S) (ptGraph S) where
  P := ptMap S
  a := 0
  J' := {1, 2, 3}
  Q := fun _ => True
  step_Q := fun _ _ _ => trivial
  step_P := fun {i e g} hi hadj _ =>
    (ptMap_eq_iff e g).2 (residue_mono (Set.singleton_subset_iff.2 hi) e
      (mem_residue_singleton.2 hadj))
  step_a := fun {e g} hadj _ => by
    by_cases h : ptMap S e = ptMap S g
    · exact Or.inl (h0 hadj h)
    · exact Or.inr (ptGraph_adj_of_adj hadj h)

end Points

section Rigid

variable (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S)
  (h2 : (2 : K) ≠ 0)

theorem twoHomotopic_of_nullOn {J : Set (Fin 4)} (hJ : NullOnPhan S J) {x : G ⧸ torusSub S}
    {γ₁ γ₂ : List (Fin 4 × G ⧸ torusSub S)} (h₁ : (phanSystem S).IsGallery x γ₁)
    (h₂ : (phanSystem S).IsGallery x γ₂) (hJ₁ : ∀ i ∈ galleryType γ₁, i ∈ J)
    (hJ₂ : ∀ i ∈ galleryType γ₂, i ∈ J) (hend : galleryEnd x γ₁ = galleryEnd x γ₂) :
    (phanSystem S).TwoHomotopic x γ₁ γ₂ := by
  have h₂' : (phanSystem S).IsGallery (galleryEnd x γ₁) (galleryReverse x γ₂) := by
    rw [hend]
    exact h₂.reverse
  have hc : (phanSystem S).IsGallery x (γ₁ ++ galleryReverse x γ₂) := h₁.append h₂'
  have hend' : galleryEnd x (γ₁ ++ galleryReverse x γ₂) = x := by
    rw [galleryEnd_append, hend, galleryEnd_galleryReverse]
  have hJc : ∀ i ∈ galleryType (γ₁ ++ galleryReverse x γ₂), i ∈ J := by
    intro i hi
    rw [galleryType_append, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hJ₁ i hi
    · rw [galleryType_galleryReverse, List.mem_reverse] at hi
      exact hJ₂ i hi
  have h0 := hJ x _ hc hJc hend'
  have hrev : (phanSystem S).TwoHomotopic (galleryEnd x γ₁) (galleryReverse x γ₂ ++ γ₂) [] := by
    rw [hend]
    exact twoHomotopic_reverse_append h₂
  have h1 := TwoHomotopic.append_left (X := phanSystem S) (x := x) γ₁ hrev
  have h2' := h0.append_right γ₂
  simp only [List.nil_append, List.append_assoc, List.append_nil] at h1 h2'
  exact h1.symm.trans h2'

theorem pair_subset_triple : ({2, 3} : Set (Fin 4)) ⊆ {1, 2, 3} := by
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  rcases hi with rfl | rfl <;> simp

theorem pair_subset_triple' : ({2, 3} : Set (Fin 4)) ⊆ {0, 2, 3} := by
  intro i hi
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
  rcases hi with rfl | rfl <;> simp

include hK hq hg h2 in
theorem phanFib_rigid (h0 : PtStep0 S) (he : PtEdge S) : (phanFib S h0).Rigid where
  null := fun {e γ} _ hγ hend => nullOn_123 hK hq hg h2 e γ hγ.1 hγ.2 hend
  edge := by
    intro e e' f g ρ ρ' x' _ _ hPe hΓ hρ hf hPf hρ' hf' hPf'
    have hP1 : ptMap S (galleryEnd e ρ) = ptMap S e :=
      (phanFib S h0).P_galleryEnd trivial hρ
    have hP1' : ptMap S (galleryEnd e' ρ') = ptMap S e' :=
      (phanFib S h0).P_galleryEnd trivial hρ'
    have hPe' : ptMap S e = ptMap S e' := hPe
    have hPf₁ : ptMap S f = x' := hPf
    have hPf₂ : ptMap S g = x' := hPf'
    have hne : ptMap S (galleryEnd e ρ) ≠ ptMap S f := by
      rw [hP1, hPf₁]
      exact hΓ.1
    obtain ⟨hgres, hE'res⟩ := he hf hf' (hP1.trans (hPe'.trans hP1'.symm))
      (hPf₁.trans hPf₂.symm) hne
    obtain ⟨τ₂₃, hτ₂₃, hτ₂₃e⟩ := mem_residue_iff_exists_isJGallery.1 hE'res
    obtain ⟨τ', hτ', hτ'e⟩ := mem_residue_iff_exists_isJGallery.1 hgres
    have hτ₂₃J : IsJGallery (phanSystem S) {1, 2, 3} (galleryEnd e ρ) τ₂₃ :=
      hτ₂₃.mono pair_subset_triple
    have hcat₁ : IsJGallery (phanSystem S) {1, 2, 3} e (ρ ++ τ₂₃) := hρ.append hτ₂₃J
    have hend₁ : galleryEnd e (ρ ++ τ₂₃) = galleryEnd e' ρ' := by
      rw [galleryEnd_append, hτ₂₃e]
    have hrevJ : IsJGallery (phanSystem S) {1, 2, 3} (galleryEnd e (ρ ++ τ₂₃))
        (galleryReverse e' ρ') := by
      rw [hend₁]
      exact hρ'.reverse
    refine ⟨ρ ++ τ₂₃ ++ galleryReverse e' ρ', τ', hcat₁.append hrevJ, ?_,
      hτ'.mono pair_subset_triple, hτ'e, ?_⟩
    · rw [galleryEnd_append, hend₁, galleryEnd_galleryReverse]
    ·
      have hrev : (phanSystem S).TwoHomotopic (galleryEnd e' ρ')
          (galleryReverse e' ρ' ++ ρ') [] := twoHomotopic_reverse_append hρ'.1
      have hA : (phanSystem S).TwoHomotopic e
          (ρ ++ τ₂₃ ++ galleryReverse e' ρ' ++ ρ' ++ [(0, g)])
          (ρ ++ τ₂₃ ++ [(0, g)]) := by
        have e1 : ρ ++ τ₂₃ ++ galleryReverse e' ρ' ++ ρ' ++ [(0, g)] =
            (ρ ++ τ₂₃) ++ ((galleryReverse e' ρ' ++ ρ') ++ [(0, g)]) := by simp
        have e2 : ρ ++ τ₂₃ ++ [(0, g)] = (ρ ++ τ₂₃) ++ ([] ++ [(0, g)]) := by simp
        rw [e1, e2]
        refine TwoHomotopic.append_left (X := phanSystem S) (x := e) (ρ ++ τ₂₃) ?_
        rw [hend₁]
        exact hrev.append_right [(0, g)]
      have hB : (phanSystem S).TwoHomotopic (galleryEnd e ρ) (τ₂₃ ++ [(0, g)])
          ((0, f) :: τ') := by
        refine twoHomotopic_of_nullOn (nullOn_023 hK (by omega) hg) ?_ ?_ ?_ ?_ ?_
        · refine hτ₂₃.1.append ?_
          rw [hτ₂₃e]
          exact ⟨hf', trivial⟩
        · exact ⟨hf, hτ'.1⟩
        · intro i hi
          rw [galleryType_append, List.mem_append] at hi
          rcases hi with hi | hi
          · exact pair_subset_triple' (hτ₂₃.2 i hi)
          · simp [galleryType] at hi
            subst hi
            simp
        · intro i hi
          simp only [galleryType, List.map_cons, List.mem_cons] at hi
          rcases hi with rfl | hi
          · simp
          · exact pair_subset_triple' (hτ'.2 i (by simpa [galleryType] using hi))
        · rw [galleryEnd_append, hτ₂₃e]
          simp only [galleryEnd_cons]
          rw [hτ'e]
          simp
      have hB' := TwoHomotopic.append_left (X := phanSystem S) (x := e) ρ hB
      have e3 : ρ ++ τ₂₃ ++ [(0, g)] = ρ ++ (τ₂₃ ++ [(0, g)]) := by simp
      show (phanSystem S).TwoHomotopic e
        (ρ ++ τ₂₃ ++ galleryReverse e' ρ' ++ ρ' ++ [(0, g)]) (ρ ++ (0, f) :: τ')
      rw [e3] at hA
      exact hA.trans hB'

end Rigid

section Assembly

variable (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) (hg : GoodFamily S)
  (h2 : (2 : K) ≠ 0)

theorem phanFib_lift {e : G ⧸ torusSub S} {x' : G ⧸ parab S {1, 2, 3}}
    (hΓ : (ptGraph S).Adj (ptMap S e) x') :
    ∃ (ρ : List (Fin 4 × G ⧸ torusSub S)) (g : G ⧸ torusSub S),
      IsJGallery (phanSystem S) {1, 2, 3} e ρ ∧ (phanSystem S).adj 0 (galleryEnd e ρ) g ∧
        ptMap S g = x' := by
  obtain ⟨-, c, d, hc, hd, hadj⟩ := hΓ
  obtain ⟨ρ, hρ, hρe⟩ := mem_residue_iff_exists_isJGallery.1 ((ptMap_eq_iff e c).1 hc.symm)
  exact ⟨ρ, d, hρ, by rw [hρe]; exact hadj, hd⟩

theorem exists_fibre_gallery {e e' : G ⧸ torusSub S} (h : ptMap S e = ptMap S e') :
    ∃ τ, IsJGallery (phanSystem S) {1, 2, 3} e τ ∧ galleryEnd e τ = e' :=
  mem_residue_iff_exists_isJGallery.1 ((ptMap_eq_iff e e').1 h)

theorem phanSystem_connected (h0 : PtStep0 S) (hc : (ptGraph S).Connected) :
    (phanSystem S).Connected := by
  intro x y
  obtain ⟨w⟩ := hc.preconnected (ptMap S x) (ptMap S y)
  obtain ⟨γ, hγ⟩ := (phanFib S h0).exists_lift (D := fun _ => True)
    (fun {e x'} _ _ _ hΓ => by
      obtain ⟨ρ, g, h1, h2, h3⟩ := phanFib_lift hΓ
      exact ⟨ρ, g, h1, h2, h3, trivial⟩) w (fun _ _ => trivial) x trivial rfl
  have hend : ptMap S (galleryEnd x γ) = ptMap S y := hγ.end_eq trivial
  obtain ⟨τ, hτ, hτe⟩ := exists_fibre_gallery hend
  refine ⟨γ ++ τ, hγ.isJGallery.1.append hτ.1, ?_⟩
  rw [galleryEnd_append, hτe]

variable (S) in
@[expose] def SolidNull (h0 : PtStep0 S) {x : G ⧸ parab S {1, 2, 3}}
    (w : (ptGraph S).Walk x x) : Prop :=
  ∃ J₀ : Set (Fin 4), (J₀ = {0, 1, 2} ∨ J₀ = {0, 1, 3}) ∧
    ∃ (e₁ : G ⧸ torusSub S) (γ₁ τ₁ : List (Fin 4 × G ⧸ torusSub S)),
      (phanFib S h0).Lift w e₁ γ₁ ∧ (∀ i ∈ galleryType γ₁, i ∈ J₀) ∧
      IsJGallery (phanSystem S) {1, 2, 3} (galleryEnd e₁ γ₁) τ₁ ∧
      (∀ i ∈ galleryType τ₁, i ∈ J₀) ∧ galleryEnd (galleryEnd e₁ γ₁) τ₁ = e₁

include hK hq hg h2 in
theorem fibreNull_of_solidNull (h0 : PtStep0 S) (he : PtEdge S) {x : G ⧸ parab S {1, 2, 3}}
    {w : (ptGraph S).Walk x x} (hw : SolidNull S h0 w) : (phanFib S h0).FibreNull w := by
  obtain ⟨J₀, hJ₀, e₁, γ₁, τ₁, hl, hγJ, hτ, hτJ, hτe⟩ := hw
  have hN : NullOnPhan S J₀ := by
    rcases hJ₀ with rfl | rfl
    · exact nullOn_012 hK hq hg h2
    · exact nullOn_013 hK hq hg h2
  refine (phanFib_rigid hK hq hg h2 h0 he).fibreNull_of_exists
    (fun {e e'} _ _ hP => exists_fibre_gallery hP) (trivial : (phanFib S h0).Q e₁) hl hτ hτe ?_
  refine hN e₁ (γ₁ ++ τ₁) (hl.isJGallery.1.append hτ.1) ?_ ?_
  · intro i hi
    rw [galleryType_append, List.mem_append] at hi
    rcases hi with hi | hi
    · exact hγJ i hi
    · exact hτJ i hi
  · rw [galleryEnd_append, hτe]

end Assembly

end CFSG.ClassicalInvolution.PhanG
