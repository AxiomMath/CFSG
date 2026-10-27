module

public import CFSG.ClassicalInvolution.Phan.PhanS1Fib
public import CFSG.ClassicalInvolution.Phan.PhanS0Graph

public section

namespace CFSG.ClassicalInvolution.PhanB3.S

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]
  {hK : Nat.card K = (p ^ f) ^ 2} {F : Type} [Field F] {h2 : (2 : F) ≠ 0}
  {C : B2Coord hK F h2} {G : Type} [Group G] {S : PhanFamilyB3 C G}

section Assembly

theorem phanFib_lift {e : G ⧸ torusSub S} {x' : G ⧸ parab S {1, 2}}
    (hΓ : (ptGraph S).Adj (ptMap S e) x') :
    ∃ (ρ : List (Fin 3 × G ⧸ torusSub S)) (g : G ⧸ torusSub S),
      IsJGallery (phanSystem S) {1, 2} e ρ ∧ (phanSystem S).adj 0 (galleryEnd e ρ) g ∧
        ptMap S g = x' := by
  obtain ⟨-, c, d, hc, hd, hadj⟩ := hΓ
  obtain ⟨ρ, hρ, hρe⟩ := mem_residue_iff_exists_isJGallery.1 ((ptMap_eq_iff e c).1 hc.symm)
  exact ⟨ρ, d, hρ, by rw [hρe]; exact hadj, hd⟩

theorem exists_fibre_gallery {e e' : G ⧸ torusSub S} (h : ptMap S e = ptMap S e') :
    ∃ τ, IsJGallery (phanSystem S) {1, 2} e τ ∧ galleryEnd e τ = e' :=
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
@[expose] def Null2 (h0 : PtStep0 S) {x : G ⧸ parab S {1, 2}} (w : (ptGraph S).Walk x x) :
    Prop :=
  ∃ J₀ : Set (Fin 3), J₀.encard ≤ 2 ∧
    ∃ (e₁ : G ⧸ torusSub S) (γ₁ τ₁ : List (Fin 3 × G ⧸ torusSub S)),
      (phanFib S h0).Lift w e₁ γ₁ ∧ (∀ i ∈ galleryType γ₁, i ∈ J₀) ∧
      IsJGallery (phanSystem S) {1, 2} (galleryEnd e₁ γ₁) τ₁ ∧
      (∀ i ∈ galleryType τ₁, i ∈ J₀) ∧ galleryEnd (galleryEnd e₁ γ₁) τ₁ = e₁

theorem fibreNull_of_null2 (h0 : PtStep0 S) (he : PtEdge S) {x : G ⧸ parab S {1, 2}}
    {w : (ptGraph S).Walk x x} (hw : Null2 S h0 w) : (phanFib S h0).FibreNull w := by
  obtain ⟨J₀, hJ₀, e₁, γ₁, τ₁, hl, hγJ, hτ, hτJ, hτe⟩ := hw
  refine (phanFib_rigid h0 he).fibreNull_of_exists
    (fun {e e'} _ _ hP => exists_fibre_gallery hP) (trivial : (phanFib S h0).Q e₁) hl hτ hτe ?_
  refine twoHomotopic_of_types hJ₀ (hl.isJGallery.1.append hτ.1) (isGallery_nil e₁) ?_ (by simp)
    (by rw [galleryEnd_append, hτe]; rfl)
  intro i hi
  rw [galleryType_append, List.mem_append] at hi
  rcases hi with hi | hi
  · exact hγJ i hi
  · exact hτJ i hi

variable (S) in
@[expose] def null2Walks (h0 : PtStep0 S) : ∀ x : G ⧸ parab S {1, 2}, Set ((ptGraph S).Walk x x) :=
  fun _ => {w | Null2 S h0 w}

variable (S) in
structure PhanB3PointGeometry : Prop where
  step0 : PtStep0 S
  edge : PtEdge S
  connected : (ptGraph S).Connected
  ediam_le_two : (ptGraph S).ediam ≤ 2
  tri : ∀ (a b c : G ⧸ parab S {1, 2}) (hab : (ptGraph S).Adj a b) (hbc : (ptGraph S).Adj b c)
    (hca : (ptGraph S).Adj c a),
    CycleHomotopic (null2Walks S step0)
      (.cons hab (.cons hbc (.cons hca .nil)) : (ptGraph S).Walk a a) .nil
  quad : QuadNull (ptGraph S)
  pent : PentNull (ptGraph S)

theorem PhanB3PointGeometry.connected_phanSystem (H : PhanB3PointGeometry S) :
    (phanSystem S).Connected :=
  phanSystem_connected H.step0 H.connected

theorem PhanB3PointGeometry.simplyTwoConnected_phanSystem (H : PhanB3PointGeometry S) :
    (phanSystem S).SimplyTwoConnected := by
  let F := phanFib S H.step0
  have R := phanFib_rigid H.step0 H.edge
  let E : ∀ x : G ⧸ parab S {1, 2}, Set ((ptGraph S).Walk x x) :=
    fun _ => {c | F.FibreNull c}
  have h3 : ∀ {u : G ⧸ parab S {1, 2}} (q : (ptGraph S).Walk u u), q.length = 3 →
      CycleHomotopic E q .nil := by
    intro u q hq
    match u, q, hq with
    | _, .cons hab (.cons hbc (.cons hca .nil)), _ =>
      exact cycleHomotopic_mono (fun x c hc =>
        cycleHomotopic_of_mem E (fibreNull_of_null2 H.step0 H.edge hc)) (H.tri _ _ _ hab hbc hca)
  have htriv := cycleTrivial_of_cycles_le_five_B3 E H.connected H.ediam_le_two h3 H.quad H.pent
  intro x γ hγ hend
  refine R.twoHomotopic_nil (E := E) (fun _ _ hc => hc)
    (fun {e x'} _ hΓ => by
      obtain ⟨ρ, g, h1, h2', h3⟩ := phanFib_lift hΓ
      exact ⟨ρ, g, h1, h2', h3, trivial⟩) htriv (trivial : F.Q x)
    ⟨hγ, fun i _ => ?_⟩ hend
  fin_cases i <;> simp [phanFib]

end Assembly

end CFSG.ClassicalInvolution.PhanB3.S
