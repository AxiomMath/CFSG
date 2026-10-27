module

public import CFSG.ClassicalInvolution.Phan.Phan3KerA3
public import CFSG.ClassicalInvolution.Phan.PhanD1Family
public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanD4

variable {Y : Type} [Group Y]

@[expose] def genIdx8 : Fin 8 → Fin 4 := ![0, 0, 1, 1, 2, 2, 3, 3]

@[expose] noncomputable def genElt8 : Fin 8 → Su K9 3 1 2 := ![A2, B2, A2, B2, A2, B2, A2, B2]

@[expose] noncomputable def d4Gens (F : PhanFamilyD4 K9 3 1 Y) : Fin 8 → Y := fun i =>
  F.ι (genIdx8 i) (genElt8 i)

@[expose] def edgeGen (e : Fin 3) : Fin 4 → Fin 8 :=
  ![![0, 1, 2, 3], ![2, 3, 4, 5], ![2, 3, 6, 7]] e

@[expose] def edgeLetter (e : Fin 3) (l : Fin 4 × Bool) : Fin 8 × Bool := (edgeGen e l.1, l.2)

theorem wordVal_map_reindex {G H : Type*} [Group G] [Group H] (θ : G →* H) {n k : Nat}
    (g : Fin n → H) (h : Fin k → G) (f : Fin k → Fin n) (hgh : ∀ i, g (f i) = θ (h i))
    (r : List (Fin k × Bool)) :
    wordVal g (r.map fun l => (f l.1, l.2)) = θ (wordVal h r) := by
  induction r with
  | nil => simp [wordVal]
  | cons l r ih =>
    simp only [wordVal, List.map_cons, List.prod_cons, map_mul] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b <;> simp [letterVal, hgh i]

theorem d4Gens_edge (F : PhanFamilyD4 K9 3 1 Y) (e : Fin 3) (k : Fin 4) :
    d4Gens F (edgeGen e k) = F.θ e (x3 k) := by
  fin_cases e <;> fin_cases k
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.left 0)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.left 0)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.right 0)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.right 0)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.left 1)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.left 1)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.right 1)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.right 1)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.left 2)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.left 2)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ A2) (F.right 2)).symm
  · exact (congrArg (fun φ : Su K9 3 1 2 →* Y => φ B2) (F.right 2)).symm

theorem wordVal_edge (F : PhanFamilyD4 K9 3 1 Y) (e : Fin 3) {r : List (Fin 4 × Bool)}
    (hr : r ∈ su3Rels) : wordVal (d4Gens F) (r.map (edgeLetter e)) = 1 := by
  have := wordVal_map_reindex (F.θ e) (d4Gens F) x3 (edgeGen e) (d4Gens_edge F e) r
  rw [wordVal_x3_su3Rels r hr, map_one] at this
  exact this

@[expose] def commWord8 (g h : Fin 8) : List (Fin 8 × Bool) :=
  [(g, true), (h, true), (g, false), (h, false)]

theorem wordVal_commWord8 (x : Fin 8 → Y) {g h : Fin 8} (hc : x g * x h = x h * x g) :
    wordVal x (commWord8 g h) = 1 := by
  simp only [commWord8, wordVal, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    letterVal, Bool.cond_true, Bool.cond_false, mul_one]
  calc x g * (x h * ((x g)⁻¹ * (x h)⁻¹)) = (x g * x h) * (x g)⁻¹ * (x h)⁻¹ := by group
    _ = 1 := by rw [hc]; group

theorem d4Gens_comm (F : PhanFamilyD4 K9 3 1 Y) {g h : Fin 8}
    (hij : genIdx8 g ≠ genIdx8 h) (h1 : ¬ Timmesfeld.edgeD 4 (genIdx8 g) (genIdx8 h))
    (h2 : ¬ Timmesfeld.edgeD 4 (genIdx8 h) (genIdx8 g)) :
    d4Gens F g * d4Gens F h = d4Gens F h * d4Gens F g :=
  F.comm (genIdx8 g) (genIdx8 h) hij h1 h2 _ _

theorem d4RankTwoRels_cases : ∀ w ∈ d4RankTwoRels,
    (∃ e : Fin 3, ∃ r ∈ su3Rels, w = r.map (edgeLetter e)) ∨
      (∃ g h : Fin 8, genIdx8 g ≠ genIdx8 h ∧ ¬ Timmesfeld.edgeD 4 (genIdx8 g) (genIdx8 h) ∧
        ¬ Timmesfeld.edgeD 4 (genIdx8 h) (genIdx8 g) ∧ w = commWord8 g h) := by
  decide +kernel

theorem wordVal_d4RankTwoRels (F : PhanFamilyD4 K9 3 1 Y) :
    ∀ w ∈ d4RankTwoRels, wordVal (d4Gens F) w = 1 := by
  intro w hw
  rcases d4RankTwoRels_cases w hw with ⟨e, r, hr, rfl⟩ | ⟨g, h, h0, h1, h2, rfl⟩
  · exact wordVal_edge F e hr
  · exact wordVal_commWord8 _ (d4Gens_comm F h0 h1 h2)

@[expose] noncomputable def d4Gens6 (F : PhanFamilyD4 K9 3 1 Y) : Fin 6 → Y := fun i =>
  d4Gens F ⟨i.val, by omega⟩

theorem wordVal_liftWord68 (F : PhanFamilyD4 K9 3 1 Y) (w : List (Fin 6 × Bool)) :
    wordVal (d4Gens F) (liftWord68 w) = wordVal (d4Gens6 F) w := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    simp only [liftWord68, wordVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    rfl

theorem wordVal_phanA3Rels_d4 (F : PhanFamilyD4 K9 3 1 Y) :
    ∀ w ∈ phanA3Rels, wordVal (d4Gens6 F) w = 1 := by
  intro w hw
  have hmem : liftWord68 w ∈ d4RankTwoRels := by
    have : ∀ w ∈ phanA3Rels, liftWord68 w ∈ d4RankTwoRels := by decide +kernel
    exact this w hw
  rw [← wordVal_liftWord68]
  exact wordVal_d4RankTwoRels F _ hmem

theorem wordVal_phanD4Rels (F : PhanFamilyD4 K9 3 1 Y)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (d4Gens6 F))))) :
    ∀ w ∈ phanD4Rels, wordVal (d4Gens F) w = 1 := by
  obtain ⟨hu1, hu2⟩ := phanA3_kernel_vanish (d4Gens6 F) (wordVal_phanA3Rels_d4 F) h3
  intro w hw
  simp only [phanD4Rels, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact wordVal_d4RankTwoRels F w hw
  · rw [wordVal_liftWord68]
    exact hu1
  · rw [wordVal_liftWord68]
    exact hu2

@[expose] noncomputable def d4Hom (F : PhanFamilyD4 K9 3 1 Y)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (d4Gens6 F))))) :
    PhanD4Group →* Y :=
  PresentedGroup.toGroup (f := d4Gens F) (by
    intro r hr
    simp only [Set.mem_ofPred_eq, List.mem_map] at hr
    obtain ⟨w, hw, rfl⟩ := hr
    rw [FreeGroup.lift_mk]
    exact wordVal_phanD4Rels F h3 w hw)

theorem range_d4Hom (F : PhanFamilyD4 K9 3 1 Y)
    (h3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(Subgroup.closure (Set.range (d4Gens6 F))))) :
    (d4Hom F h3).range = Subgroup.closure (Set.range (d4Gens F)) := by
  have hcomp : (d4Hom F h3) ∘ (PresentedGroup.of : Fin 8 → PhanD4Group) = d4Gens F :=
    funext fun i => PresentedGroup.toGroup.of _
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp, hcomp]

end CFSG.ClassicalInvolution.Phan.Q3G
