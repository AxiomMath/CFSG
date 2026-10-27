module

public import CFSG.ClassicalInvolution.Uniform.UOmegaLie

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups

section Defs

@[expose] def CompIs (p f : ℕ) [Fact p.Prime] (c : Q3.CompData) (t : LowTwoRank.StatedLieTag)
    (n : ℕ) : Prop :=
  ∃ e : ℕ, (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) ∧ IsFundTag t ∧
    LowTwoRank.StatedLieAdmissible t n p e ∧ c = compModel p e t n

@[expose] def HasLieTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (t : LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∃ D : OmegaLieU p f Ω, D.card = 1 ∧ ∃ i : Fin D.card, CompIs p f (D.kind i) t n

@[expose] def HasM11TypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) : Prop :=
  p ^ f = 3 ∧ ∃ D : OmegaLieU p f Ω, D.card = 1 ∧ ∃ i : Fin D.card, D.kind i = Q3.CompData.m11

@[expose] def SectionLieTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (Y : Subgroup G) (t : LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∃ D : LieSystemDataU p f (Fin 1) (↥Y ⧸ classicalInvolutionOddCore ↥Y)
    (oddQuotientFamily (restrictFamily Ω Y)), CompIs p f (D.kind 0) t n

@[expose] def SectionCompU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (Y : Subgroup G) (c : Q3.CompData) : Prop :=
  ∃ D : LieSystemDataU p f (Fin 1) (↥Y ⧸ classicalInvolutionOddCore ↥Y)
    (oddQuotientFamily (restrictFamily Ω Y)), D.kind 0 = c

@[expose] def HasOrthTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (d : ℕ) (ε : Bool) : Prop :=
  ∃ t n, IsOrthTag d ε t n ∧ HasLieTypeU p f Ω t n

@[expose] def SectionOrthTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (Y : Subgroup G) (d : ℕ) (ε : Bool) : Prop :=
  ∃ t n, IsOrthTag d ε t n ∧ SectionLieTypeU p f Ω Y t n

end Defs

section Facades

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def CompIs.modelSpec {c : Q3.CompData} {t : LowTwoRank.StatedLieTag} {n : ℕ}
    (h : CompIs p f c t n) : ModelSpec p f c :=
  ⟨t, n, h.choose, h.choose_spec.2.1, h.choose_spec.2.2.1, h.choose_spec.1,
    h.choose_spec.2.2.2⟩

namespace OmegaLieU

@[expose] noncomputable def ofOmegaLie (h3 : p ^ f ≠ 3) (D : OmegaLie p f Ω) : OmegaLieU p f Ω where
  card := D.card
  kind i := compModel p (D.exp i) (D.tag i) (D.rank i)
  valid i := Or.inl ⟨D.tag i, D.rank i, D.exp i, D.isFundTag i, D.admissible i, D.exp_eq i, rfl⟩
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq h := absurd h h3

@[expose] noncomputable def toOmegaLieOfSpec (D : OmegaLieU p f Ω)
    (σ : ∀ i, ModelSpec p f (D.kind i)) : OmegaLie p f Ω where
  card := D.card
  tag i := (σ i).tag
  rank i := (σ i).rank
  exp i := (σ i).exp
  hom i := castHom (σ i).eq (D.hom i)
  isFundTag i := (σ i).isFundTag
  admissible i := (σ i).admissible
  exp_eq i := (σ i).exp_eq
  ker_le_center i := castHom_ker_le_center _ _ (D.ker_le_center i)
  commute i j hij x y := by
    obtain ⟨x', hx⟩ := exists_castHom_eq (σ i).eq (D.hom i) x
    obtain ⟨y', hy⟩ := exists_castHom_eq (σ j).eq (D.hom j) y
    rw [hx, hy]
    exact D.commute i j hij x' y'
  generate := by
    have h : ∀ i, (castHom (σ i).eq (D.hom i)).range = (D.hom i).range :=
      fun i => range_castHom _ _
    exact (iSup_congr h).trans D.generate
  fundamental L hL := by
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
    exact ⟨i, R', hR', hLR.trans hRR.symm⟩
  meets i := by
    obtain ⟨R, hR, hΩ⟩ := D.meets i
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
    exact ⟨R', hR', hRR ▸ hΩ⟩

end OmegaLieU

@[expose] noncomputable def LieSystemDataU.toGenericOfSpec {X : Type} [Group X]
    {Φ : Set (Subgroup X)} {n : ℕ} (D : LieSystemDataU p f (Fin n) X Φ)
    (σ : ∀ i, ModelSpec p f (D.kind i)) : LieSystemData p f X Φ where
  card := n
  tag i := (σ i).tag
  rank i := (σ i).rank
  exp i := (σ i).exp
  hom i := castHom (σ i).eq (D.hom i)
  isFundTag i := (σ i).isFundTag
  admissible i := (σ i).admissible
  exp_eq i := (σ i).exp_eq
  ker_le_center i := castHom_ker_le_center _ _ (D.ker_le_center i)
  commute i j hij x y := by
    obtain ⟨x', hx⟩ := exists_castHom_eq (σ i).eq (D.hom i) x
    obtain ⟨y', hy⟩ := exists_castHom_eq (σ j).eq (D.hom j) y
    rw [hx, hy]
    exact D.commute i j hij x' y'
  generate := by
    have h : ∀ i, (castHom (σ i).eq (D.hom i)).range = (D.hom i).range :=
      fun i => range_castHom _ _
    exact (iSup_congr h).trans D.generate
  fundamental L hL := by
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
    exact ⟨i, R', hR', hLR.trans hRR.symm⟩
  meets i := by
    obtain ⟨R, hR, hΦ⟩ := D.meets i
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
    exact ⟨R', hR', hRR ▸ hΦ⟩

theorem fin_eq_of_eq_one {n : ℕ} (h : n = 1) (i j : Fin n) : i = j :=
  Fin.ext (by have := i.2; have := j.2; omega)

@[expose] noncomputable def LieSystemDataU.ofGenericOne {X : Type} [Group X]
    {Φ : Set (Subgroup X)} (h3 : p ^ f ≠ 3) (D : LieSystemData p f X Φ) (i₀ : Fin D.card)
    (hc : D.card = 1) : LieSystemDataU p f (Fin 1) X Φ where
  kind _ := compModel p (D.exp i₀) (D.tag i₀) (D.rank i₀)
  valid _ := Or.inl ⟨D.tag i₀, D.rank i₀, D.exp i₀, D.isFundTag i₀, D.admissible i₀,
    D.exp_eq i₀, rfl⟩
  hom _ := D.hom i₀
  ker_le_center _ := D.ker_le_center i₀
  commute i j hij _ _ := absurd (Subsingleton.elim i j) hij
  generate := by
    refine le_antisymm le_top ?_
    rw [← D.generate]
    refine iSup_le fun i => ?_
    obtain rfl := fin_eq_of_eq_one hc i i₀
    exact le_iSup (fun _ : Fin 1 => (D.hom i).range) 0
  fundamental L hL := by
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain rfl := fin_eq_of_eq_one hc i i₀
    exact ⟨0, R, hR, hLR⟩
  meets _ := D.meets i₀
  card_eq h := absurd h h3

@[expose] noncomputable def specAt {n : ℕ} (kind : Fin n → Q3.CompData)
    (valid : ∀ i, CompValid p f (kind i)) (h3 : p ^ f ≠ 3) (i : Fin n)
    (σi : ModelSpec p f (kind i)) : ∀ j, ModelSpec p f (kind j) :=
  fun j => if hj : j = i then hj ▸ σi else ((valid j).nonempty_modelSpec h3).some

theorem specAt_self {n : ℕ} (kind : Fin n → Q3.CompData)
    (valid : ∀ i, CompValid p f (kind i)) (h3 : p ^ f ≠ 3) (i : Fin n)
    (σi : ModelSpec p f (kind i)) : specAt kind valid h3 i σi i = σi := by
  simp [specAt]

theorem nonempty_omegaLieU_iff (h3 : p ^ f ≠ 3) :
    Nonempty (OmegaLieU p f Ω) ↔ Nonempty (OmegaLie p f Ω) :=
  ⟨fun ⟨D⟩ => ⟨D.toOmegaLieOfSpec fun i => ((D.valid i).nonempty_modelSpec h3).some⟩,
    fun ⟨D⟩ => ⟨OmegaLieU.ofOmegaLie h3 D⟩⟩

theorem hasLieTypeU_iff (h3 : p ^ f ≠ 3) {t : LowTwoRank.StatedLieTag} {n : ℕ} :
    HasLieTypeU p f Ω t n ↔ HasLieType p f Ω t n := by
  constructor
  · rintro ⟨D, hc, i, hi⟩
    have hσ : specAt D.kind D.valid h3 i hi.modelSpec i = hi.modelSpec := specAt_self _ _ _ _ _
    refine ⟨D.toOmegaLieOfSpec (specAt D.kind D.valid h3 i hi.modelSpec), hc, i, ?_, ?_⟩
    · change (specAt D.kind D.valid h3 i hi.modelSpec i).tag = t
      rw [hσ]
      rfl
    · change (specAt D.kind D.valid h3 i hi.modelSpec i).rank = n
      rw [hσ]
      rfl
  · rintro ⟨D, hc, i, htag, hrank⟩
    subst htag hrank
    exact ⟨OmegaLieU.ofOmegaLie h3 D, hc, i,
      ⟨D.exp i, D.exp_eq i, D.isFundTag i, D.admissible i, rfl⟩⟩

theorem sectionLieTypeU_iff (h3 : p ^ f ≠ 3) {Y : Subgroup G} {t : LowTwoRank.StatedLieTag}
    {n : ℕ} : SectionLieTypeU p f Ω Y t n ↔ SectionLieType p f Ω Y t n := by
  constructor
  · rintro ⟨D, hi⟩
    have hσ : specAt D.kind D.valid h3 0 hi.modelSpec 0 = hi.modelSpec := specAt_self _ _ _ _ _
    refine ⟨D.toGenericOfSpec (specAt D.kind D.valid h3 0 hi.modelSpec), rfl, (0 : Fin 1), ?_, ?_⟩
    · change (specAt D.kind D.valid h3 0 hi.modelSpec 0).tag = t
      rw [hσ]
      rfl
    · change (specAt D.kind D.valid h3 0 hi.modelSpec 0).rank = n
      rw [hσ]
      rfl
  · rintro ⟨D, hc, i, htag, hrank⟩
    subst htag hrank
    exact ⟨LieSystemDataU.ofGenericOne h3 D i hc,
      ⟨D.exp i, D.exp_eq i, D.isFundTag i, D.admissible i, rfl⟩⟩

theorem hasOrthTypeU_iff (h3 : p ^ f ≠ 3) {d : ℕ} {ε : Bool} :
    HasOrthTypeU p f Ω d ε ↔ HasOrthType p f Ω d ε := by
  simp only [HasOrthTypeU, HasOrthType, hasLieTypeU_iff h3]

theorem sectionOrthTypeU_iff (h3 : p ^ f ≠ 3) {Y : Subgroup G} {d : ℕ} {ε : Bool} :
    SectionOrthTypeU p f Ω Y d ε ↔ SectionOrthType p f Ω Y d ε := by
  simp only [SectionOrthTypeU, SectionOrthType, sectionLieTypeU_iff h3]

theorem not_hasM11TypeU (h3 : p ^ f ≠ 3) : ¬ HasM11TypeU p f Ω := fun h => h3 h.1

end Facades

end CFSG.ClassicalInvolution.Uniform
