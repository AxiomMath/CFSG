module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Naturality
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.Basic2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section MapS

variable {G : Type} [Group G]

@[expose] def mapS (φ : G ≃* G) (B : Subgroup G) : Subgroup G := B.map φ.toMonoidHom

theorem mapS_surjective (φ : G ≃* G) : Function.Surjective (mapS φ) := fun B =>
  ⟨mapS φ.symm B, by
    unfold mapS
    rw [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G by
      ext x; exact φ.apply_symm_apply x, Subgroup.map_id]⟩

theorem mapS_le_iff (φ : G ≃* G) {A B : Subgroup G} : mapS φ A ≤ mapS φ B ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective φ.injective

theorem mapS_eq_bot_iff (φ : G ≃* G) {A : Subgroup G} : mapS φ A = ⊥ ↔ A = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective A φ.injective

theorem mem_mapS_iff (φ : G ≃* G) {B : Subgroup G} {x : G} : x ∈ mapS φ B ↔ φ.symm x ∈ B :=
  Subgroup.mem_map_equiv

theorem apply_mem_mapS_iff (φ : G ≃* G) {B : Subgroup G} {x : G} : φ x ∈ mapS φ B ↔ x ∈ B := by
  rw [mem_mapS_iff, MulEquiv.symm_apply_apply]

theorem mapS_comm (φ : G ≃* G) (A B : Subgroup G) : mapS φ ⁅A, B⁆ = ⁅mapS φ A, mapS φ B⁆ :=
  Subgroup.map_commutator A B _

theorem mapS_centralizer (φ : G ≃* G) (B : Subgroup G) :
    mapS φ (centralizer (B : Set G)) = centralizer ((mapS φ B : Subgroup G) : Set G) := by
  ext x
  rw [mem_mapS_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h y hy
    have hy' : φ.symm y ∈ B := (mem_mapS_iff φ).mp hy
    have := h _ hy'
    have h2 : φ (φ.symm y * φ.symm x) = φ (φ.symm x * φ.symm y) := congrArg φ this
    simpa using h2
  · intro h y hy
    have hy' : φ y ∈ mapS φ B := (apply_mem_mapS_iff φ).mpr hy
    have := h _ hy'
    have h2 : φ.symm (φ y * x) = φ.symm (x * φ y) := congrArg φ.symm this
    simpa using h2

theorem mapS_zOf (φ : G ≃* G) (B : Subgroup G) : mapS φ (zOf B) = zOf (mapS φ B) := by
  unfold zOf
  unfold mapS
  rw [Subgroup.map_inf _ _ _ φ.injective]
  exact congrArg _ (mapS_centralizer φ B)

theorem mapS_le_normalizer_iff (φ : G ≃* G) (B A : Subgroup G) :
    mapS φ B ≤ normalizer ((mapS φ A : Subgroup G) : Set G) ↔ B ≤ normalizer (A : Set G) := by
  constructor
  · intro h x hx
    exact (mem_normalizer_map_iff φ A x).mp (h ((apply_mem_mapS_iff φ).mpr hx))
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (mem_normalizer_map_iff φ A y).mpr (h hy)

theorem mapS_mem_classTwo (φ : G ≃* G) (P B : Subgroup G) :
    mapS φ B ∈ classTwo (mapS φ P) ↔ B ∈ classTwo P := by
  show (mapS φ B ≤ mapS φ P ∧ ⁅⁅mapS φ B, mapS φ B⁆, mapS φ B⁆ = ⊥) ↔ (B ≤ P ∧ ⁅⁅B, B⁆, B⁆ = ⊥)
  simp only [mapS_le_iff, ← mapS_comm, mapS_eq_bot_iff]

theorem mapS_mem_Kup (φ : G ≃* G) (P Q B : Subgroup G) :
    mapS φ B ∈ Kup (mapS φ P) (mapS φ Q) ↔ B ∈ Kup P Q := by
  show (mapS φ B ∈ classTwo (mapS φ P) ∧ ⁅mapS φ B, mapS φ Q⁆ ≤ zOf (mapS φ B)) ↔
    (B ∈ classTwo P ∧ ⁅B, Q⁆ ≤ zOf B)
  simp only [mapS_mem_classTwo, ← mapS_comm, ← mapS_zOf, mapS_le_iff]

theorem mapS_mem_Klow (φ : G ≃* G) (P Q B : Subgroup G) :
    mapS φ B ∈ Klow (mapS φ P) (mapS φ Q) ↔ B ∈ Klow P Q := by
  show (mapS φ B ∈ classTwo (mapS φ P) ∧ mapS φ Q ≤ normalizer ((mapS φ B : Subgroup G) : Set G) ∧
      ∀ A ∈ classTwo (mapS φ P), A ≤ mapS φ Q → mapS φ B ≤ normalizer (A : Set G) →
        ⁅mapS φ B, ⁅A, A⁆⁆ = ⊥ → ⁅⁅zOf (mapS φ B), A⁆, A⁆ = ⊥ → ⁅mapS φ B, A⁆ ≤ zOf (mapS φ B)) ↔
    (B ∈ classTwo P ∧ Q ≤ normalizer (B : Set G) ∧
      ∀ A ∈ classTwo P, A ≤ Q → B ≤ normalizer (A : Set G) →
        ⁅B, ⁅A, A⁆⁆ = ⊥ → ⁅⁅zOf B, A⁆, A⁆ = ⊥ → ⁅B, A⁆ ≤ zOf B)
  rw [mapS_mem_classTwo, mapS_le_normalizer_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  constructor
  · intro h A hA hAQ hBA h1 h2
    have := h (mapS φ A) ((mapS_mem_classTwo φ P A).mpr hA) ((mapS_le_iff φ).mpr hAQ)
      ((mapS_le_normalizer_iff φ B A).mpr hBA)
      (by rw [← mapS_comm, ← mapS_comm, mapS_eq_bot_iff]; exact h1)
      (by rw [← mapS_zOf, ← mapS_comm, ← mapS_comm, mapS_eq_bot_iff]; exact h2)
    rwa [← mapS_comm, ← mapS_zOf, mapS_le_iff] at this
  · intro h A₂ hA₂ hAQ hBA h1 h2
    obtain ⟨A, rfl⟩ := mapS_surjective φ A₂
    have hA : A ∈ classTwo P := (mapS_mem_classTwo φ P A).mp hA₂
    rw [mapS_le_iff] at hAQ
    rw [mapS_le_normalizer_iff] at hBA
    rw [← mapS_comm, ← mapS_comm, mapS_eq_bot_iff] at h1
    rw [← mapS_zOf, ← mapS_comm, ← mapS_comm, mapS_eq_bot_iff] at h2
    have := h A hA hAQ hBA h1 h2
    rw [← mapS_comm, ← mapS_zOf, mapS_le_iff]
    exact this

theorem gen_mapS (φ : G ≃* G) (S S' : Set (Subgroup G)) (h : ∀ B, mapS φ B ∈ S' ↔ B ∈ S) :
    gen S' = mapS φ (gen S) := by
  unfold gen mapS
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_iUnion, SetLike.mem_coe]
  constructor
  · rintro ⟨B, hB, hx⟩
    obtain ⟨B₀, rfl⟩ := mapS_surjective φ B
    have hB₀ : B₀ ∈ S := (h B₀).mp hB
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨b, ⟨B₀, hB₀, hb⟩, rfl⟩
  · rintro ⟨b, ⟨B₀, hB₀, hb⟩, rfl⟩
    exact ⟨mapS φ B₀, (h B₀).mpr hB₀, Subgroup.mem_map_of_mem _ hb⟩

theorem mapS_mem_Kfam (φ : G ≃* G) (P : Subgroup G) (n : ℕ) (B : Subgroup G) :
    mapS φ B ∈ Kfam (mapS φ P) n ↔ B ∈ Kfam P n := by
  induction n generalizing B with
  | zero => exact mapS_mem_classTwo φ P B
  | succ n ih =>
    have hgen : gen (Kfam (mapS φ P) n) = mapS φ (gen (Kfam P n)) := gen_mapS φ _ _ ih
    show mapS φ B ∈ (if Even n then Klow (mapS φ P) (gen (Kfam (mapS φ P) n))
        else Kup (mapS φ P) (gen (Kfam (mapS φ P) n))) ↔
      B ∈ (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n)))
    rw [hgen]
    by_cases he : Even n
    · simp only [he, ↓reduceIte]
      exact mapS_mem_Klow φ P _ B
    · simp only [he, ↓reduceIte]
      exact mapS_mem_Kup φ P _ B

theorem kInfty_map (φ : G ≃* G) (P : Subgroup G) : kInfty (mapS φ P) = mapS φ (kInfty P) := by
  unfold kInfty
  apply gen_mapS φ
  intro B
  simp only [Set.mem_iInter]
  exact forall_congr' fun i => mapS_mem_Kfam φ P (2 * i) B

theorem normalizer_le_kInfty (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer ((kInfty P : Subgroup G) : Set G) := by
  intro x hx
  have hmap : mapS (MulAut.conj x) P = P := map_conj_eq_of_mem_normalizer hx
  have h1 := kInfty_map (MulAut.conj x) P
  rw [hmap] at h1
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have h2 : (MulAut.conj x) y ∈ mapS (MulAut.conj x) (kInfty P) ↔ y ∈ kInfty P := apply_mem_mapS_iff _
  rw [← h1] at h2
  simpa [MulAut.conj_apply] using h2.symm

end MapS

end CFSG.GH74.GLS.Stage2.Bender.Thm2
