module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerTwisted
public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime]

theorem ShapeTable.le_two {a : ℕ} {t : StatedLieTag} {n : ℕ} (h : ShapeTable a t n) : a ≤ 2 := by
  simp only [ShapeTable, ShapeSL7, ShapeSL6, ShapeSLs, ShapeSU7, ShapeSU6, ShapeSUs, ShapeSp4,
    ShapeSp3, ShapeE7, ShapeE8, ShapeTwinD, ShapeTwinSL4, ShapeTwinB, ShapeTwinSp2, ShapeTwinTD,
    ShapeTwinSU4] at h
  omega

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {x : G}

theorem modelTwinClass_of_layer_family {ι : Type} (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {j : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (hperf : FundPerfect (D.tag j) (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (T : ι → Subgroup G) (hTx : ∀ k, T k ∈ centralizingMembers Ω {x})
    (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range) (hinj : Function.Injective T)
    (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    ∃ F : ι → Subgroup (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).K,
      (∀ k, F k ∈ compFund D j) ∧ Function.Injective F ∧
      (∀ k l, k ≠ l → Commutes (F k) (F l)) ∧
      ∀ k l, ∀ S ∈ compFund D j, (S = F k ∨ Commutes S (F k)) ↔ (S = F l ∨ Commutes S (F l)) := by
  choose R hR using fun k => exists_corr_left hΩ hex D (⟨hTx k, hTj k⟩ : T k ∈ compMembers Ω x D j)
  refine ⟨R, fun k => (hR k).2.1, ?_, ?_, ?_⟩
  · intro k l hkl
    exact hinj (corr_unique_right hΩ hP1 (hR k) (hkl ▸ hR l))
  · intro k l hkl
    exact (corr_commutes hΩ hP1 hperf (hR k) (hR l)).mp (hcomm k l hkl)
  · intro k l S hS
    obtain ⟨N, hN⟩ := exists_corr_right hΩ D hsc hS
    have key : ∀ m, (S = R m ∨ Commutes S (R m)) ↔ (N = T m ∨ Commutes N (T m)) := by
      intro m
      constructor
      · rintro (h | h)
        · left
          exact corr_unique_right hΩ hP1 (h ▸ hN) (hR m)
        · right
          exact (corr_commutes hΩ hP1 hperf hN (hR m)).mpr h
      · rintro (h | h)
        · left
          exact corr_unique_left hperf (h ▸ hN) (hR m)
        · right
          exact (corr_commutes hΩ hP1 hperf hN (hR m)).mp h
    rw [key k, key l]
    exact htwin N hN.1 k l

theorem tag_rank_of_twinFamily (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) {j : Fin D.card}
    (hnA1 : ¬ (D.tag j = .PSL ∧ D.rank j = 2)) {a : ℕ} (ha : 2 ≤ a) (T : Fin a → Subgroup G)
    (hTx : ∀ k, T k ∈ centralizingMembers Ω {x}) (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range)
    (hinj : Function.Injective T) (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    ShapeTable a (D.tag j) (D.rank j) ∨ (D.tag j = .POmegaPlus ∧ D.rank j = 4 ∧ a ≤ 4) := by
  have hq4 : 4 ≤ p ^ f := by omega
  obtain ⟨hsc, hperf⟩ := NonClassical.componentFacts_of_no_exotic D hp2 hq4 hD
  obtain ⟨F, hF, hFinj, hFcomm, hFtwin⟩ :=
    modelTwinClass_of_layer_family hΩ hex hP1 D (j := j) (hsc j) (hperf j) T hTx hTj hinj
      hcomm htwin
  have hexp : D.exp j = f := by
    rcases D.exp_eq j with h | ⟨h, -⟩
    · exact h
    · exact absurd h (hD j).2
  have hmtc : ModelTwinClass p (D.tag j) (D.rank j) (D.exp j) a :=
    ⟨F, hF, hFinj, hFcomm, fun k l S hS => hFtwin k l S hS⟩
  have hmtc' := modelTwinClass_congr (p := p) rfl rfl hexp hmtc
  have hadm : StatedLieAdmissible (D.tag j) (D.rank j) p f := by
    have := D.admissible j
    rwa [hexp] at this
  exact mfTwin (p := p) (f := f) hp2 hq (D.tag j) (D.rank j) a (D.isFundTag j) (hD j).1 (hD j).2
    hadm hnA1 ha hmtc'

theorem tag_rank_of_twinFamily_of_three_le (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hex : ExactMembers Ω) (hP1 : LocalOddCentral Ω {x})
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    (hD : ∀ i, D.tag i ≠ .G2 ∧ D.tag i ≠ .trialityD4) {j : Fin D.card}
    (hnA1 : ¬ (D.tag j = .PSL ∧ D.rank j = 2)) {a : ℕ} (ha : 3 ≤ a) (T : Fin a → Subgroup G)
    (hTx : ∀ k, T k ∈ centralizingMembers Ω {x}) (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range)
    (hinj : Function.Injective T) (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ centralizingMembers Ω {x}, ∀ k l,
      (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    D.tag j = .POmegaPlus ∧ D.rank j = 4 ∧ a ≤ 4 := by
  rcases tag_rank_of_twinFamily hp2 hq hΩ hex hP1 D hD hnA1 (by omega) T hTx hTj hinj hcomm htwin
    with h | h
  · have h' : ShapeTable a (D.tag j) (D.rank j) := h
    exact absurd (ShapeTable.le_two h') (by omega)
  · exact h

end Layer

end CFSG.ClassicalInvolution.Asc77
