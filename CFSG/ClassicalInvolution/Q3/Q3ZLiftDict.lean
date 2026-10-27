module

public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (planeGroup IsHyperbolicPlane)
open CFSG.ClassicalInvolution.Q3.Q3W (LocalShapeC3)
open scoped MatrixGroups

structure ShapeCDict3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (z : G) where
  ψ : StatedSp 2 (GaloisField 3 1) →* locQuot Ω z
  ker_le : ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField 3 1))
  Q₀ : Subgroup (locQuot Ω z)
  commutes : Commutes ψ.range Q₀
  mem_fam : ∀ P, IsHyperbolicPlane P → (planeGroup P).map ψ ∈ locFamily Ω z
  fam_cases : ∀ K' ∈ locFamily Ω z,
    K' ≤ Q₀ ∨ ∃ P, IsHyperbolicPlane P ∧ K' = (planeGroup P).map ψ
  card_le : Nat.card Q₀ ≤ Nat.card SL(2, GaloisField 3 1)
  gen : ψ.range ⊔ Q₀ = ⊤

private theorem admissible_psp_two_three : StatedLieAdmissible .PSp 2 3 1 :=
  ⟨Nat.prime_three, le_rfl, le_rfl, by decide⟩

theorem exists_conj_planeGroup {F : Type} [Field F] {n : ℕ} (hn : 1 ≤ n)
    {P P' : Submodule F (Fin n ⊕ Fin n → F)} (hP : IsHyperbolicPlane P)
    (hP' : IsHyperbolicPlane P') :
    ∃ g : StatedSp n F, planeGroup P' = (planeGroup P).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP
    (⟨0, hn⟩ : Fin n)
  obtain ⟨g', hg'⟩ := Models.SymplecticPairs.exists_planeGroup_eq_conj_longBlock hP'
    (⟨0, hn⟩ : Fin n)
  refine ⟨g' * g⁻¹, ?_⟩
  rw [hg, hg', Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]


theorem exists_psp_hom3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) (hk : D.kind i = CompData.model .PSp 2) :
    ∃ ψ : StatedSp 2 (GaloisField 3 1) →* X,
      ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField 3 1)) ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ (D.kind i).fund, K = R.map (D.hom i)) ↔
        ∃ P, IsHyperbolicPlane P ∧ K = (planeGroup P).map ψ := by
  have key : ∀ c : CompData, c = CompData.model .PSp 2 →
      ∀ (φ : c.G →* X) (_ : φ.ker ≤ Subgroup.center c.G),
      ∃ ψ : StatedSp 2 (GaloisField 3 1) →* X,
        ψ.ker ≤ Subgroup.center (StatedSp 2 (GaloisField 3 1)) ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ c.fund, K = R.map φ) ↔
          ∃ P, IsHyperbolicPlane P ∧ K = (planeGroup P).map ψ := by
    rintro c rfl φ hφ
    refine ⟨φ, hφ, rfl, fun K => ?_⟩
    constructor
    · rintro ⟨R, hR, rfl⟩
      obtain ⟨P, hP, rfl⟩ :=
        (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff admissible_psp_two_three R).1 hR
      exact ⟨P, hP, rfl⟩
    · rintro ⟨P, hP, rfl⟩
      exact ⟨planeGroup P,
        (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff admissible_psp_two_three _).2
          ⟨P, hP, rfl⟩, rfl⟩
  exact key _ hk (D.hom i) (D.ker_le_center i)

theorem map_mem_of_psp3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (hΦ : ConjInvariant Φ) (i : ι)
    (hk : D.kind i = CompData.model .PSp 2) :
    ∀ R ∈ (D.kind i).fund, R.map (D.hom i) ∈ Φ := by
  have key : ∀ c : CompData, c = CompData.model .PSp 2 → ∀ (φ : c.G →* X),
      (∃ R₀ ∈ c.fund, R₀.map φ ∈ Φ) → ∀ R ∈ c.fund, R.map φ ∈ Φ := by
    rintro c rfl φ ⟨R₀, hR₀, hmem⟩ R hR
    obtain ⟨P₀, hP₀, rfl⟩ :=
      (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff admissible_psp_two_three R₀).1 hR₀
    obtain ⟨P, hP, rfl⟩ :=
      (Models.SymplecticPairs.mem_fundamentalSubgroups_PSp_iff admissible_psp_two_three R).1 hR
    obtain ⟨g, hg⟩ := exists_conj_planeGroup (by norm_num) hP₀ hP
    rw [hg]
    exact (conjSub_map φ g (planeGroup P₀)) ▸ hΦ (φ g) _ hmem
  exact key _ hk (D.hom i) (D.meets i)

theorem LocalShapeC3.nonempty_cdict {G : Type} [Group G] {Ω : Set (Subgroup G)}
    (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (h : LocalShapeC3 1 (CompData.model .PSp 2) Ω z) : Nonempty (ShapeCDict3 Ω z) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk₁, hrest⟩ := h
  obtain ⟨i₀, hne, hall⟩ : ∃ i₀ : ι, i₀ ≠ i₁ ∧ ∀ i, i = i₀ ∨ i = i₁ := by
    obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp (by simpa using hcard : Nat.card ι = 2)
    have hx : ∀ i, i = x ∨ i = y := fun i => by
      have : i ∈ ({x, y} : Set ι) := by rw [hset]; trivial
      simpa using this
    rcases hx i₁ with h1 | h1
    · refine ⟨y, fun e => hxy (h1 ▸ e.symm), fun i => ?_⟩
      rcases hx i with h2 | h2
      · exact Or.inr (h2.trans h1.symm)
      · exact Or.inl h2
    · refine ⟨x, fun e => hxy (h1 ▸ e), fun i => ?_⟩
      rcases hx i with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2.trans h1.symm)
  obtain ⟨ψ₁, hker₁, hrange₁, hfund₁⟩ := exists_psp_hom3 D i₁ hk₁
  have hk0 : D.kind i₀ = CompData.sl23 := hrest i₀ hne
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass3_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  refine ⟨{
    ψ := ψ₁
    ker_le := hker₁
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_
    gen := ?_ }⟩
  · rw [hrange₁]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₁ i₀ hne.symm a b
  · intro P hP
    obtain ⟨R', hR', hRR'⟩ := (hfund₁ ((planeGroup P).map ψ₁)).mpr ⟨P, hP, rfl⟩
    rw [hRR']
    exact map_mem_of_psp3 D hΦ i₁ hk₁ R' hR'
  · intro K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with h0 | h1
    · subst h0
      exact Or.inl (Subgroup.map_le_range _ _)
    · subst h1
      exact Or.inr ((hfund₁ _).mp ⟨R, hR, rfl⟩)
  · have hF : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 one_ne_zero]
      norm_num
    have h24 : Nat.card SL(2, GaloisField 3 1) = 24 := by
      rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
      norm_num
    have key : ∀ c : CompData, c = CompData.sl23 → ∀ φ : c.G →* locQuot Ω z,
        Nat.card φ.range ≤ Nat.card SL(2, GaloisField 3 1) := by
      rintro c rfl φ
      rw [h24, ← natCard_sl2Three]
      exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    exact key _ hk0 (D.hom i₀)
  · rw [hrange₁, sup_comm, eq_top_iff, ← D.generate]
    refine iSup_le fun i => ?_
    rcases hall i with h0 | h1
    · subst h0
      exact le_sup_left
    · subst h1
      exact le_sup_right

end CFSG.ClassicalInvolution.Q3.Q3Z
