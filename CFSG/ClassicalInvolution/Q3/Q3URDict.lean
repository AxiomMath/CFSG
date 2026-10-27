module

public import CFSG.ClassicalInvolution.Q3.Q3WShape

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Models CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal
open CFSG.ClassicalInvolution.Phan (Su)
open scoped MatrixGroups


theorem statedLieAdmissible_psu3 {k : ℕ} (hk : 3 ≤ k) : StatedLieAdmissible .PSU k 3 1 :=
  ⟨Nat.prime_three, le_rfl, hk, fun h => by have := (Prod.mk.inj h).2; norm_num at this⟩

theorem exists_psu_hom3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) {k : ℕ} (hk : D.kind i = CompData.model .PSU k)
    (hk3 : 3 ≤ k) :
    ∃ ψ : Su (GaloisField 3 2) 3 1 k →* X,
      ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 k) ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ (D.kind i).fund, K = R.map (D.hom i)) ↔
        ∃ L ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) (by omega : 2 ≤ k),
          K = L.map ψ := by
  have hadm := statedLieAdmissible_psu3 hk3
  have key : ∀ c : CompData, c = CompData.model .PSU k →
      ∀ (φ : c.G →* X) (_ : φ.ker ≤ Subgroup.center c.G),
      ∃ ψ : Su (GaloisField 3 2) 3 1 k →* X,
        ψ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 k) ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ c.fund, K = R.map φ) ↔
          ∃ L ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) (by omega : 2 ≤ k),
            K = L.map ψ := by
    rintro c rfl φ hφ
    obtain ⟨e, he⟩ := psu_model_equiv (p := 3) (f := 1) (by norm_num) hadm
    refine ⟨φ.comp e.symm.toMonoidHom, ?_, ?_, fun K => ?_⟩
    · intro x hx
      have h1 : e.symm x ∈ Subgroup.center (modelUniv .PSU k 3 1 Nat.prime_three).K :=
        hφ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro y
      apply e.symm.injective
      rw [map_mul, map_mul]
      exact h1 (e.symm y)
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
        ← MonoidHom.range_eq_map]
    · constructor
      · rintro ⟨R, hR, rfl⟩
        refine ⟨R.map e.toMonoidHom, (he R).mp hR, ?_⟩
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp
      · rintro ⟨L, hL, rfl⟩
        refine ⟨L.map e.symm.toMonoidHom, (he _).mpr ?_, ?_⟩
        · rw [Subgroup.map_map]
          have : (e.toMonoidHom.comp e.symm.toMonoidHom) = MonoidHom.id _ := by
            ext x; simp
          rw [this, Subgroup.map_id]
          exact hL
        · rw [Subgroup.map_map]
  exact key _ hk (D.hom i) (D.ker_le_center i)

theorem map_mem_of_psu3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (hΦ : ConjInvariant Φ) (i : ι) {k : ℕ}
    (hk : D.kind i = CompData.model .PSU k) (hk3 : 3 ≤ k) :
    ∀ R ∈ (D.kind i).fund, R.map (D.hom i) ∈ Φ := by
  have hadm := statedLieAdmissible_psu3 hk3
  have hsc : FundamentalSingleClass .PSU (modelUniv .PSU k 3 1 Nat.prime_three).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .PSU k 3 1 Nat.prime_three
      trivial hadm (by decide) (by decide)
  have key : ∀ c : CompData, c = CompData.model .PSU k → ∀ (φ : c.G →* X),
      (∃ R₀ ∈ c.fund, R₀.map φ ∈ Φ) → ∀ R ∈ c.fund, R.map φ ∈ Φ := by
    rintro c rfl φ ⟨R₀, hR₀, hmem⟩ R hR
    obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
    exact (conjSub_map φ g R₀) ▸ hΦ (φ g) _ hmem
  exact key _ hk (D.hom i) (D.meets i)

theorem LocalShapeC3.nonempty_dictU {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 2 ≤ m)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (h : LocalShapeC3 1 (CompData.model .PSU (m + 1)) Ω z) :
    Nonempty (ShapeUDict 3 1 m Ω z) := by
  obtain ⟨ι, hι, D, hcard, i₁, hk₁, hrest⟩ := h
  have hk : 2 ≤ m + 1 := by omega
  have hk3 : 3 ≤ m + 1 := by omega
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
  obtain ⟨ψ₁, hker₁, hrange₁, hfund₁⟩ := exists_psu_hom3 D i₁ hk₁ hk3
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
    card_le := ?_ }⟩
  · rw [hrange₁]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro hk' L hL
    obtain ⟨R', hR', hRR'⟩ := (hfund₁ (L.map ψ₁)).mpr ⟨L, hL, rfl⟩
    rw [hRR']
    exact map_mem_of_psu3 D hΦ i₁ hk₁ hk3 R' hR'
  · intro hk' K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with h0 | h1
    · subst h0
      exact Or.inl (Subgroup.map_le_range _ _)
    · subst h1
      obtain ⟨L, hL, hLL⟩ := (hfund₁ _).mp ⟨R, hR, rfl⟩
      exact Or.inr ⟨L, hL, hLL⟩
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

end CFSG.ClassicalInvolution.Q3.Q3W
