module

public import CFSG.ClassicalInvolution.Q3.Q3WATwinD
public import CFSG.LieType.Steinberg.CentralExt.MinusculeCenter

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


theorem exists_hom_of_comp3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (i : ι) {tY : StatedLieTag} {nY : ℕ}
    (hk : D.kind i = CompData.model tY nY) :
    ∃ ψ : (modelUniv tY nY 3 1 Nat.prime_three).K →* X,
      ψ.ker ≤ Subgroup.center _ ∧ ψ.range = (D.hom i).range ∧
      ∀ K : Subgroup X, (∃ R ∈ (D.kind i).fund, K = R.map (D.hom i)) ↔
        ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D, K = R.map ψ := by
  have key : ∀ c : CompData, c = CompData.model tY nY →
      ∀ (φ : c.G →* X) (_ : φ.ker ≤ Subgroup.center c.G),
      ∃ ψ : (modelUniv tY nY 3 1 Nat.prime_three).K →* X,
        ψ.ker ≤ Subgroup.center _ ∧ ψ.range = φ.range ∧
        ∀ K : Subgroup X, (∃ R ∈ c.fund, K = R.map φ) ↔
          ∃ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D, K = R.map ψ := by
    rintro c rfl φ hφ
    exact ⟨φ, hφ, rfl, fun K => Iff.rfl⟩
  exact key _ hk (D.hom i) (D.ker_le_center i)

theorem map_mem_of_comp3 {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData3 ι X Φ) (hΦ : ConjInvariant Φ) (i : ι) {tY : StatedLieTag} {nY : ℕ}
    (hk : D.kind i = CompData.model tY nY)
    (hsc : FundamentalSingleClass tY (modelUniv tY nY 3 1 Nat.prime_three).D) :
    ∀ R ∈ (D.kind i).fund, R.map (D.hom i) ∈ Φ := by
  have key : ∀ c : CompData, c = CompData.model tY nY → ∀ (φ : c.G →* X),
      (∃ R₀ ∈ c.fund, R₀.map φ ∈ Φ) → ∀ R ∈ c.fund, R.map φ ∈ Φ := by
    rintro c rfl φ ⟨R₀, hR₀, hmem⟩ R hR
    obtain ⟨g, rfl⟩ := hsc R₀ hR₀ R hR
    exact (conjSub_map φ g R₀) ▸ hΦ (φ g) _ hmem
  exact key _ hk (D.hom i) (D.meets i)

theorem LocalShapeC3.nonempty_dictT {G : Type} [Group G] [Finite G] {tY : StatedLieTag} {nY : ℕ}
    (hsc : FundamentalSingleClass tY (modelUniv tY nY 3 1 Nat.prime_three).D)
    {Ω : Set (Subgroup G)} (hΩ : InClass3 Ω) {K : Subgroup G} (hK : K ∈ Ω) {z : G}
    (hz : IsClassicalMember3 K z) (h : LocalShapeC3 1 (CompData.model tY nY) Ω z) :
    Nonempty (ShapeDictT 3 1 tY nY Ω z) := by
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
  obtain ⟨ψ, hker, hrange, hfund⟩ := exists_hom_of_comp3 D i₁ hk₁
  have hk0 : D.kind i₀ = CompData.sl23 := hrest i₀ hne
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨hK, isSubnormal_le hz.subnormal⟩
  have hΦ : ConjInvariant (locFamily Ω z) :=
    conjInvariant_oddQuotientFamily (inClass3_local hΩ {z} ⟨K, hKz⟩).conjInvariant
  refine ⟨{
    ψ := ψ
    ker_le := hker
    Q₀ := (D.hom i₀).range
    commutes := ?_
    mem_fam := ?_
    fam_cases := ?_
    card_le := ?_ }⟩
  · rw [hrange]
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact D.commute i₀ i₁ hne a b
  · intro R hR
    obtain ⟨R', hR', hRR'⟩ := (hfund (R.map ψ)).mpr ⟨R, hR, rfl⟩
    rw [hRR']
    exact map_mem_of_comp3 D hΦ i₁ hk₁ hsc R' hR'
  · intro K' hK'
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K' hK'
    rcases hall i with h0 | h1
    · subst h0
      exact Or.inl (Subgroup.map_le_range _ _)
    · subst h1
      obtain ⟨R', hR', hRR'⟩ := (hfund _).mp ⟨R, hR, rfl⟩
      exact Or.inr ⟨R', hR', hRR'⟩
  · have key : ∀ c : CompData, c = CompData.sl23 → ∀ φ : c.G →* locQuot Ω z,
        Nat.card φ.range ≤ Nat.card SL(2, GaloisField 3 1) := by
      rintro c rfl φ
      rw [card_sl2_gf3, ← natCard_sl2Three]
      exact Nat.card_le_card_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
    exact key _ hk0 (D.hom i₀)

structure YData3 (tY : StatedLieTag) (nY : ℕ) : Prop where
  sc : FundamentalSingleClass tY (modelUniv tY nY 3 1 Nat.prime_three).D
  perfK : Group.IsPerfect (modelUniv tY nY 3 1 Nat.prime_three).K
  pow3 : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D, Pow3 R
  central : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
    ∀ r ∈ R, r ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K → r = 1
  std : ∀ R ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
    ∃ R' ∈ fundamentalSubgroups tY (modelUniv tY nY 3 1 Nat.prime_three).D,
      ∃ W : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K,
        LinearBlockStandardPair (GaloisField 3 1) W R R'
  cop : ∀ w ∈ Subgroup.center (modelUniv tY nY 3 1 Nat.prime_three).K, ¬ 3 ∣ orderOf w

section Facts


theorem yData3_D6 (hadm : StatedLieAdmissible .POmegaPlus 6 3 1) : YData3 .POmegaPlus 6 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .POmegaPlus
      (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 6 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_plusDatum (F := GaloisField 3 1)
    (by norm_num : 3 ≤ 6) (by norm_num : 4 ≤ 6)
  have hl := ModelFacts.isLongestRoot_single .POmegaPlus 6 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .POmegaPlus)
    (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D
    (k := ⟨0, by show 0 < 6; decide⟩) (hl ⟨0, by show 0 < 6; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .POmegaPlus)
    (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D
    (k := ⟨1, by show 1 < 6; decide⟩) (hl ⟨1, by show 1 < 6; decide⟩ trivial)
  exact ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁,
    fun w hw h3 => absurd (h3.trans (orderOf_dvd_of_pow_eq_one
      (pow_four_of_mem_center_spinPlus (by norm_num : 3 ≤ 6) hw))) (by norm_num)⟩

theorem yData3_E7 (hadm : StatedLieAdmissible .E7 0 3 1) : YData3 .E7 0 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hsc : FundamentalSingleClass .E7 (modelUniv .E7 0 3 1 Nat.prime_three).D :=
    ModelFacts.fundamentalSingleClass .E7 0 3 1 hp trivial hadm (by decide) (by decide)
  obtain ⟨-, W₁, hW₁⟩ := ModelFacts.standardPair_e7Datum (F := GaloisField 3 1)
  have hl := ModelFacts.isLongestRoot_single .E7 0 3 1 hp trivial hadm
  have hR₀ := rankOne_mem_fundamental (t := .E7) (modelUniv .E7 0 3 1 Nat.prime_three).D
    (k := ⟨0, by show 0 < 7; decide⟩) (hl ⟨0, by show 0 < 7; decide⟩ trivial)
  have hR₁ := rankOne_mem_fundamental (t := .E7) (modelUniv .E7 0 3 1 Nat.prime_three).D
    (k := ⟨2, by show 2 < 7; decide⟩) (hl ⟨2, by show 2 < 7; decide⟩ trivial)
  refine ⟨hsc, perfectK_of_admissible hp trivial hadm,
    pow3_of_mem_fundamental hsc hR₀ (pow3_of_stdPair card_gf3 hW₁).1,
    central_of_stdPair hsc hR₀ hW₁, std_of_stdPair hsc hR₀ hR₁ hW₁, ?_⟩
  intro w hw
  have hcard := (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e7
    (k := GaloisField 3 1)).1
  rw [card_gf3] at hcard
  have hw' : w ∈ Subgroup.center
      (CFSG.LieType.Steinberg.Minuscule.e7Data_valid.minGroup (GaloisField 3 1)) := hw
  have hd : orderOf w ∣ Nat.gcd 2 (3 - 1) :=
    (Subgroup.orderOf_dvd_natCard _ hw').trans (dvd_of_eq hcard)
  exact fun h3 => absurd (h3.trans hd) (by norm_num)

end Facts

end CFSG.ClassicalInvolution.Q3.Q3W
