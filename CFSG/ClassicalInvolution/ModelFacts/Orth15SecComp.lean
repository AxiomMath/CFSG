module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Vertex

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.Assembly.LowTwoRank
open scoped commutatorElement

namespace SecComp

section Basic

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem comp_commute (hN : NormalizesLayer Φ a) (D : LocalLieSystemAt p f Φ a) {i j : Fin D.card}
    (hij : i ≠ j) (x : (compModel D i).K) (y : (compModel D j).K) :
    secComponentHom hN D i x * secComponentHom hN D j y =
      secComponentHom hN D j y * secComponentHom hN D i x := by
  have h1 := map_mul (sectionQuotientHom hN) (D.hom i x) (D.hom j y)
  have h2 := map_mul (sectionQuotientHom hN) (D.hom j y) (D.hom i x)
  have h3 := congrArg (sectionQuotientHom hN) (D.commute i j hij x y)
  exact h1.symm.trans (h3.trans h2)

theorem exists_component_of_member (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    {M : Subgroup G} (hM : M ∈ centMembers Φ a) :
    ∃ (i : Fin D.card) (R : Subgroup (compModel D i).K),
      R ∈ fundamentalSubgroups (D.tag i) (compModel D i).D ∧
        R.map (secComponentHom hs.normalizes D i) = modOdd a M := by
  set Y := centralizingLayer Φ {a} with hY
  have hMY : M ≤ Y := le_centralizingLayer hM
  have hMfam : DeltaClosure.modOddIn Y M ∈ DeltaClosure.localFamily Φ a :=
    ⟨M.subgroupOf Y, ⟨M, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  refine ⟨i, R, hR, ?_⟩
  have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
  rw [← h1, ← hMR]
  exact map_sectionQuotientHom_modOddIn hs.normalizes hM

theorem le_range_or_commute (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) {M : Subgroup G} (hM : M ∈ centMembers Φ a) :
    modOdd a M ≤ (secComponentHom hs.normalizes D j).range ∨
      ∀ x ∈ modOdd a M, ∀ y ∈ (secComponentHom hs.normalizes D j).range, x * y = y * x := by
  obtain ⟨i, R, -, hR⟩ := exists_component_of_member hs D hM
  by_cases hij : i = j
  · subst hij
    left
    rw [← hR]
    exact Subgroup.map_le_range _ _
  · right
    intro x hx y hy
    rw [← hR] at hx
    obtain ⟨r, -, rfl⟩ := hx
    obtain ⟨s, rfl⟩ := hy
    exact comp_commute hs.normalizes D hij r s

end Basic

section AOne

variable {p : ℕ} [Fact p.Prime]

theorem fund_eq_top_of_A1 :
    ∀ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (n e : ℕ), t = .PSL → n = 2 →
      StatedLieAdmissible t n p e →
      ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, R = ⊤ := by
  intro t n e ht hn hadm R hR
  subst ht hn
  exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_eq_top_PSL_two p e Fact.out
    hadm R hR

end AOne

section Component

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem modOdd_eq_range_of_A1 (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) {M : Subgroup G} (hM : M ∈ centMembers Φ a)
    (hMj : modOdd a M ≤ (secComponentHom hs.normalizes D j).range)
    (hA1 : D.tag j = .PSL ∧ D.rank j = 2) :
    modOdd a M = (secComponentHom hs.normalizes D j).range := by
  obtain ⟨R, hR, hRM⟩ := exists_fundamental_of_modOdd_le_sec hs D j hM hMj
  have htop : R = ⊤ := fund_eq_top_of_A1 (p := p) (D.tag j) (D.rank j) (D.exp j) hA1.1 hA1.2
    (D.admissible j) R hR
  rw [← hRM, htop, Subgroup.map_top]

theorem tag_of_central (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a) (j : Fin D.card)
    {M : Subgroup G} (hM : M ∈ centMembers Φ a)
    (hMj : modOdd a M ≤ (secComponentHom hs.normalizes D j).range) {w : OddQuot a}
    (hwM : w ∈ modOdd a M) (hw1 : w ≠ 1)
    (hwc : ∀ y ∈ (secComponentHom hs.normalizes D j).range, w * y = y * w) :
    D.tag j = .PSL ∧ D.rank j = 2 := by
  by_contra hne
  obtain ⟨R, hR, hRM⟩ := exists_fundamental_of_modOdd_le_sec hs D j hM hMj
  rw [← hRM] at hwM
  obtain ⟨r, hrR, rfl⟩ := hwM
  have hker := secComponentHom_ker_le_center hs.normalizes D j
  have hcen : ∀ y : (compModel D j).K, r * y * r⁻¹ * y⁻¹ ∈ Subgroup.center (compModel D j).K := by
    intro y
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have := hwc (secComponentHom hs.normalizes D j y) ⟨y, rfl⟩
    calc secComponentHom hs.normalizes D j r * secComponentHom hs.normalizes D j y *
          (secComponentHom hs.normalizes D j r)⁻¹ * (secComponentHom hs.normalizes D j y)⁻¹
        = (secComponentHom hs.normalizes D j r * secComponentHom hs.normalizes D j y) *
          (secComponentHom hs.normalizes D j r)⁻¹ * (secComponentHom hs.normalizes D j y)⁻¹ := by
          rfl
      _ = (secComponentHom hs.normalizes D j y * secComponentHom hs.normalizes D j r) *
          (secComponentHom hs.normalizes D j r)⁻¹ * (secComponentHom hs.normalizes D j y)⁻¹ := by
          rw [this]
      _ = 1 := by group
  have hr1 : r = 1 :=
    CFSG.ClassicalInvolution.ModelFacts.fundNoncentral_generic p (D.tag j) (D.rank j) (D.exp j)
      (D.isFundTag j) (D.admissible j) hne R hR r hrR hcen
  exact hw1 (by rw [hr1, map_one])

end Component

section Moved

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem exists_index_of_moved (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : ConjInvariant Ω)
    (hcls : ∀ K ∈ Ω, ∃ z, IsClassicalMember p f K z)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    {M : Subgroup G} (hM : M ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (Dsys : LocalLieSystemAt p f (exactFamily Ω c) c) {L : Subgroup (OddQuot c)}
    (hL : CFSG.IsComponent L) (hmov : MovedByAll B c L) :
    ∃ j : Fin Dsys.card,
      L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range ∧
        modOdd c (exactCore c M) ≤ L := by
  have hne : (tqMembers Ω c).Nonempty := ⟨M, hM⟩
  obtain ⟨D', hD'Q, -⟩ := lieDecomposition_exactFamily_comp hp2
    CFSG.ClassicalInvolution.ModelFacts.modelClauseZero fundamentalWholeA1 hq hΩ hcls hc2 hne Dsys
  obtain ⟨j₀, hMj₀, hj₀⟩ := FrameVertex.movedComponent_eq' hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hMb D'
  obtain ⟨j, hj⟩ := hD'Q j₀
  have hLeq : L = (secComponentHom (normalizesLayer_exactFamily hΩ) Dsys j).range :=
    (hj₀ L hL hmov).trans hj.symm
  refine ⟨j, hLeq, ?_⟩
  rw [hLeq]
  exact hMj₀.trans hj.symm.le

end Moved

end SecComp

end CFSG.ClassicalInvolution.Asc77
