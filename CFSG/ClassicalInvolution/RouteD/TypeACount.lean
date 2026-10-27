module

public import CFSG.ClassicalInvolution.RouteD.LocalPair
public import CFSG.ClassicalInvolution.RouteD.TypeABridge

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime]

theorem ncard_fundamental_le_of_psl {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSL) {k : ℕ}
    (hr : D.rank i = k + 1) (hk : 2 ≤ k + 1) :
    {K : Subgroup X | ∃ R ∈ fundamentalSubgroups (D.tag i)
        (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)}.ncard ≤
      (longRootSet (K := GaloisField p f) hk).ncard := by
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · rw [ht] at h; exact absurd h (by decide)
  have key : ∀ (t : StatedLieTag) (n e : ℕ) (hT : t = .PSL) (hN : n = k + 1) (hE : e = f)
      (φ : (modelUniv t n p e Fact.out).K →* X),
      {K : Subgroup X | ∃ R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        K = R.map φ}.ncard ≤ (longRootSet (K := GaloisField p f) hk).ncard := by
    intro t n e hT hN hE φ
    have hE' : f = e := hE.symm
    subst hT hN hE'
    have himg : {K : Subgroup X | ∃ R ∈ fundamentalSubgroups .PSL
        (modelUniv .PSL (k + 1) p f Fact.out).D, K = R.map φ} =
        (fun R : Subgroup SL(k + 1, GaloisField p f) => R.map φ) ''
          fundamentalSubgroups .PSL (SpecialLinear.rootDatum k (GaloisField p f)) := by
      ext K
      constructor
      · rintro ⟨R, hR, rfl⟩
        exact ⟨R, hR, rfl⟩
      · rintro ⟨R, hR, rfl⟩
        exact ⟨R, hR, rfl⟩
    rw [himg]
    exact (Set.ncard_image_le (Set.toFinite _)).trans
      (Set.ncard_le_ncard (fundamentalSubgroups_psl_subset hk) (Set.toFinite _))
  exact key _ _ _ ht hr he (D.hom i)

theorem LocalShapeA.ncard_locFamily_le {G : Type} [Group G] [Finite G] {m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeA p f m Ω x) :
    (locFamily Ω x).ncard ≤
      1 + (longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1)).ncard := by
  obtain ⟨D, hcard, i₀, i₁, hne, ht₀, hr₀, ht₁, hr₁⟩ := h
  let P : Fin D.card → Set (Subgroup (locQuot Ω x)) := fun i =>
    {K | ∃ R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)}
  have hΦ : locFamily Ω x ⊆ P i₀ ∪ P i₁ := by
    intro K hK
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental K hK
    have hi := i.isLt
    have hi₀ := i₀.isLt
    have hi₁ := i₁.isLt
    have hne' : i₀.val ≠ i₁.val := fun e => hne (Fin.ext e)
    have : i = i₀ ∨ i = i₁ := by
      rcases Nat.lt_or_ge i.val 1 with h1 | h1
      · by_cases h0 : i₀.val = 0
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
      · by_cases h0 : i₀.val = 1
        · left; exact Fin.ext (by omega)
        · right; exact Fin.ext (by omega)
    rcases this with rfl | rfl
    · exact Or.inl ⟨R, hR, rfl⟩
    · exact Or.inr ⟨R, hR, rfl⟩
  have h0 : (P i₀).ncard ≤ 1 :=
    (ncard_fundamental_le_of_psl D i₀ ht₀ (k := 1) hr₀ (by omega)).trans
      (longRootSet_two_ncard_le (F := GaloisField p f) (by omega))
  have h1 : (P i₁).ncard ≤ (longRootSet (K := GaloisField p f) (by omega : 2 ≤ m + 1)).ncard :=
    ncard_fundamental_le_of_psl D i₁ ht₁ (k := m) hr₁ (by omega)
  calc (locFamily Ω x).ncard ≤ (P i₀ ∪ P i₁).ncard := Set.ncard_le_ncard hΦ (Set.toFinite _)
    _ ≤ (P i₀).ncard + (P i₁).ncard := Set.ncard_union_le _ _
    _ ≤ _ := by omega

end CFSG.ClassicalInvolution.RouteD
