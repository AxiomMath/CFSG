module

public import CFSG.ClassicalInvolution.RouteD.TypeULocal

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType.BorelTits
open scoped MatrixGroups

section Tail

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

variable (K p f) in
@[expose] noncomputable def tailBlockU (k : ℕ) : Su K p f k →* Su K p f (k + 2) :=
  blockEmb K p f (k + 2) k 2 (by omega)

theorem tailBlockU_injective (k : ℕ) : Function.Injective (tailBlockU K p f k) :=
  blockEmb_injective _

theorem tailBlockU_commutes_rootSU2 {k : ℕ} (s : Su K p f k) (r : Su K p f 2) :
    tailBlockU K p f k s * blockEmb K p f (k + 2) 2 0 (by omega) r =
      blockEmb K p f (k + 2) 2 0 (by omega) r * tailBlockU K p f k s :=
  blockEmb_comm (i := 2) (j := 0) (k := k) (l := 2) _ _ (Or.inr (by omega)) s r

theorem map_tailBlockU_mem_longRootSetU (h2 : (2 : K) ≠ 0) {k : ℕ} (hk : 2 ≤ k)
    {R : Subgroup (Su K p f k)} (hR : R ∈ longRootSetU hk) :
    R.map (tailBlockU K p f k) ∈ longRootSetU (by omega : 2 ≤ k + 2) := by
  obtain ⟨g, rfl⟩ := (mem_longRootSetU_iff hk).mp hR
  have h1 : (rootSU2 K p f hk).map (tailBlockU K p f k) =
      (blockEmb K p f (k + 2) 2 2 (by omega)).range := by
    rw [rootSU2, ← MonoidHom.range_comp]
    exact congrArg MonoidHom.range
      (blockEmb_comp (K := K) (p := p) (f := f) (by omega) (by omega))
  rw [map_map_conj, h1]
  have hT : (blockEmb K p f (k + 2) 2 2 (by omega)).range =
      LcU K p f (⟨{⟨2, by omega⟩, ⟨3, by omega⟩}, by
        rw [Finset.card_pair]
        intro h
        have := congrArg Fin.val h
        simp at this⟩ : Pair (k + 2)) := by
    rw [range_blockEmb_eq_longRootGroupSU h2 (by omega), negBlock_eq_zMat (by omega)]
    rfl
  rw [hT]
  exact longRootSetU_conjInvariant _ _ _ ⟨_, isLongRootSU2_LcU h2 (by omega) _⟩

theorem tailBlockU_eq_one_of_mem_center (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {k : ℕ}
    (hk : 1 ≤ k) {s : Su K p f k}
    (hs : tailBlockU K p f k s ∈ Subgroup.center (Su K p f (k + 2))) : s = 1 := by
  obtain ⟨c, hc⟩ := Transfer.exists_scalar_of_mem_center_su hK hq (by omega : 3 ≤ k + 2) hs
  have h0 : suMat (tailBlockU K p f k s) ⟨0, by omega⟩ ⟨0, by omega⟩ = 1 := by
    rw [tailBlockU, suMat_blockEmb, blockMat_apply_of_not_mem_left _ (by simp)]
    simp
  have hc1 : c = 1 := by
    rw [hc] at h0
    simpa [Matrix.scalar_apply] using h0
  apply tailBlockU_injective k
  rw [map_one]
  apply suMat_injective
  rw [hc, hc1, map_one, suMat_one]

theorem injective_comp_tailBlockU (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f) {k : ℕ}
    (hk : 1 ≤ k) {H : Type} [Group H] {ψ : Su K p f (k + 2) →* H}
    (hker : ψ.ker ≤ Subgroup.center (Su K p f (k + 2))) :
    Function.Injective (ψ.comp (tailBlockU K p f k)) := by
  rw [injective_iff_map_eq_one]
  intro s hs
  exact tailBlockU_eq_one_of_mem_center hK hq hk (hker (MonoidHom.mem_ker.mpr hs))

end Tail

section Count

variable {p f : ℕ} [Fact p.Prime]

theorem ncard_fundamental_le_of_psu (hp2 : p ≠ 2) {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) (i : Fin D.card) (ht : D.tag i = .PSU) {n : ℕ}
    (hr : D.rank i = n) (hn : 2 ≤ n) :
    {K : Subgroup X | ∃ R ∈ fundamentalSubgroups (D.tag i)
        (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)}.ncard ≤
      (longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn).ncard := by
  obtain ⟨ψ, -, -, hfund⟩ := exists_psu_hom hp2 D i ht hr hn
  have hsub : {K : Subgroup X | ∃ R ∈ fundamentalSubgroups (D.tag i)
      (modelUniv (D.tag i) (D.rank i) p (D.exp i) Fact.out).D, K = R.map (D.hom i)} ⊆
      (fun L : Subgroup (Su (GaloisField p (2 * f)) p f n) => L.map ψ) ''
        longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) hn := by
    intro K hK
    obtain ⟨L, hL, hKL⟩ := (hfund K).mp hK
    exact ⟨L, hL, hKL.symm⟩
  exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

theorem LocalShapeU.ncard_locFamily_le (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G] {m : ℕ}
    (hm : 1 ≤ m) {Ω : Set (Subgroup G)} {x : G} (h : LocalShapeU p f m Ω x) :
    (locFamily Ω x).ncard ≤
      1 + (longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
        (by omega : 2 ≤ m + 1)).ncard := by
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
  have h1 : (P i₁).ncard ≤ (longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f)
      (by omega : 2 ≤ m + 1)).ncard :=
    ncard_fundamental_le_of_psu hp2 D i₁ ht₁ hr₁ (by omega)
  calc (locFamily Ω x).ncard ≤ (P i₀ ∪ P i₁).ncard := Set.ncard_le_ncard hΦ (Set.toFinite _)
    _ ≤ (P i₀).ncard + (P i₁).ncard := Set.ncard_union_le _ _
    _ ≤ _ := by omega

end Count

end CFSG.ClassicalInvolution.RouteD
