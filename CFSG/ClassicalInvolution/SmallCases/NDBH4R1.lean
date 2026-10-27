module

public import CFSG.ClassicalInvolution.RouteD.NoG2D4Row
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Shared
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Pair
public import CFSG.ClassicalInvolution.SmallCases.NDBH2T2

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.RouteD.G2D4
  CFSG.ClassicalInvolution.RouteD.Exotic

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable (p f : ℕ) [Fact p.Prime]

@[expose] def G2D4SingleNoTwin : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteDSetup p f K z → ¬ HasTwin p f K z →
      ∀ (tY : StatedLieTag) (nY : ℕ), (tY = .G2 ∨ tY = .trialityD4) →
        LocalShapeT p f 1 tY nY (𝒞 K) z → False

variable {p f}

namespace NDBH4

variable {G : Type} [Group G]

theorem false_of_g2d4_noTwin [Finite G] {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) (hnt : ¬ HasTwin p f K z) {a : ℕ} {tY : StatedLieTag} {nY : ℕ}
    (htY : tY = .G2 ∨ tY = .trialityD4) (ha : 2 ≤ a)
    (h : LocalShapeT p f a tY nY (𝒞 K) z) : False := by
  classical
  have hΩ : InClass p f (𝒞 K) := S.inClass
  have hex : ExactMembers (𝒞 K) := S.exact
  have hp2 : p ≠ 2 := S.odd
  have hq5 : 5 ≤ p ^ f := S.five
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0] at hq5
      simp at hq5
    · exact h0
  have hsingle : ∀ L ∈ 𝒞 K, ∃ g : G, L = conjSub g K := single_class K
  have hMFZ : FundNoncentral p := Gaps.fundNoncentral p
  have hP1 : LocalOddCentral (𝒞 K) {z} := S.p1
  have hshape := h
  obtain ⟨D, hcard, i₁, ht₁, hr₁, hrest⟩ := h
  let A := {i : Fin D.card // i ≠ i₁}
  have hA1 : ∀ i : A, D.tag i.1 = .PSL ∧ D.rank i.1 = 2 := fun i => hrest i.1 i.2
  have hcardA : Fintype.card A = a := by
    simp [A, Fintype.card_subtype_compl, hcard]
  choose T hTmem hTimg using fun i : A => exists_member_of_a1 (Ω := 𝒞 K) D (hA1 i)
  have hTΩ : ∀ i, T i ∈ 𝒞 K := fun i => (hTmem i).1
  have hcommz : ∀ i : A, ∀ N ∈ centralizingMembers (𝒞 K) {z}, N ≠ T i →
      Commutes (T i) N := fun i N hN hne =>
    (commutes_or_eq_of_whole hΩ hex hP1 D (hTmem i) hN (hTimg i)).resolve_right hne
  choose w hw using fun i : A => hΩ.classical (T i) (hTΩ i)
  have hΩw : ∀ i : A, centralizingMembers (𝒞 K) {w i} =
      centralizingMembers (𝒞 K) {z} := fun i =>
    centralizingMembers_eq_of_twin hp2 hf hΩ S.cls (hw i) (hsingle (T i) (hTΩ i)) (hTmem i)
      (hcommz i)
  have hnbhd : ∀ i : A, ∀ N ∈ 𝒞 K,
      (N = T i ∨ Commutes N (T i)) ↔ N ∈ centralizingMembers (𝒞 K) {z} := by
    intro i N hN
    constructor
    · rintro (rfl | hc)
      · exact hTmem i
      · rw [← hΩw i]
        exact mem_centralizingMembers_of_commutes hN (hw i).mem hc
    · intro hNz
      by_cases hNT : N = T i
      · exact Or.inl hNT
      · exact Or.inr (hcommz i N hNz hNT).symm
  obtain ⟨R₀, hR₀, hmem⟩ := D.meets i₁
  obtain ⟨M, hMz, hMR⟩ := mem_locFamily_iff.mp hmem
  have hMi : locImg (𝒞 K) z M ≤ (D.hom i₁).range := hMR ▸ Subgroup.map_le_range _ _
  have hMT : ∀ i : A, M ≠ T i := by
    intro i hMi'
    have h1 : locImg (𝒞 K) z (T i) ≤ (D.hom i₁).range := hMi' ▸ hMi
    exact i.2 (eq_of_locImg_le_range hΩ hex D (hTmem i) (hTimg i).le h1)
  have hcommM : ∀ i : A, Commutes (T i) M := fun i => hcommz i M hMz (hMT i)
  have hnotall : ∃ L ∈ centralizingMembers (𝒞 K) {z}, L ≠ M ∧ ¬ Commutes M L := by
    have hi₁na : ¬ IsA1Comp D i₁ := by
      rintro ⟨hh, -⟩
      rw [ht₁] at hh
      rcases htY with h' | h' <;> rw [h'] at hh <;> exact absurd hh (by decide)
    obtain ⟨N, N', hN, hN', hNN'⟩ := exists_ne_of_not_isA1Comp hΩ hex hi₁na
    have hMcomp : M ∈ compMembers (𝒞 K) z D i₁ := ⟨hMz, hMi⟩
    by_contra hall
    push Not at hall
    have hblock : ∀ B, Linked (𝒞 K) z M B → B = M := by
      intro B hB
      induction hB with
      | refl => rfl
      | @tail b c _ hbc ih =>
        rw [ih] at hbc
        by_contra hcM
        exact hbc.2.2 (hall c hbc.2.1 hcM)
    have hN_M : N = M := hblock N ((linked_iff_mem_compMembers hΩ hex hP1 hMcomp).mpr hN)
    have hN'_M : N' = M := hblock N' ((linked_iff_mem_compMembers hΩ hex hP1 hMcomp).mpr hN')
    exact hNN' (hN_M.trans hN'_M.symm)
  obtain ⟨g, hg⟩ := hsingle M hMz.1
  have hzx : IsClassicalMember p f M (g * z * g⁻¹) := by
    rw [hg]
    exact S.cls.conj g
  have hP1x : LocalOddCentral (𝒞 K) {g * z * g⁻¹} :=
    localOddCentral_conj hΩ.conjInvariant g z hP1
  have hncard : (centralizingMembers (𝒞 K) {g * z * g⁻¹}).ncard =
      (centralizingMembers (𝒞 K) {z}).ncard :=
    ncard_centralizingMembers_conj hΩ.conjInvariant g z
  obtain ⟨Dx, hcardx, j₁, htx, hrx, hrestx⟩ :=
    LocalShapeT.conj (p := p) (f := f) hΩ.conjInvariant g hshape
  generalize g * z * g⁻¹ = x at hzx hP1x hncard Dx
  have hTx : ∀ i : A, T i ∈ centralizingMembers (𝒞 K) {x} := fun i =>
    mem_centralizingMembers_of_commutes (hTΩ i) hzx.mem (hcommM i)
  have hMx : M ∈ centralizingMembers (𝒞 K) {x} :=
    ⟨hMz.1, le_centralizer_of_isClassicalMember hzx⟩
  have hTj : ∀ i : A, locImg (𝒞 K) x (T i) ≤ (Dx.hom j₁).range := by
    intro i
    obtain ⟨j, hj⟩ := RouteD.exists_range_of_mem Dx (mem_locFamily_iff.mpr ⟨T i, hTx i, rfl⟩)
    by_cases hjj : j = j₁
    · subst hjj
      exact hj
    · exfalso
      have hwhole := locImg_eq_range_of_le_a1 hΩ hex Dx (hTx i) (hrestx j hjj) hj
      have hsub : centralizingMembers (𝒞 K) {x} ⊆
          centralizingMembers (𝒞 K) {z} := by
        intro L hL
        rcases commutes_or_eq_of_whole hΩ hex hP1x Dx (hTx i) hL hwhole with hc | rfl
        · exact (hnbhd i L hL.1).mp (Or.inr hc.symm)
        · exact hTmem i
      have heq : centralizingMembers (𝒞 K) {x} =
          centralizingMembers (𝒞 K) {z} :=
        Set.eq_of_subset_of_ncard_le hsub hncard.ge (Set.toFinite _)
      obtain ⟨L, hLz, hLM, hLnc⟩ := hnotall
      have hLx : L ∈ centralizingMembers (𝒞 K) {x} := by
        rw [heq]
        exact hLz
      rcases commutes_or_eq_of_involution hMFZ hΩ hex hP1x Dx hMx hLx hzx with hc | hLM'
      · exact hLnc hc
      · exact hLM hLM'
  have hinjT : Function.Injective T := by
    intro i k hik
    refine Subtype.ext (eq_of_locImg_le_range hΩ hex D (hTmem i) (hTimg i).le ?_)
    rw [hik]
    exact (hTimg k).le
  have hcommT : ∀ i k : A, i ≠ k → Commutes (T i) (T k) := fun i k hik =>
    hcommz i (T k) (hTmem k) (fun h => hik (hinjT h.symm))
  obtain ⟨i, k, hik⟩ := Fintype.exists_pair_of_one_lt_card (show 1 < Fintype.card A by omega)
  have hmemx : ∀ m : A, T m ∈ compMembers (𝒞 K) x Dx j₁ := fun m => ⟨hTx m, hTj m⟩
  have hww : w i = w k := eq_involution_of_commuting_pair (g2d4SharedInvolution p) hp2 hΩ hP1x
    Dx (by rw [htx]; exact htY) (hmemx i) (hmemx k) (hw i) (hw k) (hcommT i k hik)
  have hwk : IsClassicalMember p f (T k) (w i) := hww ▸ hw k
  exact hik (hinjT (NDBH2.eq_of_isClassicalMember hp2 hq5 S.cls hnt (hTΩ i) (hTΩ k) (hw i) hwk))

end NDBH4

end CFSG.ClassicalInvolution.NDB
