module

public import CFSG.ClassicalInvolution.RouteD.ExoticShapes
public import CFSG.ClassicalInvolution.RouteD.NoG2D4Local
public import CFSG.ClassicalInvolution.RouteD.MultiStarComp

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.RouteD.G2D4

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem false_of_localShapeT_g2d4_of_three_le [Finite G] {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) {a : ℕ} {tY : StatedLieTag} {nY : ℕ}
    (htY : tY = .G2 ∨ tY = .trialityD4) (ha : 3 ≤ a)
    (h : LocalShapeT p f a tY nY (conjClass K) z) : False := by
  classical
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex : ExactMembers (conjClass K) := S.exact
  have hp2 : p ≠ 2 := S.odd
  have hq5 : 5 ≤ p ^ f := S.five
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0] at hq5
      simp at hq5
    · exact h0
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
  have hMFZ : FundNoncentral p := Gaps.fundNoncentral p
  have hP1 : LocalOddCentral (conjClass K) {z} := S.p1
  have hshape := h
  obtain ⟨D, hcard, i₁, ht₁, hr₁, hrest⟩ := h
  let A := {i : Fin D.card // i ≠ i₁}
  have hA1 : ∀ i : A, D.tag i.1 = .PSL ∧ D.rank i.1 = 2 := fun i => hrest i.1 i.2
  have hcardA : Fintype.card A = a := by
    simp [A, Fintype.card_subtype_compl, hcard]
  choose T hTmem hTimg using fun i : A => exists_member_of_a1 (Ω := conjClass K) D (hA1 i)
  have hTΩ : ∀ i, T i ∈ conjClass K := fun i => (hTmem i).1
  have hcommz : ∀ i : A, ∀ N ∈ centralizingMembers (conjClass K) {z}, N ≠ T i →
      Commutes (T i) N := fun i N hN hne =>
    (commutes_or_eq_of_whole hΩ hex hP1 D (hTmem i) hN (hTimg i)).resolve_right hne
  choose w hw using fun i : A => hΩ.classical (T i) (hTΩ i)
  have hΩw : ∀ i : A, centralizingMembers (conjClass K) {w i} =
      centralizingMembers (conjClass K) {z} := fun i =>
    centralizingMembers_eq_of_twin hp2 hf hΩ S.cls (hw i) (hsingle (T i) (hTΩ i)) (hTmem i)
      (hcommz i)
  have hnbhd : ∀ i : A, ∀ N ∈ conjClass K,
      (N = T i ∨ Commutes N (T i)) ↔ N ∈ centralizingMembers (conjClass K) {z} := by
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
  have hMi : locImg (conjClass K) z M ≤ (D.hom i₁).range := hMR ▸ Subgroup.map_le_range _ _
  have hMT : ∀ i : A, M ≠ T i := by
    intro i hMi'
    have h1 : locImg (conjClass K) z (T i) ≤ (D.hom i₁).range := hMi' ▸ hMi
    exact i.2 (eq_of_locImg_le_range hΩ hex D (hTmem i) (hTimg i).le h1)
  have hcommM : ∀ i : A, Commutes (T i) M := fun i => hcommz i M hMz (hMT i)
  have hnotall : ∃ L ∈ centralizingMembers (conjClass K) {z}, L ≠ M ∧ ¬ Commutes M L := by
    have hi₁na : ¬ IsA1Comp D i₁ := by
      rintro ⟨hh, -⟩
      rw [ht₁] at hh
      rcases htY with h' | h' <;> rw [h'] at hh <;> exact absurd hh (by decide)
    obtain ⟨N, N', hN, hN', hNN'⟩ := exists_ne_of_not_isA1Comp hΩ hex hi₁na
    have hMcomp : M ∈ compMembers (conjClass K) z D i₁ := ⟨hMz, hMi⟩
    by_contra hall
    push Not at hall
    have hblock : ∀ B, Linked (conjClass K) z M B → B = M := by
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
  have hP1x : LocalOddCentral (conjClass K) {g * z * g⁻¹} :=
    localOddCentral_conj hΩ.conjInvariant g z hP1
  have hncard : (centralizingMembers (conjClass K) {g * z * g⁻¹}).ncard =
      (centralizingMembers (conjClass K) {z}).ncard :=
    ncard_centralizingMembers_conj hΩ.conjInvariant g z
  obtain ⟨Dx, hcardx, j₁, htx, hrx, hrestx⟩ :=
    LocalShapeT.conj (p := p) (f := f) hΩ.conjInvariant g hshape
  generalize g * z * g⁻¹ = x at hzx hP1x hncard Dx
  have hTx : ∀ i : A, T i ∈ centralizingMembers (conjClass K) {x} := fun i =>
    mem_centralizingMembers_of_commutes (hTΩ i) hzx.mem (hcommM i)
  have hMx : M ∈ centralizingMembers (conjClass K) {x} :=
    ⟨hMz.1, le_centralizer_of_isClassicalMember hzx⟩
  have hTj : ∀ i : A, locImg (conjClass K) x (T i) ≤ (Dx.hom j₁).range := by
    intro i
    obtain ⟨j, hj⟩ := exists_range_of_mem Dx (mem_locFamily_iff.mpr ⟨T i, hTx i, rfl⟩)
    by_cases hjj : j = j₁
    · subst hjj
      exact hj
    · exfalso
      have hwhole := locImg_eq_range_of_le_a1 hΩ hex Dx (hTx i) (hrestx j hjj) hj
      have hsub : centralizingMembers (conjClass K) {x} ⊆
          centralizingMembers (conjClass K) {z} := by
        intro L hL
        rcases commutes_or_eq_of_whole hΩ hex hP1x Dx (hTx i) hL hwhole with hc | rfl
        · exact (hnbhd i L hL.1).mp (Or.inr hc.symm)
        · exact hTmem i
      have heq : centralizingMembers (conjClass K) {x} =
          centralizingMembers (conjClass K) {z} :=
        Set.eq_of_subset_of_ncard_le hsub hncard.ge (Set.toFinite _)
      obtain ⟨L, hLz, hLM, hLnc⟩ := hnotall
      have hLx : L ∈ centralizingMembers (conjClass K) {x} := by
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
  have h3 : 2 < Fintype.card A := by omega
  obtain ⟨i, k, l, hik, hil, hkl⟩ := Fintype.two_lt_card_iff.mp h3
  have hmemx : ∀ m : A, T m ∈ compMembers (conjClass K) x Dx j₁ := fun m => ⟨hTx m, hTj m⟩
  have hno := tag_ne_of_commuting_triple hp2 hΩ hex Dx (hmemx i) (hmemx k) (hmemx l)
    (hcommT i k hik) (hcommT i l hil) (hcommT k l hkl)
  rcases htY with h' | h'
  · exact hno.1 (htx.trans h')
  · exact hno.2 (htx.trans h')

@[expose] def ShapeExoticG2D4Small (a : ℕ) (t : StatedLieTag) (n : ℕ) : Prop :=
  ShapeExoticG2D4 a t n ∧ a ≤ 2

theorem rowExoticG2D4_of_small (h : RowPiece p f ShapeExoticG2D4Small) :
    RowPiece p f ShapeExoticG2D4 := by
  intro a t n hshape
  by_cases ha : a ≤ 2
  · exact h a t n ⟨hshape, ha⟩
  · intro G _ _ _ hnab K z S hloc
    exfalso
    exact false_of_localShapeT_g2d4_of_three_le S hshape.2 (by omega) hloc

end CFSG.ClassicalInvolution.RouteD.Exotic
