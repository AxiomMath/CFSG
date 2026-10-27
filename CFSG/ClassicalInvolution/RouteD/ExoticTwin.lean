module

public import CFSG.ClassicalInvolution.RouteD.ExoticTwinModel
public import CFSG.ClassicalInvolution.RouteD.LocalTwinPartner
public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectBridge

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

section Whole

variable [Finite G] {Ω : Set (Subgroup G)}

theorem commutes_or_eq_of_whole (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {N L : Subgroup G} (hN : N ∈ centralizingMembers Ω {x}) (hL : L ∈ centralizingMembers Ω {x})
    {i : Fin D.card} (hi : locImg Ω x N = (D.hom i).range) : Commutes N L ∨ L = N := by
  have hLmem : locImg Ω x L ∈ locFamily Ω x := mem_locFamily_iff.mpr ⟨L, hL, rfl⟩
  obtain ⟨j, hj⟩ := exists_range_of_mem D hLmem
  by_cases hij : j = i
  · subst hij
    right
    have hle : L ≤ N := le_of_locImg_le hΩ hP1 hL (hi ▸ hj)
    obtain ⟨zL, hzL⟩ := hΩ.classical L hL.1
    obtain ⟨zN, hzN⟩ := hΩ.classical N hN.1
    obtain ⟨eL⟩ := hzL.nonempty_equiv_sl2 (hex L hL.1)
    obtain ⟨eN⟩ := hzN.nonempty_equiv_sl2 (hex N hN.1)
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_congr eL.toEquiv, Nat.card_congr eN.toEquiv])
  · left
    refine commutes_of_commutes_locImg hΩ hP1 hN hL ?_
    intro a ha b hb
    exact commutes_range D (Ne.symm hij) a (hi ▸ ha) b (hj hb)

theorem locImg_eq_range_of_le_a1 (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) {N : Subgroup G}
    (hN : N ∈ centralizingMembers Ω {x}) {j : Fin D.card}
    (hj : D.tag j = .PSL ∧ D.rank j = 2) (hle : locImg Ω x N ≤ (D.hom j).range) :
    locImg Ω x N = (D.hom j).range := by
  obtain ⟨j', R, hR, hRN⟩ := D.fundamental _ (mem_locFamily_iff.mpr ⟨N, hN, rfl⟩)
  have hj' : locImg Ω x N ≤ (D.hom j').range := hRN ▸ Subgroup.map_le_range _ _
  have hjj : j' = j := eq_of_locImg_le_range hΩ hex D hN hj' hle
  subst hjj
  have hR' : R = ⊤ := eq_top_of_psl_two (e := D.exp j') hj.1 hj.2 hR
  rw [hRN, hR', Subgroup.map_top]

omit [Finite G] in
theorem exists_member_of_a1 {x : G} (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {i : Fin D.card} (hi : D.tag i = .PSL ∧ D.rank i = 2) :
    ∃ T ∈ centralizingMembers Ω {x}, locImg Ω x T = (D.hom i).range := by
  obtain ⟨R, hR, hmem⟩ := D.meets i
  have hR' : R = ⊤ := eq_top_of_psl_two (e := D.exp i) hi.1 hi.2 hR
  obtain ⟨T, hT, hTR⟩ := mem_locFamily_iff.mp hmem
  exact ⟨T, hT, by rw [hTR, hR', Subgroup.map_top]⟩

theorem modelTwinClass_of_family {ι : Type} (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {x : G}
    (hP1 : LocalOddCentral Ω {x}) (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x))
    {j : Fin D.card}
    (hsc : FundamentalSingleClass (D.tag j)
      (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (hperf : FundPerfect (D.tag j) (modelUniv (D.tag j) (D.rank j) p (D.exp j) Fact.out).D)
    (T : ι → Subgroup G) (hTx : ∀ k, T k ∈ centralizingMembers Ω {x})
    (hTj : ∀ k, locImg Ω x (T k) ≤ (D.hom j).range) (hinj : Function.Injective T)
    (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ Ω, ∀ k l, (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
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
    exact htwin N hN.1.1 k l

end Whole

theorem modelTwinClass_congr {t t' : StatedLieTag} {n n' e e' a : ℕ} (ht : t = t') (hn : n = n')
    (he : e = e') (h : ModelTwinClass p t n e a) : ModelTwinClass p t' n' e' a := by
  subst ht hn he
  exact h

theorem trialityD4_vacuous {X : Type} [Group X] {Φ : Set (Subgroup X)}
    (D : LieSystemData p f X Φ) {j₁ : Fin D.card} {tY : StatedLieTag} (hD4 : tY ≠ .trialityD4)
    (ht : D.tag j₁ = tY) (hrest : ∀ i, i ≠ j₁ → D.tag i = .PSL ∧ D.rank i = 2) :
    ∀ i, D.tag i = .trialityD4 → 4 ≤ p ^ D.exp i := by
  intro i hi
  exfalso
  by_cases hii : i = j₁
  · subst hii
    rw [ht] at hi
    exact hD4 hi
  · rw [(hrest i hii).1] at hi
    exact absurd hi (by decide)

section Main

variable [Finite G]

theorem exotic_modelTwinClass {K : Subgroup G} {z : G} (S : RouteDSetup p f K z) {a : ℕ}
    {tY : StatedLieTag} {nY : ℕ} (hnA1 : ¬ (tY = .PSL ∧ nY = 2)) (hG2 : tY ≠ .G2)
    (hD4 : tY ≠ .trialityD4) (h : LocalShapeT p f a tY nY (conjClass K) z) :
    ModelTwinClass p tY nY f a := by
  classical
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex : ExactMembers (conjClass K) := S.exact
  have hp2 : p ≠ 2 := S.odd
  have hq5 : 5 ≤ p ^ f := S.five
  have hq4 : 4 ≤ p ^ f := by omega
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
  have hsc₁ := fundamentalSingleClass_of_ne D i₁ (by rw [ht₁]; exact hG2) (by rw [ht₁]; exact hD4)
  have hperf₁ := D.fundPerfect hp2 hq4 (trialityD4_vacuous D hD4 ht₁ hrest) i₁
  have hnotall : ∃ L ∈ centralizingMembers (conjClass K) {z}, L ≠ M ∧ ¬ Commutes M L := by
    obtain ⟨RM, hRM⟩ := exists_corr_left hΩ hex D
      (⟨hMz, hMi⟩ : M ∈ compMembers (conjClass K) z D i₁)
    obtain ⟨S', hS', hSne, hScomm⟩ := exists_fund_not_commuting (D.isFundTag i₁)
      (D.admissible i₁) (by rw [ht₁, hr₁]; exact hnA1) hRM.2.1
    obtain ⟨L, hL⟩ := exists_corr_right hΩ D hsc₁ hS'
    refine ⟨L, hL.1, ?_, ?_⟩
    · intro hLM
      exact hSne (corr_unique_left hperf₁ (hLM ▸ hL) hRM)
    · intro hc
      exact hScomm ((corr_commutes hΩ hP1 hperf₁ hRM hL).mp hc).symm
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
  have htwinT : ∀ N ∈ conjClass K, ∀ i k : A,
      (N = T i ∨ Commutes N (T i)) ↔ (N = T k ∨ Commutes N (T k)) := fun N hN i k =>
    (hnbhd i N hN).trans (hnbhd k N hN).symm
  have hsc_x := fundamentalSingleClass_of_ne Dx j₁ (by rw [htx]; exact hG2)
    (by rw [htx]; exact hD4)
  have hperf_x := Dx.fundPerfect hp2 hq4 (trialityD4_vacuous Dx hD4 htx hrestx) j₁
  obtain ⟨F, hFmem, hFinj, hFcomm, hFtwin⟩ :=
    modelTwinClass_of_family hΩ hex hP1x Dx hsc_x hperf_x T hTx hTj hinjT hcommT htwinT
  have hexp : Dx.exp j₁ = f := by
    rcases Dx.exp_eq j₁ with h | ⟨h, -⟩
    · exact h
    · rw [htx] at h
      exact absurd h hD4
  let e : A ≃ Fin a := Fintype.equivFinOfCardEq hcardA
  refine modelTwinClass_congr htx hrx hexp ⟨fun k => F (e.symm k), fun k => hFmem _, ?_, ?_, ?_⟩
  · intro k l hkl
    exact e.symm.injective (hFinj hkl)
  · intro k l hkl
    exact hFcomm _ _ (fun h => hkl (e.symm.injective h))
  · intro k l S hS
    exact hFtwin _ _ S hS

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
