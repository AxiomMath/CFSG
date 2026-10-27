module

public import CFSG.ClassicalInvolution.Q3.Q3WAM11

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD.Exotic


variable {G : Type} [Group G] {ι : Type}

noncomputable def transport3 {X X' : Type} [Group X] [Group X'] {Φ : Set (Subgroup X)}
    (e : X ≃* X') (D : LieSystemData3 ι X Φ) :
    LieSystemData3 ι X' (Subgroup.map e.toMonoidHom '' Φ) where
  kind := D.kind
  valid := D.valid
  hom i := e.toMonoidHom.comp (D.hom i)
  ker_le_center i := by
    intro x hx
    have h1 : D.hom i x = 1 := by
      have h2 : e (D.hom i x) = 1 := hx
      simpa using h2
    exact D.ker_le_center i (by simpa using h1)
  commute i j h x y := by
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← map_mul]
    rw [D.commute i j h x y]
  generate := by
    have h1 : ∀ i, (e.toMonoidHom.comp (D.hom i)).range = (D.hom i).range.map e.toMonoidHom :=
      fun i => MonoidHom.range_comp _ _
    simp only [h1]
    rw [← Subgroup.map_iSup, D.generate, Subgroup.map_top]
    exact MonoidHom.range_eq_top.mpr e.surjective
  fundamental := by
    rintro _ ⟨L, hL, rfl⟩
    obtain ⟨i, R, hR, rfl⟩ := D.fundamental L hL
    exact ⟨i, R, hR, Subgroup.map_map _ _ _⟩
  meets i := by
    obtain ⟨R, hR, hmem⟩ := D.meets i
    exact ⟨R, hR, ⟨_, hmem, Subgroup.map_map _ _ _⟩⟩
  card_eq := by
    rintro _ ⟨L, hL, rfl⟩
    rw [← D.card_eq L hL]
    exact Nat.card_congr (L.equivMapOfInjective e.toMonoidHom e.injective).toEquiv.symm

theorem exists_lieSystemData3_of_image_eq {X X' : Type} [Group X] [Group X'] (e : X ≃* X')
    {Φ : Set (Subgroup X)} {Φ' : Set (Subgroup X')}
    (h : Subgroup.map e.toMonoidHom '' Φ = Φ') (D : LieSystemData3 ι X Φ) :
    ∃ D' : LieSystemData3 ι X' Φ', D'.kind = D.kind := by
  subst h
  exact ⟨transport3 e D, rfl⟩

theorem exists_lieSystemData3_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) (g x : G)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) :
    ∃ D' : LieSystemData3 ι (locQuot Ω (g * x * g⁻¹)) (locFamily Ω (g * x * g⁻¹)),
      D'.kind = D.kind :=
  exists_lieSystemData3_of_image_eq (Gaps.locQuotConj hΩ g x) (Gaps.locFamily_conj hΩ g x) D

theorem twinFamily_of_family3 [Finite G] {ι' : Type} {Ω : Set (Subgroup G)} {x : G}
    (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω) (hP1 : LocalOddCentral Ω {x})
    (hO3 : LocalOddThreeFree3 Ω x) (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {j : ι}
    (hsc : ∀ R ∈ (D.kind j).fund, ∀ R' ∈ (D.kind j).fund, ∃ g, R' = conjSub g R)
    (hk : PowCop3 (D.kind j)) (T : ι' → Subgroup G) (hTx : ∀ k, T k ∈ compMembers3 Ω x D j)
    (hinj : Function.Injective T) (hcomm : ∀ k l, k ≠ l → Commutes (T k) (T l))
    (htwin : ∀ N ∈ Ω, ∀ k l, (N = T k ∨ Commutes N (T k)) ↔ (N = T l ∨ Commutes N (T l))) :
    ∃ F : ι' → Subgroup (D.kind j).G, (∀ k, F k ∈ (D.kind j).fund) ∧ Function.Injective F ∧
      (∀ k l, k ≠ l → Commutes (F k) (F l)) ∧
      ∀ k l, ∀ S ∈ (D.kind j).fund,
        (S = F k ∨ Commutes S (F k)) ↔ (S = F l ∨ Commutes S (F l)) := by
  choose R hR using fun k => exists_corr_left3 hΩ hex hP1 hO3 D (hTx k)
  refine ⟨R, fun k => (hR k).2.1, ?_, ?_, ?_⟩
  · intro k l hkl
    exact hinj (corr_unique_right3 hΩ hex hP1 hO3 (hR k) (hkl ▸ hR l))
  · intro k l hkl
    exact (corr_commutes3 hΩ hex hP1 hO3 hk (hR k) (hR l)).mp (hcomm k l hkl)
  · intro k l S hS
    obtain ⟨N, hN⟩ := exists_corr_right3 hΩ D hsc hS
    have key : ∀ m, (S = R m ∨ Commutes S (R m)) ↔ (N = T m ∨ Commutes N (T m)) := by
      intro m
      constructor
      · rintro (h | h)
        · left
          exact corr_unique_right3 hΩ hex hP1 hO3 (h ▸ hN) (hR m)
        · right
          exact (corr_commutes3 hΩ hex hP1 hO3 hk hN (hR m)).mpr h
      · rintro (h | h)
        · left
          exact corr_unique_left3 hk (h ▸ hN) (hR m)
        · right
          exact (corr_commutes3 hΩ hex hP1 hO3 hk hN (hR m)).mp h
    rw [key k, key l]
    exact htwin N hN.1.1 k l

theorem modelTwinClass_of_compData {t : StatedLieTag} {n a : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (F : Fin a → Subgroup c.G) (hF : ∀ k, F k ∈ c.fund)
    (hinj : Function.Injective F) (hcomm : ∀ k l, k ≠ l → Commutes (F k) (F l))
    (htwin : ∀ k l, ∀ S ∈ c.fund, (S = F k ∨ Commutes S (F k)) ↔ (S = F l ∨ Commutes S (F l))) :
    ModelTwinClass 3 t n 1 a := by
  subst hc
  exact ⟨F, hF, hinj, hcomm, htwin⟩

theorem exists_fund_not_commuting_of_kind {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hnA1 : ¬ (t = .PSL ∧ n = 2)) {R : Subgroup c.G} (hR : R ∈ c.fund) :
    ∃ S ∈ c.fund, S ≠ R ∧ ¬ Commutes S R := by
  subst hc
  exact exists_fund_not_commuting (p := 3) (e := 1) hfund hadm hnA1 hR

theorem singleClass_of_kind {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) :
    ∀ R ∈ c.fund, ∀ R' ∈ c.fund, ∃ g, R' = conjSub g R := by
  subst hc
  exact CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass t n 3 1 Nat.prime_three hfund
    hadm hG2 hD4

theorem powCop3_of_kind {t : StatedLieTag} {n : ℕ} {c : CompData}
    (hc : c = CompData.model t n) (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) : PowCop3 c := by
  subst hc
  exact powCop3_model hfund hadm hG2 hD4

theorem exotic_modelTwinClass3 [Finite G] {K : Subgroup G} {z : G} (h : RouteD3Setup K z)
    (h3 : LocalOddThreeFree3 (conjClass3 K) z) {a : ℕ} {t : StatedLieTag} {n : ℕ}
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n 3 1) (hG2 : t ≠ .G2)
    (hD4 : t ≠ .trialityD4) (hshape : LocalShapeC3 a (CompData.model t n) (conjClass3 K) z) :
    ModelTwinClass 3 t n 1 a := by
  classical
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.inClass
  obtain ⟨hex, hP1⟩ := h.setup
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hnA1 := not_psl_two_of_admissible3 hadm
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := hshape
  have := Fintype.ofFinite ι
  let A := {i : ι // i ≠ i₁}
  have hcardA : Fintype.card A = a := by
    have h1 : Fintype.card A = Fintype.card ι - 1 := by
      simp [A, Fintype.card_subtype_compl]
    rw [h1, ← Nat.card_eq_fintype_card, hcard]
    rfl
  choose T hT using fun i : A => exists_mem_compMembers3 (D := D) i.1
  have hTz : ∀ i : A, T i ∈ centralizingMembers (conjClass3 K) {z} := fun i => (hT i).1
  have hTΩ : ∀ i : A, T i ∈ conjClass3 K := fun i => (hT i).1.1
  have hu : ∀ i : A, Universal3 (conjClass3 K) z (T i) := fun i =>
    universal3_of_a1comp hΩ hex hP1 h3 D (hrest i.1 i.2) (hT i)
  choose w hw using fun i : A => hΩ.classical (T i) (hTΩ i)
  have hΩw : ∀ i : A, centralizingMembers (conjClass3 K) {w i} =
      centralizingMembers (conjClass3 K) {z} := fun i =>
    centralizingMembers_eq_of_twin3 hΩ h.cls (hw i) (exists_conj_of_mem3 hKΩ (hTΩ i)) (hTz i)
      (hu i)
  have hnbhd : ∀ i : A, ∀ N ∈ conjClass3 K,
      (N = T i ∨ Commutes N (T i)) ↔ N ∈ centralizingMembers (conjClass3 K) {z} := by
    intro i N hN
    constructor
    · rintro (rfl | hc)
      · exact hTz i
      · rw [← hΩw i]
        exact mem_centralizingMembers_of_commutes hN (hw i).mem hc
    · intro hNz
      by_cases hNT : N = T i
      · exact Or.inl hNT
      · exact Or.inr (hu i N hNz hNT).symm
  obtain ⟨M, hM⟩ := exists_mem_compMembers3 (D := D) i₁
  have hMz : M ∈ centralizingMembers (conjClass3 K) {z} := hM.1
  have hMT : ∀ i : A, M ≠ T i := by
    intro i hMi
    obtain ⟨j, -, hj⟩ := exists_unique_comp3 hΩ hex hP1 h3 D hMz
    exact i.2 ((hj i.1 (hMi ▸ hT i)).trans (hj i₁ hM).symm)
  have hcommM : ∀ i : A, Commutes (T i) M := fun i => hu i M hMz (hMT i)
  have hsc := singleClass_of_kind hk hfund hadm hG2 hD4
  have hpc := powCop3_of_kind hk hfund hadm hG2 hD4
  have hnotall : ∃ L ∈ centralizingMembers (conjClass3 K) {z}, L ≠ M ∧ ¬ Commutes M L := by
    obtain ⟨RM, hRM⟩ := exists_corr_left3 hΩ hex hP1 h3 D hM
    obtain ⟨S', hS', hSne, hScomm⟩ :=
      exists_fund_not_commuting_of_kind hk hfund hadm hnA1 hRM.2.1
    obtain ⟨L, hL⟩ := exists_corr_right3 hΩ D hsc hS'
    refine ⟨L, hL.1, ?_, ?_⟩
    · intro hLM
      exact hSne (corr_unique_left3 hpc (hLM ▸ hL) hRM)
    · intro hc
      exact hScomm ((corr_commutes3 hΩ hex hP1 h3 hpc hRM hL).mp hc).symm
  obtain ⟨g, hg⟩ := single_class3 K M hMz.1
  have hzx : IsClassicalMember3 M (g * z * g⁻¹) := by
    rw [hg]
    exact h.cls.conj g
  have hP1x : LocalOddCentral (conjClass3 K) {g * z * g⁻¹} :=
    RouteD.Gaps.localOddCentral_conj hΩ.conjInvariant g z hP1
  have hO3x : LocalOddThreeFree3 (conjClass3 K) (g * z * g⁻¹) :=
    localOddThreeFree3_conj hΩ.conjInvariant g z h3
  have hncard : (centralizingMembers (conjClass3 K) {g * z * g⁻¹}).ncard =
      (centralizingMembers (conjClass3 K) {z}).ncard :=
    ncard_centralizingMembers_conj hΩ.conjInvariant g z
  obtain ⟨Dx, hDx⟩ := exists_lieSystemData3_conj hΩ.conjInvariant g z D
  generalize g * z * g⁻¹ = x at hzx hP1x hO3x hncard Dx hDx
  have hTx : ∀ i : A, T i ∈ centralizingMembers (conjClass3 K) {x} := fun i =>
    mem_centralizingMembers_of_commutes (hTΩ i) hzx.mem (hcommM i)
  have hMx : M ∈ centralizingMembers (conjClass3 K) {x} :=
    ⟨hMz.1, isSubnormal_le hzx.subnormal⟩
  have hkx : Dx.kind i₁ = CompData.model t n := by rw [hDx]; exact hk
  have hTj : ∀ i : A, T i ∈ compMembers3 (conjClass3 K) x Dx i₁ := by
    intro i
    obtain ⟨j, hj⟩ := exists_range_of_mem3 Dx (mem_locFamily_iff.mpr ⟨T i, hTx i, rfl⟩)
    by_cases hjj : j = i₁
    · subst hjj
      exact ⟨hTx i, hj⟩
    · exfalso
      have hA1x : IsA1Comp3 Dx j := by
        unfold IsA1Comp3
        rw [hDx]
        exact hrest j hjj
      have huT := universal3_of_a1comp hΩ hex hP1x hO3x Dx hA1x ⟨hTx i, hj⟩
      have hsub : centralizingMembers (conjClass3 K) {x} ⊆
          centralizingMembers (conjClass3 K) {z} := by
        intro L hL
        by_cases hLT : L = T i
        · exact hLT ▸ hTz i
        · exact (hnbhd i L hL.1).mp (Or.inr (huT L hL hLT).symm)
      have heq : centralizingMembers (conjClass3 K) {x} =
          centralizingMembers (conjClass3 K) {z} :=
        Set.eq_of_subset_of_ncard_le hsub hncard.ge (Set.toFinite _)
      obtain ⟨L, hLz, hLM, hLnc⟩ := hnotall
      have hLx : L ∈ centralizingMembers (conjClass3 K) {x} := by
        rw [heq]
        exact hLz
      rcases commutes_or_eq_of_involution3 hMFZ hΩ hex hP1x hO3x Dx hMx hLx hzx with hc | hLM'
      · exact hLnc hc
      · exact hLM hLM'
  have hinjT : Function.Injective T := by
    intro i k hik
    refine Subtype.ext (eq_of_locImg_le_range3 hΩ hex hP1 h3 D (hTz i) (hT i).2 ?_)
    rw [hik]
    exact (hT k).2
  have hcommT : ∀ i k : A, i ≠ k → Commutes (T i) (T k) := fun i k hik =>
    hu i (T k) (hTz k) (fun h' => hik (hinjT h'.symm))
  have htwinT : ∀ N ∈ conjClass3 K, ∀ i k : A,
      (N = T i ∨ Commutes N (T i)) ↔ (N = T k ∨ Commutes N (T k)) := fun N hN i k =>
    (hnbhd i N hN).trans (hnbhd k N hN).symm
  obtain ⟨F, hFmem, hFinj, hFcomm, hFtwin⟩ := twinFamily_of_family3 hΩ hex hP1x hO3x Dx
    (singleClass_of_kind hkx hfund hadm hG2 hD4) (powCop3_of_kind hkx hfund hadm hG2 hD4) T hTj
    hinjT hcommT htwinT
  let e : A ≃ Fin a := Fintype.equivFinOfCardEq hcardA
  refine modelTwinClass_of_compData hkx (fun k => F (e.symm k)) (fun k => hFmem _) ?_ ?_ ?_
  · intro k l hkl
    exact e.symm.injective (hFinj hkl)
  · intro k l hkl
    exact hFcomm _ _ (fun h' => hkl (e.symm.injective h'))
  · intro k l S hS
    exact hFtwin _ _ S hS

end CFSG.ClassicalInvolution.Q3.Q3W.EX
