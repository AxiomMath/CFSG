module

public import CFSG.ClassicalInvolution.Asc77.WP3SCSLift

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem mem_modOdd_of_commutes_gen (hΩ : ConjInvariant Ω) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hcB : c ∈ B) (hc1 : c ≠ 1) {e : G} (heB : e ∈ B) (he1 : e ≠ 1)
    (hec : e ≠ c) {q : OddQuot c} (hq : q ∈ memberJoin (exactFamily Ω c) c)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({c} : Set G),
      oddQuotMk c ⟨e, he⟩ * q = q * oddQuotMk c ⟨e, he⟩) :
    q ∈ modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c)) := by
  have hBC : B ≤ Subgroup.centralizer ({c} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hcB
  have hcB' : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => comm_of_mem_elemAbelian hB hx hy
  have hsqB : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← pow_two]; exact hB.2 x hx
  have hesq : e * e = 1 := hsqB e heB
  have hze : c * e = e * c := hcB' c hcB e heB
  have hcC : c ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set F : Subgroup G := Subgroup.closure ({c, e} : Set G) with hF
  have hFB : F ≤ B := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hcB
    · exact heB
  have hcard : Nat.card F = 4 :=
    card_closure_pair_eq_four (hsqB c hcB) hesq hc1 he1 (fun h => hec h.symm) hze
  have hFE : F ∈ signalizerFunctorEk 2 2 B := ⟨hFB, by rw [hcard]; norm_num⟩
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => hsqB x (hFB hx)
  have hFC : F ≤ Subgroup.centralizer ({c} : Set G) := hFB.trans hBC
  have hFN : F ≤ Subgroup.normalizer ((exactLayer Ω c : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_exactLayer hΩ (hFC hx)
  have hcent : ∀ (x : G) (_ : x ∈ F) (hC : x ∈ Subgroup.centralizer ({c} : Set G)),
      oddQuotMk c ⟨x, hC⟩ * q = q * oddQuotMk c ⟨x, hC⟩ := by
    refine ChainFrame.commutes_of_closure (oddQuotMk c) q (S := ({c, e} : Set G)) ?_ ?_
    · rintro s (rfl | rfl)
      · exact hcC
      · exact hBC heB
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central hcC q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ :=
    exists_lift_centralizer_of_normalizes (a := c) hF2 hFC hFN hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c) ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c) :=
    le_iSup₂ (f := fun F (_ : F ∈ signalizerFunctorEk 2 2 B) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

theorem exists_comp_of_mem (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) {N : Subgroup G} (hN : N ∈ tqMembers Ω c) :
    ∃ j : Fin D.card, modOdd c (exactCore c N) ≤
      (secComponentHom hs.normalizes D j).range := by
  have hM : exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hMY : exactCore c N ≤ centralizingLayer (exactFamily Ω c) {c} := le_centralizingLayer hM
  have hMfam : modOddIn (centralizingLayer (exactFamily Ω c) {c}) (exactCore c N) ∈
      localFamily (exactFamily Ω c) c := ⟨(exactCore c N).subgroupOf _, ⟨_, hM, hMY, rfl⟩, rfl⟩
  obtain ⟨i, R, hR, hMR⟩ := D.fundamental _ hMfam
  refine ⟨i, ?_⟩
  have h1 : (R.map (D.hom i)).map (sectionQuotientHom hs.normalizes) =
      R.map (secComponentHom hs.normalizes D i) := Subgroup.map_map _ _ _
  have h2 : modOdd c (exactCore c N) = R.map (secComponentHom hs.normalizes D i) := by
    rw [← h1, ← hMR]
    exact (map_sectionQuotientHom_modOddIn hs.normalizes hM).symm
  rw [h2]
  rintro _ ⟨r, -, rfl⟩
  exact ⟨r, rfl⟩

theorem centralizerGenerationStar_of_components (hs : SecData p f c (exactFamily Ω c))
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) {B : Subgroup G}
    (hcomp : ∀ (j : Fin D.card) (k : (compModel D j).K),
      secComponentHom hs.normalizes D j k ∈ modOdd c (⨆ F ∈ signalizerFunctorEk 2 2 B,
        (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω c))) :
    CentralizerGenerationStar Ω B c := by
  refine centralizerGenerationStar_of_images hs.normalizes fun N hN y hy hyC => ?_
  obtain ⟨j, hj⟩ := exists_comp_of_mem hs D hN
  obtain ⟨k, hk⟩ := hj (oddQuotMk_mem_modOdd hy hyC)
  rw [← hk]
  exact hcomp j k

end Gen

end CFSG.ClassicalInvolution.Asc77
