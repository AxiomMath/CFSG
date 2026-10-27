module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.F3.Defs
public import CFSG.Blueprint.LieModelAPI
public import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitSchur
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.OddStandard.HigherRank.F3

open CFSG CFSG.ComponentClassification.HarrisLit
open scoped MatrixGroups

private lemma card_griessHopfMultiplier_of_subsingleton {Q : Type} [Group Q] [Subsingleton Q] :
    Nat.card (Open.griessHopfMultiplier Q) = 1 := by
  have hR : Open.griessHopfRelations Q = ⊤ := by
    show (FreeGroup.lift (id : Q → Q)).ker = ⊤
    exact MonoidHom.ker_eq_top_iff.mpr (MonoidHom.ext fun x => Subsingleton.elim _ _)
  have hB : (⁅(⊤ : Subgroup (FreeGroup Q)), Open.griessHopfRelations Q⁆).subgroupOf
      (Open.griessHopfRelations Q ⊓ commutator (FreeGroup Q)) = ⊤ := by
    rw [hR, top_inf_eq, ← _root_.commutator_def]
    exact Subgroup.subgroupOf_self (commutator (FreeGroup Q))
  have hsub : Subsingleton (Open.griessHopfMultiplier Q) := by
    show Subsingleton (↥(Open.griessHopfRelations Q ⊓ commutator (FreeGroup Q)) ⧸
      (⁅(⊤ : Subgroup (FreeGroup Q)), Open.griessHopfRelations Q⁆).subgroupOf
        (Open.griessHopfRelations Q ⊓ commutator (FreeGroup Q)))
    rw [hB]
    exact QuotientGroup.subsingleton_quotient_top
  exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩

private lemma pPrimeCore_le_fusionZStar (J : Type) [Group J] :
    pPrimeCore 2 J ≤ Open.fusionZStar J := by
  intro x hx
  rw [CFSG.ComponentClassification.GSThmB.OddQuot.mem_fusionZStar_iff]
  intro m
  haveI : (pPrimeCore 2 J).Normal := pPrimeCore_normal
  exact Subgroup.commutator_le_left (H₁ := pPrimeCore 2 J) (H₂ := ⊤)
    (Subgroup.commutator_mem_commutator hx (Subgroup.mem_top m))

private lemma false_of_slTwoThree {J : Type} [Group J]
    (hperf : commutator (J ⧸ Open.fusionZStar J) = ⊤) (hp : PartialCentre J)
    (hm2 : Nonempty (J ⧸ pPrimeCore 2 J ≃* SL(2, ZMod 3))) : False := by
  obtain ⟨e⟩ := hm2
  have hle := pPrimeCore_le_fusionZStar J
  have hmap : Function.Surjective (QuotientGroup.map (pPrimeCore 2 J) (Open.fusionZStar J)
      (MonoidHom.id J) (by simpa only [Subgroup.comap_id] using hle)) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Open.fusionZStar J) y
    exact ⟨QuotientGroup.mk' (pPrimeCore 2 J) x, by
      rw [QuotientGroup.map_mk']
      rfl⟩
  haveI : Group.IsSolvable SL(2, ZMod 3) := by
    refine CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      (p := 2) (q := 3) (a := 3) (b := 1) Nat.prime_two Nat.prime_three (by norm_num) ?_
    rw [← Nat.card_eq_fintype_card, card_specialLinearGroup_two_zmod_three]
    norm_num
  haveI : Group.IsSolvable (J ⧸ pPrimeCore 2 J) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  haveI : Group.IsSolvable (J ⧸ Open.fusionZStar J) :=
    Group.isSolvable_of_surjective hmap
  have hsub : Subsingleton (J ⧸ Open.fusionZStar J) := by
    by_contra h
    haveI : Nontrivial (J ⧸ Open.fusionZStar J) := not_subsingleton_iff_nontrivial.mp h
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (J ⧸ Open.fusionZStar J)
    rw [hperf] at hlt
    exact lt_irrefl _ hlt
  haveI := hsub
  have hcard := card_griessHopfMultiplier_of_subsingleton (Q := J ⧸ Open.fusionZStar J)
  unfold PartialCentre at hp
  rw [hcard] at hp
  have h0 : ordProj[2] (1 : ℕ) = 1 := by simp
  rw [h0] at hp
  have h1 : 1 ≤ ordProj[2] (Nat.card ↥(Open.fusionZStar J)) :=
    Nat.one_le_pow _ 2 (by norm_num)
  omega

theorem shape_of_partialCentre_of_E7 (hGr : CFSG.Open.GriessAllModelsStatement)
    (hE7 : ∀ (Q : Type) [Group Q], CFSG.Blueprint.LieModel Q .E7 0 3 1 →
      CFSG.Models.LieModel Q .E7 0 3 1)
    {J : Type} [Group J] [Finite J] (hs : ClassBShape J) (hp : PartialCentre J)
    (hm : IsMTypeSchur 3 J) :
    ∃ n : ℕ, (n = 4 ∨ n = 6) ∧
      CFSG.Blueprint.LieModel (J ⧸ Open.fusionZStar J) .POmegaPlus n 3 1 := by
  obtain ⟨τ, n, hLie, hshape⟩ := hs
  have hMod : CFSG.Models.LieModel (J ⧸ Open.fusionZStar J) τ n 3 1 := by
    by_cases ht : τ ∈ CFSG.Blueprint.classicalTags
    · exact CFSG.Models.LieModel.of_blueprint ht hLie
    · have hτ : τ = .E7 := by
        rcases hshape with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
        · exact absurd (h ▸ ht) (by decide)
        · exact absurd (h ▸ ht) (by decide)
        · exact absurd (h ▸ ht) (by decide)
        · exact absurd (h ▸ ht) (by decide)
        · exact h
      subst hτ
      obtain ⟨hn0, -⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff
        (t := .E7) (by decide)).mp hLie
      subst hn0
      exact hE7 (J ⧸ Open.fusionZStar J) hLie
  obtain ⟨hperf, -⟩ := hGr (J ⧸ Open.fusionZStar J) τ n 3 1 hMod
  have heven : Even (Nat.card ↥(Open.fusionZStar J)) := by
    rcases hm with h1 | h2
    · exact h1.2.2.1
    · exact (false_of_slTwoThree hperf hp h2.2).elim
  have hclause : ∀ n r : ℕ, 0 < n → 0 < r →
      (CFSG.Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSL (2 * n) 3 r ∨
        CFSG.Blueprint.LieModel (J ⧸ Open.fusionZStar J) .PSU (2 * n) 3 r) →
      ordProj[2] (Nat.card ↥(Open.fusionZStar J)) =
        ordProj[2] (Nat.card (Open.griessHopfMultiplier (J ⧸ Open.fusionZStar J))) := by
    rcases hm with h1 | h2
    · exact h1.2.2.2
    · exact (false_of_slTwoThree hperf hp h2.2).elim
  have hZpos : Nat.card ↥(Open.fusionZStar J) ≠ 0 :=
    (Finite.card_pos_iff.mpr ⟨1, one_mem _⟩).ne'
  have hZfac : 1 ≤ (Nat.card ↥(Open.fusionZStar J)).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hZpos).mp (even_iff_two_dvd.mp heven)
  have hZ2 : 2 ≤ ordProj[2] (Nat.card ↥(Open.fusionZStar J)) := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hZfac
    simpa using h
  rcases hshape with hPSL | hPSU | hPSp | hPO | hE7row
  · obtain ⟨rfl, hn⟩ := hPSL
    rcases hn with rfl | rfl
    · exfalso
      exact (ne_of_lt hp) (hclause 2 1 (by norm_num) (by norm_num)
        (Or.inl (by simpa using hLie)))
    · exfalso
      exact (ne_of_lt hp) (hclause 3 1 (by norm_num) (by norm_num)
        (Or.inl (by simpa using hLie)))
  · obtain ⟨rfl, hn⟩ := hPSU
    rcases hn with rfl | rfl
    · exfalso
      exact (ne_of_lt hp) (hclause 2 1 (by norm_num) (by norm_num)
        (Or.inr (by simpa using hLie)))
    · exfalso
      exact (ne_of_lt hp) (hclause 3 1 (by norm_num) (by norm_num)
        (Or.inr (by simpa using hLie)))
  · obtain ⟨rfl, -⟩ := hPSp
    have hval : Nat.card (Open.griessHopfMultiplier (J ⧸ Open.fusionZStar J)) = 2 := by
      rw [card_griessHopfMultiplier_eq hGr hMod]
      have hg : CFSG.Blueprint.Multiplier.genericOrders .PSp n 3 1 = (2, 1) := by
        show (Nat.gcd 2 (3 ^ 1 - 1), 1) = (2, 1)
        norm_num
      have he : CFSG.Blueprint.Multiplier.exceptionalOrders .PSp n 3 1 = (1, 1) := by
        unfold CFSG.Blueprint.Multiplier.exceptionalOrders
        split <;> first | rfl | omega | (simp_all)
      rw [hg, he]
      norm_num
    have hlt : ordProj[2] (Nat.card ↥(Open.fusionZStar J)) < 2 := by
      have h2 : ordProj[2] (Nat.card (Open.griessHopfMultiplier
          (J ⧸ Open.fusionZStar J))) = 2 := by rw [hval]; norm_num
      have hp' := hp
      unfold PartialCentre at hp'
      rwa [h2] at hp'
    omega
  · obtain ⟨rfl, hn⟩ := hPO
    exact ⟨n, hn, hLie⟩
  · subst hE7row
    have hval : Nat.card (Open.griessHopfMultiplier (J ⧸ Open.fusionZStar J)) = 2 := by
      rw [card_griessHopfMultiplier_eq hGr hMod]
      have hg : CFSG.Blueprint.Multiplier.genericOrders .E7 n 3 1 = (2, 1) := by
        show (Nat.gcd 2 (3 ^ 1 - 1), 1) = (2, 1)
        norm_num
      have he : CFSG.Blueprint.Multiplier.exceptionalOrders .E7 n 3 1 = (1, 1) := rfl
      rw [hg, he]
      norm_num
    have hlt : ordProj[2] (Nat.card ↥(Open.fusionZStar J)) < 2 := by
      have h2 : ordProj[2] (Nat.card (Open.griessHopfMultiplier
          (J ⧸ Open.fusionZStar J))) = 2 := by rw [hval]; norm_num
      have hp' := hp
      unfold PartialCentre at hp'
      rwa [h2] at hp'
    omega

end CFSG.OddStandard.HigherRank.F3
