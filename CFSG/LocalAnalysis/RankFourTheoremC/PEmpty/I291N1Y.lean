module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Comp
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291N1Defs
public import CFSG.Quasithin.Vol2.Ch12Sec8OneSix

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291

open CFSG CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.K62B
open CFSG.LocalAnalysis.RankFourTheoremC (IsLinearOrUnitaryAt)
open CFSG.AGLEmbedding (CatalogSimpleSections)

theorem two_le_pRank_three_of_surjective {A Q : Type} [Group A] [Finite A] [Group Q] [Finite Q]
    (f : A →* Q) (hf : Function.Surjective f) (h : 2 ≤ Open.pRank 3 (⊤ : Subgroup Q)) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup A) :=
  CFSG.Quasithin.H13.L128P.two_le_pRank_of_surjective' Nat.prime_three (by norm_num) f hf h

@[expose] def LinUniE9 (p : ℕ) : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsLinearOrUnitaryAt p S → (∃ a b : S, a * b ≠ b * a) →
    2 ≤ Open.pRank 3 (⊤ : Subgroup S)

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x z : Y} {L : Subgroup Y}

theorem two_le_pRank_three_of_single (hMult : KDMultP5) (hEx : KDR3Exclusion) (hE9 : LinUniE9 p)
    (hcfg : Cfg p P x z) (h4 : 4 ≤ Open.pRank p (⊤ : Subgroup Y))
    (hx : Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    (hL : IsComponentOf L ⊤) (hLu : ∀ K : Subgroup Y, IsComponentOf K ⊤ → K = L) :
    2 ≤ Open.pRank 3 (⊤ : Subgroup Y) := by
  have hprime := hcfg.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  have hp5 := hcfg.five_le
  have hLn : L.Normal := normal_of_unique hL hLu
  have hcat : CatalogSimpleSections Y := hcfg.catalog
  have hcore := hcfg.core
  have hq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hcatQ : IsCatalogGroup (↥L ⧸ center ↥L) := hcat.isCatalogGroup_center_quotient hL
  have hLY : 2 ≤ Open.pRank 3 (⊤ : Subgroup ↥L) → 2 ≤ Open.pRank 3 (⊤ : Subgroup Y) := fun h =>
    h.trans (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) L.subtype
      L.subtype_injective)
  by_cases hlu : IsLinearOrUnitaryAt p (↥L ⧸ center ↥L)
  · obtain ⟨a, b, hab⟩ :=
      ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian ↥L hq
    exact hLY (two_le_pRank_three_of_surjective (QuotientGroup.mk' (center ↥L))
      (QuotientGroup.mk'_surjective _) (hE9 _ hlu ⟨a, b, hab⟩))
  · have hZ : center ↥L = ⊥ := by
      by_contra hZne
      exact hlu (hMult p hprime hp5 ↥L hq hcatQ hZne (isPGroup_center hcore hL))
    obtain ⟨hsimp, hnonab, -⟩ := hcat.isSimpleGroup_of_center_eq_bot hL hZ
    have hpc := pCore_eq_bot hcfg hL hLn hZ
    have hC := centralizer_eq_bot hcore hpc hL hLu hZ
    by_cases h3 : 2 ≤ Open.pRank 3 L
    · exact h3.trans (CFSG.SectionRank.pRank_mono (by norm_num) le_top)
    · exfalso
      have hx1 : x ≠ 1 := by
        rintro rfl
        have h1 : centralizer ({(1 : Y)} : Set Y) = ⊤ := by simp
        rw [h1] at hx
        omega
      have hxord : orderOf x = p := orderOf_eq_prime hcfg.x_pow hx1
      obtain ⟨N, hNn, hNidx⟩ := hEx p hprime hp5 Y hcat hcore L hLn hsimp hnonab hC
        (by omega) h4 ⟨x, hxord, hx⟩
      haveI := hNn
      have hN : N = ⊤ := hperf N (IsPGroup.of_card (n := 1) (by
        rw [pow_one, ← hNidx, Subgroup.index_eq_card]))
      rw [hN, Subgroup.index_top] at hNidx
      exact hprime.one_lt.ne hNidx

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291
