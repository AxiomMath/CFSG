module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeCz
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeLift
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeScalar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroThreeSplit

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M H R : Subgroup G}
  {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}

theorem D1OneSmallData.oddCore_of_scalar_cz (hβ : KFactBeta) (hSch : KFactCatalogSchreier)
    (hKS : KFactSPLInvolveScalar) (hd : D1OneSmallData 3 P M H R Rbar K)
    (hspl : IsSPLFamily 3 K) {z : G} (hz : D1SmallCZElt 3 H R K z) (hSP : D1CzSP 3 z)
    (hout : D1CzOutside 3 z) (s : ℕ) (hs : s.Prime) (hs2 : s ≠ 2) (hs3 : s ≠ 3) :
    barM M (d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G)) ≤
        Subgroup.centralizer
          ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
            Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ CFSG.Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨A, hAM, hAel, hZA, c, hcM, hcN, m, lam, hm, hlam, hscal, horb⟩ :=
    D1OneSmallData.exists_scalar_cz hβ hSch hKS hd hspl hz hSP hout
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  by_cases hns : barM M (d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G)) ≤
      Subgroup.centralizer (Sg : Set (↥M ⧸ CFSG.pCore 2 ↥M))
  · exact Or.inl hns
  right
  have := Fact.mk hs
  set mkM := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmkM
  set AM : Subgroup M := A.subgroupOf M with hAMdef
  have hAMmap : AM.map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAM
  have hcAM : (⟨c, hcM⟩ : M) ∈ Subgroup.normalizer (AM : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.mp hcN (y : G)
  obtain ⟨hscal₁, horb₁⟩ := scalar_pull M.subtype hAMmap
    (fun a _ h => M.subtype_injective (h.trans (map_one _).symm)) hcAM
    (t₂ := c) (fun k a _ => by simp) hscal horb
  have hcop2 : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥M)) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hk]
    exact ((Nat.coprime_primes hp Nat.prime_two).mpr (by decide)).pow_right k
  have hinj : ∀ a ∈ AM, mkM a = 1 → a = 1 := by
    intro a ha h1
    have hap : IsPGroup 3 AM := fun x =>
      ⟨1, Subtype.ext (Subtype.ext (by simpa using hAel.2 ((x : M) : G) x.2))⟩
    obtain ⟨k, hk⟩ := hap ⟨a, ha⟩
    exact eq_one_of_mk_eq_one_of_coprime (CFSG.pCore 2 ↥M) hcop2 (k := k)
      (by simpa using congrArg Subtype.val hk) h1
  obtain ⟨hscal₂, horb₂⟩ := scalar_push mkM (A₂ := barM M A) rfl hinj hcAM
    (t₂ := mkM ⟨c, hcM⟩) (fun k a _ => by simp only [map_mul, map_inv, map_pow]) hscal₁ horb₁
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hZAbar : barM M (d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G)) ≤
      barM M A := barM_mono hZA
  have hrank : 4 ≤ CFSG.Open.pRank s Sg :=
    stmtOddCoreRankScalarGen hs hs2 hp hs3 Sg (barM M A) (mkM ⟨c, hcM⟩) m lam hm
      CFSG.pCore_isPGroup (le_top.trans hSgN) (isElemAbelian_map_of_isElemAbelian mkM (A₁ := AM)
        (isElemAbelian_of_map_injOn M.subtype
          (fun a _ h => M.subtype_injective (h.trans (map_one _).symm)) (hAMmap ▸ hAel)))
      (hSgN (Subgroup.mem_top _)) (Subgroup.le_normalizer_map mkM ⟨_, hcAM, rfl⟩) hlam hscal₂
      horb₂ fun h => hns (hZAbar.trans h)
  have h1 := pRank_barM_le hs hs2 M
    ((Sg.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) (Subgroup.map_subtype_le _)
  rw [barM_preimage] at h1
  exact hrank.trans h1

theorem D1OneSmallData.center_d1LiftX_ne_bot (hd : D1OneSmallData 3 P M H R Rbar K) :
    d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := d1LiftX 3 H R K
  have hXp : IsPGroup 3 X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le 3 H R K)
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hd.d1LiftX_ne_bot
  have := hXp.center_nontrivial
  obtain ⟨w, hw⟩ := exists_ne (1 : Subgroup.center X)
  intro hbot
  have hwZ : ((w : X) : G) ∈ X ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨(w : X).2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp w.2 ⟨y, hy⟩)⟩
  rw [hbot, Subgroup.mem_bot] at hwZ
  exact hw (Subtype.ext (Subtype.ext (by simpa using hwZ)))

theorem d1SmallSPLZeroIbThreeCore_of_comps (hβ : KFactBeta) (hSch : KFactCatalogSchreier)
    (hKS : KFactSPLInvolveScalar) (hC : D1SmallSPLZeroIbThreeComps) :
    D1SmallSPLZeroIbThreeCore := by
  intro G _ _ P M H R Rbar K hd huniq z hz hspl hSP hout hV hnIa hOp hXL
  exact ⟨d1LiftX 3 H R K ⊓ Subgroup.centralizer (d1LiftX 3 H R K : Set G), inf_le_left,
    D1OneSmallData.center_d1LiftX_ne_bot hd,
    hC G P M H R Rbar K hd huniq z hz hspl hSP hout hV hnIa hOp hXL,
    fun s hs hs2 hs3 => D1OneSmallData.oddCore_of_scalar_cz hβ hSch hKS hd hspl hz hSP hout s
      hs hs2 hs3⟩

end CFSG.AGLEmbedding
