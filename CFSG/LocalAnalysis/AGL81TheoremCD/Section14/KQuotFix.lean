module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.KCapM
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34AutFix
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.L34Lift
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.Assembly.RankThreeEven (projSL)

variable {G : Type} [Group G] [Finite G]
variable {M E H : Subgroup G}

theorem HypCGen.conjQuotAction_eq_one_of_pow_eq_one
    (h : HypCGen G M 3 E H) (hC3 : CaseThree M H)
    (hK : KNormalAt M) (hL : PLayerNotLeAt M) {A : Subgroup G}
    (hA : CFSG.ABGLocalTools.IsSylowOf 3 A (kSub 3 M H))
    (hNA : Subgroup.normalizer (A : Set G) ⊓ kSub 3 M H ≤ M) {x : ↥H} (hxM : (x : G) ∈ M)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    (hxq : conjQuotAction H (kSub 3 M H) (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) (kSub_le 3 M H)
      (hK 3 E H h) x ^ q = 1) :
    conjQuotAction H (kSub 3 M H) (CFSG.pPrimeCore 3 ↥(kSub 3 M H)) (kSub_le 3 M H)
      (hK 3 E H h) x = 1 := by
  classical
  let K : Subgroup G := kSub 3 M H
  let N : Subgroup ↥K := CFSG.pPrimeCore 3 ↥K
  let π : ↥K →* (↥K ⧸ N) := QuotientGroup.mk' N
  let Abar : Subgroup (↥K ⧸ N) := (A.subgroupOf K).map π
  let α : MulAut (↥K ⧸ N) := conjQuotAction H K N (kSub_le 3 M H) (hK 3 E H h) x
  have hKquot : Nonempty ((↥K ⧸ N) ≃* projSL 3 (GaloisField 2 2)) := by
    simpa [K, N, threeStar] using HypCGen.nonempty_mulEquiv_threeStar hC3
  have hαE : Abar.map α.toMonoidHom = Abar := by
    simpa [Abar, α, K, N, π] using
      HypCGen.conjQuotAction_map_aStar_eq h hC3 hK hL hA hNA (x := x) hxM
  have hcardAbar : Nat.card Abar = 9 := by
    simpa [Abar, K, N, π] using card_map_pPrimeCore_quotient_of_isSylowOf hKquot hA
  have hαq : α ^ q = 1 := by
    simpa [α, K, N] using hxq
  obtain ⟨e⟩ := hKquot
  have hα1 : α = 1 :=
    eq_one_of_map_eq_of_pow_prime e hcardAbar hq hq5 hαE hαq
  simpa [α, K, N] using hα1

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
