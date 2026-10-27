module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFifteenOne

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def FourteenFiveThreeAt (M : Subgroup G) : Prop :=
  PreambleTypes M → KNormalAt M → NineNineOneAt M → PLayerNotLeAt M →
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → ¬ TypeA M H → TypeB M H →
    ∀ p ∈ sigmaSet G M, ∀ A : Subgroup G, A ≤ Q → Nat.card A = 3 →
      2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) →
      (Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
        Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
        Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11))) →
      CFSG.HallHigman.IsPSolvable 3 ↥(kSub 3 M H ⊓ Subgroup.centralizer (A : Set G))

theorem FourteenFiveThreeAt.pRank_le_one {M H E Q J : Subgroup G}
    (h1453 : FourteenFiveThreeAt M) (hpre : PreambleTypes M) (hK : KNormalAt M)
    (hU : NineNineOneAt M) (hL : PLayerNotLeAt M) (h : S14Choice G M H E Q J) (hA : ¬ TypeA M H)
    (hB : TypeB M H) {p : ℕ} (hp : p ∈ sigmaSet G M) {A : Subgroup G} (hAQ : A ≤ Q)
    (hA3 : Nat.card A = 3)
    (hMbar : Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 9)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* alternatingGroup (Fin 11)) ∨
      Nonempty (↥M ⧸ CFSG.pPrimeCore 3 ↥M ≃* Equiv.Perm (Fin 11)))
    (hns : ¬ CFSG.HallHigman.IsPSolvable 3 ↥(kSub 3 M H ⊓ Subgroup.centralizer (A : Set G))) :
    CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (A : Set G)) ≤ 1 := by
  by_contra hle
  exact hns (h1453 hpre hK hU hL H E Q J h hA hB p hp A hAQ hA3 (by omega) hMbar)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
