module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineElevenGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneComp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneLayer
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenKStar
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveOneSection

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isTwoPrimeComponentIn_of_not_autSection {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {M H L : Subgroup G} (hL : ¬ pLayerIn p H ≤ M) (hLK : IsPComponentIn p L (kSub p M H))
    (hK : CFSG.Open.IsKGroup ↥L)
    (hrk : ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r (CFSG.pPrimeCore p ↥L) ≤ 3)
    (hfree : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ (V : Type) [Group V] [Finite V],
      IsPGroup q V → CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3 → ∀ (A : Subgroup (MulAut V))
      (φ : ↥A →* (↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pPrimeCore p ↥L)),
      ¬ Function.Surjective φ) :
    IsTwoPrimeComponentIn L H := by
  haveI : Group.IsPerfect ↥L := hLK.isPerfect hp
  by_cases hc : CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L) ≤
      center (↥L ⧸ CFSG.pCore 2 ↥L)
  · exact isTwoPrimeComponentIn_of_le_center hp hp2 hL hLK hc
  · have hgen :
        closure {y : ↥L ⧸ CFSG.pCore 2 ↥L | ∃ n : ℕ, orderOf y = p ^ n} = ⊤ :=
      closure_pElem_quot_eq_top (Y := ↥L) hp (CFSG.pCore 2 ↥L)
        (IsPComponentIn.closure_pElem_eq_top hp hLK)
    have h2 : CFSG.pCore 2 (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := pCore_two_quot_eq_bot (Y := ↥L)
    obtain ⟨e₀⟩ := nonempty_quot_pPrimeCore_quot_mulEquiv (Y := ↥L) hp hp2
    have hq : CFSG.IsQuasisimple ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸
        CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      CFSG.IsQuasisimple.of_mulEquiv e₀ (IsPComponentIn.isQuasisimple_quot hp hLK)
    have hrk' : ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.Open.pRank r (CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L)) ≤ 3 :=
      fun r hr hr2 => (pRank_pPrimeCore_quot_le (Y := ↥L) hp hp2 hr hr2).trans (hrk r hr hr2)
    have hK' : CFSG.Open.IsKGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      hK.quotient (CFSG.pCore 2 ↥L)
    have hE : CFSG.layer ↥(CFSG.pPrimeCore p (↥L ⧸ CFSG.pCore 2 ↥L)) = ⊥ :=
      layer_pPrimeCore_eq_bot (Y := ↥L ⧸ CFSG.pCore 2 ↥L) hp hgen hK' hS hrk'
    obtain ⟨q, hq', hq2, hqp, V, hV, hrank, A, φ, hφ⟩ :=
      exists_mulAut_surjective_of_not_le_center (Y := ↥L ⧸ CFSG.pCore 2 ↥L)
        hp hgen h2 hq hE hrk' hc
    obtain ⟨e₁⟩ := nonempty_center_quot_mulEquiv e₀
    let φ' : ↥A →* (↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pPrimeCore p ↥L) := e₁.toMonoidHom.comp φ
    have hφ' : Function.Surjective φ' := e₁.surjective.comp hφ
    exact (hfree q hq' hq2 hqp ↥V hV hrank A φ' hφ').elim

theorem NineSettingGen.isTwoPrimeComponentIn_of_not_autSection
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    {M Q H E : Subgroup G} {p k : ℕ} (h : NineSettingGen G M p Q H E k)
    (hL : ¬ pLayerIn p H ≤ M) {L : Subgroup G} (hLK : IsPComponentIn p L (kSub p M H))
    (hfree : ∀ q : ℕ, q.Prime → q ≠ 2 → q ≠ p → ∀ (V : Type) [Group V] [Finite V],
      IsPGroup q V → CFSG.Open.pRank q (⊤ : Subgroup V) ≤ 3 → ∀ (A : Subgroup (MulAut V))
      (φ : ↥A →* (↥L ⧸ CFSG.pPrimeCore p ↥L) ⧸
        Subgroup.center (↥L ⧸ CFSG.pPrimeCore p ↥L)),
      ¬ Function.Surjective φ) :
    IsTwoPrimeComponentIn L H := by
  have hp : p.Prime := QSet.prime_of_mem h.mem_Q
  have hp2 : p ≠ 2 := QSet.ne_two_of_mem h.mem_Q
  have hLH : L ≤ H := hLK.1.trans (kSub_le p M H)
  have hLs : (L.subgroupOf H).IsSubnormal := hLK.isSubnormal_of_kSub hL
  exact CFSG.LocalAnalysis.RankThreeUC.AGL81C.isTwoPrimeComponentIn_of_not_autSection
    hp hp2 hS hL hLK
    (h.isKGroup_of_le hLH) (fun r hr hr2 => h.pRank_pPrimeCore_le_three hLH hLs hr hr2) hfree

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
