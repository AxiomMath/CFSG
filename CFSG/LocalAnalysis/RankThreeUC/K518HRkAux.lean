module

public import CFSG.GroupTheory.PGroup.RankTwoCommute
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.K518H

theorem exists_mem_zpowers_notMem_pow_mem_of_orderOf {G : Type*} [Group G] (I : Subgroup G)
    {ℓ k : ℕ} {ψ : G} (hψ : orderOf ψ = ℓ ^ k) (hψI : ψ ∉ I) :
    ∃ φ ∈ Subgroup.zpowers ψ, φ ∉ I ∧ φ ^ ℓ ∈ I := by
  classical
  have hex : ∃ j : ℕ, ψ ^ (ℓ ^ j) ∈ I :=
    ⟨k, by rw [← hψ, pow_orderOf_eq_one]; exact I.one_mem⟩
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at this
    exact hψI this
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨ψ ^ (ℓ ^ m), Subgroup.pow_mem _ (Subgroup.mem_zpowers ψ) _, ?_, ?_⟩
  · exact Nat.find_min hex (by omega)
  · rw [← pow_mul, ← pow_succ]
    have := Nat.find_spec hex
    rwa [hm] at this

theorem two_le_pRank_sup_zpowers_of_commute {G : Type*} [Group G] [Finite G] {ℓ : ℕ}
    [Fact ℓ.Prime] {I : Subgroup G} {ψ x y : G} (hx : x ∈ I) (hy : y ∈ I ⊔ Subgroup.zpowers ψ)
    (hyI : y ∉ I) (hxo : orderOf x = ℓ) (hyo : orderOf y = ℓ) (hxy : Commute x y) :
    2 ≤ CFSG.Open.pRank ℓ (I ⊔ Subgroup.zpowers ψ) :=
  CFSG.GroupTheory.two_le_pRank_of_commute (Subgroup.mem_sup_left hx) hy hxo hyo hxy
    fun h => hyI (Subgroup.zpowers_le.mpr hx h)

end CFSG.LocalAnalysis.RankThreeUC.S15.K518H
