module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinCuts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveAbstract
public import CFSG.Monster.B.TwoA.Base.ElemAut
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
  CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open CFSG.AGLEmbedding.ParabPrime (perfectJoin)
open CFSG.RankThree.PartOne.OutStructure
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open scoped commutatorElement

theorem linear_pCentralP (p : ℕ) [OddPrime p] {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 3 ≤ n) : PCentral p (linearAutGroup n K) := by
  obtain ⟨hgenTop, hgen⟩ := automorphism_generation (K := K) hn
  obtain ⟨hID, -, hDn, -, -, ⟨g, -, hg⟩, -, hidx, -, -⟩ :=
    standard_outer_quotients (n := n) (K := K)
  have htrans := standard_automorphism_transport (K := K) (n := n)
  have : Finite (MulAut (projectiveSL n K)) := inferInstance
  have hDnorm : (linearAutGroup n K).Normal := by
    refine ⟨fun d hd γ => ?_⟩
    have hγ : γ ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top γ
    have hd' : d ∈ standardAutGroup n K := hgenTop ▸ Subgroup.mem_top d
    have := hDn.conj_mem ⟨d, hd'⟩ (Subgroup.mem_subgroupOf.mpr hd) ⟨γ, hγ⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hpE : ∀ α : MulAut (projectiveSL n K),
      (∃ k : ℕ, α ^ (p ^ k) ∈ linearAutGroup n K) → α ∈ semilinearAutGroup n K := by
    rintro α ⟨k, hk⟩
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2 : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2
    have hpodd : Odd (p ^ k) := OddPrime.odd_pow p k
    exact mem_of_pow_mem_of_index_le_two _ hidx' hpodd (linearAutGroup_le_semilinearAutGroup hk)
  have hD3 : ∀ γ α : MulAut (projectiveSL n K), α ∈ semilinearAutGroup n K →
      ⁅γ, α⁆ ∈ linearAutGroup n K := by
    intro γ α hα
    obtain ⟨B, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp hα
    obtain ⟨A, σ, ε, hε, rfl⟩ := hgen γ
    set π := QuotientGroup.mk' (linearAutGroup n K) with hπ
    have hπc : ∀ C : GL (Fin n) K, π (conjAut n K C) = 1 := fun C =>
      (QuotientGroup.eq_one_iff _).mpr (conjAut_mem_linearAutGroup C)
    have hfσ : Commute (π (fieldAut n K σ)) (π (fieldAut n K τ)) := by
      have h1 : fieldAut n K σ * fieldAut n K τ = fieldAut n K τ * fieldAut n K σ := by
        rw [htrans.2.1, htrans.2.1, ringAut_comm K σ τ]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hδf : Commute (π (dualAut n K)) (π (fieldAut n K τ)) := by
      have h1 : dualAut n K * fieldAut n K τ = fieldAut n K τ * dualAut n K := by
        have h2 := htrans.2.2.2.2.2.1 τ
        calc dualAut n K * fieldAut n K τ
            = (dualAut n K * fieldAut n K τ * dualAut n K) * dualAut n K := by
              rw [mul_assoc (dualAut n K * fieldAut n K τ), htrans.2.2.2.1, mul_one]
          _ = fieldAut n K τ * dualAut n K := by rw [h2]
      have h3 := congrArg π h1
      rw [map_mul π, map_mul π] at h3
      exact h3
    have hc : Commute (π (conjAut n K A * fieldAut n K σ * dualAut n K ^ ε))
        (π (conjAut n K B * fieldAut n K τ)) := by
      rw [map_mul, map_mul, map_mul, hπc, hπc, one_mul, one_mul, map_pow]
      exact (hfσ.mul_left (hδf.pow_left ε))
    have h1 : π ⁅conjAut n K A * fieldAut n K σ * dualAut n K ^ ε,
        conjAut n K B * fieldAut n K τ⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hc
    exact (QuotientGroup.eq_one_iff _).mp h1
  exact ⟨hDnorm, fun α hα γ => hD3 γ α (hpE α hα)⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
