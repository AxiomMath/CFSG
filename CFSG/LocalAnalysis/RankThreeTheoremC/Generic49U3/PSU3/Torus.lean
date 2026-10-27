module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Defs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryTorus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open

theorem galoisField_exists_unit_of_not_dvd {p : ℕ} [Fact p.Prime] (m : ℕ) {k : ℤ}
    (hk : ¬ (p : ℤ) ∣ k) :
    ∃ μ : (GaloisField p m)ˣ, (μ : GaloisField p m) = (k : GaloisField p m) := by
  have hμ : (k : GaloisField p m) ≠ 0 := by
    rw [Ne, CharP.intCast_eq_zero_iff (GaloisField p m) p]
    exact hk
  exact ⟨Units.mk0 _ hμ, rfl⟩

theorem u3_torus_on_center {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) {K : Type} [Group K] [Finite K]
    (hK : IsU3Pred p K) (T : Sylow p K) {c : K} (hcT : c ∈ (T : Subgroup K))
    (hcZ : c ∈ Subgroup.centralizer ((T : Subgroup K) : Set K)) (hc1 : c ≠ 1) (k : ℤ)
    (hk : ¬ (p : ℤ) ∣ k) :
    ∃ n ∈ Subgroup.normalizer ((T : Subgroup K) : Set K), n * c * n⁻¹ = c ^ k := by
  obtain ⟨q, hqp, -, hv, he⟩ := hK
  have hd : CFSG.AGLEmbedding.IsUnitaryIndex p ⟨.twistedA 2 q, hv⟩ := ⟨q, hqp, rfl⟩
  obtain ⟨ψ, -, hrange, htor⟩ :=
    CFSG.AGLEmbedding.kFactUnitarySylowCenterTorus K p ⟨.twistedA 2 q, hv⟩ hd he T
  have hcr : c ∈ ψ.range := by
    rw [hrange]
    exact Subgroup.mem_inf.mpr ⟨hcT, hcZ⟩
  obtain ⟨a, rfl⟩ := hcr
  obtain ⟨μ, hμ⟩ := galoisField_exists_unit_of_not_dvd
    (⟨.twistedA 2 q, hv⟩ : TauCeti.ValidLieTypeIndex).1.fieldExponent hk
  obtain ⟨n, hn, hconj⟩ := htor μ
  refine ⟨n, hn, ?_⟩
  rw [hconj a, ← map_zpow]
  congr 1
  rw [hμ]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, toAdd_zpow, zsmul_eq_mul]

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
