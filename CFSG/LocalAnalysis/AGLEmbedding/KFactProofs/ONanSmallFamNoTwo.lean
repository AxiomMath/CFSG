module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallNoTwoGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFam
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneLinTwo
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneUnitary

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open CFSG.PSL2Table

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem pow_eq_one_of_isSmallLinTwo (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsSmallLinTwo p K)
    (T : Sylow p K) : ∀ t ∈ (T : Subgroup K), t ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, ⟨e₁⟩⟩ := hK
  obtain ⟨e₂⟩ := nonempty_mulEquiv_psl2GF_of_isLinTwoIndex hd
  let e : K ≃* PSL2GF p 2 := e₁.trans e₂
  have hfs : Function.Surjective (e : K →* PSL2GF p 2) := e.surjective
  obtain ⟨ψ, -, hψU, -⟩ := exists_torus_action hp2 (by norm_num : 1 ≤ 2) (T.mapSurjective hfs)
  intro t ht
  have h1 : e t ∈ ((T.mapSurjective hfs : Sylow p (PSL2GF p 2)) : Subgroup (PSL2GF p 2)) := by
    rw [Sylow.coe_mapSurjective hfs T]
    exact ⟨t, ht, rfl⟩
  rw [← hψU] at h1
  obtain ⟨m, hm⟩ := h1
  have hm1 : m ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  apply e.injective
  rw [map_pow, ← hm, ← map_pow, hm1, map_one, map_one]

theorem noTwo_of_isSmallLinTwo (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsSmallLinTwo p K)
    (S : Sylow p K) (U : Subgroup K) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have D := smallRankOneData_of_isSmallLinTwo hp2 hK S
  exact noTwo_of_gamma_le_normalizer hp hp2 S
    ⟨1, by rw [sylowSq_of_isSmallLinTwo hp hp2 hK S, mul_one]⟩
    (pow_eq_one_of_isSmallLinTwo hp hp2 hK S) (glbCore_eq_normalizer_of_ti hp D.dvd D.ti).le
    (fun g hg => D.centralizer_le hg) U hU hSU

theorem noTwo_of_isSmallUnitary (hp : p.Prime) (hp2 : p ≠ 2) (hK : IsSmallUnitary p K)
    (S : Sylow p K) (U : Subgroup K) (hU : IsPGroup 2 U)
    (hSU : (S : Subgroup K) ≤ Subgroup.normalizer (U : Set K)) : U = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have D := smallRankOneData_of_isSmallUnitary hp hK S
  obtain ⟨hcard, hexp⟩ := sylowCube_of_isSmallUnitary hp hp2 hK S
  exact noTwo_of_gamma_le_normalizer hp hp2 S
    ⟨p, by rw [hcard]; ring⟩ hexp (glbCore_eq_normalizer_of_ti hp D.dvd D.ti).le
    (fun g hg => D.centralizer_le hg) U hU hSU

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
