module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Defs
public import CFSG.Quasithin.Background.F6ResL28
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Subgroup CFSG.Quasithin
open CFSG.Quasithin.F6.L28Res (G8)

@[expose] def l28mC : G8 :=
  ⟨(GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 2), by decide⟩

@[expose] def l28mN : G8 :=
  ⟨(GF8.ofNat' 0, GF8.ofNat' 1, GF8.ofNat' 1, GF8.ofNat' 0), by decide⟩

private theorem l28mC_pow_nine : l28mC ^ 9 = 1 := by decide +kernel

private theorem l28mC_pow_ne (m : ℕ) (h0 : 0 < m) (h9 : m < 9) : l28mC ^ m ≠ 1 := by
  interval_cases m <;> decide +kernel

theorem l28mC_orderOf : orderOf l28mC = 9 := by
  rw [orderOf_eq_iff (by norm_num)]
  exact ⟨l28mC_pow_nine, fun m hm h0 => l28mC_pow_ne m h0 hm⟩

theorem l28mN_mul_self : l28mN * l28mN = 1 := by decide +kernel

theorem l28mN_inv : l28mN * l28mC * l28mN⁻¹ = l28mC⁻¹ := by decide +kernel

theorem l28m_sylow_inv_of_cyclic {K : Type} [Group K] [Finite K] (hK : Nat.card K = 504)
    {c n : K} (hc : orderOf c = 9) (hn2 : n * n = 1) (hn : n * c * n⁻¹ = c⁻¹) (T : Sylow 3 K) :
    ∃ m ∈ normalizer ((T : Subgroup K) : Set K), m * m = 1 ∧
      ∀ t ∈ (T : Subgroup K), m * t * m⁻¹ = t⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (zpowers c) = 3 ^ 2 := by
    rw [Nat.card_zpowers, hc]
    norm_num
  have hp : IsPGroup 3 (zpowers c) := IsPGroup.of_card hcard
  have hidx : ¬ 3 ∣ (zpowers c).index := by
    have h := (zpowers c).index_mul_card
    rw [hcard, hK] at h
    have : (zpowers c).index = 56 := by omega
    rw [this]
    norm_num
  let T₀ : Sylow 3 K := hp.toSylow hidx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K T₀ T
  have hT : ∀ t ∈ (T : Subgroup K), ∃ x ∈ zpowers c, g * x * g⁻¹ = t := by
    intro t ht
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at ht
    obtain ⟨x, hx, hxt⟩ := ht
    refine ⟨x, hx, ?_⟩
    simpa [MulAut.smul_def, MulAut.conj_apply] using hxt
  have hnx : ∀ x ∈ zpowers c, n * x * n⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have h := map_zpow (MulAut.conj n) c k
    simp only [MulAut.conj_apply] at h
    rw [h, hn, _root_.inv_zpow]
  have hinv : ∀ t ∈ (T : Subgroup K), (g * n * g⁻¹) * t * (g * n * g⁻¹)⁻¹ = t⁻¹ := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := hT t ht
    calc g * n * g⁻¹ * (g * x * g⁻¹) * (g * n * g⁻¹)⁻¹ = g * (n * x * n⁻¹) * g⁻¹ := by group
      _ = g * x⁻¹ * g⁻¹ := by rw [hnx x hx]
      _ = (g * x * g⁻¹)⁻¹ := by group
  have hsq : (g * n * g⁻¹) * (g * n * g⁻¹) = 1 := by
    calc (g * n * g⁻¹) * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
      _ = 1 := by rw [hn2]; group
  refine ⟨g * n * g⁻¹, ?_, hsq, hinv⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hinv h hh]
    exact inv_mem hh
  · intro hh
    have h1 := hinv _ hh
    have h2 : (g * n * g⁻¹) * ((g * n * g⁻¹) * h * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹)⁻¹ = h := by
      calc (g * n * g⁻¹) * ((g * n * g⁻¹) * h * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹)⁻¹
          = ((g * n * g⁻¹) * (g * n * g⁻¹)) * h * ((g * n * g⁻¹) * (g * n * g⁻¹))⁻¹ := by group
        _ = h := by rw [hsq]; group
    rw [h2] at h1
    rw [show h = ((g * n * g⁻¹) * h * (g * n * g⁻¹)⁻¹)⁻¹ from h1]
    exact inv_mem hh

section Transport

variable {K : Type} [Group K]

theorem l28m_equiv_psl (hK : IsRankThreeL28 K) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) := by
  obtain ⟨hv, ⟨e⟩⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hv)⟩

theorem l28m_equiv (hK : IsRankThreeL28 K) : Nonempty (K ≃* G8) := by
  obtain ⟨e⟩ := l28m_equiv_psl hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 3) = 8 := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  obtain ⟨e₂⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) hcard
  exact ⟨e.trans
    ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 _).trans e₂)⟩

theorem l28m_card (hK : IsRankThreeL28 K) : Nat.card K = 504 := by
  obtain ⟨e⟩ := l28m_equiv hK
  rw [Nat.card_congr e.toEquiv, CFSG.Quasithin.F6.L28Res.card_G8]

theorem l28m_simple (hK : IsRankThreeL28 K) : IsSimpleGroup K := by
  obtain ⟨e⟩ := l28m_equiv_psl hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : 4 ≤ Nat.card (GaloisField 2 3) := by
    rw [GaloisField.card 2 3 (by norm_num)]
    norm_num
  have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  exact e.isSimpleGroup

theorem l28m_eq_one_of_central (hK : IsRankThreeL28 K) {x : K} (hx : ∀ y : K, x * y = y * x) :
    x = 1 := by
  obtain ⟨e⟩ := l28m_equiv hK
  have h1 : e x = 1 := by
    refine CFSG.Quasithin.F6.L28Res.eq_one_of_commute _ ?_ ?_
    · rw [← e.apply_symm_apply CFSG.Quasithin.F6.L28Res.ga, ← map_mul, ← map_mul, hx]
    · rw [← e.apply_symm_apply CFSG.Quasithin.F6.L28Res.gb, ← map_mul, ← map_mul, hx]
  simpa using h1

theorem l28m_card_mulAut (hK : IsRankThreeL28 K) : Nat.card (MulAut K) = 1512 := by
  obtain ⟨e⟩ := l28m_equiv hK
  rw [Nat.card_congr (MulAut.congr e).toEquiv, CFSG.Quasithin.F6.L28Res.card_mulAut]

theorem l28m_exists_order_nine (hK : IsRankThreeL28 K) : ∃ c : K, orderOf c = 9 := by
  obtain ⟨e⟩ := l28m_equiv hK
  exact ⟨e.symm l28mC, by rw [MulEquiv.orderOf_eq]; exact l28mC_orderOf⟩

theorem l28m_sylow_inv [Finite K] (hK : IsRankThreeL28 K) (T : Sylow 3 K) :
    ∃ m ∈ normalizer ((T : Subgroup K) : Set K), m * m = 1 ∧
      ∀ t ∈ (T : Subgroup K), m * t * m⁻¹ = t⁻¹ := by
  obtain ⟨e⟩ := l28m_equiv hK
  exact l28m_sylow_inv_of_cyclic (l28m_card hK) (c := e.symm l28mC) (n := e.symm l28mN)
    (by rw [MulEquiv.orderOf_eq]; exact l28mC_orderOf) (by rw [← map_mul, l28mN_mul_self, map_one])
    (by rw [← map_inv e.symm l28mN, ← map_mul, ← map_mul, l28mN_inv, map_inv]) T

end Transport

end CFSG.LocalAnalysis.RankThreeTheoremC
