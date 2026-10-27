module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28WCDefs
import CFSG.Quasithin.Recognition.CertF8
import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open Matrix Subgroup CFSG.Quasithin CFSG.Open

private abbrev SL28 := Matrix.SpecialLinearGroup (Fin 2) GF8

private def cm : SL28 :=
  ⟨!![GF8.ofNat' 0, GF8.ofNat' 1; GF8.ofNat' 1, GF8.ofNat' 2], by
    rw [Matrix.det_fin_two_of]; decide⟩

private def nm : SL28 :=
  ⟨!![GF8.ofNat' 0, GF8.ofNat' 1; GF8.ofNat' 1, GF8.ofNat' 0], by
    rw [Matrix.det_fin_two_of]; decide⟩

private theorem cm_pow_nine : cm ^ 9 = 1 := by decide +kernel

private theorem cm_pow_ne (m : ℕ) (h0 : 0 < m) (h9 : m < 9) : cm ^ m ≠ 1 := by
  interval_cases m <;> decide +kernel

private theorem nm_mul_self : nm * nm = 1 := by decide +kernel

private theorem nm_inv_cm : nm * cm * nm⁻¹ = cm⁻¹ := by decide +kernel

private theorem sl28_center (x : SL28) (hx : x ∈ Subgroup.center SL28) : x = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have key : ∀ r : GF8, r ^ Fintype.card (Fin 2) = 1 → r = 1 := by decide
  have h1 : r = 1 := key r hr
  subst h1
  ext i j
  rw [← hrx]
  simp [Matrix.one_apply]

private theorem sylow_inv_of_cyclic {K : Type} [Group K] [Finite K] (hK : Nat.card K = 504)
    {c n : K} (hc : orderOf c = 9) (hn2 : n * n = 1) (hn : n * c * n⁻¹ = c⁻¹) (T : Sylow 3 K) :
    ∃ m ∈ normalizer ((T : Subgroup K) : Set K), ∀ t ∈ (T : Subgroup K), m * t * m⁻¹ = t⁻¹ := by
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
  refine ⟨g * n * g⁻¹, ?_, hinv⟩
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hinv h hh]
    exact inv_mem hh
  · intro hh
    have h1 := hinv _ hh
    have hsq : (g * n * g⁻¹) * (g * n * g⁻¹) = 1 := by
      calc (g * n * g⁻¹) * (g * n * g⁻¹) = g * (n * n) * g⁻¹ := by group
        _ = 1 := by rw [hn2]; group
    have h2 : (g * n * g⁻¹) * ((g * n * g⁻¹) * h * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹)⁻¹ = h := by
      calc (g * n * g⁻¹) * ((g * n * g⁻¹) * h * (g * n * g⁻¹)⁻¹) * (g * n * g⁻¹)⁻¹
          = ((g * n * g⁻¹) * (g * n * g⁻¹)) * h * ((g * n * g⁻¹) * (g * n * g⁻¹))⁻¹ := by group
        _ = h := by rw [hsq]; group
    rw [h2] at h1
    rw [show h = ((g * n * g⁻¹) * h * (g * n * g⁻¹)⁻¹)⁻¹ from h1]
    exact inv_mem hh

private theorem psl28_witness :
    ∃ c n : Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF8,
      orderOf c = 9 ∧ n * n = 1 ∧ n * c * n⁻¹ = c⁻¹ := by
  let π : SL28 →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF8 := QuotientGroup.mk' _
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact sl28_center x ((QuotientGroup.eq_one_iff x).mp hx)
  refine ⟨π cm, π nm, ?_, ?_, ?_⟩
  · rw [orderOf_injective π hinj, orderOf_eq_iff (by norm_num)]
    exact ⟨cm_pow_nine, fun m hm h0 => cm_pow_ne m h0 hm⟩
  · rw [← map_mul, nm_mul_self, map_one]
  · rw [← map_inv π nm, ← map_mul, ← map_mul, nm_inv_cm, map_inv]

private theorem l28_equiv_psl {K : Type} [Group K] (hK : IsRankThreeL28 K) :
    Nonempty (K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 3)) := by
  obtain ⟨hv, ⟨e⟩⟩ := hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 _ hv)⟩

theorem l28SylowInversion_proved : L28SylowInversion := by
  intro K _ _ hK T
  obtain ⟨eK⟩ := l28_equiv_psl hK
  have hcardF : Nat.card GF8 = 2 ^ 3 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let eF : GF8 ≃+* GaloisField 2 3 :=
    CFSG.ClassicalModels.finiteFieldEquivGaloisField GF8 2 3 (by norm_num) hcardF
  let eG : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) GF8 :=
    eK.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv eF (Fin 2)).symm
  have hK504 : Nat.card K = 504 := by
    rw [Nat.card_congr eK.toEquiv]
    have h := CFSG.Walter.psl2_even_card (f := 3) (by norm_num)
    norm_num at h
    exact h
  obtain ⟨c, n, hc, hn2, hn⟩ := psl28_witness
  obtain ⟨m, hmN, hm⟩ := sylow_inv_of_cyclic hK504 (c := eG.symm c) (n := eG.symm n)
    (by rw [MulEquiv.orderOf_eq]; exact hc) (by rw [← map_mul, hn2, map_one])
    (by rw [← map_inv eG.symm n, ← map_mul, ← map_mul, hn, map_inv]) T
  exact ⟨m, hmN, fun t ht _ => hm t ht⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
