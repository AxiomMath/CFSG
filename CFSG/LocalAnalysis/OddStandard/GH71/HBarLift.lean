module

public import CFSG.LocalAnalysis.OddStandard.GH71.CoversTransfer
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L121Alt

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Bender.Thm2

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_conj_le {H R : Subgroup G} (hR : IsPGroup 2 ↥R) (hRH : R ≤ H)
    {h : G} (hle : R.map (MulAut.conj h).toMonoidHom ≤ pPrimeCoreOf 2 H ⊔ R) :
    ∃ n ∈ pPrimeCoreOf 2 H, n⁻¹ * h ∈ normalizer (R : Set G) := by
  set N := pPrimeCoreOf 2 H
  have hHN : H ≤ normalizer (N : Set G) := le_normalizer_pPrimeCoreOf' H
  have hRN : R ≤ normalizer (N : Set G) := hRH.trans hHN
  have hNodd : Odd (Nat.card N) := odd_card_pPrimeCoreOf' H
  have hR'card : Nat.card (R.map (MulAut.conj h).toMonoidHom) = Nat.card R :=
    card_map_of_injective (MulAut.conj h).injective
  have hsylR : Open.fusionIsSylowIn 2 R (N ⊔ R) :=
    fusionIsSylowIn_two_of_sup hR hRN hNodd hR le_sup_right rfl
  have hsylR' : Open.fusionIsSylowIn 2 (R.map (MulAut.conj h).toMonoidHom) (N ⊔ R) :=
    fusionIsSylowIn_two_of_sup hR hRN hNodd (hR.map _) hle hR'card
  obtain ⟨c, hc, hcR⟩ := exists_conj_sylow Nat.prime_two hsylR hsylR'
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left N R hRN
  have hc' : c ∈ ((N ⊔ R : Subgroup G) : Set G) := hc
  rw [hset] at hc'
  obtain ⟨n, hn, r₀, hr₀, rfl⟩ := hc'
  refine ⟨n, hn, ?_⟩
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 : h * y * h⁻¹ ∈ R.map (MulAut.conj h).toMonoidHom := ⟨y, hy, rfl⟩
    rw [hcR] at h1
    obtain ⟨w, hw, hwy⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwy
    have e : n⁻¹ * h * y * (n⁻¹ * h)⁻¹ = r₀ * w * r₀⁻¹ := by
      calc n⁻¹ * h * y * (n⁻¹ * h)⁻¹ = n⁻¹ * (h * y * h⁻¹) * n := by group
        _ = n⁻¹ * (n * r₀ * w * (n * r₀)⁻¹) * n := by rw [← hwy]
        _ = r₀ * w * r₀⁻¹ := by group
    rw [e]
    exact R.mul_mem (R.mul_mem hr₀ hw) (R.inv_mem hr₀)
  · intro hy
    have h1 : n * r₀ * (r₀⁻¹ * (n⁻¹ * h * y * (n⁻¹ * h)⁻¹) * r₀) * (n * r₀)⁻¹ ∈
        R.map (MulAut.conj (n * r₀)).toMonoidHom :=
      ⟨_, R.mul_mem (R.mul_mem (R.inv_mem hr₀) hy) hr₀, rfl⟩
    rw [← hcR] at h1
    obtain ⟨w, hw, hwy⟩ := h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwy
    have e : y = w := by
      have e1 : h * w * h⁻¹ = h * y * h⁻¹ := by rw [hwy]; group
      exact (mul_left_cancel (mul_right_cancel e1)).symm
    rw [e]; exact hw

omit [Finite G] in
theorem normalizer_zpowers_eq_centralizer {z : G} (hz : orderOf z = 2) :
    normalizer ((zpowers z : Subgroup G) : Set G) = centralizer ({z} : Set G) := by
  ext g
  rw [mem_normalizer_iff, mem_centralizer_singleton_iff]
  constructor
  · intro hg
    have hz' : g * z * g⁻¹ ∈ zpowers z := (hg z).mp (mem_zpowers z)
    have hzz : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz'
    have hk2 : z ^ k = 1 ∨ z ^ k = z := by
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
      rcases Int.emod_two_eq_zero_or_one k with h0 | h1
      · left
        obtain ⟨m, hm⟩ := Int.dvd_of_emod_eq_zero h0
        rw [hm, zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two, hzz], one_zpow]
      · right
        have : k = 2 * (k / 2) + 1 := by omega
        rw [this, zpow_add, zpow_mul, show z ^ (2 : ℤ) = 1 by rw [zpow_two, hzz], one_zpow,
          one_mul, zpow_one]
    rcases hk2 with h1 | h1
    · exfalso
      rw [h1] at hk
      have : z = 1 := by
        have := congrArg (fun x => g⁻¹ * x * g) hk
        rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
        rw [← this]; group
      rw [this, orderOf_one] at hz
      omega
    · rw [h1] at hk
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [← hk]
  · intro hg x
    have hc : ∀ w : G, w ∈ zpowers z → g * w * g⁻¹ = w := by
      intro w hw
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
      have hcomm : Commute g (z ^ k) := (Commute.zpow_right hg k)
      rw [hcomm.eq]; group
    constructor
    · intro hx; rw [hc x hx]; exact hx
    · intro hx
      have hx' := hc _ hx
      have e : x = g * x * g⁻¹ := by
        have h1 : g * (g * x * g⁻¹) * g⁻¹ = g * x * g⁻¹ := hx'
        have h2 := mul_left_cancel (mul_right_cancel h1)
        exact h2.symm
      rw [e]; exact hx

theorem centralizer_bar_le {H : Subgroup G} {z : G} (hzH : z ∈ H) (hz : orderOf z = 2) :
    centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨z, hzH⟩} : Set (HBar H)) ≤
      barIn H (centralizer ({z} : Set G)) := by
  intro x hx
  obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) x
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  have hcomm : π ⟨h, hh⟩ * π ⟨z, hzH⟩ = π ⟨z, hzH⟩ * π ⟨h, hh⟩ :=
    mem_centralizer_singleton_iff.mp hx
  have hz2 : IsPGroup 2 ↥(zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hzR : zpowers z ≤ H := zpowers_le.mpr hzH
  have hle : (zpowers z).map (MulAut.conj h).toMonoidHom ≤ pPrimeCoreOf 2 H ⊔ zpowers z := by
    rw [MonoidHom.map_zpowers, zpowers_le]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hmem : (⟨h, hh⟩ * ⟨z, hzH⟩ * ⟨h, hh⟩⁻¹ * ⟨z, hzH⟩⁻¹ : ↥H) ∈ pPrimeCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      show π (⟨h, hh⟩ * ⟨z, hzH⟩ * ⟨h, hh⟩⁻¹ * ⟨z, hzH⟩⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]; group
    have hO : h * z * h⁻¹ * z⁻¹ ∈ pPrimeCoreOf 2 H := ⟨_, hmem, rfl⟩
    have e : h * z * h⁻¹ = (h * z * h⁻¹ * z⁻¹) * z := by group
    rw [e]
    exact mul_mem (mem_sup_left hO) (mem_sup_right (mem_zpowers z))
  obtain ⟨n, hn, hnc⟩ := exists_mem_normalizer_of_conj_le hz2 hzR hle
  rw [normalizer_zpowers_eq_centralizer hz] at hnc
  have hnH : n ∈ H := pPrimeCoreOf_le' H hn
  refine ⟨⟨n⁻¹ * h, H.mul_mem (H.inv_mem hnH) hh⟩, hnc, ?_⟩
  obtain ⟨n', hn', rfl⟩ := hn
  show π (n'⁻¹ * ⟨h, hh⟩) = π ⟨h, hh⟩
  have h1 : π n' = 1 := (QuotientGroup.eq_one_iff _).mpr hn'
  rw [map_mul, map_inv, h1, inv_one, one_mul]

end CFSG.OddStandard.GH71
