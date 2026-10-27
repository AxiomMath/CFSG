module

public import CFSG.ClassicalInvolution.AschTight.Sec6GenAPI

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.AscL62
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G]

structure Pair (Ω : Set (Subgroup G)) (K J : Subgroup G) (z t : G) : Prop where
  hK : K ∈ Ω
  hJ : J ∈ Ω
  hz : IsUniqueInvolution K z
  ht : IsUniqueInvolution J t
  hne : z ≠ t

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {z t : G}

theorem Pair.symm (h : Pair Ω K J z t) : Pair Ω J K t z :=
  ⟨h.hJ, h.hK, h.ht, h.hz, h.hne.symm⟩

theorem Pair.ne (h : Pair Ω K J z t) : K ≠ J := by
  rintro rfl
  exact h.hne (h.hz.eq h.ht)

theorem Pair.eq_one_of_mem_of_mem (h : Pair Ω K J z t) {g : G} (hgK : g ∈ K) (hgJ : g ∈ J)
    (hg : ∃ i : ℕ, orderOf g = 2 ^ i) : g = 1 := by
  by_contra hg1
  obtain ⟨i, hi⟩ := hg
  obtain ⟨y, hy, hy2, hy1⟩ := exists_involution_pow hg1 hi
  have hyK : y ∈ K := (Subgroup.zpowers_le.mpr hgK) hy
  have hyJ : y ∈ J := (Subgroup.zpowers_le.mpr hgJ) hy
  rcases h.hz.unique y hyK hy2 with h1 | h1
  · exact hy1 h1
  rcases h.ht.unique y hyJ hy2 with h2 | h2
  · exact hy1 h2
  exact h.hne (h1 ▸ h2)

theorem Pair.coreCfg [Finite G] (hΩ : HypOmegaGen Ω) (h : Pair Ω K J z t)
    {R V : Subgroup G} (hR : IsSylow2In R K) (hV2 : IsPGroup 2 ↥V) (hVJ : V ≤ J) (htV : t ∈ V)
    (hVR : ∀ y ∈ V, conjSub y R = R) : CoreCfg R V z t := by
  have hquat : IsQuatSub R := isQuatSub_of_mem_RSet hΩ (mem_RSet_of_isSylow2In h.hK hR)
  have hzR : z ∈ R :=
    mem_of_uniqueInvolution_of_pGroup h.hz hR.1 hR.2.1 (by have := hquat.eight_le; omega)
  exact ⟨hquat, isUniqueInvolution_of_le h.hz hR.1 hzR, hV2, hVR,
    fun g hgV hgR => h.eq_one_of_mem_of_mem (hR.1 hgR) (hVJ hgV)
      (orderOf_eq_two_pow_of_isPGroup hV2 hgV), isUniqueInvolution_of_le h.ht hVJ htV⟩

theorem Pair.comm_of_normalizes (h : Pair Ω K J z t) {R V : Subgroup G} (hRK : R ≤ K)
    (hR2 : IsPGroup 2 ↥R) (hVJ : V ≤ J) (hVR : ∀ y ∈ V, conjSub y R = R) {u v : G} (hu : u ∈ R)
    (huJ : u ∈ Subgroup.normalizer (J : Set G)) (hv : v ∈ V) : u * v = v * u := by
  have hgJ : u * v * u⁻¹ * v⁻¹ ∈ J := by
    have h1 : u * v * u⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp huJ v).mp (hVJ hv)
    exact J.mul_mem h1 (J.inv_mem (hVJ hv))
  have hgR : u * v * u⁻¹ * v⁻¹ ∈ R := by
    have h1 : v * u⁻¹ * v⁻¹ ∈ conjSub v R := conj_mem_conjSub (R.inv_mem hu)
    rw [hVR v hv] at h1
    have : u * v * u⁻¹ * v⁻¹ = u * (v * u⁻¹ * v⁻¹) := by group
    rw [this]
    exact R.mul_mem hu h1
  have h1 := h.eq_one_of_mem_of_mem (hRK hgR) hgJ (orderOf_eq_two_pow_of_isPGroup hR2 hgR)
  have h2 : u * v * u⁻¹ = v := by
    have := congrArg (fun w => w * v) h1
    simpa [mul_assoc] using this
  calc u * v = (u * v * u⁻¹) * u := by group
    _ = v * u := by rw [h2]

theorem Pair.bootstrap [Finite G] (hΩ : HypOmegaGen Ω) (h : Pair Ω K J z t) {W : Subgroup G}
    (hWK : W ≤ K) (hW2 : IsPGroup 2 ↥W) (hzW : z ∈ W)
    (hWc : W ≤ Subgroup.centralizer ({t} : Set G)) (hW4 : 4 ≤ Nat.card W) :
    W ≤ Subgroup.normalizer (J : Set G) ∧
      ∃ R : Subgroup G, IsSylow2In R J ∧ CoreCfg R W t z ∧
        4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({z} : Set G)) ∧
        R ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
        (∀ u ∈ R ⊓ Subgroup.centralizer ({z} : Set G), ∀ w ∈ W, u * w = w * u) ∧
        CoreDich R W z := by
  have hWJ : W ≤ Subgroup.normalizer (J : Set G) :=
    le_normalizer_of_le_centralizer hΩ h.hJ h.hK h.ne.symm h.ht hWK hW2 (by omega) hWc
  refine ⟨hWJ, ?_⟩
  obtain ⟨R, hR, hRinv⟩ := AscL62.exists_sylow_normalized hW2 hWJ
  have hcfg : CoreCfg R W t z := h.symm.coreCfg hΩ hR hW2 hWK hzW hRinv
  have hWne : W ≠ Subgroup.zpowers z := by
    intro hW
    have : Nat.card W = 2 := by
      rw [hW, Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
    omega
  have hU4 := hcfg.four_le_natCard_cent hWne
  have hUJ : R ⊓ Subgroup.centralizer ({z} : Set G) ≤ J := inf_le_left.trans hR.1
  have hU2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer ({z} : Set G)) := hR.2.1.to_inf_left
  have hUN : R ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_le_centralizer hΩ h.hK h.hJ h.ne h.hz hUJ hU2 (by omega) inf_le_right
  have hcomm : ∀ u ∈ R ⊓ Subgroup.centralizer ({z} : Set G), ∀ w ∈ W, u * w = w * u := by
    intro u hu w hw
    exact h.symm.comm_of_normalizes hR.1 hR.2.1 hWK hRinv hu.1 (hUN hu) hw
  exact ⟨R, hR, hcfg, hU4, hUN, hcomm, hcfg.core_dichotomy hWne hcomm⟩

theorem Pair.natCard_sylow_eq (hΩ : HypOmegaGen Ω) (h : Pair Ω K J z t)
    {R R' : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' J) :
    Nat.card R = Nat.card R' :=
  natCard_isSylow2In_eq hΩ h.hK h.hJ hR hR'

theorem Pair.eq_zpowers_of_not_le_normalizer [Finite G] (hΩ : HypOmegaGen Ω)
    (h : Pair Ω K J z t) {V : Subgroup G} (hV2 : IsPGroup 2 ↥V)
    (hVJ : V ≤ J) (hVc : V ≤ Subgroup.centralizer ({z} : Set G)) (htV : t ∈ V)
    (hVN : ¬ V ≤ Subgroup.normalizer (K : Set G)) :
    V = Subgroup.zpowers t ∧ conjSub t K ≠ K := by
  have hV2' : Nat.card V ≤ 2 := by
    by_contra hgt
    push Not at hgt
    exact hVN (le_normalizer_of_le_centralizer hΩ h.hK h.hJ h.ne h.hz hVJ hV2 (by omega) hVc)
  have hzp : Nat.card (Subgroup.zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.ht.sq) h.ht.ne_one
  have hle : Subgroup.zpowers t ≤ V := Subgroup.zpowers_le.mpr htV
  have hVeq : V = Subgroup.zpowers t :=
    (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  refine ⟨hVeq, fun hcon => hVN ?_⟩
  rw [hVeq, Subgroup.zpowers_le]
  exact mem_normalizer_iff_conjSub_eq.mpr hcon

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
