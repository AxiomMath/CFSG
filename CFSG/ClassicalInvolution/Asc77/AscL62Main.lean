module

public import CFSG.ClassicalInvolution.Asc77.AscL62Aut
public import CFSG.ClassicalInvolution.Asc77.WP1Section6

public section

namespace CFSG.ClassicalInvolution.Asc77.AscL62

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {z t : G}

theorem Pair.six_two [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hM3 : CentSylow Ω) (h : Pair Ω K J z t) {V : Subgroup G}
    (hV : IsSylow2In V (J ⊓ Subgroup.centralizer ({z} : Set G))) (htV : t ∈ V) :
    (V = Subgroup.zpowers t ∧ conjSub t K ≠ K) ∨
    (V = Subgroup.zpowers t ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
      ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧ IsSemidihedral (R ⊔ V)) ∨
    (V ∈ USet Ω ∧ V ≤ Subgroup.normalizer (K : Set G) ∧
      ∃ R ∈ RSet Ω, R ≤ K ∧ V ≤ Subgroup.normalizer (R : Set G) ∧ IsWreathed (R ⊔ V)) ∨
    (V ∈ RSet Ω ∧ ⁅V, K⁆ ≤ oddCoreOf K) := by
  have hV2 : IsPGroup 2 ↥V := hV.2.1
  have hVJ : V ≤ J := hV.1.trans inf_le_left
  have hVc : V ≤ Subgroup.centralizer ({z} : Set G) := hV.1.trans inf_le_right
  have hzt : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hVc htV)
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact h.hz.sq) h.hz.ne_one
  have hzle : Subgroup.zpowers z ≤ K ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact ⟨h.hz.mem, Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm⟩
  obtain ⟨W, hW, hzWle⟩ := IsSylow2In.exists_ge hz2 hzle
  have hzW : z ∈ W := hzWle (Subgroup.mem_zpowers z)
  have hW2 : IsPGroup 2 ↥W := hW.2.1
  have hWK : W ≤ K := hW.1.trans inf_le_left
  have hWc : W ≤ Subgroup.centralizer ({t} : Set G) := hW.1.trans inf_le_right
  by_cases hW4 : 4 ≤ Nat.card W
  ·
    obtain ⟨hWJ, RJ, hRJ, hcfgJ, hU4J, hUNJ, hcommJ, hdichJ⟩ :=
      h.bootstrap hp hq hΩ hWK hW2 hzW hWc hW4
    have hUJ2 : IsPGroup 2 ↥(RJ ⊓ Subgroup.centralizer ({z} : Set G)) := hRJ.2.1.to_inf_left
    have hUJle :
        RJ ⊓ Subgroup.centralizer ({z} : Set G) ≤ J ⊓ Subgroup.centralizer ({z} : Set G) :=
      inf_le_inf_right _ hRJ.1
    have hVUJ : Nat.card ↥(RJ ⊓ Subgroup.centralizer ({z} : Set G)) ≤ Nat.card V :=
      hV.natCard_le hUJ2 hUJle
    have hV4 : 4 ≤ Nat.card V := le_trans hU4J hVUJ
    obtain ⟨hVK, R, hR, hcfg, hU4, hUN, hcomm, hdich⟩ :=
      h.symm.bootstrap hp hq hΩ hVJ hV2 htV hVc hV4
    have hVinv : ∀ y ∈ V, conjSub y K = K := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mp (hVK hy)
    have hRRJ : Nat.card R = Nat.card RJ := h.natCard_sylow_eq hΩ hR hRJ
    have hVR : V ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
      mem_normalizer_iff_conjSub_eq.mpr (hcfg.norm y hy)
    rcases hdich with hUR | ⟨C, hUC, hCR, hCc, hCcard, hCinv, hVcyc, hVC, htrans, hwr⟩
    ·
      have hRc : R ≤ Subgroup.centralizer ({t} : Set G) := fun r hr =>
        ((SetLike.ext_iff.mp hUR r).mpr hr).2
      have hWR : Nat.card R ≤ Nat.card W := hW.natCard_le hR.2.1 (le_inf hR.1 hRc)
      rcases hdichJ with hUJR | ⟨CJ, hUCJ, hCJR, hCJc, hCJcard, hCJinv, hWcyc, hWCJ, htransJ, hwrJ⟩
      · have hRJV : Nat.card RJ ≤ Nat.card V := by
          have : Nat.card ↥(RJ ⊓ Subgroup.centralizer ({z} : Set G)) = Nat.card RJ := by
            rw [hUJR]
          omega
        have hVsyl : IsSylow2In V J := hRJ.of_natCard_le hV2 hVJ hRJV
        refine Or.inr (Or.inr (Or.inr ⟨mem_RSet_of_isSylow2In h.hJ hVsyl, ?_⟩))
        have hcommR : ∀ r ∈ R, ∀ v ∈ V, r * v = v * r := fun r hr v hv =>
          hcomm r ((SetLike.ext_iff.mp hUR r).mpr hr) v hv
        have := hM3 h.hK hR hV2 hVinv hcommR
        exact Subgroup.commutator_le.mpr fun v hv k hk => this k hk v hv
      · exfalso
        have h0 : 0 < Nat.card CJ := Nat.card_pos
        omega
    ·
      rcases hdichJ with hUJR | ⟨CJ, hUCJ, hCJR, hCJc, hCJcard, hCJinv, hWcyc, hWCJ, htransJ, hwrJ⟩
      · exfalso
        have hRJV : Nat.card RJ ≤ Nat.card V := by
          have : Nat.card ↥(RJ ⊓ Subgroup.centralizer ({z} : Set G)) = Nat.card RJ := by
            rw [hUJR]
          omega
        have h0 : 0 < Nat.card C := Nat.card_pos
        omega
      · have hVCJ : Nat.card CJ ≤ Nat.card V := by
          have : Nat.card ↥(RJ ⊓ Subgroup.centralizer ({z} : Set G)) = Nat.card CJ := by
            rw [hUCJ]
          omega
        have hVeq : Nat.card V = Nat.card C := by omega
        obtain ⟨RV, hRV, hVRV⟩ := IsSylow2In.exists_ge hV2 hVJ
        have hRVcard : Nat.card RV = 2 * Nat.card V := by
          have := hRV.natCard_eq hRJ
          omega
        have hVU : V ∈ USet Ω := mem_USet_of_natCard h.hJ hRV hVRV hVcyc hRVcard
        exact Or.inr (Or.inr (Or.inl ⟨hVU, hVK, R, mem_RSet_of_isSylow2In h.hK hR, hR.1, hVR,
          hwr hVeq⟩))
  ·
    have hWcard : Nat.card W ≤ 2 := by
      obtain ⟨n, hn⟩ := hW2.exists_card_eq
      by_contra hgt
      push Not at hgt
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by
        by_contra hn1
        have : n ≤ 1 := by omega
        have : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
        omega)
      omega
    by_cases hVN : V ≤ Subgroup.normalizer (K : Set G)
    · obtain ⟨R, hR, hRinv⟩ := exists_sylow_normalized hV2 hVN
      have hcfg : CoreCfg R V z t := h.coreCfg hp hΩ hR hV2 hVJ htV hRinv
      have hU : ¬ 4 ≤ Nat.card ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := by
        intro hU4
        have hle :
            R ⊓ Subgroup.centralizer ({t} : Set G) ≤ K ⊓ Subgroup.centralizer ({t} : Set G) :=
          inf_le_inf_right _ hR.1
        have hU2 : IsPGroup 2 ↥(R ⊓ Subgroup.centralizer ({t} : Set G)) := hR.2.1.to_inf_left
        have := hW.natCard_le hU2 hle
        omega
      obtain ⟨hVeq, hsd⟩ := hcfg.eq_zpowers_and_isSemidihedral hU
      refine Or.inr (Or.inl ⟨hVeq, hVN, R, mem_RSet_of_isSylow2In h.hK hR, hR.1, ?_, hsd⟩)
      intro y hy
      exact mem_normalizer_iff_conjSub_eq.mpr (hRinv y hy)
    · exact Or.inl (h.eq_zpowers_of_not_le_normalizer hp hq hΩ hV2 hVJ hVc htV hVN)

end CFSG.ClassicalInvolution.Asc77.AscL62

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable (p f : ℕ) [Fact p.Prime]

theorem l6_2 : L6_2 p f := by
  intro hp hq G _ _ Ω hΩ K hK z hz J hJ hJnt t ht V hV htV
  have hzt : z ≠ t := fun h => hJnt ⟨hJ, z, hz, h ▸ ht⟩
  exact AscL62.Pair.six_two hp hq hΩ (AscL62.centSylow hp hq hΩ) ⟨hK, hJ, hz, ht, hzt⟩ hV htV

end CFSG.ClassicalInvolution.Asc77
