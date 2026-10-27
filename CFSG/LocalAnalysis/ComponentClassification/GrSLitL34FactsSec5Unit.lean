module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCentralizer

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem unitaryCenter :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G) (x : G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsL34Unitary K x → IsSylowTwoIn P K →
      x ∈ normalizer (P : Set G) → (∀ z ∈ P ⊓ zStarIn K, z * z = 1) →
      Nat.card ↥(P ⊓ centralizer (P : Set G) ⊓ centralizer ({x} : Set G)) =
        2 * Nat.card ↥(P ⊓ zStarIn K) ∧
      (P ⊓ zStarIn K = ⊥ → ∀ w ∈ P ⊓ centralizer (P : Set G) ⊓ centralizer ({x} : Set G),
        ∃ v ∈ P ⊓ centralizer (P : Set G), v⁻¹ * x⁻¹ * v * x = w) := by
  intro G _ _ K P x hK hL hx hP hxP hZ
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hβ, hT⟩ := exists_standard hK hL hx hP hxP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hU : IsUSetting q l (betaHat K hx.1) := ⟨hqS, hqsurj, hqker, h3, hl, hls, hβ⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hk2 := ker_mul_self_of_elem hP hqker hZ
  have hinvZ := (l34UnitaryCentralizerFact G K P x hK hL hx hP hxP).1
  have hc4 : wordPerm (tg 4) * wordPerm (tg 4) = 1 := qc_mul_self
  have hxq : ∀ {y : G} (hy : y ∈ P),
      q (jq K ⟨x⁻¹ * y * x, hP.1 (conj_mem_of_mem_normalizer hxP hy)⟩) =
        r₄ * q (jq K ⟨y, hP.1 hy⟩) * r₄⁻¹ := fun hy => by
    rw [← hβ, betaHat_jq]
    rfl
  have hfixZ : ∀ {z : G} (hzP : z ∈ P), q (jq K ⟨z, hP.1 hzP⟩) = 1 → x⁻¹ * z * x = z := by
    intro z hzP hz1
    have hzZ : z ∈ P ⊓ zStarIn K := by
      refine ⟨hzP, (mem_zStarIn_iff (hP.1 hzP)).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker]
      exact hz1
    rw [hinvZ z hzZ]
    exact inv_eq_of_mul_eq_one_right (hZ z hzZ)
  obtain ⟨e₀, he₀, hq₀⟩ := hU.exists_fix_qc
  obtain ⟨y₀, hy₀P, hy₀K, rfl⟩ := (hT e₀).1 he₀.1
  have hy₀x : x⁻¹ * y₀ * x = y₀ :=
    eq_of_jq_eq hP.1 hP2 (conj_mem_of_mem_normalizer hxP hy₀P) hy₀P he₀.2
  have hqc0 : wordPerm (tg 4) ∈ Z0 := mem_Z0.2 ⟨4, by simp, rfl⟩
  have hqcT : wordPerm (tg 4) ∈ T0 := hqc0.2
  set H : Subgroup (Jhat K) := (zpowers (wordPerm (tg 4))).comap q with hH
  have hC : P ⊓ centralizer (P : Set G) ⊓ centralizer ({x} : Set G) = pullP K P hP.1 H := by
    ext y
    rw [mem_pullP, mem_inf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨hy, hc⟩, hcx⟩
      refine ⟨hy, ?_⟩
      have hZ0 := (mem_centralizer_P_iff hP hQ hk2 hT hy).1 hc
      have hfix : x⁻¹ * y * x = y := by
        calc x⁻¹ * y * x = x⁻¹ * (y * x) := by group
          _ = x⁻¹ * (x * y) := by rw [hcx]
          _ = y := by group
      have h1 := hxq hy
      rw [show (⟨x⁻¹ * y * x, hP.1 (conj_mem_of_mem_normalizer hxP hy)⟩ : K) =
        ⟨y, hP.1 hy⟩ from Subtype.ext hfix] at h1
      have hr : r₄ * q (jq K ⟨y, hP.1 hy⟩) = q (jq K ⟨y, hP.1 hy⟩) * r₄ := by
        calc r₄ * q (jq K ⟨y, hP.1 hy⟩) = r₄ * q (jq K ⟨y, hP.1 hy⟩) * r₄⁻¹ * r₄ := by group
          _ = q (jq K ⟨y, hP.1 hy⟩) * r₄ := by rw [← h1]
      exact mem_zpowers_of_comm_r4 hZ0 hr
    · rintro ⟨hy, hyH⟩
      have hzp : q (jq K ⟨y, hP.1 hy⟩) ∈ Z0 := (zpowers_le.2 hqc0) hyH
      refine ⟨⟨hy, (mem_centralizer_P_iff hP hQ hk2 hT hy).2 hzp⟩, ?_⟩
      have hfix : x⁻¹ * y * x = y := by
        rcases eq_one_or_eq_of_mem_zpowers hc4 hyH with h1 | h1
        · exact hfixZ hy h1
        · have hzP : y₀⁻¹ * y ∈ P := P.mul_mem (P.inv_mem hy₀P) hy
          have hz1 : q (jq K ⟨y₀⁻¹ * y, hP.1 hzP⟩) = 1 := by
            have e1 : (⟨y₀⁻¹ * y, hP.1 hzP⟩ : K) = (⟨y₀, hy₀K⟩ : K)⁻¹ * ⟨y, hP.1 hy⟩ := rfl
            rw [e1, map_mul, map_mul, map_inv, map_inv, hq₀, h1, inv_mul_cancel]
          have hz := hfixZ hzP hz1
          calc x⁻¹ * y * x = (x⁻¹ * y₀ * x) * (x⁻¹ * (y₀⁻¹ * y) * x) := by group
            _ = y := by rw [hy₀x, hz]; group
      calc y * x = x * (x⁻¹ * y * x) := by group
        _ = x * y := by rw [hfix]
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  refine ⟨?_, fun hZ1 w hw => ?_⟩
  · rw [hC, card_pullP hP2 hT (comap_mono (zpowers_le.2 hqcT)),
      card_comap_eq q _ (zpowers_le.2 (hqsurj _ (T0_le_S hqcT))), Nat.card_zpowers, orderOf_qc,
      Nat.card_congr ζ.toEquiv]
  · rw [hC] at hw
    obtain ⟨hwP, hwH⟩ := mem_pullP.1 hw
    have hbot : ∀ {u : G} (hu : u ∈ P), q (jq K ⟨u, hP.1 hu⟩) = 1 → u = 1 := by
      intro u hu hu1
      have huZ : u ∈ P ⊓ zStarIn K := by
        refine ⟨hu, (mem_zStarIn_iff (hP.1 hu)).2 ?_⟩
        rw [← hqker, MonoidHom.mem_ker]
        exact hu1
      rw [hZ1] at huZ
      exact (mem_bot.mp huZ)
    rcases eq_one_or_eq_of_mem_zpowers hc4 hwH with h1 | h1
    · refine ⟨1, ⟨one_mem _, one_mem _⟩, ?_⟩
      rw [hbot hwP h1]
      group
    · obtain ⟨v, hvP, hvK, hv⟩ := exists_over hQ hT (tg_mem_T0 8 (by norm_num))
      have hv0 : q (jq K ⟨v, hP.1 hvP⟩) ∈ Z0 := by
        rw [show (⟨v, hP.1 hvP⟩ : K) = ⟨v, hvK⟩ from rfl, hv]
        exact mem_Z0.2 ⟨8, by simp, rfl⟩
      refine ⟨v, ⟨hvP, (mem_centralizer_P_iff hP hQ hk2 hT hvP).2 hv0⟩, ?_⟩
      have hcP : v⁻¹ * x⁻¹ * v * x ∈ P := by
        have := P.mul_mem (P.inv_mem hvP) (conj_mem_of_mem_normalizer hxP hvP)
        rwa [show v⁻¹ * (x⁻¹ * v * x) = v⁻¹ * x⁻¹ * v * x by group] at this
      have hq8 : q (jq K ⟨v⁻¹ * x⁻¹ * v * x, hP.1 hcP⟩) = wordPerm (tg 4) := by
        have e1 : (⟨v⁻¹ * x⁻¹ * v * x, hP.1 hcP⟩ : K) = (⟨v, hvK⟩ : K)⁻¹ *
            ⟨x⁻¹ * v * x, hP.1 (conj_mem_of_mem_normalizer hxP hvP)⟩ := Subtype.ext (by
          show v⁻¹ * x⁻¹ * v * x = v⁻¹ * (x⁻¹ * v * x)
          group)
        rw [e1, map_mul, map_mul, map_inv, map_inv, hxq hvP,
          show (⟨v, hP.1 hvP⟩ : K) = ⟨v, hvK⟩ from rfl, hv, unit_parts.2.2.2]
        group
      have hdiff : (v⁻¹ * x⁻¹ * v * x)⁻¹ * w = 1 := by
        refine hbot (P.mul_mem (P.inv_mem hcP) hwP) ?_
        have e1 : (⟨(v⁻¹ * x⁻¹ * v * x)⁻¹ * w, hP.1 (P.mul_mem (P.inv_mem hcP) hwP)⟩ : K) =
            (⟨v⁻¹ * x⁻¹ * v * x, hP.1 hcP⟩ : K)⁻¹ * ⟨w, hP.1 hwP⟩ := rfl
        rw [e1, map_mul, map_mul, map_inv, map_inv, hq8, h1, inv_mul_cancel]
      exact (inv_mul_eq_one.mp hdiff)

end CFSG.ComponentClassification.GrSLit.L34Facts
