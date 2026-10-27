module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YGomiBasic

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Gomi6Data

variable {A V C₀ C₁ : Subgroup G} {t u : G} (h : Gomi6Data A V C₀ C₁ t u)

include h

theorem hyp_quot :
    IsQuotIso (normIn (centralizer (V : Set G)) (A ⊔ V))
      (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V) (Equiv.Perm (Fin 6)) := by
  change IsQuotIso (centralizer (V : Set G) ⊓ normalizer ((A ⊔ V : Subgroup G) : Set G))
    (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V) (Equiv.Perm (Fin 6))
  obtain ⟨hK_le_N, φ, hφsurj, hφker⟩ := h.four1
  let hle : centralizer (V : Set G) ⊓ normalizer ((A ⊔ V : Subgroup G) : Set G) ≤
      normalizer ((A ⊔ V : Subgroup G) : Set G) := inf_le_right
  let φ' : ↥(centralizer (V : Set G) ⊓ normalizer ((A ⊔ V : Subgroup G) : Set G)) →*
      Equiv.Perm (Fin 6) := φ.comp (Subgroup.inclusion hle)
  refine ⟨?_, φ', ?_, ?_⟩
  · intro x hx
    obtain ⟨hxGh, hxK⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨hxGh, hK_le_N hxK⟩
  · intro σ
    obtain ⟨n, hn⟩ := hφsurj σ
    have hnV : (n : G) ∈ normalizer (V : Set G) := h.N_AV_le n.2
    rcases h.mem_cent_or_mul_t hnV with hcent | hmul
    · refine ⟨⟨(n : G), Subgroup.mem_inf.mpr ⟨hcent, n.2⟩⟩, ?_⟩
      have hinc : Subgroup.inclusion hle
          (⟨(n : G), Subgroup.mem_inf.mpr ⟨hcent, n.2⟩⟩ :
            ↥(centralizer (V : Set G) ⊓
              normalizer ((A ⊔ V : Subgroup G) : Set G))) = n :=
        Subtype.ext (Subgroup.coe_inclusion hle _)
      calc φ' ⟨(n : G), Subgroup.mem_inf.mpr ⟨hcent, n.2⟩⟩
          = φ (Subgroup.inclusion hle ⟨(n : G), Subgroup.mem_inf.mpr ⟨hcent, n.2⟩⟩) := rfl
        _ = φ n := congrArg φ hinc
        _ = σ := hn
    · let y : ↥(normalizer ((A ⊔ V : Subgroup G) : Set G)) :=
        ⟨t, h.t_mem_normalizer_AV⟩
      have hyker : y ∈ φ.ker := by
        rw [hφker, Subgroup.mem_subgroupOf]
        exact h.t_mem_K
      have hyone : φ y = 1 := MonoidHom.mem_ker.mp hyker
      have hmulN : (n : G) * t ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) :=
        mul_mem n.2 h.t_mem_normalizer_AV
      refine ⟨⟨(n : G) * t, Subgroup.mem_inf.mpr ⟨hmul, hmulN⟩⟩, ?_⟩
      have hinc : Subgroup.inclusion hle
          (⟨(n : G) * t, Subgroup.mem_inf.mpr ⟨hmul, hmulN⟩⟩ :
            ↥(centralizer (V : Set G) ⊓
              normalizer ((A ⊔ V : Subgroup G) : Set G))) = n * y := by
        apply Subtype.ext
        rw [Subgroup.coe_inclusion hle]
        rfl
      calc φ' ⟨(n : G) * t, Subgroup.mem_inf.mpr ⟨hmul, hmulN⟩⟩
          = φ (Subgroup.inclusion hle
              ⟨(n : G) * t, Subgroup.mem_inf.mpr ⟨hmul, hmulN⟩⟩) := rfl
        _ = φ (n * y) := congrArg φ hinc
        _ = φ n * φ y := map_mul φ n y
        _ = σ * 1 := by rw [hn, hyone]
        _ = σ := mul_one σ
  · apply Subgroup.ext
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx1
      have hx1' : φ (Subgroup.inclusion hle x) = 1 := hx1
      have hxker : Subgroup.inclusion hle x ∈ φ.ker := MonoidHom.mem_ker.mpr hx1'
      rw [hφker, Subgroup.mem_subgroupOf] at hxker
      have hxN : (x : G) ∈ centralizer (V : Set G) ∧
          (x : G) ∈ normalizer ((A ⊔ V : Subgroup G) : Set G) :=
        Subgroup.mem_inf.mp x.2
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr
        ⟨hxN.1, by simpa only [Subgroup.coe_inclusion hle] using hxker⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hxK : (x : G) ∈ centralizerSection (A ⊔ V) V :=
        (Subgroup.mem_inf.mp hx).2
      have hxker : Subgroup.inclusion hle x ∈ φ.ker := by
        rw [hφker, Subgroup.mem_subgroupOf]
        simpa only [Subgroup.coe_inclusion hle] using hxK
      rw [MonoidHom.mem_ker] at hxker
      exact hxker

theorem hyp_quot6 :
    IsQuotIso (centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V)
      (centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V ⊓
        (centralizer (V : Set G) ⊓ centralizerSection (A ⊔ V) V)) ↥blockStab := by
  obtain ⟨hK_le_N3, φ₃, hφ₃surj, hφ₃ker⟩ := h.four3
  have hcs_le : centralizerSection (V ⊔ zpowers t) V ≤ normalizer (C₀ : Set G) := by
    rw [h.C0_eq]
    exact fun x hx => hx.1
  have hD : centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V ≤
      normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V :=
    fun x hx => Subgroup.mem_sup_left (hcs_le hx.2)
  let φ' : ↥(centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V) →* ↥blockStab :=
    φ₃.comp (Subgroup.inclusion hD)
  refine ⟨?_, φ', ?_, ?_⟩
  · exact inf_le_left
  · intro σ
    obtain ⟨n, hn⟩ := hφ₃surj σ
    have hXle : normalizer (C₀ : Set G) ≤ normalizer ((A ⊔ V : Subgroup G) : Set G) :=
      h.N_C0_le.trans h.N_C1_le
    obtain ⟨m, hmX, k, hkK, hnk⟩ :=
      h.mem_sup_K (X := normalizer (C₀ : Set G)) hXle n.2
    have hm_N3 : m ∈ normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V :=
      Subgroup.mem_sup_left hmX
    have hk_N3 : k ∈ normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V :=
      Subgroup.mem_sup_right hkK
    have hn_eq : n =
        (⟨m, hm_N3⟩ : ↥(normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)) *
          ⟨k, hk_N3⟩ := by
      apply Subtype.ext
      simpa using hnk
    have hk_ker : (⟨k, hk_N3⟩ :
        ↥(normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)) ∈ φ₃.ker := by
      rw [hφ₃ker, Subgroup.mem_subgroupOf]
      exact hkK
    have hk_one : φ₃ ⟨k, hk_N3⟩ = 1 := MonoidHom.mem_ker.mp hk_ker
    have hφm : φ₃ ⟨m, hm_N3⟩ = σ := by
      calc φ₃ ⟨m, hm_N3⟩
          = φ₃ ⟨m, hm_N3⟩ * 1 := (mul_one _).symm
        _ = φ₃ ⟨m, hm_N3⟩ * φ₃ ⟨k, hk_N3⟩ := by rw [hk_one]
        _ = φ₃ (⟨m, hm_N3⟩ * ⟨k, hk_N3⟩) := (map_mul φ₃ _ _).symm
        _ = φ₃ n := by rw [hn_eq]
        _ = σ := hn
    have hmV : m ∈ normalizer (V : Set G) := h.N_AV_le (hXle hmX)
    rcases h.mem_cent_or_mul_t hmV with hmGh | hmtGh
    · have hmD : m ∈ centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V := by
        rw [h.cent_inf_cs_eq]
        exact Subgroup.mem_inf.mpr ⟨hmGh, hmX⟩
      refine ⟨⟨m, hmD⟩, ?_⟩
      have hinc : Subgroup.inclusion hD (⟨m, hmD⟩ :
          ↥(centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V)) =
          (⟨m, hm_N3⟩ :
            ↥(normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)) :=
        Subtype.ext (Subgroup.coe_inclusion hD _)
      calc φ' ⟨m, hmD⟩
          = φ₃ (Subgroup.inclusion hD ⟨m, hmD⟩) := rfl
        _ = φ₃ ⟨m, hm_N3⟩ := congrArg φ₃ hinc
        _ = σ := hφm
    · have hmtX : m * t ∈ normalizer (C₀ : Set G) := mul_mem hmX h.t_mem_normalizer_C0
      have hmtD : m * t ∈ centralizer (V : Set G) ⊓
          centralizerSection (V ⊔ zpowers t) V := by
        rw [h.cent_inf_cs_eq]
        exact Subgroup.mem_inf.mpr ⟨hmtGh, hmtX⟩
      have hmt_N3 : m * t ∈ normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V :=
        Subgroup.mem_sup_left hmtX
      have ht_N3 : t ∈ normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V :=
        Subgroup.mem_sup_left h.t_mem_normalizer_C0
      have ht_ker : (⟨t, ht_N3⟩ :
          ↥(normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)) ∈ φ₃.ker := by
        rw [hφ₃ker, Subgroup.mem_subgroupOf]
        exact h.t_mem_K
      refine ⟨⟨m * t, hmtD⟩, ?_⟩
      have hinc : Subgroup.inclusion hD (⟨m * t, hmtD⟩ :
          ↥(centralizer (V : Set G) ⊓ centralizerSection (V ⊔ zpowers t) V)) =
          (⟨m * t, hmt_N3⟩ :
            ↥(normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)) :=
        Subtype.ext (Subgroup.coe_inclusion hD _)
      have hmul_eq : (⟨m * t, hmt_N3⟩ :
          ↥(normalizer (C₀ : Set G) ⊔ centralizerSection (A ⊔ V) V)) =
          ⟨m, hm_N3⟩ * ⟨t, ht_N3⟩ :=
        Subtype.ext rfl
      calc φ' ⟨m * t, hmtD⟩
          = φ₃ (Subgroup.inclusion hD ⟨m * t, hmtD⟩) := rfl
        _ = φ₃ ⟨m * t, hmt_N3⟩ := congrArg φ₃ hinc
        _ = φ₃ (⟨m, hm_N3⟩ * ⟨t, ht_N3⟩) := congrArg φ₃ hmul_eq
        _ = φ₃ ⟨m, hm_N3⟩ * φ₃ ⟨t, ht_N3⟩ := map_mul φ₃ _ _
        _ = σ := by rw [MonoidHom.mem_ker.mp ht_ker, mul_one, hφm]
  · apply Subgroup.ext
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx1
      have hx1' : φ₃ (Subgroup.inclusion hD x) = 1 := hx1
      have hxker : Subgroup.inclusion hD x ∈ φ₃.ker := MonoidHom.mem_ker.mpr hx1'
      rw [hφ₃ker, Subgroup.mem_subgroupOf] at hxker
      have hxGh : (x : G) ∈ centralizer (V : Set G) := (Subgroup.mem_inf.mp x.2).1
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr
        ⟨x.2, Subgroup.mem_inf.mpr
          ⟨hxGh, by simpa only [Subgroup.coe_inclusion hD] using hxker⟩⟩
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hxK : (x : G) ∈ centralizerSection (A ⊔ V) V :=
        (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).2).2
      have hxker : Subgroup.inclusion hD x ∈ φ₃.ker := by
        rw [hφ₃ker, Subgroup.mem_subgroupOf]
        simpa only [Subgroup.coe_inclusion hD] using hxK
      rw [MonoidHom.mem_ker] at hxker
      exact hxker

theorem hyp_even :
    Even ((normIn (centralizer (V : Set G)) (A ⊔ V)).relIndex (centralizer (V : Set G))) := by
  let NC : Subgroup G := centralizer (V : Set G) ⊓ normalizer ((A ⊔ V : Subgroup G) : Set G)
  change Even (NC.relIndex (centralizer (V : Set G)))
  obtain ⟨k, hk⟩ := h.four4
  have hNC_le_X1 : NC ≤ normalizer ((A ⊔ V : Subgroup G) : Set G) :=
    fun _ hx => (Subgroup.mem_inf.mp hx).2
  have hNC_le_Gh : NC ≤ centralizer (V : Set G) :=
    fun _ hx => (Subgroup.mem_inf.mp hx).1
  have hX1_le_X2 : normalizer ((A ⊔ V : Subgroup G) : Set G) ≤ normalizer (V : Set G) :=
    h.N_AV_le
  have hGh_le_X2 : centralizer (V : Set G) ≤ normalizer (V : Set G) :=
    Subgroup.centralizer_le_normalizer (V : Set G)
  have h1 : NC.relIndex (normalizer ((A ⊔ V : Subgroup G) : Set G)) = 2 :=
    h.relIndex_cent (X := normalizer ((A ⊔ V : Subgroup G) : Set G)) h.N_AV_le
      h.t_mem_normalizer_AV
  have h2 : (centralizer (V : Set G)).relIndex (normalizer (V : Set G)) = 2 := by
    have hh := h.relIndex_cent (X := normalizer (V : Set G)) le_rfl h.t_mem_normalizer_V
    rwa [inf_eq_left.mpr hGh_le_X2] at hh
  have htower1 : NC.relIndex (normalizer ((A ⊔ V : Subgroup G) : Set G)) *
      (normalizer ((A ⊔ V : Subgroup G) : Set G)).relIndex (normalizer (V : Set G)) =
      NC.relIndex (normalizer (V : Set G)) :=
    Subgroup.relIndex_mul_relIndex NC (normalizer ((A ⊔ V : Subgroup G) : Set G))
      (normalizer (V : Set G)) hNC_le_X1 hX1_le_X2
  have htower2 : NC.relIndex (centralizer (V : Set G)) *
      (centralizer (V : Set G)).relIndex (normalizer (V : Set G)) =
      NC.relIndex (normalizer (V : Set G)) :=
    Subgroup.relIndex_mul_relIndex NC (centralizer (V : Set G)) (normalizer (V : Set G))
      hNC_le_Gh hGh_le_X2
  rw [h1] at htower1
  rw [h2] at htower2
  rw [← htower2] at htower1
  rw [hk] at htower1
  exact ⟨k, by omega⟩

end Gomi6Data

end CFSG.OddStandard.HigherRank.YamadaG23
