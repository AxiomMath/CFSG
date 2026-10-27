module

public import CFSG.LocalAnalysis.OddStandard.ONanIdL34
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowLift
public import CFSG.Goldschmidt75.WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverInvModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicGen
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsStandard
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.Walter.J1

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.PSL3Four CFSG.LieType.Multipliers.L34
open scoped commutatorElement

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

local notation "𝔵" => xel v1 v2 v3
local notation "𝔷" => invRep v1 v2 v3 s t 0
local notation "𝐉" => centralizer ({xel v1 v2 v3} : Set G)

theorem center_Cx
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    center 𝐉 = zpowers (zIn 𝔵) := by
  have hS := isSimpleGroup_of_lieModel_PSL (D.lieModel_quot hF hone hbal)
  apply le_antisymm
  · intro c hc
    have hcen : πQ 𝔵 c ∈ center (KQ 𝔵) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := πQ_surjective 𝔵 y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc y']
    have hbot : center (KQ 𝔵) = ⊥ := by
      rcases (inferInstance : (center (KQ 𝔵)).Normal).eq_bot_or_eq_top with h | h
      · exact h
      · exfalso
        have h1 : πQ 𝔵 ⟨t, D.t_mem_Cx⟩ ∈ center (KQ 𝔵) := h ▸ mem_top _
        have h2 := Subgroup.mem_center_iff.1 h1 (πQ 𝔵 ⟨v1, D.v1_mem_Cx⟩)
        rw [← map_mul, ← map_mul, πQ_eq_iff] at h2
        have hv : ((⟨v1, D.v1_mem_Cx⟩ * ⟨t, D.t_mem_Cx⟩ : 𝐉) : G)⁻¹ *
            ((⟨t, D.t_mem_Cx⟩ * ⟨v1, D.v1_mem_Cx⟩ : 𝐉) : G) =
            D.E.φ ((gen 0 * gen 4)⁻¹ * (gen 4 * gen 0)) := by
          show (v1 * t)⁻¹ * (t * v1) = _
          simp only [map_mul, map_inv, AlpEmb.φ_t, AlpEmb.φ_v1]
        rw [hv] at h2
        have hne : (gen 0 * gen 4)⁻¹ * (gen 4 * gen 0) ≠ 1 ∧
            (gen 0 * gen 4)⁻¹ * (gen 4 * gen 0) ≠ xE ∧
            (gen 0 * gen 4)⁻¹ * (gen 4 * gen 0) ≠ zc ∧
            (gen 0 * gen 4)⁻¹ * (gen 4 * gen 0) ≠ xE⁻¹ := by decide
        exact D.notMem_zpowers_x_of_phi hne h2
    rw [hbot, mem_bot, πQ_eq_one_iff] at hcen
    exact (mem_zpowers_zIn_iff c).2 hcen
  · exact zpowers_le.2 (Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (mem_centralizer_singleton_iff.1 y.2))

omit [Finite G] D in
theorem fusionOddCore_eq_pPrimeCore (X : Type*) [Group X] :
    CFSG.Open.fusionOddCore X = pPrimeCore 2 X := by
  unfold CFSG.Open.fusionOddCore pPrimeCore
  congr 1
  ext K
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem fusionZStar_Cx (hone : OneClass G) (hbal : Balanced G) :
    CFSG.Open.fusionZStar 𝐉 = center 𝐉 := by
  have hO : CFSG.Open.fusionOddCore 𝐉 = ⊥ := by
    rw [fusionOddCore_eq_pPrimeCore]
    exact D.pPrimeCore_Cx_eq_bot hone hbal
  ext c
  show (QuotientGroup.mk c : 𝐉 ⧸ CFSG.Open.fusionOddCore 𝐉) ∈
      center (𝐉 ⧸ CFSG.Open.fusionOddCore 𝐉) ↔ c ∈ center 𝐉
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h y
    have h1 := h (QuotientGroup.mk y)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hO, mem_bot,
      inv_mul_eq_one] at h1
    exact h1
  · intro h y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h y']

theorem commutator_Cx
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) : ⁅𝐉, 𝐉⁆ = 𝐉 :=
  Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr (D.isPerfect_Cx hF hone hbal))

theorem isL34Type_Cx
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    IsL34Type (𝐉 ⧸ CFSG.Open.fusionZStar 𝐉) := by
  have he : CFSG.Open.fusionZStar 𝐉 = zpowers (zIn 𝔵) := by
    rw [D.fusionZStar_Cx hone hbal, D.center_Cx hF hone hbal]
  exact lieModel_PSL_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq he).symm
    (D.lieModel_quot hF hone hbal)

theorem normalizer_Cx_le
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    normalizer (𝐉 : Set G) ≤ centralizer ({𝔷} : Set G) := by
  intro n hn
  have hxJ : 𝔵 ∈ 𝐉 := mem_centralizer_singleton_iff.2 rfl
  have hnx : n * 𝔵 * n⁻¹ ∈ 𝐉 := (mem_normalizer_iff.1 hn 𝔵).1 hxJ
  have hcen : (⟨n * 𝔵 * n⁻¹, hnx⟩ : 𝐉) ∈ center 𝐉 := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    show (y : G) * (n * 𝔵 * n⁻¹) = n * 𝔵 * n⁻¹ * y
    have hy' : n⁻¹ * y * n ∈ 𝐉 := by
      have := (mem_normalizer_iff.1 (inv_mem hn) y).1 y.2
      rwa [inv_inv] at this
    have h := mem_centralizer_singleton_iff.1 hy'
    calc (y : G) * (n * 𝔵 * n⁻¹) = n * (n⁻¹ * y * n * 𝔵) * n⁻¹ := by group
      _ = n * (𝔵 * (n⁻¹ * y * n)) * n⁻¹ := by rw [h]
      _ = n * 𝔵 * n⁻¹ * y := by group
  rw [D.center_Cx hF hone hbal] at hcen
  have hm : n * 𝔵 * n⁻¹ ∈ zpowers 𝔵 := (mem_zpowers_zIn_iff _).1 hcen
  have hsq : n * 𝔵 * n⁻¹ * (n * 𝔵 * n⁻¹) = 𝔷 := by
    rcases D.mem_zpowers_x.1 hm with h | h | h | h
    · exfalso
      have : 𝔵 = 1 := by
        calc 𝔵 = n⁻¹ * (n * 𝔵 * n⁻¹) * n := by group
          _ = 1 := by rw [h]; group
      exact D.x_notMem_zpowers_z (this ▸ one_mem _)
    · rw [h, D.xel_sq]
    · exfalso
      have h2 : (n * 𝔵 * n⁻¹) * (n * 𝔵 * n⁻¹) = 1 := by rw [h]; exact D.rep_sq 0
      have h3 : 𝔵 * 𝔵 = 1 := by
        calc 𝔵 * 𝔵 = n⁻¹ * ((n * 𝔵 * n⁻¹) * (n * 𝔵 * n⁻¹)) * n := by group
          _ = 1 := by rw [h2]; group
      rw [D.xel_sq] at h3
      exact D.rep_ne_one 0 h3
    · rw [h, ← mul_inv_rev, D.xel_sq]
      exact inv_eq_of_mul_eq_one_right (D.rep_sq 0)
  rw [mem_centralizer_singleton_iff]
  calc n * 𝔷 = n * (𝔵 * 𝔵) * n⁻¹ * n := by rw [D.xel_sq]; group
    _ = n * 𝔵 * n⁻¹ * (n * 𝔵 * n⁻¹) * n := by group
    _ = 𝔷 * n := by rw [hsq]

theorem Cz_le_normalizer_Cx (hone : OneClass G) (hbal : Balanced G) :
    centralizer ({𝔷} : Set G) ≤ normalizer (𝐉 : Set G) := by
  intro c hc
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => D.conj_mem_Cx hone hbal hc hy
  · intro hy
    have := D.conj_mem_Cx hone hbal (inv_mem hc) hy
    simpa [mul_assoc] using this

theorem isSylowTwoIn_P_normalizer
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    IsSylowTwoIn (alpP v1 v2 v3 s t) (normalizer (𝐉 : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := D.isSylowOf_P_centralizer_z.of_le (D.P_le_Cz.trans (D.Cz_le_normalizer_Cx hone hbal))
    (D.normalizer_Cx_le hF hone hbal)
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  exact ⟨h.le, Q, hQ⟩

theorem st_mem_normalizer (hone : OneClass G) (hbal : Balanced G) :
    s * t ∈ normalizer (𝐉 : Set G) :=
  D.Cz_le_normalizer_Cx hone hbal D.st_mem_Cz

theorem exists_frame
    (hF : ThmC.ThmCFull) (hone : OneClass G) (hbal : Balanced G) :
    ∃ (q : Jhat 𝐉 →* Equiv.Perm (Fin 42)) (l : Cover →* Jhat 𝐉), IsQSetting q l ∧
      (∀ e, q e ∈ T0 ↔ ∃ p ∈ alpP v1 v2 v3 s t ⊓ 𝐉, ∃ hp : p ∈ 𝐉, jq 𝐉 ⟨p, hp⟩ = e) ∧
      ∃ ρ ∈ Sigma0, ∀ e, q (betaHat 𝐉 (D.st_mem_normalizer hone hbal) e) = ρ * q e * ρ⁻¹ := by
  obtain ⟨q, l, hq, hT, hρ⟩ := exists_frame_Sigma0 (D.commutator_Cx hF hone hbal)
    (D.isL34Type_Cx hF hone hbal) (D.isSylowTwoIn_P_normalizer hF hone hbal)
  exact ⟨q, l, hq, hT, hρ (s * t) (mul_mem s_mem_P t_mem_P)⟩

end FusCtx

end CFSG.OddStandard.ONanRec
