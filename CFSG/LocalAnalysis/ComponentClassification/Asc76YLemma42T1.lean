module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YLemma42S4
public import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFacts
import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingConjugate

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.Open

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem oddCoreIn_le_of_isSubnormal {X M : Subgroup G} (hX : CFSG.Assembly.IsSubnormal X M) :
    oddCoreIn X ≤ oddCoreIn M := by
  induction hX with
  | refl => exact le_rfl
  | step hHM hn _ ih =>
    refine le_trans ?_ ih
    exact le_oddCoreIn_of_le_normalizer ((oddCoreIn_le _).trans hHM)
      (((normal_subgroupOf_iff_le_normalizer hHM).mp hn).trans
        (normalizer_le_normalizer_oddCoreIn _)) (odd_card_oddCoreIn _)

theorem oddCoreIn_top_eq_bot (hO : standardComponentOddCore G = ⊥) :
    oddCoreIn (⊤ : Subgroup G) = ⊥ := by
  have h1 := CFSG.ComponentClassification.Asc76.L26.oddCore_map_mulEquiv
    (Subgroup.topEquiv (G := G))
  have h2 : CFSG.Assembly.oddCore G = ⊥ := hO
  rw [h2, eq_bot_iff] at h1
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  have := h1 ⟨x, hx, rfl⟩
  rw [mem_bot] at this ⊢
  simpa using this

theorem standardComponentOddCore_eq_bot_of_isSubnormal (hO : standardComponentOddCore G = ⊥)
    {X : Subgroup G} (hX : CFSG.Assembly.IsSubnormal X ⊤) :
    standardComponentOddCore X = ⊥ := by
  have h1 := (oddCoreIn_le_of_isSubnormal hX).trans (oddCoreIn_top_eq_bot hO).le
  rw [le_bot_iff, oddCoreIn, map_eq_bot_iff_of_injective _ X.subtype_injective] at h1
  exact h1

theorem exists_isSubnormal_normalClosure (K : Subgroup G) :
    ∃ X : Subgroup G, K ≤ X ∧ CFSG.Assembly.IsSubnormal X ⊤ ∧
      normalClosure ((K.subgroupOf X : Subgroup X) : Set X) = ⊤ := by
  classical
  set S : Set (Subgroup G) := {X | K ≤ X ∧ CFSG.Assembly.IsSubnormal X ⊤}
  have hS : S.Nonempty := ⟨⊤, le_top, CFSG.Assembly.IsSubnormal.refl ⊤⟩
  obtain ⟨X, ⟨hKX, hX⟩, hmin⟩ := WellFounded.has_min wellFounded_lt S hS
  refine ⟨X, hKX, hX, ?_⟩
  set N := normalClosure ((K.subgroupOf X : Subgroup X) : Set X)
  by_contra hN
  set Y := N.map X.subtype
  have hYX : Y ≤ X := map_subtype_le N
  have hKY : K ≤ Y := by
    intro k hk
    exact ⟨⟨k, hKX hk⟩, subset_normalClosure (show (⟨k, hKX hk⟩ : X) ∈ K.subgroupOf X from hk),
      rfl⟩
  have hYsub : Y.subgroupOf X = N := by
    rw [subgroupOf, comap_map_eq_self_of_injective X.subtype_injective]
  have hYn : (Y.subgroupOf X).Normal := by rw [hYsub]; exact normalClosure_normal
  have hYs : CFSG.Assembly.IsSubnormal Y ⊤ := CFSG.Assembly.IsSubnormal.step hYX hYn hX
  have hlt : Y < X := lt_of_le_of_ne hYX fun h => hN (by
    rw [← hYsub, h, subgroupOf_self])
  exact hmin Y ⟨hKY, hYs⟩ hlt

omit [Finite G] in
theorem card_subgroupOf_of_le {A X : Subgroup G} (h : A ≤ X) :
    Nat.card (A.subgroupOf X) = Nat.card A :=
  Nat.card_congr (subgroupOfEquivOfLe h).toEquiv

omit [Finite G] in
theorem tightlyEmbedded_subgroupOf {K X : Subgroup G} (hK : TightlyEmbedded K) (hKX : K ≤ X) :
    TightlyEmbedded (K.subgroupOf X) :=
  StandardSubgroupAPI.tightlyEmbedded_subgroupOf hKX hK

omit [Finite G] in
theorem rightConjugate_le_of_le {K X : Subgroup G} (hKX : K ≤ X) {g : G} (hg : g ∈ X) :
    AschbacherTightEmbedding.rightConjugate K g ≤ X := by
  intro x hx
  rw [mem_rightConjugate_iff] at hx
  have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
  rw [this]
  exact mul_mem (mul_mem (inv_mem hg) (hKX hx)) hg

theorem isSylowOf_subgroupOf {S K X : Subgroup G} (hS : IsSylowOf 2 S K) (hKX : K ≤ X) :
    IsSylowOf 2 (S.subgroupOf X) (K.subgroupOf X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← isSylowOf_map_subtype_iff X, map_subgroupOf_eq_of_le (hS.le.trans hKX),
    map_subgroupOf_eq_of_le hKX]
  exact hS

theorem sylowNormalizes_subgroupOf {K X : Subgroup G} (hKX : K ≤ X)
    (hstar : ∀ g : G, Even (Nat.card
      (AschbacherTightEmbedding.rightConjugate K g ⊓ normalizer (K : Set G) : Subgroup G)) →
      SylowNormalizes (AschbacherTightEmbedding.rightConjugate K g) K) (g : X)
    (heven : Even (Nat.card (AschbacherTightEmbedding.rightConjugate (K.subgroupOf X) g ⊓
      normalizer ((K.subgroupOf X : Subgroup X) : Set X) : Subgroup X))) :
    SylowNormalizes (AschbacherTightEmbedding.rightConjugate (K.subgroupOf X) g)
      (K.subgroupOf X) := by
  have hKgX := rightConjugate_le_of_le hKX g.2
  rw [← rightConjugate_subgroupOf, ← subgroupOf_normalizer_eq hKX, ← inf_subgroupOf',
    card_subgroupOf_of_le (inf_le_left.trans hKgX)] at heven
  obtain ⟨S, hS, hSN⟩ := hstar g heven
  refine ⟨S.subgroupOf X, ?_, ?_⟩
  · rw [← rightConjugate_subgroupOf]
    exact isSylowOf_subgroupOf hS hKgX
  · rw [← subgroupOf_normalizer_eq hKX]
    exact fun x hx => hSN hx

theorem not_isSzOrU3_of_isDihedralRot {X : Type} [Group X] [Finite X] {U R : Subgroup X}
    (hU : IsDihedralRot U R) : ¬ CFSG.ComponentClassification.Asc76.IsSzOrU3 X := by
  intro hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hRP⟩ := hU.isPGroup.exists_le_sylow
  obtain ⟨s, hsR, hsU⟩ := hU.exists_not_mem
  obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
  have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
  have hss : s * s = 1 := hU.mul_self s hsR hsU
  have h1 := CFSG.ComponentClassification.Asc76X.benderFacts.involution_center X hX P s
    (hRP hsR) (by rw [pow_two]; exact hss)
  have h2 := (mem_centralizer_iff.mp h1) (s * ρ) (hRP (mul_mem hsR (hU.le hρU)))
  have h3 := hU.conj_eq s hsR hsU ρ hρU
  have h4 : ρ⁻¹ = ρ := by
    calc ρ⁻¹ = s * ρ * s⁻¹ := h3.symm
      _ = s * ρ * s := by rw [inv_eq_of_mul_eq_one_right hss]
      _ = s * (s * ρ) := h2
      _ = ρ := by rw [← mul_assoc, hss, one_mul]
  apply hU.gen_mul_self_ne_one hρo
  calc ρ * ρ = ρ⁻¹ * ρ := by rw [h4]
    _ = 1 := inv_mul_cancel ρ

theorem normal_of_star (h1 : Asc76Theorem1) (hΩ : Assumption41 Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hstar : ∀ g : G, Even (Nat.card
      (AschbacherTightEmbedding.rightConjugate K g ⊓ normalizer (K : Set G) : Subgroup G)) →
      SylowNormalizes (AschbacherTightEmbedding.rightConjugate K g) K) : K.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨X, hKX, hX, hcl⟩ := exists_isSubnormal_normalClosure K
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  have hU' := hU.subgroupOf (hR.le.trans hKX)
  rcases h1 X (K.subgroupOf X) (tightlyEmbedded_subgroupOf (Assumption41.tightlyEmbedded hΩ hK)
      hKX) hcl (by rw [oUpperTwoPrime_subgroupOf hKX, hΩ.perfect K hK])
      (standardComponentOddCore_eq_bot_of_isSubnormal hΩ.oddCore hX)
      (sylowNormalizes_subgroupOf hKX hstar) (R.subgroupOf X) (isSylowOf_subgroupOf hR hKX)
      hU'.one_lt_pRank with hKtop | hab | ⟨hsz, -⟩
  · have hKeq : K = X := le_antisymm hKX fun x hx => by
      have : (⟨x, hx⟩ : X) ∈ K.subgroupOf X := hKtop ▸ mem_top _
      exact this
    exact normal_of_isSubnormal hΩ hK (hKeq ▸ hX)
  · exact absurd hab.1 hU'.not_isMulCommutative
  · exact absurd hsz (not_isSzOrU3_of_isDihedralRot hU')

theorem normal_of_not_twoNil (h22 : Asc76Lemma22) (h1 : Asc76Theorem1) (hΩ : Assumption41 Ω)
    {K : Subgroup G} (hK : K ∈ Ω) (hlayer : twoPrimeLayerIn K = oddCoreIn K)
    (hnil : ∀ R, IsSylowOf 2 R K → ¬ IsTwoNil K R) : K.Normal :=
  normal_of_star h1 hΩ hK fun g heven =>
    sylowNormalizes_of_not_twoNil h22 hΩ hK (hΩ.conj_mem K hK g) hlayer hnil heven

end CFSG.ComponentClassification.Asc76.Sec4
