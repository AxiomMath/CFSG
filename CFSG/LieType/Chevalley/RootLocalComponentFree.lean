module

public import CFSG.LieType.Chevalley.RootWeightOptimalParabolic
public import CFSG.LieType.Chevalley.GraphFixedParabolicSelfCentralizing
public import CFSG.LocalAnalysis.ComponentInitial.ParabolicLocalCharacteristicTransfer
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTIBasic

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open Subgroup

namespace RootWeightDatum

variable {K : Type} [Field K]

@[expose] def radical
    : (D : RootWeightDatum K) → Set (Fin D.rank) → Subgroup (ModGL D.tag K)
  | ordinary τ, J => parabolicRadical τ K J
  | fixed t σ _, J => graphFixedParabolicRadical t K σ.toRingHom J

variable (D : RootWeightDatum K)

theorem radical_le_parabolic
    (J : Set (Fin D.rank)) : D.radical J ≤ D.parabolic J := by
  cases D with
  | ordinary τ => exact (parabolic_root_radical_Levi_factors τ K J).1
  | fixed t σ hσ =>
    obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
    exact h

theorem conj_mem_radical
    (J : Set (Fin D.rank)) {x : ModGL D.tag K} (hx : x ∈ D.parabolic J)
    {y : ModGL D.tag K} (hy : y ∈ D.radical J) : x * y * x⁻¹ ∈ D.radical J := by
  cases D with
  | ordinary τ =>
    exact (mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hx) y).1 hy
  | fixed t σ hσ =>
    obtain ⟨-, -, -, -, -, -, -, -, hle, hN, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
    have h := hN.conj_mem ⟨y, hle hy⟩ (mem_subgroupOf.2 hy) ⟨x, hx⟩
    exact mem_subgroupOf.1 h

theorem isPGroup_radical
    [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (J : Set (Fin D.rank)) :
    IsPGroup p (D.radical J) := by
  cases D with
  | ordinary τ => exact ((parabolic_root_radical_Levi_factors τ K J).2.2.2.2.2.2.2.2.2.2.2.2 p).2.1
  | fixed t σ hσ =>
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ :=
      diagram_fixed_parabolic_root_radical_Levi_factors t K σ J
    exact h p

theorem parabolic_inf_centralizer_le_radical
    {J : Set (Fin D.rank)} (hJ : J ≠ Set.univ) :
    D.parabolic J ⊓ centralizer (D.radical J : Set (ModGL D.tag K)) ≤ D.radical J := by
  cases D with
  | ordinary τ => exact (Chevalley_proper_parabolic_root_radical_self_centralizing τ K hJ).2
  | fixed t σ hσ => exact (diagram_fixed_proper_parabolic_root_radical_self_centralizing t K σ hJ).2

theorem not_isComponent_of_isCharacteristicP {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] (hchar : CFSG.IsCharacteristicP p H) (L : Subgroup H) :
    ¬ CFSG.IsComponent L :=
  CFSG.ComponentClassification.OutcomeLocal.not_isComponent_of_selfCentralizing
    (CFSG.pCore_normal (p := p) (G := H)) (CFSG.pCore_isPGroup (p := p) (G := H)) hchar L

theorem defining_characteristic_root_local_groups_component_free
    [Finite K] (p : ℕ)
    [Fact p.Prime] [CharP K p] (Q : Subgroup D.group) (hQp : IsPGroup p Q) (hQ : Q ≠ ⊥)
    (H : Subgroup D.group)
    (hH : H = normalizer (Q : Set D.group) ∨ H = centralizer (Q : Set D.group)) :
    CFSG.IsCharacteristicP p H ∧ ∀ L : Subgroup H, ¬ CFSG.IsComponent L := by
  have : Finite (ModGL D.tag K) := finite_modGL
  set Q₀ := Q.map D.group.subtype with hQ₀
  have hQ₀G : Q₀ ≤ D.group := map_subtype_le Q
  have hQ₀p : IsPGroup p Q₀ := hQp.of_equiv (Q.equivMapOfInjective _ D.group.subtype_injective)
  have hQ₀1 : Q₀ ≠ ⊥ := by
    intro h
    apply hQ
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : ModGL D.tag K) ∈ Q₀ := ⟨x, hx, rfl⟩
    rw [h, mem_bot] at h1
    rw [mem_bot]
    exact Subtype.ext h1
  obtain ⟨M, -, -, -, F, hFmax, -, ⟨g, hg, l, hl, hl1, hgl⟩, hdom, -⟩ :=
    D.root_p_subgroup_optimal_parabolic_containment p Q₀ hQ₀G hQ₀p hQ₀1
  obtain ⟨hJ, -, hNF, hstab, -⟩ := hdom g hg l hl hl1 hgl
  set J := D.face l with hJdef
  set ψ := (MulAut.conj g).toMonoidHom with hψ
  set P₀ := (D.parabolic J).map ψ with hP₀
  set U₀ := (D.radical J).map ψ with hU₀
  have hNP : ∀ x ∈ D.group, x ∈ normalizer (Q₀ : Set (ModGL D.tag K)) → x ∈ P₀ := by
    intro x hxG hxN
    have h1 : x ∈ {y : ModGL D.tag K | y ∈ D.group ∧ ∀ c : ℝ,
        (F c).map (y : Module.End K (RootModule D.tag K)) = F c} :=
      ⟨hxG, hNF x (mem_inf.2 ⟨hxG, hxN⟩)⟩
    rw [hstab] at h1
    exact h1
  have hP₀G : P₀ ≤ D.group := by
    rintro _ ⟨y, hy, rfl⟩
    exact D.group.mul_mem (D.group.mul_mem hg (D.parabolic_le_group J hy)) (D.group.inv_mem hg)
  have hU₀P₀ : U₀ ≤ P₀ := map_mono (D.radical_le_parabolic J)
  set P := P₀.subgroupOf D.group with hP
  set U := U₀.subgroupOf D.group with hU
  have hUP : U ≤ P := fun x hx => mem_subgroupOf.2 (hU₀P₀ (mem_subgroupOf.1 hx))
  have hUn : (U.subgroupOf P).Normal := by
    refine ⟨fun n hn x => ?_⟩
    rw [mem_subgroupOf, mem_subgroupOf] at hn ⊢
    obtain ⟨y, hy, hyn⟩ := hn
    obtain ⟨z, hz, hzx⟩ := mem_subgroupOf.1 x.2
    refine ⟨z * y * z⁻¹, D.conj_mem_radical J hz hy, ?_⟩
    change g * (z * y * z⁻¹) * g⁻¹ = ((x : D.group) : ModGL D.tag K) *
      ((n : D.group) : ModGL D.tag K) * ((x : D.group) : ModGL D.tag K)⁻¹
    change g * z * g⁻¹ = ((x : D.group) : ModGL D.tag K) at hzx
    change g * y * g⁻¹ = ((n : D.group) : ModGL D.tag K) at hyn
    rw [← hzx, ← hyn]
    group
  have hUp : IsPGroup p U := by
    have h1 : IsPGroup p U₀ := (D.isPGroup_radical p J).of_equiv
      ((D.radical J).equivMapOfInjective _ (MulAut.conj g).injective)
    exact h1.of_equiv (subgroupOfEquivOfLe (hU₀P₀.trans hP₀G)).symm
  have hCU : centralizer (U : Set D.group) ⊓ P ≤ U := by
    intro x hx
    obtain ⟨hxC, hxP⟩ := mem_inf.1 hx
    obtain ⟨y, hy, hyx⟩ := mem_subgroupOf.1 hxP
    change g * y * g⁻¹ = ((x : D.group) : ModGL D.tag K) at hyx
    have hyC : y ∈ D.parabolic J ⊓ centralizer (D.radical J : Set (ModGL D.tag K)) := by
      refine mem_inf.2 ⟨hy, mem_centralizer_iff.2 fun r hr => ?_⟩
      have hrU : g * r * g⁻¹ ∈ U₀ := ⟨r, hr, rfl⟩
      have hrG : g * r * g⁻¹ ∈ D.group := hU₀P₀.trans hP₀G hrU
      have h1 := mem_centralizer_iff.1 hxC ⟨_, hrG⟩ (mem_subgroupOf.2 hrU)
      have h2 : g * r * g⁻¹ * (g * y * g⁻¹) = g * y * g⁻¹ * (g * r * g⁻¹) := by
        rw [hyx]
        exact congrArg Subtype.val h1
      have h3 : g * (r * y) * g⁻¹ = g * (y * r) * g⁻¹ := by
        calc g * (r * y) * g⁻¹ = g * r * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * r * g⁻¹) := h2
          _ = g * (y * r) * g⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel h3)
    have hyU := D.parabolic_inf_centralizer_le_radical hJ hyC
    exact mem_subgroupOf.2 ⟨y, hyU, hyx⟩
  have hNQP : normalizer (Q : Set D.group) ≤ P := by
    intro x hx
    refine mem_subgroupOf.2 (hNP x x.2 ?_)
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨x * q * x⁻¹, (mem_normalizer_iff.1 hx q).1 hq, rfl⟩
    · rintro ⟨q, hq, hqy⟩
      have hyG : y ∈ D.group := by
        have : y = (x : ModGL D.tag K)⁻¹ * (q : ModGL D.tag K) * x := by
          rw [show (q : ModGL D.tag K) = x * y * (x : ModGL D.tag K)⁻¹ from hqy]
          group
        rw [this]
        exact D.group.mul_mem (D.group.mul_mem (D.group.inv_mem x.2) q.2) x.2
      refine ⟨⟨y, hyG⟩, (mem_normalizer_iff.1 hx ⟨y, hyG⟩).2 ?_, rfl⟩
      have : x * ⟨y, hyG⟩ * x⁻¹ = q := Subtype.ext hqy.symm
      rw [this]
      exact hq
  have hQP : Q ≤ P := le_normalizer.trans hNQP
  have hCN : centralizer (Q : Set D.group) ≤ normalizer (Q : Set D.group) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [← mem_centralizer_iff.1 hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have hcomm := mem_centralizer_iff.1 hx _ hy
      have h1 : x * y = x * (x * y * x⁻¹) :=
        calc x * y = x * y * x⁻¹ * x := by group
          _ = x * (x * y * x⁻¹) := hcomm
      rw [mul_left_cancel h1]
      exact hy
  have hHP : H ≤ P := by
    rcases hH with h | h <;> rw [h]
    · exact hNQP
    · exact hCN.trans hNQP
  obtain ⟨-, hchar, -, -⟩ := parabolic_containing_subgroup_local_characteristic_transfer
    (G := D.group) (p := p) hUP hUn hUp hCU hQP hQp hH hHP
  exact ⟨hchar, not_isComponent_of_isCharacteristicP hchar⟩

end RootWeightDatum

end CFSG.LieType.Chevalley
