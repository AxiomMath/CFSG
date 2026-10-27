module

public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.G2NoL2
public import CFSG.HardMathSupport.Dickson.Sec6.I923Fam.R2Aux.NoComp

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.Open CFSG.HardMathSupport.Dickson.Sec6.I923.TriD4Aux
open scoped commutatorElement

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem noGLAP3_centralizer_g2Top [CharP K 3] (h3 : 3 ≤ Nat.card K) {y : K} (hy : y ≠ 0) :
    ∀ A : Subgroup (adjointGroup .G2 K),
      ¬ GLAPComponent 3 (Subgroup.centralizer {g2Top K y}) A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (adjointGroup .G2 K) := generated_group_finite .G2 K
  set D : Subgroup (adjointGroup .G2 K) := Subgroup.centralizer {g2Top K y} with hDdef
  set Q' : Subgroup (adjointGroup .G2 K) := (g2Q K).subgroupOf (adjointGroup .G2 K) with hQ'def
  have hmemQ' : ∀ g : adjointGroup .G2 K, g ∈ Q' ↔ (g : ModGL .G2 K) ∈ g2Q K := fun g => Iff.rfl
  have hmemD : ∀ g : adjointGroup .G2 K, g ∈ D ↔
      (g : ModGL .G2 K) * pinnedX .G2 K g2c y = pinnedX .G2 K g2c y * (g : ModGL .G2 K) := by
    intro g
    rw [hDdef, Subgroup.mem_centralizer_singleton_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hQD : Q' ≤ D := fun g hg => (hmemD g).2
    ((commute_g2Q_pinnedX_c ((hmemQ' g).1 hg) y).eq)
  have hdec : ∀ g ∈ D, ∃ q ∈ g2Q K, ∃ l ∈ g2RankOne K g2ir, (g : ModGL .G2 K) = q * l :=
    fun g hg => exists_mem_mul_of_commute_c g.2 hy ((hmemD g).1 hg)
  have hQn : ∀ g ∈ D, ∀ n ∈ Q', g * n * g⁻¹ ∈ Q' := by
    intro g hg n hn
    obtain ⟨q, hq, l, hl, hgql⟩ := hdec g hg
    rw [hmemQ'] at hn ⊢
    have h1 : ((g * n * g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) =
        q * (l * (n : ModGL .G2 K) * l⁻¹) * q⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgql, mul_inv_rev]
      group
    rw [h1]
    exact mul_mem (mul_mem hq (g2RankOne_normalizes_g2Q hl hn)) (inv_mem hq)
  have hQp : IsPGroup 3 Q' :=
    (g2Q_isPGroup (K := K) 3).comap_of_injective (adjointGroup .G2 K).subtype
      (adjointGroup .G2 K).subtype_injective
  refine noGLAP3_of_constrained D Q' hQD hQn hQp ?_
  by_cases hK3 : Nat.card K = 3
  ·
    have hLsol : Group.IsSolvable ↥(g2RankOne K g2ir) := isSolvable_g2RankOne_of_card_three hK3
    set N0 : Subgroup ↥D := Q'.subgroupOf D with hN0
    haveI hN0n : N0.Normal := ⟨fun n hn g => by
      rw [hN0, Subgroup.mem_subgroupOf] at hn ⊢
      exact hQn g g.2 n hn⟩
    haveI hN0p : IsPGroup 3 ↥N0 := hQp.comap_of_injective D.subtype D.subtype_injective
    haveI : Group.IsNilpotent ↥N0 := IsPGroup.isNilpotent hN0p
    haveI : Group.IsSolvable ↥N0 := inferInstance
    set L'' : Subgroup (adjointGroup .G2 K) := (g2RankOne K g2ir).subgroupOf (adjointGroup .G2 K)
      with hL''
    have hL''mem : ∀ g : adjointGroup .G2 K, g ∈ L'' ↔ (g : ModGL .G2 K) ∈ g2RankOne K g2ir :=
      fun g => Iff.rfl
    have hL''D : L'' ≤ D := fun g hg => (hmemD g).2
      ((commute_g2RankOne_pinnedX_c ((hL''mem g).1 hg) y).eq)
    haveI : Group.IsSolvable ↥L'' := by
      refine Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
        (g2RankOne_le_adjointGroup (K := K) g2ir)).toMonoidHom) ?_
      exact (Subgroup.subgroupOfEquivOfLe (g2RankOne_le_adjointGroup (K := K) g2ir)).injective
    let ψ : ↥L'' →* ↥D ⧸ N0 := (QuotientGroup.mk' N0).comp (Subgroup.inclusion hL''D)
    have hψ : Function.Surjective ψ := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨q, hq, l, hl, hgql⟩ := hdec g g.2
      set qP : adjointGroup .G2 K := ⟨q, g2Q_le_adjointGroup hq⟩ with hqP_def
      set lP : adjointGroup .G2 K := ⟨l, g2RankOne_le_adjointGroup g2ir hl⟩ with hlP_def
      have hqP : qP ∈ Q' := (hmemQ' _).2 hq
      have hlP : lP ∈ L'' := (hL''mem _).2 hl
      have hgeq : (g : adjointGroup .G2 K) = qP * lP := Subtype.ext hgql
      refine ⟨⟨lP, hlP⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hL''D ⟨lP, hlP⟩) = QuotientGroup.mk g
      rw [QuotientGroup.eq, hN0, Subgroup.mem_subgroupOf]
      have e : (((Subgroup.inclusion hL''D ⟨lP, hlP⟩)⁻¹ * g : ↥D) : adjointGroup .G2 K) =
          lP⁻¹ * qP * lP⁻¹⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hgeq]
        simp only [Subgroup.coe_inclusion]
        group
      rw [e]
      exact hQn lP⁻¹ (inv_mem (hL''D hlP)) qP hqP
    haveI : Group.IsSolvable (↥D ⧸ N0) := Group.isSolvable_of_surjective hψ
    haveI : Group.IsSolvable ↥D := Group.isSolvable_of_subgroup_quotient N0
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (inf_le_left : D ⊓ Subgroup.centralizer (Q' : Set _) ≤ D))
  · have hK4 : 4 ≤ Nat.card K := by omega
    set D' : Subgroup (adjointGroup .G2 K) :=
      D ⊓ Subgroup.centralizer (Q' : Set (adjointGroup .G2 K)) with hD'
    have hD'D : D' ≤ D := inf_le_left
    have hcen : ∀ g ∈ D', ∃ q ∈ g2Q K, ∃ l ∈ g2RankOne K g2ir, (g : ModGL .G2 K) = q * l ∧
        ∀ m ∈ g2RankOne K g2ir, m * l = l * m := by
      intro g hg
      obtain ⟨q, hq, l, hl, hgql⟩ := hdec g (hD'D hg)
      refine ⟨q, hq, l, hl, hgql, ?_⟩
      refine central_of_acts_trivially hK4 hl ?_
      intro y' hy'
      have hyP : (⟨y', g2Q_le_adjointGroup hy'⟩ : adjointGroup .G2 K) ∈ Q' := (hmemQ' _).2 hy'
      have hcomm := (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2) _ hyP
      have h1 : y' * (q * l) = (q * l) * y' := by
        rw [← hgql]
        exact congrArg Subtype.val hcomm
      have h2 : l * y' * l⁻¹ * y'⁻¹ = ⁅q⁻¹, y'⁆ := by
        have h3 : l * y' * l⁻¹ = q⁻¹ * y' * q := by
          calc l * y' * l⁻¹ = q⁻¹ * (q * l * y') * l⁻¹ := by group
            _ = q⁻¹ * (y' * (q * l)) * l⁻¹ := by rw [h1]
            _ = q⁻¹ * y' * q := by group
        rw [h3, commutatorElement_def]
        group
      rw [h2]
      exact g2Q_commutator_le (Subgroup.commutator_mem_commutator (inv_mem hq) hy')
    have hcomm' : ∀ a ∈ D', ∀ b ∈ D', ⁅a, b⁆ ∈ Q' := by
      intro a ha b hb
      obtain ⟨q₁, hq₁, l₁, hl₁, ha1, hc₁⟩ := hcen a ha
      obtain ⟨q₂, hq₂, l₂, hl₂, hb1, hc₂⟩ := hcen b hb
      rw [hmemQ']
      have e : ((⁅a, b⁆ : adjointGroup .G2 K) : ModGL .G2 K) =
          ⁅(a : ModGL .G2 K), (b : ModGL .G2 K)⁆ := by simp [commutatorElement_def]
      rw [e, ha1, hb1]
      exact commutator_mul_mem_of_central (fun l hl q hq => g2RankOne_normalizes_g2Q hl hq) hq₁ hq₂
        hl₁ hl₂ hc₁
    exact isSolvable_of_commutator_mem_pGroup (p := 3) D' Q' hQp
      (fun h hh n hn => hQn h (hD'D hh) n hn) hcomm'

end CFSG.HardMathSupport.Dickson.Sec6.I923.R2Aux
