module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L51Setup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Basic

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsShortGroup)
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Case4

variable {K T P S W : Subgroup G} {x : G} (c : Case4 K T P S W x)

include c

theorem blockU_le_CKW (hne : ⁅T, K⁆ ≠ ⊥) :
    blockU K ≤ K ⊓ Subgroup.centralizer (W : Set G) :=
  le_inf (blockU_le K) (c.blockU_le_centralizer_W hne)

theorem mem_CKW_of_sq (hne : ⁅T, K⁆ ≠ ⊥) {g : G}
    (hg : g ∈ K ⊓ Subgroup.centralizer (T : Set G))
    (hg2 : g * g ∈ K ⊓ Subgroup.centralizer (W : Set G)) :
    g ∈ K ⊓ Subgroup.centralizer (W : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H₀ := K ⊓ Subgroup.centralizer (T : Set G) with hH₀
  have hsyl := c.sylow_blockU hne
  have hodd : ¬ 2 ∣ ((blockU K).subgroupOf H₀).index := ((isSylowOf_iff).1 hsyl).2.2
  have hn : H₀ ≤ Subgroup.normalizer (blockU K : Set G) :=
    fun y hy => le_normalizer_blockU K (Subgroup.mem_inf.1 hy).1
  have hnorm : ((blockU K).subgroupOf H₀).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hn
  have hpow := Subgroup.pow_index_mem ((blockU K).subgroupOf H₀) (⟨g, hg⟩ : ↥H₀)
  have hgm : g ^ ((blockU K).subgroupOf H₀).index ∈ blockU K := by
    have := Subgroup.mem_subgroupOf.1 hpow
    simpa using this
  obtain ⟨k, hk⟩ : Odd ((blockU K).subgroupOf H₀).index := Nat.odd_iff.2 (by omega)
  rw [hk] at hgm
  have e1 : (g * g) ^ (k + 1) = g * g ^ (2 * k + 1) := by
    rw [← pow_two, ← pow_mul, show 2 * (k + 1) = (2 * k + 1) + 1 by ring, pow_succ']
  have h1 : g = (g * g) ^ (k + 1) * (g ^ (2 * k + 1))⁻¹ := by
    rw [e1, mul_inv_cancel_right]
  rw [h1]
  exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hg2 _)
    (Subgroup.inv_mem _ (c.blockU_le_CKW hne hgm))

theorem inf_eq_bot_of_ne {g : G} (hg : g ∈ K ⊔ T) (hne : rightConjugate T g ≠ T) :
    T ⊓ rightConjugate T g = ⊥ := by
  by_contra hbot
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTP : T ≤ P := c.sylowP.le
  have hA : T ⊓ rightConjugate T g ≤ P ⊓ rightConjugate P g :=
    inf_le_inf hTP
      (ComponentClassification.AschbacherTheorem3.rightConjugate_le_rightConjugate hTP g)
  have hApg : IsPGroup 2 ↥(T ⊓ rightConjugate T g) := c.tIsPGroup.to_inf_left
  have hdvdA : 2 ∣ Nat.card ↥(T ⊓ rightConjugate T g) := by
    rcases hApg.card_eq_or_dvd with h1 | h1
    · exact absurd ((Subgroup.eq_bot_iff_card _).2 h1) hbot
    · exact h1
  have heven : Even (Nat.card ↥(P ⊓ rightConjugate P g)) :=
    even_iff_two_dvd.2 (hdvdA.trans (Subgroup.card_dvd_of_le hA))
  have hgP : g ∈ Subgroup.normalizer (P : Set G) := mem_normalizer_of_tight c.ple c.tight hg heven
  have hPg : rightConjugate P g = P := (rightConjugate_eq_self_iff P g).2 hgP
  have hWg : rightConjugate W g = W := (rightConjugate_eq_self_iff W g).2 (c.hWnorm hg)
  have hle1 : rightConjugate T g ≤ P :=
    hPg ▸ ComponentClassification.AschbacherTheorem3.rightConjugate_le_rightConjugate hTP g
  have hle2 : rightConjugate T g ≤ W :=
    hWg ▸ ComponentClassification.AschbacherTheorem3.rightConjugate_le_rightConjugate c.T_le_W g
  have hPW : P ⊓ W = T :=
    c.sylowP.eq_of_le (le_inf hTP c.T_le_W) inf_le_left (c.W_isPGroup.to_le inf_le_right)
  have hle3 : rightConjugate T g ≤ T := (le_inf hle1 hle2).trans hPW.le
  exact hne (Subgroup.eq_of_le_of_card_ge hle3 (by rw [rightConjugate_card]))

theorem inf_eq_bot_of_sq_mem (hne : ⁅T, K⁆ ≠ ⊥) {g : G} (hgK : g ∈ K)
    (hg : g ∉ K ⊓ Subgroup.centralizer (W : Set G))
    (hg2 : g * g ∈ K ⊓ Subgroup.centralizer (W : Set G)) : T ⊓ rightConjugate T g = ⊥ := by
  have hcT : g ∉ Subgroup.centralizer (T : Set G) := fun h =>
    hg (c.mem_CKW_of_sq hne (Subgroup.mem_inf.2 ⟨hgK, h⟩) hg2)
  have hnT : g ∉ Subgroup.normalizer (T : Set G) := by
    intro hn
    apply hcT
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h1 : g * t * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hn t).1 ht
    have h2 : t * g⁻¹ * t⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.1 (c.tnorm ht) g⁻¹).1 (K.inv_mem hgK)
    have h3 : (g * t * g⁻¹) * t⁻¹ ∈ T ⊓ K :=
      Subgroup.mem_inf.2 ⟨T.mul_mem h1 (T.inv_mem ht), by
        have : (g * t * g⁻¹) * t⁻¹ = g * (t * g⁻¹ * t⁻¹) := by group
        rw [this]
        exact K.mul_mem hgK h2⟩
    rw [c.tinf, Subgroup.mem_bot] at h3
    have h4 : g * t * g⁻¹ = t := by
      calc g * t * g⁻¹ = ((g * t * g⁻¹) * t⁻¹) * t := by group
        _ = t := by rw [h3, one_mul]
    calc t * g = (g * t * g⁻¹) * g := by rw [h4]
      _ = g * t := by group
  have hne' : rightConjugate T g ≠ T := fun h => hnT ((rightConjugate_eq_self_iff T g).1 h)
  exact c.inf_eq_bot_of_ne (Subgroup.mem_sup_left hgK) hne'

end Case4

end CFSG.CGT.PushingUpLit.LIT.Foote
