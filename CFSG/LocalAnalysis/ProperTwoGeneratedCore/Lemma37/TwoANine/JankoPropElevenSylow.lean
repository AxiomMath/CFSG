module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropElevenDerived

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G] {z : G} {fr : JankoFrame G z}

theorem F_le_normalizer_M : fr.F ≤ normalizer (fr.M : Set G) :=
  fun _ hf => centralizer_P₁_le_normalizer_M (fr.F_le_centralizer hf)

theorem card_centralizer_P₁ (p10 : JankoProp10 fr) :
    Nat.card (centralizer (fr.P₁ : Set G)) = 3 ^ 5 * 720 := by
  have h := card_sup_mul_card_inf (F_le_normalizer_M (fr := fr))
  rw [sup_comm, inf_comm, p10.M_inf_F, Subgroup.card_bot, mul_one, ← p10.centralizer_P₁,
    fr.card_F, p10.card_M] at h
  rw [h, mul_comm]

theorem card_normalizer_P₁ [Finite G] (p7 : JankoProp7 fr) :
    Nat.card (normalizer (fr.P₁ : Set G)) = 2 * Nat.card (centralizer (fr.P₁ : Set G)) := by
  have hle : zpowers fr.t ≤ normalizer (centralizer (fr.P₁ : Set G) : Set G) :=
    zpowers_le.mpr (mem_normalizer_centralizer (t_mem_normalizer_P₁ p7))
  have h := card_sup_mul_card_inf hle
  have h2 : Nat.card (zpowers fr.t) = 2 := by rw [Nat.card_zpowers, fr.orderOf_t]
  have hbot : zpowers fr.t ⊓ centralizer (fr.P₁ : Set G) = ⊥ := by
    have hdvd := Subgroup.card_dvd_of_le
      (inf_le_left : zpowers fr.t ⊓ centralizer (fr.P₁ : Set G) ≤ zpowers fr.t)
    rw [h2] at hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge
        (inf_le_left : zpowers fr.t ⊓ centralizer (fr.P₁ : Set G) ≤ zpowers fr.t)
        (by rw [h1, h2])
      have ht : fr.t ∈ zpowers fr.t ⊓ centralizer (fr.P₁ : Set G) := by
        rw [heq]; exact mem_zpowers _
      exact t_not_mem_centralizer_P₁ ht.2
  rw [hbot, Subgroup.card_bot, mul_one, sup_comm, ← p7.normalizer_P₁, h2] at h
  exact h

theorem N_le_normalizer_P₁ : fr.N ≤ normalizer (fr.P₁ : Set G) :=
  N_le_centralizer_P₁.trans centralizer_P₁_le_normalizer_P₁

theorem isSylowOf_N [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) :
    IsSylowOf (normalizer (fr.P₁ : Set G)) 3 fr.N := by
  have hNK := N_le_normalizer_P₁ (fr := fr)
  have hP : IsPGroup 3 (fr.N.subgroupOf (normalizer (fr.P₁ : Set G))) :=
    (isPGroup_N p10).comap_subtype
  have hidx : ¬ 3 ∣ (fr.N.subgroupOf (normalizer (fr.P₁ : Set G))).index := by
    have h := Subgroup.card_mul_index (fr.N.subgroupOf (normalizer (fr.P₁ : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv, card_N p10,
      card_normalizer_P₁ p7, card_centralizer_P₁ p10] at h
    have h160 : (fr.N.subgroupOf (normalizer (fr.P₁ : Set G))).index = 160 := by omega
    rw [h160]
    norm_num
  exact ⟨hP.toSylow hidx, by rw [IsPGroup.toSylow_coe]; exact Subgroup.map_subgroupOf_eq_of_le hNK⟩

theorem normalizer_N_inf [Finite G] (p7 : JankoProp7 fr) (p10 : JankoProp10 fr) :
    normalizer (fr.N : Set G) ⊓ normalizer (fr.P₁ : Set G) = fr.N ⊔ fr.L := by
  refine le_antisymm (fun g hg => ?_) (sup_le (le_inf Subgroup.le_normalizer N_le_normalizer_P₁)
    (le_inf (L_le_normalizer_N p7) (L_le_normalizer_P₁ p7)))
  obtain ⟨hgN, hgP⟩ := hg
  rw [p7.normalizer_P₁] at hgP
  obtain ⟨c, hc, t', ht', rfl⟩ := exists_mul_of_mem_sup_right
    (zpowers_le.mpr (mem_normalizer_centralizer (t_mem_normalizer_P₁ p7))) hgP
  have ht'L : t' ∈ fr.L := zpowers_le.mpr t_mem_L ht'
  have hcN : c ∈ normalizer (fr.N : Set G) := by
    rw [show c = c * t' * t'⁻¹ by group]
    exact mul_mem hgN (inv_mem (L_le_normalizer_N p7 ht'L))
  rw [p10.centralizer_P₁] at hc
  obtain ⟨m, hm, f, hf, rfl⟩ := exists_mul_of_mem_sup_right F_le_normalizer_M hc
  have hfN : f ∈ normalizer (fr.N : Set G) := by
    rw [show f = m⁻¹ * (m * f) by group]
    exact mul_mem (inv_mem (Subgroup.le_normalizer (M_le_N hm))) hcN
  have hfz : f * z = z * f := mem_centralizer_singleton_iff.mp (fr.F_le hf)
  have hfE : f ∈ normalizer (fr.E : Set G) := by
    rw [← N_inf_centralizer_z p10]
    exact inf_mem_normalizer hfN (mem_normalizer_centralizer_singleton hfz)
  have hfEF : f ∈ normalizer (fr.EF : Set G) := by
    rw [fr.EF_eq]
    exact inf_mem_normalizer hfE (Subgroup.le_normalizer hf)
  have hf' : f ∈ fr.EF ⊔ fr.L₁ := by rw [← fr.normalizer_EF]; exact ⟨hfEF, hf⟩
  have hEFL : fr.EF ⊔ fr.L₁ ≤ fr.N ⊔ fr.L :=
    sup_le_sup (fr.EF_eq ▸ inf_le_left.trans E_le_N) (fr.L₁_eq ▸ zpowers_le.mpr ℓ_mem_L)
  exact mul_mem (mul_mem (mem_sup_left (M_le_N hm)) (hEFL hf')) (mem_sup_right ht'L)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoEleven
