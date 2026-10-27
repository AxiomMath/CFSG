module

public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbConcl2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

section Normalizer

variable {G : Type} [Group G] {ρ lam : G}

private lemma conj_zpow_inv (hlam : lam * ρ * lam⁻¹ = ρ⁻¹) (k : ℤ) :
    lam * ρ ^ k * lam⁻¹ = ρ ^ (-k) := by
  rw [← conj_zpow, hlam, inv_zpow']

theorem mem_normalizer_zpowers_of_inv (hlam2 : lam ^ 2 = 1) (hlam : lam * ρ * lam⁻¹ = ρ⁻¹) :
    lam ∈ normalizer ((zpowers ρ : Subgroup G) : Set G) := by
  have hlinv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hlam2)
  refine (Subgroup.mem_normalizer_iff).mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    rw [← hk, conj_zpow_inv hlam k]
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    refine Subgroup.mem_zpowers_iff.mpr ⟨-k, ?_⟩
    calc ρ ^ (-k) = lam * ρ ^ k * lam⁻¹ := (conj_zpow_inv hlam k).symm
      _ = lam⁻¹ * ρ ^ k * lam := by rw [hlinv]
      _ = h := by rw [hk]; group

theorem centralizer_le_normalizer_zpowers :
    centralizer ({ρ} : Set G) ≤ normalizer ((zpowers ρ : Subgroup G) : Set G) := by
  rw [← Subgroup.centralizer_closure ({ρ} : Set G), ← Subgroup.zpowers_eq_closure ρ]
  exact Subgroup.centralizer_le_normalizer _

theorem not_mem_centralizer_of_inv (h3 : orderOf ρ = 3) (hlam : lam * ρ * lam⁻¹ = ρ⁻¹) :
    lam ∉ centralizer ({ρ} : Set G) := by
  intro hmem
  have hcomm : ρ * lam = lam * ρ := (Subgroup.mem_centralizer_iff.mp hmem) ρ rfl
  have hρinv : ρ⁻¹ = ρ := by
    rw [← hlam, hcomm.symm]
    group
  have hsq : ρ ^ 2 = 1 := by
    rw [pow_two]
    exact (mul_eq_one_iff_eq_inv).mpr hρinv.symm
  have hdvd : orderOf ρ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rw [h3] at hdvd
  norm_num at hdvd

end Normalizer

section Extension

variable {G : Type} [Group G] [Finite G]

private lemma inf_zpowers_eq_bot_of_sq_eq_one {T : Subgroup G} {lam : G} (hlam2 : lam ^ 2 = 1)
    (hlam : lam ∉ T) : T ⊓ zpowers lam = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyT, hyZ⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyZ
  have hord : orderOf lam = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hlam2 (fun h1 => hlam (h1 ▸ Subgroup.one_mem T))
  have hmod : lam ^ (k % 2) = lam ^ k := by
    have h := zpow_mod_orderOf lam k
    rw [hord] at h
    exact h
  have h0 : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
  have hlt : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
  have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hcases with hm | hm
  · rw [hm, zpow_zero] at hmod
    exact Subgroup.mem_bot.mpr (by rw [← hk]; exact hmod.symm)
  · rw [hm, zpow_one] at hmod
    exact absurd (hmod.trans hk ▸ hyT) hlam

private lemma natCard_zpowers_of_sq_eq_one {lam : G} (hlam2 : lam ^ 2 = 1) (hlam1 : lam ≠ 1) :
    Nat.card (zpowers lam) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers, orderOf_eq_prime hlam2 hlam1]

theorem closure_triple_eq (t om lam : G) :
    closure ({t, om, lam} : Set G) = closure ({t, om} : Set G) ⊔ zpowers lam := by
  rw [show ({t, om, lam} : Set G) = {t, om} ∪ {lam} by
        ext x; simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]; tauto,
      Subgroup.closure_union, Subgroup.zpowers_eq_closure]

theorem card_sup_zpowers_of_commute {T : Subgroup G} {lam : G} (hlam2 : lam ^ 2 = 1)
    (hlam : lam ∉ T) (hcomm : ∀ x ∈ T, x * lam = lam * x) :
    Nat.card ↥(T ⊔ zpowers lam) = 2 * Nat.card T := by
  have hlam1 : lam ≠ 1 := fun h1 => hlam (h1 ▸ Subgroup.one_mem T)
  have hc : ∀ x ∈ T, ∀ y ∈ zpowers lam, x * y = y * x := by
    intro x hx y hy
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcx : Commute x lam := hcomm x hx
    rw [← hk]
    exact hcx.zpow_right k
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute T (zpowers lam) hc).1
  rw [inf_zpowers_eq_bot_of_sq_eq_one hlam2 hlam, Subgroup.card_bot,
    natCard_zpowers_of_sq_eq_one hlam2 hlam1, mul_one] at hcard
  rw [hcard, mul_comm]

end Extension

section Ctx

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau om : G}

theorem ctx13_lam_facts (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    lam ^ 2 = 1 ∧ ∀ x ∈ closure ({t, om} : Set G), x * lam = lam * x := by
  have hlam2 : lam ^ 2 = 1 := by
    rw [← hc.wreath.ord_lam]
    exact pow_orderOf_eq_one lam
  have hlamW : lam ∈ wreathGrp x₁ x₂ lam := Subgroup.subset_closure (by simp)
  have hlamL : lam ∈ L := (Subgroup.mem_inf.mp (hc.inf_eq ▸ hlamW)).2
  have ht_lam : t * lam = lam * t :=
    ((Subgroup.mem_centralizer_iff.mp hc.hyp.mem_centralizer) lam hlamL).symm
  have hom_lam : om * lam = lam * om :=
    ((mul_inv_eq_iff_eq_mul).mp hc.lam_om).symm
  refine ⟨hlam2, fun x hx => ?_⟩
  have hle : closure ({t, om} : Set G) ≤ centralizer ({lam} : Set G) := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr ht_lam
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hom_lam
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

end Ctx

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
