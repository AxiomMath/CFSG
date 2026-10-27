module

public import CFSG.CGT.Timmesfeld75.Sec3Lift

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups

section Algebra

variable {G : Type*} [Group G]

theorem conj_conj_eq_mul_of_orderOf_mul_eq_three {M : Subgroup G} (hM : IsElemAbelian 2 M)
    {a t u : G} (haa : a * a = 1) (htt : t * t = 1) (hat : orderOf (a * t) = 3)
    (hau : a * u * a⁻¹ = u) (hu : u ∈ M) (hu' : t * u * t⁻¹ ∈ M)
    (hv : a * (t * u * t⁻¹) * a⁻¹ ∈ M)
    (hC : M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) = ⊥) :
    a * (t * u * t⁻¹) * a⁻¹ = u * (t * u * t⁻¹) := by
  have hbr : a * t * a = t * a * t := by
    have h3 : (a * t * a) * (t * a * t) = 1 := by
      have := pow_orderOf_eq_one (a * t)
      rw [hat] at this
      simpa only [pow_three, mul_assoc] using this
    rw [eq_inv_of_mul_eq_one_left h3]
    simp only [mul_inv_rev, inv_eq_of_mul_eq_one_right haa, inv_eq_of_mul_eq_one_right htt,
      mul_assoc]
  obtain ⟨u', hu'def⟩ : ∃ u', t * u * t⁻¹ = u' := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, a * u' * a⁻¹ = v := ⟨_, rfl⟩
  rw [hu'def] at hu' hv ⊢
  rw [hvdef] at hv ⊢
  have hτu' : t * u' * t⁻¹ = u := by
    rw [← hu'def]
    calc t * (t * u * t⁻¹) * t⁻¹ = (t * t) * u * (t * t)⁻¹ := by group
      _ = u := by rw [htt]; group
  have hσv : a * v * a⁻¹ = u' := by
    rw [← hvdef]
    calc a * (a * u' * a⁻¹) * a⁻¹ = (a * a) * u' * (a * a)⁻¹ := by group
      _ = u' := by rw [haa]; group
  have hτv : t * v * t⁻¹ = v := by
    rw [← hvdef, ← hu'def]
    calc t * (a * (t * u * t⁻¹) * a⁻¹) * t⁻¹ = (t * a * t) * u * (t * a * t)⁻¹ := by group
      _ = (a * t * a) * u * (a * t * a)⁻¹ := by rw [hbr]
      _ = a * (t * (a * u * a⁻¹) * t⁻¹) * a⁻¹ := by group
      _ = a * (t * u * t⁻¹) * a⁻¹ := by rw [hau]
  have hσe : a * (u * u' * v) * a⁻¹ = u * u' * v := by
    calc a * (u * u' * v) * a⁻¹ = (a * u * a⁻¹) * (a * u' * a⁻¹) * (a * v * a⁻¹) := by group
      _ = u * v * u' := by rw [hau, hvdef, hσv]
      _ = u * u' * v := by rw [mul_assoc, elemAbelian_mul_comm hM hv hu', ← mul_assoc]
  have hτe : t * (u * u' * v) * t⁻¹ = u * u' * v := by
    calc t * (u * u' * v) * t⁻¹ = (t * u * t⁻¹) * (t * u' * t⁻¹) * (t * v * t⁻¹) := by group
      _ = u' * u * v := by rw [hu'def, hτu', hτv]
      _ = u * u' * v := by rw [elemAbelian_mul_comm hM hu' hu]
  have heC : u * u' * v ∈
      M ⊓ Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) := by
    refine ⟨⟨M.mul_mem (M.mul_mem hu hu') hv, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · calc u * u' * v * a = (a * (u * u' * v) * a⁻¹) * a := by rw [hσe]
        _ = a * (u * u' * v) := by group
    · calc u * u' * v * t = (t * (u * u' * v) * t⁻¹) * t := by rw [hτe]
        _ = t * (u * u' * v) := by group
  rw [hC, Subgroup.mem_bot] at heC
  rw [eq_inv_of_mul_eq_one_right heC, mul_inv_rev, elemAbelian_inv hM hu', elemAbelian_inv hM hu,
    elemAbelian_mul_comm hM hu' hu]

end Algebra

section Normalizer

variable {G : Type} [Group G] {T T₁ U : Subgroup G}

theorem conjSubgroup_eq_of_normalizer_le {g s : G} (hg : conjSubgroup g T = T₁)
    (hs : conjSubgroup s T = T₁)
    (hU : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    conjSubgroup s U = conjSubgroup g U :=
  (conjSubgroup_eq_conjSubgroup_iff.2
    (hU (conjSubgroup_eq_conjSubgroup_iff.1 (hg.trans hs.symm)))).symm

variable [Finite G]

theorem Sec3.conjSubgroup_le_cfgM_of_normalizer_le (hS : Sec3 T T₁) {g : G}
    (hg : conjSubgroup g T = T₁) (hUM : U ≤ cfgM T T₁)
    (hU : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    conjSubgroup g U ≤ cfgM T T₁ := by
  obtain ⟨s, hsX, -, hsT, -⟩ := hS.exists_swap
  rw [← conjSubgroup_eq_of_normalizer_le hg hsT hU]
  intro z hz
  rw [mem_conjSubgroup] at hz
  exact (hS.cfg.inv_mul_mul_mem_cfgM_iff hsX).1 (hUM hz)

end Normalizer

section Quotient

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}
  [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]

set_option quotPrecheck false in
local notation "XQ" => ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁)

theorem Sec3.conjSubgroup_sup_conj_eq (hS : Sec3 T T₁) {f : ℕ} (hf : f ≠ 0)
    (h : Nonempty (XQ ≃* PSL(2, GaloisField 2 f))) {g : G} (hg : conjSubgroup g T = T₁)
    {U : Subgroup G} (hUL : U ≤ normIn T T₁)
    (hU : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (U : Set G)) :
    ∀ x ∈ T ⊔ T₁, conjSubgroup x (U ⊔ conjSubgroup g U) = U ⊔ conjSubgroup g U := by
  have hM : IsElemAbelian 2 (cfgM T T₁) := hS.cfg.isElemAbelian_cfgM
  have hUM : U ≤ cfgM T T₁ := hUL.trans (Cfg.normIn_le_cfgM_left T T₁)
  have hUT : U ≤ T := hUL.trans (normIn_le T T₁)
  have hU'M : conjSubgroup g U ≤ cfgM T T₁ :=
    hS.conjSubgroup_le_cfgM_of_normalizer_le hg hUM hU
  obtain ⟨s, hsX, hss, hsT, hsT₁⟩ := hS.exists_swap
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsU : conjSubgroup s U = conjSubgroup g U := conjSubgroup_eq_of_normalizer_le hg hsT hU
  have hsU' : conjSubgroup s (conjSubgroup g U) = U := by
    rw [← hsU, conjSubgroup_conjSubgroup, hss, conjSubgroup_one]
  have hsV : conjSubgroup s (U ⊔ conjSubgroup g U) = U ⊔ conjSubgroup g U := by
    rw [conjSubgroup_sup_eq_sup, hsU, hsU', sup_comm]
  have hmain : ∀ a ∈ T, ∀ w ∈ conjSubgroup g U, a * w * a⁻¹ ∈ U ⊔ conjSubgroup g U := by
    intro a haT w hw
    have haX : a ∈ T ⊔ T₁ := Subgroup.mem_sup_left haT
    by_cases haM : a ∈ cfgM T T₁
    · rw [elemAbelian_mul_comm hM haM (hU'M hw)]
      rw [mul_inv_cancel_right]
      exact Subgroup.mem_sup_right hw
    · obtain ⟨t, htX, htt, hconjt, hord⟩ := hS.exists_swap_orderOf_three_of_mem hf h haT haM
      have htU : conjSubgroup t U = conjSubgroup g U :=
        conjSubgroup_eq_of_normalizer_le hg hconjt hU
      rw [← htU] at hw
      obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, w = t * u * t⁻¹ :=
        ⟨t⁻¹ * w * t, mem_conjSubgroup.1 hw, by group⟩
      rw [htU] at hw
      have haa : a * a = 1 := elemAbelian_mul_self hS.cfg.wc.1 haT
      have hau : a * u * a⁻¹ = u := by
        rw [elemAbelian_mul_comm hS.cfg.wc.1 haT (hUT hu), mul_inv_cancel_right]
      have hodd : Odd (orderOf (a * t)) := by rw [hord]; decide
      have hne : a * t ≠ 1 := fun h1 => by
        rw [h1, orderOf_one] at hord
        exact absurd hord (by norm_num)
      have hno : ¬ ∃ P : Subgroup G, P ≤ T ⊔ T₁ ∧ IsPGroup 2 P ∧ a ∈ P ∧ t ∈ P := by
        rintro ⟨P, -, hP, haP, htP⟩
        exact not_exists_isPGroup_two_mem_of_odd_orderOf (x := a * t) rfl hodd hne
          ⟨P, hP, haP, htP⟩
      have hC := hS.cfgM_inf_centralizer_inf_centralizer_of_not_common_two_group haX haa htX htt
        hno
      rw [conj_conj_eq_mul_of_orderOf_mul_eq_three hM haa htt hord hau (hUM hu) (hU'M hw)
        (hS.cfg.conj_mem_cfgM haX (hU'M hw)) hC]
      exact (U ⊔ conjSubgroup g U).mul_mem (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right hw)
  have hTle : ∀ a ∈ T, conjSubgroup a (U ⊔ conjSubgroup g U) ≤ U ⊔ conjSubgroup g U := by
    intro a haT
    have haU : conjSubgroup a U = U :=
      mem_normalizer_iff_conjSubgroup_eq.1 (hU (Subgroup.le_normalizer haT))
    rw [conjSubgroup_sup_eq_sup, haU]
    refine sup_le le_sup_left fun z hz => ?_
    rw [mem_conjSubgroup] at hz
    have := hmain a haT _ hz
    rwa [show a * (a⁻¹ * z * a) * a⁻¹ = z by group] at this
  have hT : ∀ a ∈ T, conjSubgroup a (U ⊔ conjSubgroup g U) = U ⊔ conjSubgroup g U := fun a ha =>
    le_antisymm (hTle a ha) (by
      have := hTle a⁻¹ (T.inv_mem ha)
      rwa [conjSubgroup_le_iff, inv_inv] at this)
  have hT₁ : ∀ x ∈ T₁, conjSubgroup x (U ⊔ conjSubgroup g U) = U ⊔ conjSubgroup g U := by
    intro x hx
    have hy : s * x * s⁻¹ ∈ T := by
      rw [← hsT₁, mem_conjSubgroup]
      simpa [mul_assoc] using hx
    have e : conjSubgroup x (U ⊔ conjSubgroup g U) =
        conjSubgroup s⁻¹ (conjSubgroup (s * x * s⁻¹) (conjSubgroup s (U ⊔ conjSubgroup g U))) := by
      rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
      congr 1
      group
    rw [e, hsV, hT _ hy, hsi, hsV]
  have hX : T ⊔ T₁ ≤ Subgroup.normalizer ((U ⊔ conjSubgroup g U : Subgroup G) : Set G) :=
    sup_le (fun a ha => mem_normalizer_of_conjSubgroup_eq (hT a ha))
      (fun x hx => mem_normalizer_of_conjSubgroup_eq (hT₁ x hx))
  exact fun x hx => mem_normalizer_iff_conjSubgroup_eq.1 (hX hx)

end Quotient

end CFSG.CGT.Timmesfeld75
