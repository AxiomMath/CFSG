module

public import Mathlib.GroupTheory.Complement
import CFSG.FeitThompson.Foundations.CoprimeAbelianComplementsConjugate

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Pointwise

variable {G : Type*} [Group G] {A H U : Subgroup G} [A.Normal]

theorem sup_inf_eq_of_sup_eq_top (hsup : A ⊔ H = ⊤) {K : Subgroup G} (hAK : A ≤ K) :
    A ⊔ (H ⊓ K) = K := by
  refine le_antisymm (sup_le hAK inf_le_right) fun k hk => ?_
  have hk' : (k : G) ∈ (A : Set G) * (H : Set G) := by
    rw [← Subgroup.normal_mul, hsup]; trivial
  obtain ⟨a, ha, h, hh, rfl⟩ := hk'
  have hhK : h ∈ K := by
    have : a⁻¹ * (a * h) ∈ K := K.mul_mem (K.inv_mem (hAK ha)) hk
    simpa using this
  exact Subgroup.mul_mem_sup ha ⟨hh, hhK⟩

theorem inf_subgroupOf (X Y K : Subgroup G) :
    (X ⊓ Y).subgroupOf K = X.subgroupOf K ⊓ Y.subgroupOf K := by
  ext x; simp [Subgroup.mem_subgroupOf]

variable [IsMulCommutative ↥A]

theorem exists_mem_le_conj_smul [Finite G]
    (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥) (hU : (Nat.card ↥U).Coprime (Nat.card ↥A)) :
    ∃ a ∈ A, U ≤ MulAut.conj a • H := by
  set K : Subgroup G := A ⊔ U with hK
  have hAK : A ≤ K := le_sup_left
  have hUK : U ≤ K := le_sup_right
  set A' : Subgroup ↥K := A.subgroupOf K with hA'
  set U' : Subgroup ↥K := U.subgroupOf K with hU'
  set H' : Subgroup ↥K := (H ⊓ K).subgroupOf K with hH'
  have hAU : A ⊓ U = ⊥ := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hU.symm)
  have hsupU : A' ⊔ U' = ⊤ := by
    rw [hA', hU', ← Subgroup.subgroupOf_sup hAK hUK, ← hK, Subgroup.subgroupOf_self]
  have hinfU : A' ⊓ U' = ⊥ := by
    rw [hA', hU', ← inf_subgroupOf, hAU, Subgroup.bot_subgroupOf]
  have hsupH : A' ⊔ H' = ⊤ := by
    rw [hA', hH', ← Subgroup.subgroupOf_sup hAK inf_le_right,
      sup_inf_eq_of_sup_eq_top hHsup hAK, Subgroup.subgroupOf_self]
  have hinfH : A' ⊓ H' = ⊥ := by
    rw [hA', hH', ← inf_subgroupOf,
      show A ⊓ (H ⊓ K) = ⊥ by rw [← inf_assoc, hHinf, bot_inf_eq], Subgroup.bot_subgroupOf]
  have hcompU : U'.IsComplement' A' := isComplement'_of_sup_eq_top_of_inf_eq_bot hsupU hinfU
  have hcompH : H'.IsComplement' A' := isComplement'_of_sup_eq_top_of_inf_eq_bot hsupH hinfH
  have hcardA' : Nat.card ↥A' = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hcardU' : Nat.card ↥U' = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
  have hcop' : (Nat.card ↥A').Coprime A'.index := by
    rw [hcardA', hcompU.index_eq_card, hcardU']
    exact hU.symm
  obtain ⟨a, ha, hconj⟩ := exists_mem_conj_smul_eq_of_isComplement' hcop' hcompH hcompU
  refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, fun u hu => ?_⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]
  have hmem : (⟨u, hUK hu⟩ : ↥K) ∈ U' := by rw [hU', Subgroup.mem_subgroupOf]; exact hu
  rw [← hconj, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply, hH', Subgroup.mem_subgroupOf] at hmem
  simpa using hmem.1

theorem exists_mem_le_conj_smul_of_coprime_index [Finite G]
    (_hcop : (Nat.card ↥A).Coprime (Nat.card (G ⧸ A)))
    (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥) (hU : (Nat.card ↥U).Coprime (Nat.card ↥A)) :
    ∃ a ∈ A, U ≤ MulAut.conj a • H :=
  exists_mem_le_conj_smul hHsup hHinf hU

theorem exists_mem_le_conj_smul_of_isComplement' [Finite G] (hH : H.IsComplement' A)
    (hU : (Nat.card ↥U).Coprime (Nat.card ↥A)) : ∃ a ∈ A, U ≤ MulAut.conj a • H :=
  exists_mem_le_conj_smul (by simpa [sup_comm] using hH.isCompl.sup_eq_top)
    (disjoint_iff.mp hH.disjoint.symm) hU

theorem exists_mem_forall_mem_conj_mem [Finite G] (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥)
    (hU : (Nat.card ↥U).Coprime (Nat.card ↥A)) : ∃ a ∈ A, ∀ u ∈ U, a⁻¹ * u * a ∈ H := by
  obtain ⟨a, ha, hle⟩ := exists_mem_le_conj_smul hHsup hHinf hU
  refine ⟨a, ha, fun u hu => ?_⟩
  have h := hle hu
  rwa [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply] at h

theorem exists_mem_le_map_conj [Finite G] (hHsup : A ⊔ H = ⊤) (hHinf : A ⊓ H = ⊥)
    (hU : (Nat.card ↥U).Coprime (Nat.card ↥A)) :
    ∃ a ∈ A, U ≤ H.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨a, ha, hle⟩ := exists_mem_forall_mem_conj_mem hHsup hHinf hU
  refine ⟨a, ha, fun u hu => ⟨a⁻¹ * u * a, hle u hu, ?_⟩⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end CFSG.FeitThompson
