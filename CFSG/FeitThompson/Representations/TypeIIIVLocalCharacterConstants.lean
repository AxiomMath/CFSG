module

public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Representations.LinearQuotientCharactersLocalArray
import CFSG.FeitThompson.Representations.PrimeTIUniformNonprincipalConstants
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup CFSG.FeitThompson.Prep06

variable {G : Type*} [Group G] {M W₁ W₂ : Subgroup G}

theorem natCard_subgroupOf_eq_of_le (hle : W₁ ≤ M) :
    Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
  Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hle).bijective

theorem IsWitnessedPConfiguration.isPrimeCyclicTIHyp_subgroupOf [Finite G]
    (hodd : Odd (Nat.card G)) {U : Subgroup G} (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M) := by
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hKeq : derivedOf M = (⁅M, M⁆ : Subgroup G).subgroupOf M := by
    rw [derivedOf_eq, Subgroup.subgroupOf, ← Subgroup.map_subtype_commutator M,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁).bijective
  have hcard2 : Nat.card ↥(W₂.subgroupOf M) = Nat.card ↥W₂ :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hc.le_M_W₂).bijective
  have hcardK : Nat.card ↥(derivedOf M) = Nat.card ↥(⁅M, M⁆ : Subgroup G) := by
    rw [hKeq]
    exact Nat.card_eq_of_bijective _
      (Subgroup.subgroupOfEquivOfLe (Subgroup.commutator_le_self M)).bijective
  have hcardW : Nat.card ↥((W₁ ⊔ W₂).subgroupOf M) = Nat.card ↥(W₁ ⊔ W₂ : Subgroup G) :=
    Nat.card_eq_of_bijective _ (Subgroup.subgroupOfEquivOfLe hc.le_M_sup_W₁_W₂).bijective
  have hcompl := hc.isComplement'_subgroupOf_commutator_W₁
  rw [← hKeq] at hcompl
  refine
  { normal := hKeq ▸ normal_subgroupOf_commutator_self M
    mul_eq_univ := Set.eq_univ_of_forall fun g => ?_
    inf_eq_bot := disjoint_iff.1 hcompl.disjoint
    coprime_natCard := by
      rw [hcardK, hcard1]; exact hc.coprime_natCard_W₁_natCard_commutator.symm
    left_ne_bot := fun hbot => hc.ne_bot_W₁ (Subgroup.card_eq_one.1
      (by rw [← hcard1, hbot]; simp))
    right_ne_bot := fun hbot => hc.ne_bot_W₂ (Subgroup.card_eq_one.1
      (by rw [← hcard2, hbot]; simp))
    isCyclic_left := isCyclic_of_surjective (hH := hc.isCyclic_W₁) _
      (Subgroup.subgroupOfEquivOfLe hc.le_M_W₁).symm.surjective
    isCyclic_right := isCyclic_of_surjective (hH := hc.isCyclic_W₂) _
      (Subgroup.subgroupOfEquivOfLe hc.le_M_W₂).symm.surjective
    right_le := hKeq ▸ Subgroup.comap_mono
      (hc.le_hallCore_W₂.trans hc.hallCore_le_commutator)
    centralizer_eq := ?_
    odd_natCard := ?_ }
  ·
    obtain ⟨⟨k, w⟩, hkw, -⟩ := hcompl.existsUnique g
    exact ⟨(k : ↥M), k.2, (w : ↥M), w.2, hkw⟩
  ·
    intro x hx hx1
    have hxG : (x : G) ∈ W₁ := hx
    have hxG1 : (x : G) ≠ 1 := fun hcon => hx1 (Subtype.ext hcon)
    have hkey := hc.inf_centralizer_eq_W₂ (x : G) hxG hxG1
    have hcen : (Subgroup.centralizer ({x} : Set ↥M))
        = (Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf M := by
      ext y
      simp [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subtype.ext_iff]
    rw [hKeq, hcen, Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hkey,
      Subgroup.subgroupOf]
  ·
    rw [hcard1, hcard2, ← hc.natCard_sup_W₁_W₂, ← hcardW]
    exact hModd.of_dvd_nat (Subgroup.card_subgroup_dvd_card _)

variable [Fintype G]

theorem rowData_w_eq
    (h : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {σ : ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) →ₗ[ℂ] ↥(classFun ↥M)}
    {w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M))}
    {l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ}
    (hrow : IsRowData M W₁ W₂ σ w l) (i : Irr ↥(W₁.subgroupOf M))
    (j : Irr ↥(W₂.subgroupOf M)) :
    w i j = h.isCyclicTIPair.basisProdIrr (i, j) := by
  refine Subtype.ext (funext fun z => ?_)
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_mul_eq_of_mem_sup z.2
  rw [IsCyclicTIPair.coe_basisProdIrr_apply]
  have hz : z = (⟨x * y, hxy ▸ z.2⟩ : ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) :=
    Subtype.ext hxy.symm
  rw [hz, hrow.prod i j ⟨x, hx⟩ ⟨y, hy⟩ _ rfl,
    h.isCyclicTIPair.prodChar_apply_mul _ _ hx hy]

theorem rowData_l_eq
    (h : IsPrimeCyclicTIHyp (derivedOf M) (W₁.subgroupOf M) (W₂.subgroupOf M))
    {σ : ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M)) →ₗ[ℂ] ↥(classFun ↥M)}
    {w : ↑(Irr ↥(W₁.subgroupOf M)) → ↑(Irr ↥(W₂.subgroupOf M)) →
      ↥(classFun ↥(W₁.subgroupOf M ⊔ W₂.subgroupOf M))}
    {l : ↑(Irr ↥(W₁.subgroupOf M)) → ↥M → ℂ}
    (hrow : IsRowData M W₁ W₂ σ w l) (i : Irr ↥(W₁.subgroupOf M)) :
    l i = h.inflateLeft i := by
  funext z
  obtain ⟨k, hk, v, hv, rfl⟩ := h.exists_decomp z
  rw [hrow.infl i ⟨k, hk⟩ ⟨v, hv⟩ _ rfl, h.inflateLeft_apply_mul i hk hv]

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson CFSG.FeitThompson.Prep06

universe u

open scoped Classical in
theorem FPF_type_iii_v_local_character_constants
    (hprime : Statements.FPF_type_iii_v_second_factor_prime.{u}) :
    Statements.FPF_type_iii_v_local_character_constants.{u} := by
  intro G _ _ hG M U W₁ W₂ hM htype hc
  have h := hc.isPrimeCyclicTIHyp_subgroupOf hG.odd
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hcard1 : Nat.card ↥(W₁.subgroupOf M) = Nat.card ↥W₁ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₁
  have hcard2 : Nat.card ↥(W₂.subgroupOf M) = Nat.card ↥W₂ :=
    natCard_subgroupOf_eq_of_le hc.le_M_W₂
  have hp : (Nat.card ↥(W₂.subgroupOf M)).Prime := by
    rw [hcard2]; exact hprime G hG M U W₁ W₂ hM htype hc
  have hW₂le : W₂.subgroupOf M ≤ commutator ↥M := derivedOf_eq M ▸ h.right_le
  refine ⟨h.exists_isCyclicTIIsometry, ?_, ?_⟩
  ·
    intro σ w l hrow j
    rw [rowData_w_eq h hrow]
    exact h.existsUnique_primeTISign hrow.isometry j
  ·
    intro σ w l δ μ hsetup
    have hσ := hsetup.isometry
    have hδ : ∀ j, δ j = h.primeTISign σ j := by
      intro j
      refine (h.existsUnique_primeTISign hσ j).unique ⟨hsetup.sign j, ?_⟩
        ⟨h.primeTISign_eq_one_or_eq_neg_one j, ?_⟩
      · rw [← rowData_w_eq h hsetup.toIsRowData]
        exact hsetup.mu_zero_mem j
      · exact h.primeTIirr_principal_left (σ := σ) j ▸
          h.primeTIirr_principal_left_mem_Irr hσ j
    have hμ : ∀ i j, μ i j = h.primeTIirr σ i j := by
      intro i j
      rw [hsetup.mu_eq i j, rowData_l_eq h hsetup.toIsRowData i,
        rowData_w_eq h hsetup.toIsRowData, hδ j, h.primeTIirr_eq_mul i j,
        h.primeTIirr_principal_left]
    obtain ⟨d, hdodd, hd1, s, hspm, n, hneven, hn2, hdn, hall⟩ :=
      h.exists_primeTIirr_constants hσ hModd hp hW₂le
    have hdt : ((d.toNat : ℤ)) = d := Int.toNat_of_nonneg (by omega)
    have hnt : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg (by omega)
    refine ⟨d.toNat, n.toNat, (s : ℂ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨t, ht⟩ := hdodd; exact ⟨t.toNat, by omega⟩
    · omega
    · rcases hspm with h1 | h1 <;> rw [h1] <;> norm_num
    · obtain ⟨t, ht⟩ := hneven; exact ⟨t.toNat, by omega⟩
    · omega
    · intro i j hj
      rw [hμ i j, (hall i j hj).1]
      exact_mod_cast hdt.symm
    · intro j hj
      rw [hδ j, (hall (principalIrr _) j hj).2.2]
    · have hz : (d.toNat : ℤ) - s = (n.toNat : ℤ) * (Nat.card ↥W₁ : ℤ) := by
        rw [hdt, hnt, hdn, hcard1]
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hz

end CFSG.FeitThompson.Proofs
