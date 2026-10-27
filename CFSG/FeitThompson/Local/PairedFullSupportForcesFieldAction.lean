module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TauThirteenTypeIStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.Local.TypePReducibleInnerActionOrder
import CFSG.FeitThompson.Local.LocalTypeIAlternative
import CFSG.FeitThompson.Representations.TypeISupportingGroupConfiguration
import CFSG.FeitThompson.Local.NonuniquePlaneLineCentralizerBounds
import CFSG.FeitThompson.Local.FreePrimeActionCentralizerBound
import CFSG.FeitThompson.Local.BlackburnCoprimeCentralProduct
import CFSG.FeitThompson.Local.ControlledNormalElementaryPlane
import CFSG.FeitThompson.OddOrder.PTypeClausesIndependentOfComplement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.Prep05

universe u

namespace PairedFullSupportFieldAction

section Submodule

variable {G : Type*} [Group G] {H : Subgroup G} {Vm : Type*} [AddCommGroup Vm]

def submoduleOfSubgroup (p : ℕ) [Module (ZMod p) Vm] (e : ↥H ≃* Multiplicative Vm)
    (K : Subgroup G) : Submodule (ZMod p) Vm :=
  AddSubgroup.toZModSubmodule p
    (Subgroup.toAddSubgroup' ((K.subgroupOf H).map e.toMonoidHom))

variable {p : ℕ} [Module (ZMod p) Vm] {e : ↥H ≃* Multiplicative Vm} {K : Subgroup G}

theorem mem_submoduleOfSubgroup {v : Vm} :
    v ∈ submoduleOfSubgroup p e K ↔ ((e.symm (Multiplicative.ofAdd v) : ↥H) : G) ∈ K := by
  have hiff : v ∈ submoduleOfSubgroup p e K ↔
      Multiplicative.ofAdd v ∈ (K.subgroupOf H).map e.toMonoidHom := Iff.rfl
  rw [hiff, Subgroup.mem_map]
  refine ⟨?_, fun h => ⟨e.symm (Multiplicative.ofAdd v), (Subgroup.mem_subgroupOf).2 h,
    e.apply_symm_apply _⟩⟩
  rintro ⟨x, hx, hxv⟩
  have h : e.symm (Multiplicative.ofAdd v) = x := by
    rw [← hxv]; exact e.symm_apply_apply x
  rw [h]
  exact (Subgroup.mem_subgroupOf).1 hx

theorem mem_submoduleOfSubgroup_toAdd {x : ↥H} :
    Multiplicative.toAdd (e x) ∈ submoduleOfSubgroup p e K ↔ (x : G) ∈ K := by
  rw [mem_submoduleOfSubgroup,
    show Multiplicative.ofAdd (Multiplicative.toAdd (e x)) = e x from rfl,
    MulEquiv.symm_apply_apply]

theorem submoduleOfSubgroup_eq_bot_iff (hKH : K ≤ H) :
    submoduleOfSubgroup p e K = ⊥ ↔ K = ⊥ := by
  constructor
  · intro h
    refine le_antisymm (fun x hx => ?_) bot_le
    have hxH : x ∈ H := hKH hx
    have hmem : Multiplicative.toAdd (e ⟨x, hxH⟩) ∈ submoduleOfSubgroup p e K :=
      mem_submoduleOfSubgroup_toAdd.2 hx
    rw [h, Submodule.mem_bot] at hmem
    have h2 : (⟨x, hxH⟩ : ↥H) = 1 := by
      refine e.injective ?_
      rw [map_one]
      exact Multiplicative.toAdd.injective (by simpa using hmem)
    exact Subgroup.mem_bot.2 (congrArg Subtype.val h2)
  · rintro rfl
    refine le_antisymm (fun v hv => ?_) bot_le
    have h := mem_submoduleOfSubgroup.1 hv
    rw [Subgroup.mem_bot] at h
    have h3 := congrArg e (Subtype.ext h : e.symm (Multiplicative.ofAdd v) = 1)
    rw [MulEquiv.apply_symm_apply, map_one] at h3
    exact (Submodule.mem_bot _).2 (Multiplicative.ofAdd.injective h3)

theorem submoduleOfSubgroup_eq_top_iff :
    submoduleOfSubgroup p e K = ⊤ ↔ H ≤ K := by
  refine ⟨fun h x hx => ?_, fun h => le_antisymm le_top fun v _ =>
    mem_submoduleOfSubgroup.2 (h (e.symm (Multiplicative.ofAdd v)).2)⟩
  have hmem : Multiplicative.toAdd (e ⟨x, hx⟩) ∈ submoduleOfSubgroup p e K := by
    rw [h]; exact Submodule.mem_top
  exact mem_submoduleOfSubgroup_toAdd.1 hmem

theorem isInvariantSubmodule_submoduleOfSubgroup {M U : Subgroup G}
    {ρ : ↥M →* (Vm ≃ₗ[ZMod p] Vm)} (hρ : IsConjModule p H M Vm e ρ)
    (hHM : M ≤ normalizer (H : Set G))
    (hinv : ∀ x ∈ U, ∀ z ∈ K, x * z * x⁻¹ ∈ K) :
    IsInvariantSubmodule ((U.subgroupOf M).map ρ) (submoduleOfSubgroup p e K) := by
  rintro g hg v hv
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hg
  have hxU : (x : G) ∈ U := (Subgroup.mem_subgroupOf).1 hx
  set z : ↥H := e.symm (Multiplicative.ofAdd v) with hz
  have hzK : (z : G) ∈ K := mem_submoduleOfSubgroup.1 hv
  have hvz : v = Multiplicative.toAdd (e z) := by rw [hz]; simp
  rw [hvz, CFSG.FeitThompson.Proofs.toAdd_e_conj hρ hHM x z]
  exact mem_submoduleOfSubgroup_toAdd.2 (hinv (x : G) hxU (z : G) hzK)

end Submodule

section Ambient

variable {G : Type u} [Group G]

theorem hallCoreIn_eq_hallCoreOf (M : Subgroup G) :
    CFSG.FeitThompson.hallCoreIn M = CFSG.FeitThompson.Prep05.hallCoreOf M := (rfl)

variable [Finite G]

theorem isMinimalSimpleOdd_of_isOddSimpleMinimal (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) :
    CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩

theorem isAmbient_of_isOddSimpleMinimal [Fintype G] (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) :
    CFSG.FeitThompson.Prep03.IsAmbient G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩

theorem isMinimalSimpleOddOrder_of_isOddSimpleMinimal (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) :
    CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
  ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩

end Ambient

section Clauses

variable {G : Type u} [Group G] [Finite G]

theorem natCard_hallCoreIn_of_elementary_core_structure
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    Nat.card ↥(CFSG.FeitThompson.hallCoreIn M) = Nat.card ↥W₂ ^ Nat.card ↥W₁ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcard, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc _ _ rfl rfl
  rw [hallCoreIn_eq_hallCoreOf]
  exact hcard

theorem eq_bot_or_eq_hallCoreIn_of_le_normalizer
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {N : Subgroup G}
    (hN : N ≤ CFSG.FeitThompson.hallCoreIn M) (hnorm : M ≤ normalizer (N : Set G)) :
    N = ⊥ ∨ N = CFSG.FeitThompson.hallCoreIn M := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmin, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc _ _ rfl rfl
  exact hmin N hN hnorm

theorem eq_three_of_forall_conj_mem
    (h₁ : CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) {K : Subgroup G}
    (hKH : K ≤ CFSG.FeitThompson.hallCoreIn M) (hKbot : K ≠ ⊥) (hKtop : K ≠ CFSG.FeitThompson.hallCoreIn M)
    (hinv : ∀ x ∈ U, ∀ z ∈ K, x * z * x⁻¹ ∈ K) :
    Nat.card ↥W₁ = 3 ∧ Nat.card ↥U = ((Nat.card ↥W₂ - 1) / 2) ^ 2 ∧
      Odd ((Nat.card ↥W₂ - 1) / 2) ∧ 1 < (Nat.card ↥W₂ - 1) / 2 := by
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set q : ℕ := Nat.card ↥W₁ with hqdef
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -,
    ⟨Vm, _, _, -, ⟨e⟩⟩, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc p q rfl rfl
  have hHM : M ≤ normalizer ((CFSG.FeitThompson.Prep05.hallCoreOf M : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore M
  set ρ : ↥M →* (Vm ≃ₗ[ZMod p] Vm) := conjLinear p hHM e with hρdef
  have hρ : IsConjModule p (CFSG.FeitThompson.Prep05.hallCoreOf M) M Vm e ρ :=
    isConjModule_conjLinear p hHM e
  have hKH' : K ≤ CFSG.FeitThompson.Prep05.hallCoreOf M := hKH
  have hred : ∃ W : Submodule (ZMod p) Vm, W ≠ ⊥ ∧ W ≠ ⊤ ∧
      IsInvariantSubmodule ((U.subgroupOf M).map ρ) W :=
    ⟨submoduleOfSubgroup p e K,
      fun h => hKbot ((submoduleOfSubgroup_eq_bot_iff hKH').1 h),
      fun h => hKtop (le_antisymm hKH (submoduleOfSubgroup_eq_top_iff.1 h)),
      isInvariantSubmodule_submoduleOfSubgroup hρ hHM hinv⟩
  obtain ⟨hq3, hrest⟩ :=
    CFSG.FeitThompson.Proofs.FNI_type_p_reducible_inner_action_order.{u, u} h₁ h₂ G
      (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc p q rfl rfl Vm e ρ hρ hred
  obtain ⟨hUcard, -, -, hAodd, hA1⟩ := hrest ((p - 1) / 2) rfl
  exact ⟨hq3, hUcard, hAodd, hA1⟩

end Clauses

section Core

variable {G : Type u} [Group G] [Finite G]

theorem not_sq_dvd_cube_sub_one {A : ℕ} (hodd : Odd A) (hA1 : 1 < A) (h3 : ¬ (3 ∣ A)) :
    ¬ A ^ 2 ∣ (2 * A + 1) ^ 3 - 1 := by
  intro hdvd
  have hexp : (2 * A + 1) ^ 3 - 1 = A ^ 2 * (8 * A + 12) + 6 * A := by ring_nf; omega
  rw [hexp] at hdvd
  have h6A : A ^ 2 ∣ 6 * A := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp hdvd
  have hA0 : 0 < A := by omega
  have hA6 : A ∣ 6 := by
    obtain ⟨c, hc⟩ := h6A
    exact ⟨c, Nat.eq_of_mul_eq_mul_left hA0 (by rw [mul_comm A 6, hc]; ring)⟩
  have hle : A ≤ 6 := Nat.le_of_dvd (by norm_num) hA6
  rw [Nat.odd_iff] at hodd
  interval_cases A <;> revert hodd h3 h6A <;> decide

theorem not_dvd_sub_one_and_self {r n : ℕ} (hr : 1 < r) (h1 : r ∣ n - 1) (hrn : r ∣ n)
    (hn : 1 < n) : False := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := hrn
  have hb' : r * (b - a) = 1 := by rw [Nat.mul_sub]; omega
  have := Nat.eq_one_of_mul_eq_one_right hb'
  omega

theorem exists_isSylow_mem_of_orderOf_eq {U : Subgroup G} {r : ℕ} (hr : r.Prime) {x : G}
    (hxU : x ∈ U) (hxord : orderOf x = r) :
    ∃ R0 : Subgroup G, R0 ≤ U ∧ x ∈ R0 ∧
      Nat.card ↥R0 = r ^ (Nat.card ↥U).factorization r := by
  have := Fact.mk hr
  set x' : ↥U := ⟨x, hxU⟩ with hx'
  have hzp : IsPGroup r ↥(zpowers x') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one, hx', ← hxord]
    exact (orderOf_coe (⟨x, hxU⟩ : ↥U)).symm
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  exact ⟨(P : Subgroup ↥U).map U.subtype, Subgroup.map_subtype_le _,
    Subgroup.mem_map.2 ⟨x', hP (mem_zpowers x'), rfl⟩,
    by rw [Subgroup.card_map_of_injective U.subtype_injective]; exact P.card_eq_multiplicity⟩

theorem ne_L_of_isPairedSupportingSetup
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y) : S ≠ L := by
  obtain ⟨-, -, -, -, -, -, hUne, -, -, -, hcop, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) S U W₁ W₂ hsetup.isCoatom_S
      hsetup.config_S _ _ rfl rfl
  intro hSL
  have hUH : U ≤ hallCoreOf S := by
    rw [show hallCoreOf S = _root_.CFSG.FeitThompson.hallCoreIn L by
      rw [← hSL, hallCoreIn_eq_hallCoreOf]]
    exact hsetup.le_hallCoreIn_L
  exact hUne (Subgroup.card_eq_one.1
    (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hUH) hcop)
      dvd_rfl (Dvd.intro _ rfl)))

theorem centralizer_le_of_mem_coreFixedSet
    (h₃ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    {x : G} (hxS' : x ∈ (⁅S, S⁆ : Subgroup G)) (hx1 : x ≠ 1)
    (hxc : CFSG.FeitThompson.Prep09.centIn (CFSG.FeitThompson.Prep09.hallCoreIn S) {x} ≠ ⊥) :
    centralizer ({x} : Set G) ≤ S := by
  obtain ⟨-, -, -, -, -, -, hcent⟩ :=
    h₃ G (isMinimalSimpleOddOrder_of_isOddSimpleMinimal hG) S U W₁ W₂ hsetup.isCoatom_S
      hsetup.isTypeII_S
      (hsetup.isTypeII_S.clauses_of_isWitnessedPConfiguration
        (hG.isSolvable_of_ne_top S hsetup.isCoatom_S.1) hsetup.config_S) _ rfl
  rw [hcent x (Or.inl ⟨hxS', hx1, hxc⟩)]
  exact inf_le_left

theorem natCard_W₁_ne_three_of_isPairedSupportingSetup
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hq3 : Nat.card ↥W₁ = 3)
    (hUcard : Nat.card ↥U = ((Nat.card ↥W₂ - 1) / 2) ^ 2)
    (hAodd : Odd ((Nat.card ↥W₂ - 1) / 2)) (hA1 : 1 < (Nat.card ↥W₂ - 1) / 2) :
    False := by
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set A : ℕ := (p - 1) / 2 with hAdef
  obtain ⟨-, hpp, -, hop, -, -, hUne, hUcomm, hsemiS, hsemiUW, hcop, hfpf,
    -, hHcard, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) S U W₁ W₂ hsetup.isCoatom_S
      hsetup.config_S p (Nat.card ↥W₁) rfl rfl
  have hp2A : p = 2 * A + 1 := by obtain ⟨k, hk⟩ := hop; rw [hAdef]; omega
  have hU1 : 1 < Nat.card ↥U := (Subgroup.one_lt_card_iff_ne_bot U).2 hUne
  have hUS : U ≤ S := hsetup.config_S.le_M_E
  have hSN : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hdvdW : Nat.card ↥W₁ ∣ Nat.card ↥U - 1 :=
    natCard_dvd_sub_one_of_forall_inf_centralizer_eq_bot (le_refl U)
      hsemiUW.right_le_normalizer
      fun w hw hw1 => inf_centralizer_singleton_eq_bot_of_isFixedPointFreeOn hfpf hw hw1
  have h3A : ¬ (3 ∣ A) := by
    intro h3
    have h9 : 3 ∣ A ^ 2 := Dvd.dvd.pow h3 (by norm_num)
    have hA2 : 1 ≤ A ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [hq3, hUcard] at hdvdW
    omega
  by_cases hfreeU : ∀ u ∈ U, u ≠ 1 → hallCoreOf S ⊓ centralizer ({u} : Set G) = ⊥
  ·
    have hdvd : Nat.card ↥U ∣ Nat.card ↥(hallCoreOf S) - 1 :=
      natCard_dvd_sub_one_of_forall_inf_centralizer_eq_bot (le_refl _) (hUS.trans hSN) hfreeU
    rw [hHcard, hq3, hUcard, hp2A] at hdvd
    exact not_sq_dvd_cube_sub_one hAodd hA1 h3A hdvd
  ·
    push_neg at hfreeU
    obtain ⟨u, huU, hu1, hunb⟩ := hfreeU
    have hord : orderOf u ≠ 1 := by simpa [orderOf_eq_one_iff] using hu1
    obtain ⟨r, hr, k, hk⟩ := Nat.exists_prime_and_dvd hord
    have hu0 : 0 < orderOf u := orderOf_pos u
    have hk0 : k ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hk; omega
    set x : G := u ^ k with hxdef
    have hxord : orderOf x = r := by
      rw [hxdef, orderOf_pow_of_dvd hk0 ⟨r, by rw [hk]; ring⟩, hk,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hk0)]
    have hxU : x ∈ U := U.pow_mem huU k
    have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hxord; exact hr.one_lt.ne hxord
    have hxnb : hallCoreOf S ⊓ centralizer ({x} : Set G) ≠ ⊥ := fun hb =>
      hunb (le_antisymm (le_trans (inf_le_inf_left _ fun z hz => by
        rw [mem_centralizer_singleton_iff] at hz ⊢
        rw [hxdef]
        exact (Commute.pow_left (h := hz.symm) k).symm) (le_of_eq hb)) bot_le)
    have hxS : centralizer ({x} : Set G) ≤ S :=
      centralizer_le_of_mem_coreFixedSet h₃ hG hsetup
        (hsetup.config_S.le_commutator_E hxU) hx1 hxnb
    have hrU : r ∣ Nat.card ↥U := hxord ▸ Subgroup.orderOf_dvd_natCard U hxU
    have hrleA : r ≤ A := Nat.le_of_dvd (by omega) (hr.dvd_of_dvd_pow (hUcard ▸ hrU))
    have hrH : ¬ r ∣ Nat.card ↥(hallCoreOf S) := fun hd =>
      hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcop hd (hrU.mul_right _))
    have hrW₁ : ¬ r ∣ Nat.card ↥W₁ := fun hd =>
      not_dvd_sub_one_and_self hr.one_lt (hd.trans hdvdW) hrU hU1
    obtain ⟨R0, hR0U, hxR0, hR0c⟩ := exists_isSylow_mem_of_orderOf_eq hr hxU hxord
    have hR0syl : Nat.card ↥R0 = r ^ (Nat.card ↥S).factorization r := by
      rw [hR0c]; congr 1
      rw [hsemiS.natCard_eq_mul, hsemiUW.natCard_eq_mul,
        Nat.factorization_mul Nat.card_pos.ne'
          (Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'),
        Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne']
      simp only [Finsupp.coe_add, Pi.add_apply]
      rw [Nat.factorization_eq_zero_of_not_dvd hrH, Nat.factorization_eq_zero_of_not_dvd hrW₁]
      simp
    have hR0S : R0 ≤ S := hR0U.trans hUS
    have hR0HL : R0 ≤ CFSG.FeitThompson.hallCoreIn L := hR0U.trans hsetup.le_hallCoreIn_L
    have hR0bot : R0 ≠ ⊥ := fun h => by
      rw [h, Subgroup.mem_bot] at hxR0
      rw [hxR0, orderOf_one] at hxord
      exact hr.one_lt.ne hxord
    have : IsMulCommutative ↥U := hUcomm
    have hR0comm : IsMulCommutative ↥R0 := isMulCommutative_of_le hR0U
    have := hG.isSimpleGroup
    have hrank : 3 ∉ elementaryAbelianRanks r ↥R0 := by
      rw [← elementaryAbelianPRank_le_two_iff hr.one_lt]
      exact CFSG.FeitThompson.Proofs.elementaryAbelianPRank_le_two_of_le_of_le
        hG.not_isMulCommutative hG.odd_natCard hG.isSolvable_of_ne_top hsetup.isCoatom_S
        hsetup.isCoatom_L (ne_L_of_isPairedSupportingSetup h₂ hG hsetup) hR0S
        (hR0HL.trans (CFSG.FeitThompson.hallCoreIn_le L)) r
    have hBcard : Nat.card ↥(CFSG.FeitThompson.conjSubgroup W₂ y) = p := by
      rw [CFSG.FeitThompson.conjSubgroup_eq]
      exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
    have hbound : p ≤ r + 1 := by
      refine prime_le_succ_of_centralizer_le_of_free_action hpp hr ?_
        (le_inf hR0S hR0HL) hR0bot hR0comm hR0syl hrank hxR0 hxS ?_ hBcard ?_
      · exact isNilpotent_hallCoreOf L
      · exact ((le_sup_right : CFSG.FeitThompson.conjSubgroup W₂ y ≤ _).trans
          hsetup.isInternalSemidirectProduct.right_le).trans
          (le_normalizer_map_subtype_hallCore L)
      · intro b hb hb1
        rw [inf_comm]
        exact hsetup.centralizer_eq_bot b
          ((le_sup_right : CFSG.FeitThompson.conjSubgroup W₂ y ≤ _) hb) hb1
    omega

theorem eq_bot_or_eq_hallCoreIn_of_forall_conjSubgroup_le
    (h₁ : CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y) {K : Subgroup G}
    (hK : K ≤ CFSG.FeitThompson.hallCoreIn S)
    (hinv : ∀ u ∈ U, CFSG.FeitThompson.conjSubgroup K u ≤ K) :
    K = ⊥ ∨ K = CFSG.FeitThompson.hallCoreIn S := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hKbot, hKtop⟩ := hcon
  have hinv' : ∀ x ∈ U, ∀ z ∈ K, x * z * x⁻¹ ∈ K := by
    intro x hx z hz
    refine hinv x⁻¹ (U.inv_mem hx) ?_
    refine CFSG.FeitThompson.mem_conjSubgroup.2 ?_
    simpa [mul_assoc] using hz
  obtain ⟨hq3, hUcard, hAodd, hA1⟩ :=
    eq_three_of_forall_conj_mem h₁ h₂ hG hsetup.isCoatom_S hsetup.config_S hK hKbot hKtop hinv'
  exact absurd (natCard_W₁_ne_three_of_isPairedSupportingSetup h₂ h₃ hG hsetup hq3 hUcard hAodd
    hA1) not_false

end Core

end PairedFullSupportFieldAction

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson.PairedFullSupportFieldAction

public section

universe u

theorem FNI_paired_full_support_forces_field_action
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FNI_paired_full_support_forces_field_action.{u} := by
  intro G _ _ hG S T L U V W₁ W₂ y hsetup K hK hinv
  exact eq_bot_or_eq_hallCoreIn_of_forall_conjSubgroup_le h₁ h₂ h₃ hG hsetup hK hinv

end

end CFSG.FeitThompson.Proofs
