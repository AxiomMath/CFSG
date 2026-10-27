module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.PairedFullSupportForcesFieldAction
import CFSG.FeitThompson.Local.TypePFieldInnerComplementOrder
public import CFSG.FeitThompson.Local.TypePInnerActionFaithful
import CFSG.FeitThompson.Local.PCoreLinearAlternativePConfiguration
import CFSG.FeitThompson.OddOrder.ReducedNormQuotientNoFreeKernel
import CFSG.FeitThompson.OddOrder.MobiusNormIteration
public import CFSG.FeitThompson.OddOrder.AppendixCPrimeComparison
import CFSG.FeitThompson.OddOrder.AffineFieldCentralizers
import CFSG.FeitThompson.Foundations.IrreducibleCubicSplitsCubicField

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace PairedFullSupportNotCharacteristic

open Subgroup CFSG.FeitThompson.Prep05

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open CFSG.FeitThompson.PairedFullSupportFieldAction

universe u

variable {G : Type u} [Group G]

theorem conj_mem_of_characteristic_subgroupOf {H U : Subgroup G} (hUH : U ≤ H)
    (hchar : (U.subgroupOf H).Characteristic) {g : G} (hg : g ∈ normalizer (H : Set G))
    {x : G} (hx : x ∈ U) : g * x * g⁻¹ ∈ U := by
  set φ : MulAut ↥H := conjOnNormalized H (le_refl (normalizer (H : Set G))) ⟨g, hg⟩ with hφ
  have hmap : (U.subgroupOf H).map (φ : ↥H →* ↥H) = U.subgroupOf H :=
    Subgroup.characteristic_iff_map_eq.1 hchar φ
  have hxU : (⟨x, hUH hx⟩ : ↥H) ∈ U.subgroupOf H := Subgroup.mem_subgroupOf.2 hx
  have hmem : φ ⟨x, hUH hx⟩ ∈ U.subgroupOf H := by
    rw [← hmap]; exact Subgroup.mem_map.2 ⟨_, hxU, rfl⟩
  have hcoe : ((φ ⟨x, hUH hx⟩ : ↥H) : G) = g * x * g⁻¹ :=
    conjOnNormalized_apply_coe _ ⟨g, hg⟩ ⟨x, hUH hx⟩
  have h := Subgroup.mem_subgroupOf.1 hmem
  rwa [hcoe] at h

theorem le_normalizer_of_characteristic_subgroupOf {H U K : Subgroup G} (hUH : U ≤ H)
    (hchar : (U.subgroupOf H).Characteristic) (hKH : K ≤ normalizer (H : Set G)) :
    K ≤ normalizer (U : Set G) := by
  intro g hg
  refine Subgroup.mem_set_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩
  · exact conj_mem_of_characteristic_subgroupOf hUH hchar (hKH hg) hh
  · have h2 := conj_mem_of_characteristic_subgroupOf hUH hchar
      (inv_mem (hKH hg) : g⁻¹ ∈ normalizer (H : Set G)) hh
    rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at h2

theorem natCard_conj {W : Subgroup G} {y : G} :
    Nat.card ↥(CFSG.FeitThompson.conjSubgroup W y) = Nat.card ↥W := by
  rw [CFSG.FeitThompson.conjSubgroup_eq]
  exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective

theorem conj_W₂_le_L [Finite G] {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y) :
    CFSG.FeitThompson.conjSubgroup W₂ y ≤ L :=
  (le_sup_right : CFSG.FeitThompson.conjSubgroup W₂ y ≤ _).trans
    hsetup.isInternalSemidirectProduct.right_le

theorem le_normalizer_conj_W₂ [Finite G] {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hchar : (U.subgroupOf (CFSG.FeitThompson.hallCoreIn L)).Characteristic) :
    CFSG.FeitThompson.conjSubgroup W₂ y ≤ normalizer (U : Set G) :=
  le_normalizer_of_characteristic_subgroupOf hsetup.le_hallCoreIn_L hchar
    ((conj_W₂_le_L hsetup).trans (le_normalizer_map_subtype_hallCore L))

theorem free_action [Finite G] {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hnorm : CFSG.FeitThompson.conjSubgroup W₂ y ≤ normalizer (U : Set G)) :
    ∀ k : ↥U, k ≠ 1 → ∀ a : ↥(CFSG.FeitThompson.conjSubgroup W₂ y),
      conjOnNormalized U hnorm a k = k → a = 1 := by
  intro k hk a ha
  by_contra hane
  have haE : (a : G) ∈ W₁ ⊔ CFSG.FeitThompson.conjSubgroup W₂ y :=
    (le_sup_right : CFSG.FeitThompson.conjSubgroup W₂ y ≤ _) a.2
  have ha1 : (a : G) ≠ 1 := fun h => hane (Subtype.ext h)
  have hbot := hsetup.centralizer_eq_bot (a : G) haE ha1
  have hc := congrArg (Subtype.val (p := fun z => z ∈ U)) ha
  rw [conjOnNormalized_apply_coe] at hc
  have hcomm : (a : G) * (k : G) = (k : G) * (a : G) := mul_inv_eq_iff_eq_mul.1 hc
  have hmem : (k : G) ∈ CFSG.FeitThompson.hallCoreIn L ⊓ centralizer ({(a : G)} : Set G) :=
    Subgroup.mem_inf.2 ⟨hsetup.le_hallCoreIn_L k.2, Subgroup.mem_centralizer_iff.2 (by
      intro z hz; rw [Set.mem_singleton_iff] at hz; subst hz; exact hcomm)⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hk (Subtype.ext hmem)

theorem false_of_mul_natCard_eq [Finite G] {U W₁ W₂ : Subgroup G} {y : G}
    (hlt : Nat.card ↥W₁ < Nat.card ↥W₂) (hq1 : 1 < Nat.card ↥W₁)
    (hpp : (Nat.card ↥W₂).Prime)
    (hnorm : CFSG.FeitThompson.conjSubgroup W₂ y ≤ normalizer (U : Set G))
    (hfree : ∀ k : ↥U, k ≠ 1 → ∀ a : ↥(CFSG.FeitThompson.conjSubgroup W₂ y),
      conjOnNormalized U hnorm a k = k → a = 1)
    (hcard : Nat.card ↥W₁ * Nat.card ↥U =
      ((Nat.card ↥W₂) ^ (Nat.card ↥W₁) - 1) / (Nat.card ↥W₂ - 1)) : False := by
  refine not_exists_free_mulAut_hom_of_mul_card_eq_sum_range_pow
    ↥(CFSG.FeitThompson.conjSubgroup W₂ y) ↥U hq1 hlt natCard_conj ?_ ⟨conjOnNormalized U hnorm, hfree⟩
  rw [hcard]
  exact eq_geomSum_of_eq_div hpp rfl

theorem isIrreducibleLinear_map_of_forall_conjSubgroup
    {S U : Subgroup G} {p : ℕ} {V : Type u} [AddCommGroup V] [Module (ZMod p) V]
    {e : ↥(hallCoreOf S) ≃* Multiplicative V} {ρ : ↥S →* (V ≃ₗ[ZMod p] V)}
    (hρ : IsConjModule p (hallCoreOf S) S V e ρ)
    (hSN : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G)) (hUS : U ≤ S)
    (hirr : ∀ K : Subgroup G, K ≤ CFSG.FeitThompson.hallCoreIn S →
      (∀ u ∈ U, CFSG.FeitThompson.conjSubgroup K u ≤ K) → K = ⊥ ∨ K = CFSG.FeitThompson.hallCoreIn S) :
    IsIrreducibleLinear ((U.subgroupOf S).map ρ) := by
  intro W hW
  have hK : _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W ≤ CFSG.FeitThompson.hallCoreIn S :=
    _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule_le e W
  have hconj : ∀ u ∈ U,
      CFSG.FeitThompson.conjSubgroup (_root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W) u ≤
        _root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule e W := by
    intro u hu
    rw [CFSG.FeitThompson.conjSubgroup_eq, Subgroup.map_le_iff_le_comap]
    intro z hz
    obtain ⟨hzH, hzW⟩ := _root_.CFSG.FeitThompson.Proofs.mem_subgroupOfSubmodule.1 hz
    have hu' : u⁻¹ ∈ U := U.inv_mem hu
    have hzc : u⁻¹ * z * u ∈ hallCoreOf S := by
      have h := _root_.CFSG.FeitThompson.Proofs.conj_mem_of_le_normalizer hSN (hUS hu') hzH
      simpa using h
    have hmemρ : ρ ⟨u⁻¹, hUS hu'⟩ ∈ (U.subgroupOf S).map ρ :=
      Subgroup.mem_map.2 ⟨⟨u⁻¹, hUS hu'⟩, Subgroup.mem_subgroupOf.2 hu', rfl⟩
    have h := hW _ hmemρ _ hzW
    rw [_root_.CFSG.FeitThompson.Proofs.toAdd_e_conj hρ hSN ⟨u⁻¹, hUS hu'⟩ ⟨z, hzH⟩] at h
    refine Subgroup.mem_comap.2 (_root_.CFSG.FeitThompson.Proofs.mem_subgroupOfSubmodule.2 ⟨?_, ?_⟩)
    · change (MulAut.conj u⁻¹) z ∈ hallCoreOf S
      simpa [MulAut.conj] using hzc
    · convert h using 3
      simp [MulAut.conj]
  rcases hirr _ hK hconj with h | h
  · exact Or.inl (_root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule_eq_bot_iff.1 h)
  · exact Or.inr (_root_.CFSG.FeitThompson.Proofs.subgroupOfSubmodule_eq_top_iff.1 h)

theorem inf_hallCoreIn_eq_bot [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    CFSG.FeitThompson.hallCoreIn M ⊓ U = ⊥ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcop, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc _ _ rfl rfl
  rw [hallCoreIn_eq_hallCoreOf]
  exact Subgroup.card_eq_one.1 (Nat.eq_one_of_dvd_coprimes hcop
    (Subgroup.card_dvd_of_le inf_le_left)
    (Dvd.dvd.mul_right (Subgroup.card_dvd_of_le inf_le_right) _))

theorem isMulCommutative_hallCoreIn [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂) :
    IsMulCommutative ↥(CFSG.FeitThompson.hallCoreIn M) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨Vm, _, _, -, ⟨e⟩⟩, -, -, -, -, -, -, -, -, -, -,
    -⟩ := h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc _ _ rfl rfl
  rw [hallCoreIn_eq_hallCoreOf]
  exact ⟨⟨fun x y => e.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩

theorem coprime_natCard_hallCoreIn_natCard_W₂ [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {T V W₁ W₂ : Subgroup G} (hT : IsCoatom T)
    (hc : IsWitnessedPConfiguration T V W₂ W₁) :
    (Nat.card ↥(CFSG.FeitThompson.hallCoreIn T)).Coprime (Nat.card ↥W₂) := by
  obtain ⟨-, hqp, hpp, -, -, hne, -, -, -, -, -, -, -, hcard, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) T V W₂ W₁ hT hc _ _ rfl rfl
  rw [hallCoreIn_eq_hallCoreOf, hcard]
  exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hqp hpp).2 hne)

theorem coprime_natCard_W₁_natCard_U [Finite G] {M U W₁ W₂ : Subgroup G}
    (hc : IsWitnessedPConfiguration M U W₁ W₂) : (Nat.card ↥W₁).Coprime (Nat.card ↥U) :=
  hc.coprime_natCard_W₁_natCard_commutator.coprime_dvd_right
    (Subgroup.card_dvd_of_le hc.le_commutator_E)

theorem not_dvd_sub_one_and_coprime_of_natCard_U_eq_norm [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {M U W₁ W₂ : Subgroup G} (hM : IsCoatom M)
    (hc : IsWitnessedPConfiguration M U W₁ W₂)
    (hU : Nat.card ↥U = ((Nat.card ↥W₂) ^ Nat.card ↥W₁ - 1) / (Nat.card ↥W₂ - 1)) :
    ¬ Nat.card ↥W₁ ∣ Nat.card ↥W₂ - 1 ∧ (Nat.card ↥U).Coprime (Nat.card ↥W₂ - 1) := by
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set q : ℕ := Nat.card ↥W₁ with hqdef
  obtain ⟨-, hpp, hqp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) M U W₁ W₂ hM hc p q rfl rfl
  obtain ⟨hsum, -, hgcd, hdvd0, -⟩ := sum_range_pow_congruences hpp hqp
  have hNsum : Nat.card ↥U = ∑ i ∈ Finset.range q, p ^ i := by rw [hU, ← hsum]
  have hqU : q.Coprime (Nat.card ↥U) := coprime_natCard_W₁_natCard_U hc
  have hnot : ¬ q ∣ p - 1 := by
    intro hqd
    have hpmod : p ≡ 1 [MOD q] := ((Nat.modEq_iff_dvd' hpp.one_le).2 hqd).symm
    exact hqp.one_lt.ne'
      (hqU.eq_one_of_dvd (hNsum ▸ (Nat.modEq_zero_iff_dvd).1 (hdvd0 hpmod)))
  exact ⟨hnot, by rw [Nat.Coprime, hNsum, hgcd]; exact (Nat.Prime.coprime_iff_not_dvd hqp).2 hnot⟩

theorem isIrreducibleLinear_map_of_natCard_U_eq_norm [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S U W₁ W₂ : Subgroup G} (hS : IsCoatom S)
    (hc : IsWitnessedPConfiguration S U W₁ W₂)
    {p q : ℕ} (hp : p = Nat.card ↥W₂) (hq : q = Nat.card ↥W₁)
    (hU : Nat.card ↥U = (p ^ q - 1) / (p - 1))
    {Vm : Type v} [AddCommGroup Vm] [Module (ZMod p) Vm]
    (e : ↥(hallCoreOf S) ≃* Multiplicative Vm) (ρ : ↥S →* (Vm ≃ₗ[ZMod p] Vm))
    (hρ : IsConjModule p (hallCoreOf S) S Vm e ρ) :
    IsIrreducibleLinear ((U.subgroupOf S).map ρ) := by
  set N : ℕ := (p ^ q - 1) / (p - 1) with hNdef
  set C : Subgroup G := centralizerIn U (hallCoreOf S) with hCdef
  set uu : ℕ := C.relIndex U with huudef
  obtain ⟨-, hpp, hqp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCltU, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) S U W₁ W₂ hS hc p q hp hq
  obtain ⟨-, -, hDcard, -, hucop, -, -, -, -, hxor, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_type_p_core_linear_alternative.{u, v} h₂ G
      (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) S U W₁ W₂ hS hc p q uu N hp hq rfl rfl
      Vm e ρ hρ _ _ rfl rfl
  rcases hxor with ⟨hred, -⟩ | ⟨hirr, -⟩
  · exfalso
    obtain ⟨-, L, -, -, -, -, -, ⟨a, ha1, hadvd, φ, hφ⟩, -⟩ := hred
    have hane : NeZero a := ⟨by omega⟩
    have hdvd1 : uu ∣ a ^ (q - 1) := by
      have h := Subgroup.card_dvd_of_injective φ hφ
      rw [hDcard, show Nat.card (Fin (q - 1) → Multiplicative (ZMod a)) = a ^ (q - 1) by
        simp [Nat.card_eq_fintype_card]] at h
      exact h
    have hdvdN : uu ∣ N := hU ▸ Subgroup.relIndex_dvd_card _ _
    have huu1 : uu = 1 := by
      by_contra hne
      obtain ⟨r, hr, hru⟩ := Nat.exists_prime_and_dvd hne
      have hrp : r ∣ p - 1 :=
        hr.dvd_of_dvd_pow (dvd_trans (hru.trans hdvd1) (pow_dvd_pow_of_dvd hadvd _))
      have hgcd : N.gcd (p - 1) = q.gcd (p - 1) := by
        obtain ⟨hsum, -, hg, -, -⟩ := sum_range_pow_congruences hpp hqp
        rw [hNdef, ← hsum]; exact hg
      have hrq : r ∣ q := by
        have h1 : r ∣ N.gcd (p - 1) := Nat.dvd_gcd (hru.trans hdvdN) hrp
        rw [hgcd] at h1
        exact h1.trans (Nat.gcd_dvd_left _ _)
      have h2 : r ∣ Nat.gcd uu q := Nat.dvd_gcd hru hrq
      rw [hucop] at h2
      exact hr.one_lt.ne' (Nat.dvd_one.1 h2)
    exact hCltU.ne (le_antisymm hCltU.le (Subgroup.relIndex_eq_one.1 huu1))
  · exact hirr.1

noncomputable def coreMulEquivOfLinearEquiv {p : ℕ} {H : Subgroup G} {Vm : Type v}
    [AddCommGroup Vm] [Module (ZMod p) Vm] (e : ↥H ≃* Multiplicative Vm)
    {E : Type v} [Field E] [Module (ZMod p) E] (φ : Vm ≃ₗ[ZMod p] E) :
    Multiplicative E ≃* ↥H :=
  (AddEquiv.toMultiplicative φ.symm.toAddEquiv).trans e.symm

theorem coreMulEquivOfLinearEquiv_apply {p : ℕ} {H : Subgroup G} {Vm : Type v}
    [AddCommGroup Vm] [Module (ZMod p) Vm] (e : ↥H ≃* Multiplicative Vm)
    {E : Type v} [Field E] [Module (ZMod p) E] (φ : Vm ≃ₗ[ZMod p] E) (z : E) :
    coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd z)
      = e.symm (Multiplicative.ofAdd (φ.symm z)) := (rfl)

theorem conj_coreMulEquivOfLinearEquiv {p : ℕ} {H M : Subgroup G}
    (hHM : M ≤ normalizer (H : Set G)) {Vm : Type v} [AddCommGroup Vm] [Module (ZMod p) Vm]
    (e : ↥H ≃* Multiplicative Vm) {ρ : ↥M →* (Vm ≃ₗ[ZMod p] Vm)}
    (hρ : IsConjModule p H M Vm e ρ) {E : Type v} [Field E] [Module (ZMod p) E]
    (φ : Vm ≃ₗ[ZMod p] E) (x : ↥M) {s : E} (hs : ∀ v : Vm, φ (ρ x v) = s * φ v) (z : E) :
    (x : G) * ((coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd z) : ↥H) : G) * (x : G)⁻¹
      = ((coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd (s * z)) : ↥H) : G) := by
  set h : ↥H := coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd z) with hhdef
  have hev : Multiplicative.toAdd (e h) = φ.symm z := by
    rw [hhdef, coreMulEquivOfLinearEquiv_apply, MulEquiv.apply_symm_apply]; rfl
  have hconj : (x : G) * (h : G) * (x : G)⁻¹ ∈ H :=
    _root_.CFSG.FeitThompson.Proofs.conj_mem_of_le_normalizer hHM x.2 h.2
  have hkey : Multiplicative.toAdd (e ⟨(x : G) * (h : G) * (x : G)⁻¹, hconj⟩) = φ.symm (s * z) := by
    rw [← _root_.CFSG.FeitThompson.Proofs.toAdd_e_conj hρ hHM x h, hev]
    exact φ.injective (by rw [LinearEquiv.apply_symm_apply, hs, LinearEquiv.apply_symm_apply])
  have hfinal : (⟨(x : G) * (h : G) * (x : G)⁻¹, hconj⟩ : ↥H)
      = coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd (s * z)) := by
    refine e.injective (Multiplicative.toAdd.injective ?_)
    rw [hkey, coreMulEquivOfLinearEquiv_apply, MulEquiv.apply_symm_apply]
    rfl
  exact congrArg (Subtype.val (p := fun z => z ∈ H)) hfinal

theorem inv_mul_coreMulEquivOfLinearEquiv_mul {p : ℕ} {H M : Subgroup G}
    (hHM : M ≤ normalizer (H : Set G)) {Vm : Type v} [AddCommGroup Vm] [Module (ZMod p) Vm]
    (e : ↥H ≃* Multiplicative Vm) {ρ : ↥M →* (Vm ≃ₗ[ZMod p] Vm)}
    (hρ : IsConjModule p H M Vm e ρ) {E : Type v} [Field E] [Module (ZMod p) E]
    (φ : Vm ≃ₗ[ZMod p] E) {g : G} (hg : g ∈ M) {s : E}
    (hs : ∀ v : Vm, φ (ρ ⟨g⁻¹, M.inv_mem hg⟩ v) = s * φ v) (z : E) :
    g⁻¹ * ((coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd z) : ↥H) : G) * g
      = ((coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd (z * s)) : ↥H) : G) := by
  have h := conj_coreMulEquivOfLinearEquiv hHM e hρ φ ⟨g⁻¹, M.inv_mem hg⟩ hs z
  rw [mul_comm z s]
  simpa using h

section Scalar

variable {p : ℕ} {Vm : Type v} [AddCommGroup Vm] [Module (ZMod p) Vm]
  {E : Type v} [Field E] [Module (ZMod p) E]

noncomputable def scalarLinear (φ : Vm ≃ₗ[ZMod p] E) : Eˣ →* (Vm ≃ₗ[ZMod p] Vm) where
  toFun s := (φ.trans (Units.mulLeftLinearEquiv (ZMod p) E s)).trans φ.symm
  map_one' := by ext v; simp
  map_mul' s t := by ext v; simp

theorem scalarLinear_apply (φ : Vm ≃ₗ[ZMod p] E) (s : Eˣ) (v : Vm) :
    φ (scalarLinear φ s v) = (s : E) * φ v := by simp [scalarLinear]

theorem injective_scalarLinear (φ : Vm ≃ₗ[ZMod p] E) :
    Function.Injective (scalarLinear φ) := by
  intro s t h
  have h1 : (s : E) * φ (φ.symm 1) = (t : E) * φ (φ.symm 1) := by
    rw [← scalarLinear_apply φ s, ← scalarLinear_apply φ t, h]
  rw [LinearEquiv.apply_symm_apply, mul_one, mul_one] at h1
  exact Units.ext h1

theorem eq_map_scalarLinear {D : Subgroup (Vm ≃ₗ[ZMod p] Vm)} {S₀ : Subgroup Eˣ}
    (φ : Vm ≃ₗ[ZMod p] E)
    (h : ∀ g : Vm ≃ₗ[ZMod p] Vm, g ∈ D ↔ ∃ s ∈ S₀, ∀ v : Vm, φ (g v) = (s : E) * φ v) :
    D = S₀.map (scalarLinear φ) := by
  ext g
  rw [h g, Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, hact⟩
    exact ⟨s, hs, by ext v; exact φ.injective (by rw [scalarLinear_apply, hact])⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s, hs, scalarLinear_apply φ s⟩

end Scalar

theorem eq_primeLine_of_image_fixedSubmodule_eq [Finite G] {S W₁ W₂ : Subgroup G} (hW₁S : W₁ ≤ S)
    (hW₂eq : centralizerIn (hallCoreOf S) W₁ = W₂) {p : ℕ} [Fact p.Prime]
    {Vm : Type u} [AddCommGroup Vm] [Module (ZMod p) Vm]
    (e : ↥(hallCoreOf S) ≃* Multiplicative Vm)
    {E : Type u} [Field E] [Algebra (ZMod p) E] (φ : Vm ≃ₗ[ZMod p] E)
    (himg : (fun v => φ v) ''
        (fixedSubmodule ((W₁.subgroupOf S).map
          (conjLinear p (le_normalizer_map_subtype_hallCore S) e)) : Set Vm)
      = Set.range (algebraMap (ZMod p) E)) :
    W₂ = primeLine ((CFSG.FeitThompson.hallCoreIn S).subtype.comp
        (coreMulEquivOfLinearEquiv e φ).toMonoidHom) := by
  have hρ := isConjModule_conjLinear p (le_normalizer_map_subtype_hallCore S) e
  have hbot : ((⊥ : Subfield E) : Set E) = Set.range (algebraMap (ZMod p) E) :=
    coe_bot_subfield_eq_range_algebraMap
  have hdict : ∀ h : ↥(hallCoreOf S),
      Multiplicative.toAdd (e h) ∈ fixedSubmodule ((W₁.subgroupOf S).map
        (conjLinear p (le_normalizer_map_subtype_hallCore S) e)) ↔ (h : G) ∈ W₂ :=
    fun h => (_root_.CFSG.FeitThompson.Proofs.mem_fixedSubmodule_map_rho_iff hρ
      (le_normalizer_map_subtype_hallCore S) hW₁S h).trans (SetLike.ext_iff.1 hW₂eq (h : G))
  ext g
  rw [mem_primeLine]
  constructor
  · intro hg
    have hgH : g ∈ hallCoreOf S := by
      have := hW₂eq ▸ hg
      exact (Subgroup.mem_inf.1 this).1
    refine ⟨φ (Multiplicative.toAdd (e ⟨g, hgH⟩)), ?_, ?_⟩
    · rw [← SetLike.mem_coe, hbot, ← himg]
      exact ⟨_, (hdict ⟨g, hgH⟩).2 hg, rfl⟩
    · change ((coreMulEquivOfLinearEquiv e φ
        (Multiplicative.ofAdd (φ (Multiplicative.toAdd (e ⟨g, hgH⟩)))) :
          ↥(hallCoreOf S)) : G) = g
      rw [coreMulEquivOfLinearEquiv_apply, LinearEquiv.symm_apply_apply]
      simp
  · rintro ⟨c, hc, rfl⟩
    have hc' : c ∈ (fun v => φ v) ''
        (fixedSubmodule ((W₁.subgroupOf S).map
          (conjLinear p (le_normalizer_map_subtype_hallCore S) e)) : Set Vm) := by
      rw [himg, ← hbot]; exact hc
    obtain ⟨v, hv, rfl⟩ := hc'
    have hmem := (hdict (e.symm (Multiplicative.ofAdd v))).1
      (by rw [MulEquiv.apply_symm_apply]; exact hv)
    change ((coreMulEquivOfLinearEquiv e φ (Multiplicative.ofAdd (φ v)) :
      ↥(hallCoreOf S)) : G) ∈ W₂
    rw [coreMulEquivOfLinearEquiv_apply, LinearEquiv.symm_apply_apply]
    exact hmem

theorem exists_scalar_field_model [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hU : Nat.card ↥U = ((Nat.card ↥W₂) ^ Nat.card ↥W₁ - 1) / (Nat.card ↥W₂ - 1))
    {p : ℕ} (hp : p = Nat.card ↥W₂)
    {Vm : Type u} [AddCommGroup Vm] [Module (ZMod p) Vm]
    (e : ↥(hallCoreOf S) ≃* Multiplicative Vm)
    (hirr : IsIrreducibleLinear ((U.subgroupOf S).map
      (conjLinear p (le_normalizer_map_subtype_hallCore S) e))) :
    ∃ (E : Type u) (_ : Field E) (_ : Module (ZMod p) E) (φ : Vm ≃ₗ[ZMod p] E)
      (Ue : ↥(normOneSubgroup E (Nat.card ↥U)) ≃* ↥U),
      Nat.card E = Nat.card ↥W₂ ^ Nat.card ↥W₁ ∧
      (∀ w : ↥(normOneSubgroup E (Nat.card ↥U)), ∀ v : Vm,
        φ (conjLinear p (le_normalizer_map_subtype_hallCore S) e
            ⟨((Ue w : ↥U) : G)⁻¹, S.inv_mem (hsetup.config_S.le_M_E (Ue w : ↥U).2)⟩ v)
          = ((w : Eˣ) : E) * φ v) ∧
      W₂ = primeLine ((CFSG.FeitThompson.hallCoreIn S).subtype.comp
        (coreMulEquivOfLinearEquiv e φ).toMonoidHom) := by
  have hG5 := isMinimalSimpleOdd_of_isOddSimpleMinimal hG
  have hUS : U ≤ S := hsetup.config_S.le_M_E
  have hW₁S : W₁ ≤ S := hsetup.config_S.le_M_W₁
  obtain ⟨-, hpp, -, -, -, -, -, -, -, -, -, -, -, -, -, hW₂eq, -, -, -, -, -, -, -, -⟩ :=
    h₂ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.config_S p (Nat.card ↥W₁) hp rfl
  have hfp : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hCbot, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_type_p_inner_action_faithful.{u} h₁ h₂ G hG5 S U W₁ W₂
      hsetup.isCoatom_S hsetup.config_S
  obtain ⟨-, -, -, -, -, -, -, -, -, hxor, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_type_p_core_linear_alternative.{u, u} h₂ G hG5 S U W₁ W₂
      hsetup.isCoatom_S hsetup.config_S p (Nat.card ↥W₁)
      ((centralizerIn U (hallCoreOf S)).relIndex U)
      ((p ^ Nat.card ↥W₁ - 1) / (p - 1)) hp rfl rfl rfl
      Vm e (conjLinear p (le_normalizer_map_subtype_hallCore S) e)
      (isConjModule_conjLinear p (le_normalizer_map_subtype_hallCore S) e) _ _ rfl rfl
  rcases hxor with ⟨hred, -⟩ | ⟨hfield, -⟩
  · exact absurd hirr hred.1
  obtain ⟨-, E, hE, hAlg, hEcard, φ, -, ⟨S₀, -, hS₀⟩, -, himg, -⟩ := hfield
  have hEfin : Finite E :=
    Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero _ hpp.pos.ne')
  set ψ : ↥U →* (Vm ≃ₗ[ZMod p] Vm) :=
    (conjLinear p (le_normalizer_map_subtype_hallCore S) e).comp (Subgroup.inclusion hUS)
    with hψdef
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : G) ∈ centralizerIn U (hallCoreOf S) :=
      Subgroup.mem_inf.2 ⟨x.2, (_root_.CFSG.FeitThompson.Proofs.rho_eq_one_iff
        (isConjModule_conjLinear p (le_normalizer_map_subtype_hallCore S) e)
        (le_normalizer_map_subtype_hallCore S) _).1 hx⟩
    rw [hCbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hrange : ψ.range =
      (U.subgroupOf S).map (conjLinear p (le_normalizer_map_subtype_hallCore S) e) := by
    rw [hψdef, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hD : (U.subgroupOf S).map (conjLinear p (le_normalizer_map_subtype_hallCore S) e)
      = S₀.map (scalarLinear φ) := eq_map_scalarLinear φ hS₀
  have hcardS₀ : Nat.card ↥S₀ = Nat.card ↥U := by
    have h1 : Nat.card ↥(S₀.map (scalarLinear φ)) = Nat.card ↥S₀ :=
      Subgroup.card_map_of_injective (injective_scalarLinear φ)
    have h2 : Nat.card ↥(ψ.range) = Nat.card ↥U :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    rw [← h1, ← hD, ← hrange, h2]
  have hNOcard : Nat.card ↥(normOneSubgroup E (Nat.card ↥U)) = Nat.card ↥U :=
    natCard_normOneSubgroup hpp hEcard (by rw [hU, hp])
  have hS₀le : S₀ ≤ normOneSubgroup E (Nat.card ↥U) := by
    intro s hs
    refine mem_normOneSubgroup.2 ?_
    have h := pow_card_eq_one' (x := (⟨s, hs⟩ : ↥S₀))
    rw [hcardS₀] at h
    exact congrArg Subtype.val h
  have hS₀eq : S₀ = normOneSubgroup E (Nat.card ↥U) :=
    Subgroup.eq_of_le_of_card_ge hS₀le (by rw [hNOcard, hcardS₀])
  have hmapeq : (normOneSubgroup E (Nat.card ↥U)).map (scalarLinear φ) = ψ.range := by
    rw [← hS₀eq, ← hD, hrange]
  set Ue : ↥(normOneSubgroup E (Nat.card ↥U)) ≃* ↥U :=
    ((MulEquiv.inv ↥(normOneSubgroup E (Nat.card ↥U))).trans
      (((normOneSubgroup E (Nat.card ↥U)).equivMapOfInjective (scalarLinear φ)
          (injective_scalarLinear φ)).trans
        ((MulEquiv.subgroupCongr hmapeq).trans (MonoidHom.ofInjective hψinj).symm))) with hUedef
  have key : ∀ z : ↥ψ.range,
      ψ ((MonoidHom.ofInjective hψinj).symm z) = (z : Vm ≃ₗ[ZMod p] Vm) :=
    fun z => congrArg Subtype.val ((MonoidHom.ofInjective hψinj).apply_symm_apply z)
  have hψUe : ∀ w : ↥(normOneSubgroup E (Nat.card ↥U)),
      ψ (Ue w) = scalarLinear φ ((w : Eˣ)⁻¹) := by
    intro w
    rw [hUedef]
    simp only [MulEquiv.coe_trans, Function.comp_apply, key]
    exact Subgroup.coe_equivMapOfInjective_apply (normOneSubgroup E (Nat.card ↥U))
      (scalarLinear φ) (injective_scalarLinear φ) _
  refine ⟨E, hE, Algebra.toModule, φ, Ue, by rw [hEcard, hp], fun w v => ?_,
    eq_primeLine_of_image_fixedSubmodule_eq hW₁S hW₂eq e φ himg⟩
  have h1 : (conjLinear p (le_normalizer_map_subtype_hallCore S) e) ⟨((Ue w : ↥U) : G)⁻¹,
      S.inv_mem (hsetup.config_S.le_M_E (Ue w : ↥U).2)⟩ = (ψ (Ue w))⁻¹ := by
    rw [← map_inv]
    rfl
  rw [h1, hψUe w, ← map_inv, inv_inv, scalarLinear_apply]

theorem exists_appendixC_field_model [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hU : Nat.card ↥U = ((Nat.card ↥W₂) ^ Nat.card ↥W₁ - 1) / (Nat.card ↥W₂ - 1))
    {p : ℕ} (hp : p = Nat.card ↥W₂)
    {Vm : Type u} [AddCommGroup Vm] [Module (ZMod p) Vm]
    (e : ↥(hallCoreOf S) ≃* Multiplicative Vm)
    (hirr : IsIrreducibleLinear ((U.subgroupOf S).map
      (conjLinear p (le_normalizer_map_subtype_hallCore S) e))) :
    ∃ (F : Type u) (_ : Field F) (Pe : Multiplicative F ≃* ↥(CFSG.FeitThompson.hallCoreIn S))
      (Ue : ↥(normOneSubgroup F (Nat.card ↥U)) ≃* ↥U),
      Nat.card F = Nat.card ↥W₂ ^ Nat.card ↥W₁ ∧
      (∀ (z : F) (w : ↥(normOneSubgroup F (Nat.card ↥U))),
        ((Ue w : ↥U) : G)⁻¹ *
            ((Pe (Multiplicative.ofAdd z) : ↥(CFSG.FeitThompson.hallCoreIn S)) : G) * ((Ue w : ↥U) : G)
          = ((Pe (Multiplicative.ofAdd (z * ((w : Fˣ) : F))) :
              ↥(CFSG.FeitThompson.hallCoreIn S)) : G)) ∧
      W₂ = primeLine ((CFSG.FeitThompson.hallCoreIn S).subtype.comp Pe.toMonoidHom) := by
  obtain ⟨E, _, _, φ, Ue, hcard, hscal, hP₀⟩ :=
    exists_scalar_field_model h₁ h₂ h₃ hG hsetup hU hp e hirr
  refine ⟨E, inferInstance, coreMulEquivOfLinearEquiv e φ, Ue, hcard, fun z w => ?_, hP₀⟩
  exact inv_mul_coreMulEquivOfLinearEquiv_mul (le_normalizer_map_subtype_hallCore S) e
    (isConjModule_conjLinear p (le_normalizer_map_subtype_hallCore S) e) φ
    (hsetup.config_S.le_M_E (Ue w : ↥U).2) (hscal w) z

theorem false_of_field_model [Finite G]
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hnormU : CFSG.FeitThompson.conjSubgroup W₂ y ≤ normalizer (U : Set G))
    (hU : Nat.card ↥U = ((Nat.card ↥W₂) ^ Nat.card ↥W₁ - 1) / (Nat.card ↥W₂ - 1))
    {F : Type*} [Field F] (hFcard : Nat.card F = Nat.card ↥W₂ ^ Nat.card ↥W₁)
    (Pe : Multiplicative F ≃* ↥(CFSG.FeitThompson.hallCoreIn S))
    (Ue : ↥(normOneSubgroup F (Nat.card ↥U)) ≃* ↥U)
    (hact : ∀ (z : F) (w : ↥(normOneSubgroup F (Nat.card ↥U))),
      ((Ue w : ↥U) : G)⁻¹ *
          ((Pe (Multiplicative.ofAdd z) : ↥(CFSG.FeitThompson.hallCoreIn S)) : G) * ((Ue w : ↥U) : G)
        = ((Pe (Multiplicative.ofAdd (z * ((w : Fˣ) : F))) :
            ↥(CFSG.FeitThompson.hallCoreIn S)) : G))
    (hP₀ : W₂ = primeLine ((CFSG.FeitThompson.hallCoreIn S).subtype.comp Pe.toMonoidHom)) :
    False := by
  obtain ⟨-, hpp, hqp, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) S U W₁ W₂ hsetup.isCoatom_S
      hsetup.config_S _ _ rfl rfl
  have hle : Nat.card ↥W₂ ≤ Nat.card ↥W₁ :=
    prime_le_of_appendixC_config hpp hqp hFcard hU
      (not_dvd_sub_one_and_coprime_of_natCard_U_eq_norm h₂ hG hsetup.isCoatom_S
        hsetup.config_S hU).2
      Pe Ue (inf_hallCoreIn_eq_bot h₂ hG hsetup.isCoatom_S hsetup.config_S) hact rfl hP₀
      (fun x hx z hz => congrArg Subtype.val
        ((isMulCommutative_hallCoreIn h₂ hG hsetup.isCoatom_T
          hsetup.config_T).is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩))
      (coprime_natCard_hallCoreIn_natCard_W₂ h₂ hG hsetup.isCoatom_T hsetup.config_T)
      (hsetup.config_T.le_M_W₁.trans (le_normalizer_map_subtype_hallCore T)) hsetup.mem_y
      (CFSG.FeitThompson.conjSubgroup_eq W₂ y) hnormU
  exact absurd hsetup.natCard_lt (by omega)

theorem false_of_natCard_U_eq_norm [Finite G]
    (h₁ : _root_.CFSG.FeitThompson.Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_type_II_extended_support_ti.{u})
    (hG : CFSG.FeitThompson.IsOddSimpleMinimal G) {S T L U V W₁ W₂ : Subgroup G} {y : G}
    (hsetup : CFSG.FeitThompson.IsPairedSupportingSetup S T L U V W₁ W₂ y)
    (hnormU : CFSG.FeitThompson.conjSubgroup W₂ y ≤ normalizer (U : Set G))
    (hU : Nat.card ↥U = ((Nat.card ↥W₂) ^ Nat.card ↥W₁ - 1) / (Nat.card ↥W₂ - 1)) :
    False := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨Vm, _, _, -, ⟨e⟩⟩, -, -, -, -, -, -, -, -, -, -,
    -⟩ := h₂ G (isMinimalSimpleOdd_of_isOddSimpleMinimal hG) S U W₁ W₂ hsetup.isCoatom_S
      hsetup.config_S (Nat.card ↥W₂) (Nat.card ↥W₁) rfl rfl
  have hSN : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hirr : IsIrreducibleLinear ((U.subgroupOf S).map (conjLinear (Nat.card ↥W₂) hSN e)) :=
    isIrreducibleLinear_map_of_natCard_U_eq_norm h₂ hG hsetup.isCoatom_S hsetup.config_S rfl rfl
      hU e _ (isConjModule_conjLinear _ hSN e)
  obtain ⟨F, _, Pe, Ue, hFcard, hact, hP₀⟩ :=
    exists_appendixC_field_model h₁ h₂ h₃ hG hsetup hU rfl e hirr
  exact false_of_field_model h₂ hG hsetup hnormU hU hFcard Pe Ue hact hP₀

end PairedFullSupportNotCharacteristic

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep05
open CFSG.FeitThompson.PairedFullSupportFieldAction
open CFSG.FeitThompson.PairedFullSupportNotCharacteristic

public section

universe u

theorem FNI_paired_full_support_inner_not_characteristic
    (h₁ : Statements.FCH_type_p_action_kernel_ratio.{u})
    (h₂ : Statements.FNI_type_p_elementary_core_structure.{u})
    (h₃ : Statements.FTS_type_II_extended_support_ti.{u}) :
    Statements.FNI_paired_full_support_inner_not_characteristic.{u} := by
  intro G _ _ hG S T L U V W₁ W₂ y hsetup hchar
  set p : ℕ := Nat.card ↥W₂ with hpdef
  set q : ℕ := Nat.card ↥W₁ with hqdef
  have hG5 : CFSG.FeitThompson.Prep05.IsMinimalSimpleOdd G :=
    isMinimalSimpleOdd_of_isOddSimpleMinimal hG
  obtain ⟨-, hpp, hqprime, -, -, -, -, -, -, -, -, -,
    ⟨Vm, _, _, -, ⟨e⟩⟩, -, -, -, -, -, -, -, -, -, -⟩ :=
    h₂ G hG5 S U W₁ W₂ hsetup.isCoatom_S hsetup.config_S p q rfl rfl
  have hnormU := le_normalizer_conj_W₂ hsetup hchar
  have hSN : S ≤ normalizer ((hallCoreOf S : Subgroup G) : Set G) :=
    le_normalizer_map_subtype_hallCore S
  have hUS : U ≤ S := hsetup.config_S.le_M_E
  have hρ := isConjModule_conjLinear p hSN e
  have hirr : IsIrreducibleLinear ((U.subgroupOf S).map (conjLinear p hSN e)) :=
    isIrreducibleLinear_map_of_forall_conjSubgroup hρ hSN hUS
      (FNI_paired_full_support_forces_field_action.{u} h₁ h₂ h₃ G hG S T L U V W₁ W₂ y hsetup)
  obtain ⟨-, hred, hfull⟩ :=
    FNI_type_p_field_inner_complement_order.{u, u} h₁ h₂ G hG5 S U W₁ W₂
      hsetup.isCoatom_S hsetup.config_S p q ((p ^ q - 1) / (p - 1)) rfl rfl rfl Vm e _ hρ hirr
  by_cases hqd : q ∣ p - 1
  ·
    obtain ⟨hqN, hUcard⟩ := hred hqd
    exact false_of_mul_natCard_eq hsetup.natCard_lt hqprime.one_lt hpp hnormU
      (free_action hsetup hnormU) (by rw [hUcard, Nat.mul_div_cancel' hqN])
  ·
    exact false_of_natCard_U_eq_norm.{u} h₁ h₂ h₃ hG hsetup hnormU (hfull hqd)

end

end CFSG.FeitThompson.Proofs
