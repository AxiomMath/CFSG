module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Local.PiCoreLargestNormalSubgroup
import CFSG.FeitThompson.Local.NormalPSubgroupPComplCoreTransfer
import CFSG.FeitThompson.Local.CoprimeSolvableCommutatorDecomposition
import CFSG.FeitThompson.Local.NilpotentDerivedQuotientSylowNormalizer
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem coprime_natCard_of_isPiSubgroup {π π' : Set ℕ} (hd : Disjoint π π') {A B : Subgroup G}
    (hA : IsPiSubgroup π A) (hB : IsPiSubgroup π' B) :
    (Nat.card ↥A).Coprime (Nat.card ↥B) := by
  refine (Nat.disjoint_primeFactors Nat.card_pos.ne' Nat.card_pos.ne').1 ?_
  refine Finset.disjoint_left.2 fun s hs hs' => ?_
  exact Set.disjoint_left.1 hd (isPiSubgroup_iff.1 hA s hs) (isPiSubgroup_iff.1 hB s hs')

theorem le_map_piCore_subgroupPrimeSupportCompl_of_forall {A X Y : Subgroup G} (hYX : Y ≤ X)
    (hmem : ∀ q ∈ subgroupPrimeSupport A, Y ≤ (pComplCore q ↥X).map X.subtype) :
    Y ≤ (piCore (subgroupPrimeSupportCompl A) ↥X).map X.subtype := by
  classical
  set f : (Nat.card ↥A).primeFactors → Subgroup ↥X := fun q => pComplCore (q : ℕ) ↥X with hf
  have hNnormal : (iInf f).Normal :=
    Subgroup.normal_iInf_normal fun _ => Subgroup.normal_of_characteristic _
  have hNpi : IsPiSubgroup (subgroupPrimeSupportCompl A) (iInf f) := by
    refine isPiSubgroup_iff.2 fun s hs => mem_subgroupPrimeSupportCompl_iff.2
      ⟨Nat.prime_of_mem_primeFactors hs, fun hsA => ?_⟩
    have hle : iInf f ≤ pComplCore s ↥X :=
      iInf_le f (⟨s, mem_subgroupPrimeSupport_iff.1 hsA⟩ : (Nat.card ↥A).primeFactors)
    exact not_dvd_natCard_pComplCore (Nat.prime_of_mem_primeFactors hs) ↥X
      ((Nat.dvd_of_mem_primeFactors hs).trans (Subgroup.card_dvd_of_le hle))
  have hYN : Y.subgroupOf X ≤ iInf f := by
    refine le_iInf fun q => ?_
    rw [← Subgroup.map_subtype_le_map_subtype, Subgroup.map_subgroupOf_eq_of_le hYX]
    exact hmem q (mem_subgroupPrimeSupport_iff.2 q.2)
  rw [le_map_piCore_iff _ hYX]
  exact hYN.trans (le_piCore hNnormal hNpi)

theorem le_pCoreIn_of_isPGroup_of_isNilpotent {r : ℕ} (hr : r.Prime) {N F : Subgroup G}
    (hNF : N ≤ F) [Group.IsNilpotent ↥F] (hN : IsPGroup r ↥N) : N ≤ pCoreIn r F := by
  have : Fact r.Prime := ⟨hr⟩
  have hQ : IsPGroup r ↥(N.subgroupOf F) := hN.of_equiv (subgroupOfEquivOfLe hNF).symm
  obtain S := (default : Sylow r ↥F)
  have hQS : N.subgroupOf F ≤ (S : Subgroup ↥F) := le_sylow_of_isPGroup_of_isNilpotent S hQ
  have hS : (S : Subgroup ↥F) ≤ pCore r ↥F := le_pCore hr (sylow_normal_of_isNilpotent S) S.2
  rw [pCoreIn_eq, pCore_eq_piCore, le_map_piCore_iff _ hNF]
  exact (hQS.trans hS).trans (le_of_eq (pCore_eq_piCore r ↥F))

theorem le_map_pComplCore_of_isPGroup {q r : ℕ} (hr : r.Prime) (hqr : q ≠ r) {H N : Subgroup G}
    (hNH : N ≤ H) (hnorm : H ≤ normalizer (N : Set G)) (hN : IsPGroup r ↥N) :
    N ≤ (pComplCore q ↥H).map H.subtype := by
  rw [pComplCore_eq_piCore]
  refine le_map_piCore_of_le_of_le_normalizer hNH hnorm (isPiSubgroup_iff.2 fun s hs => ?_)
  have hsr : s = r := by
    have hmem := (isPGroup_iff_primeFactors_card_subset hr.ne_zero).1 hN hs
    rwa [hr.primeFactors, Finset.mem_singleton] at hmem
  exact ⟨hsr ▸ hr, fun hcon => hqr (hcon ▸ hsr ▸ rfl)⟩

omit [Finite G] in
theorem commutator_le_of_le_of_le_normalizer {K X Y A : Subgroup G} (hYX : Y ≤ X)
    (hXK : X ≤ normalizer (K : Set G)) (hAK : A ≤ K) : ⁅Y, A⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro y hy a ha
  rw [commutatorElement_def]
  refine K.mul_mem ?_ (K.inv_mem (hAK ha))
  have hn := hXK (hYX hy)
  rw [mem_normalizer_iff] at hn
  exact (hn a).1 (hAK ha)

theorem le_commutator_of_coprime_of_inf_centralizer_eq_bot {A Y : Subgroup G}
    [Group.IsSolvable ↥A] [Group.IsSolvable ↥Y] (hAY : A ≤ normalizer (Y : Set G))
    (hcop : (Nat.card ↥A).Coprime (Nat.card ↥Y))
    (hfix : Y ⊓ centralizer (A : Set G) = ⊥) :
    Y ≤ ⁅Y, A⁆ := by
  let ρ := conjOnNormalized Y hAY
  let _inst : MulDistribMulAction ↥A ↥Y := MulDistribMulAction.compHom ↥Y ρ
  have hsmul : ∀ (a : ↥A) (v : ↥Y), ((a • v : ↥Y) : G) = (a : G) * (v : G) * (a : G)⁻¹ :=
    fun a v => conjOnNormalized_apply_coe hAY a v
  have hfix' : FixedPoints.subgroup ↥A ↥Y = ⊥ := by
    refine le_bot_iff.1 fun v hv => ?_
    rw [FixedPoints.mem_subgroup] at hv
    have hvc : (v : G) ∈ Y ⊓ centralizer (A : Set G) := by
      refine ⟨v.2, mem_centralizer_iff.2 fun a ha => ?_⟩
      have h2 := congrArg (fun w : ↥Y => (w : G)) (hv ⟨a, ha⟩)
      simp only [hsmul] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2
    rw [hfix, mem_bot] at hvc
    exact Subtype.ext hvc
  have htop := smulDisplacementSubgroup_sup_fixedPoints_subgroup ↥A ↥Y hcop
  rw [hfix', sup_bot_eq] at htop
  have hmap : (smulDisplacementSubgroup ↥A ↥Y).map Y.subtype ≤ ⁅Y, A⁆ := by
    rw [smulDisplacementSubgroup_eq_closure, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    rintro x ⟨a, v, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, coe_subtype]
    have hc := Subgroup.commutator_mem_commutator (H₁ := Y) (H₂ := A) (inv_mem v.2) a.2
    rw [commutatorElement_def, inv_inv] at hc
    have hcast : ((v⁻¹ * a • v : ↥Y) : G) = (v : G)⁻¹ * (a : G) * (v : G) * (a : G)⁻¹ := by
      rw [Subgroup.coe_mul, hsmul, coe_inv]
      group
    rw [hcast]
    exact hc
  intro y hy
  exact hmap ⟨⟨y, hy⟩, htop ▸ mem_top _, rfl⟩

variable {p : ℕ} {M E : Subgroup G}

theorem subgroupPrimeSupportCompl_mixedFittingCentralizer (h : IsMixedFittingSetup p M E) :
    subgroupPrimeSupportCompl (mixedFittingCentralizer M E)
      = subgroupPrimeSupportCompl (mixedFitting M) := by
  ext s
  simp only [mem_subgroupPrimeSupportCompl_iff, mem_subgroupPrimeSupport_iff,
    h.primeFactors_mixedFittingCentralizer]

namespace IsMixedFittingSetup

variable (h : IsMixedFittingSetup p M E)

include h

theorem pCoreIn_le_map_pComplCore [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) {q r : ℕ}
    (hq : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors)
    (hr : r ∈ (Nat.card ↥(mixedFitting M)).primeFactors) (hqr : q ≠ r)
    {X : Subgroup G} (hX : X ≠ ⊤) (hTX : mixedFittingCentralizer M E ≤ X) :
    pCoreIn r (mixedFittingCentralizer M E) ≤ (pComplCore q ↥X).map X.subtype := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hrp := Nat.prime_of_mem_primeFactors hr
  set Z := pCoreIn q (centreIn (mixedFitting M)) with hZ
  have h1 : pCoreIn r (mixedFittingCentralizer M E) ≤ pCoreIn r (mixedFitting M) :=
    le_pCoreIn_of_isPGroup_of_isNilpotent hrp
      ((pCoreIn_le r _).trans (mixedFittingCentralizer_le M E)) (isPGroup_pCoreIn hrp _)
  have h2 : pCoreIn r (mixedFitting M) ≤ (pComplCore q ↥M).map M.subtype :=
    le_map_pComplCore_of_isPGroup hrp hqr ((pCoreIn_le r _).trans (mixedFitting_le M))
      (le_normalizer_pCoreIn r (le_normalizer_mixedFitting M)) (isPGroup_pCoreIn hrp _)
  have hZM : Z ≤ M := (pCoreIn_le q _).trans ((centreIn_le _).trans (mixedFitting_le M))
  have hZnormal : (Z.subgroupOf M).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_pCoreIn_centreIn_mixedFitting q M)
  have hZX : Z ≤ X := (h.pCoreIn_centreIn_le_mixedFittingCentralizer q).trans hTX
  have htrans := inf_map_pComplCore_le_map_pComplCore_of_normal_pSubgroup hna hodd hsolv hqp
    h.isCoatom hZM hZnormal (isPGroup_pCoreIn hqp _) (h.pCoreIn_centreIn_ne_bot hqp hq) hX hZX
  exact fun x hx => htrans ⟨h2 (h1 hx), hTX ((pCoreIn_le r _) hx)⟩

theorem inf_centralizer_pCoreIn_eq_bot [IsSimpleGroup G] {q : ℕ}
    (hq : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) {Y : Subgroup G}
    (hY : IsPiSubgroup (subgroupPrimeSupportCompl (mixedFitting M)) Y)
    (hTY : mixedFittingCentralizer M E ≤ normalizer (Y : Set G)) :
    Y ⊓ centralizer ((pCoreIn q (mixedFittingCentralizer M E) : Subgroup G) : Set G) = ⊥ := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  set C := Y ⊓ centralizer ((pCoreIn q (mixedFittingCentralizer M E) : Subgroup G) : Set G) with hC
  have hCM : C ≤ M := inf_le_right.trans (h.centralizer_pCoreIn_le hqp hq)
  have hYF : mixedFitting M ⊓ Y = ⊥ := inf_eq_bot_of_isPiSubgroup_subgroupPrimeSupportCompl hY
  have hCT : C ≤ centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G) := by
    intro c hc
    refine mem_centralizer_iff.2 fun t ht => ?_
    have hcY : c ∈ Y := hc.1
    have htF : t ∈ mixedFitting M := mixedFittingCentralizer_le M E ht
    have h1 : c * t * c⁻¹ * t⁻¹ ∈ Y := by
      have h2 : t * c⁻¹ * t⁻¹ ∈ Y := by
        have hn := hTY ht
        rw [mem_normalizer_iff] at hn
        exact (hn c⁻¹).1 (Y.inv_mem hcY)
      have he : c * t * c⁻¹ * t⁻¹ = c * (t * c⁻¹ * t⁻¹) := by group
      rw [he]
      exact Y.mul_mem hcY h2
    have h2 : c * t * c⁻¹ * t⁻¹ ∈ mixedFitting M := by
      have hcF : c * t * c⁻¹ ∈ mixedFitting M := by
        have hn := le_normalizer_mixedFitting M (hCM hc)
        rw [mem_normalizer_iff] at hn
        exact (hn t).1 htF
      exact (mixedFitting M).mul_mem hcF ((mixedFitting M).inv_mem htF)
    have h3 : c * t * c⁻¹ * t⁻¹ ∈ mixedFitting M ⊓ Y := ⟨h2, h1⟩
    rw [hYF, mem_bot] at h3
    exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h3)).symm
  exact eq_bot_of_isPiSubgroup_of_isPiSubgroup
    (fun _ hs hs' => Set.disjoint_left.1
      (disjoint_subgroupPrimeSupport_subgroupPrimeSupportCompl (mixedFitting M)) hs hs')
    (h.isPiSubgroup_centralizer_mixedFittingCentralizer.of_le hCT) (hY.of_le inf_le_left)

theorem le_commutator_pCoreIn [IsSimpleGroup G] {q : ℕ}
    (hq : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) {Y : Subgroup G} [Group.IsSolvable ↥Y]
    (hY : IsPiSubgroup (subgroupPrimeSupportCompl (mixedFitting M)) Y)
    (hTY : mixedFittingCentralizer M E ≤ normalizer (Y : Set G)) :
    Y ≤ ⁅Y, pCoreIn q (mixedFittingCentralizer M E)⁆ := by
  have hqp := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqp⟩
  set Tq := pCoreIn q (mixedFittingCentralizer M E) with hTq
  have hTqpi : IsPiSubgroup (subgroupPrimeSupport (mixedFitting M)) Tq :=
    (isPiSubgroup_subgroupPrimeSupport (mixedFitting M)).of_le
      ((pCoreIn_le q _).trans (mixedFittingCentralizer_le M E))
  have hnil : Group.IsNilpotent ↥Tq := (isPGroup_pCoreIn hqp _).isNilpotent
  have : Group.IsSolvable ↥Tq := IsNilpotent.to_isSolvable
  exact le_commutator_of_coprime_of_inf_centralizer_eq_bot ((pCoreIn_le q _).trans hTY)
    (coprime_natCard_of_isPiSubgroup
      (disjoint_subgroupPrimeSupport_subgroupPrimeSupportCompl (mixedFitting M)) hTqpi hY)
    (h.inf_centralizer_pCoreIn_eq_bot hq hY hTY)

theorem isConstrained_mixedFittingCentralizer [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ H : Subgroup G, H ≠ ⊤ → Group.IsSolvable H) :
    IsConstrained (mixedFittingCentralizer M E) := by
  refine isConstrained_iff.2 fun X hX hTX Y hYX hY hTY => ?_
  have hXne : X ≠ ⊤ := hX.ne
  have hYne : Y ≠ ⊤ := fun hcon => hXne (top_le_iff.1 (hcon ▸ hYX))
  have : Group.IsSolvable ↥Y := hsolv Y hYne
  rw [subgroupPrimeSupportCompl_mixedFittingCentralizer h] at hY ⊢
  refine le_map_piCore_subgroupPrimeSupportCompl_of_forall hYX fun q hq => ?_
  obtain ⟨r, hr, hrq⟩ := Finset.exists_mem_ne h.two_le_card_primeFactors q
  have hqF : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors := mem_subgroupPrimeSupport_iff.1 hq
  have hTr := h.pCoreIn_le_map_pComplCore hna hodd hsolv hqF hr (Ne.symm hrq) hXne hTX
  refine (h.le_commutator_pCoreIn hr hY hTY).trans ?_
  exact commutator_le_of_le_of_le_normalizer hYX (le_normalizer_map_pComplCore q X) hTr

end IsMixedFittingSetup

end

end CFSG.FeitThompson
