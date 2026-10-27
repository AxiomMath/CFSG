module

public import CFSG.FeitThompson.Representations.CoprimeOrdersDisjointPuncturedSupports
public import CFSG.FeitThompson.Definitions.TotalDadeSupport
public import Mathlib.GroupTheory.Solvable
import CFSG.FeitThompson.Representations.CoherentMultipleKernelUncovered
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelTICoherence
import CFSG.FeitThompson.Representations.TISetDadeData
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI
import CFSG.FeitThompson.Representations.FreeCentralSectionJointCoherence
import CFSG.FeitThompson.Representations.CentralActionCasesComplementOrderBound
import CFSG.FeitThompson.Representations.PGroupFrobeniusTISibleyCoherence
import CFSG.FeitThompson.Representations.CrossMaximalFirstWitnessValue
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FrobeniusMultipleKernel

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_of_coe_mul_eq_left {H E L : Subgroup G}
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) : H ≤ L := by
  intro h hh
  have hx : h ∈ (H : Set G) * (E : Set G) := ⟨h, hh, 1, one_mem _, mul_one h⟩
  rw [hmul] at hx
  exact hx

theorem le_of_coe_mul_eq_right {H E L : Subgroup G}
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) : E ≤ L := by
  intro e he
  have hx : e ∈ (H : Set G) * (E : Set G) := ⟨1, one_mem _, e, he, one_mul e⟩
  rw [hmul] at hx
  exact hx

theorem sup_eq_of_coe_mul_eq {H E L : Subgroup G}
    (hmul : (H : Set G) * (E : Set G) = (L : Set G)) : H ⊔ E = L := by
  refine le_antisymm (sup_le (le_of_coe_mul_eq_left hmul) (le_of_coe_mul_eq_right hmul))
    fun l hl => ?_
  have hx : l ∈ (H : Set G) * (E : Set G) := by rw [hmul]; exact hl
  obtain ⟨h, hh, e, he, rfl⟩ := hx
  exact mul_mem (mem_sup_left hh) (mem_sup_right he)

theorem coe_sdiff_eq_image_subgroupOf {K M : Subgroup G} (hKM : K ≤ M) :
    (K : Set G) \ {1} = (fun x : ↥M => (x : G)) '' ((K.subgroupOf M : Set ↥M) \ {1}) := by
  ext x
  constructor
  · rintro ⟨hxK, hx1⟩
    exact ⟨⟨x, hKM hxK⟩, ⟨Subgroup.mem_subgroupOf.2 hxK, by simpa using hx1⟩, rfl⟩
  · rintro ⟨y, ⟨hyK, hy1⟩, rfl⟩
    exact ⟨Subgroup.mem_subgroupOf.1 hyK, by simpa using hy1⟩

theorem totalDadeSupport_bot_eq_puncturedConjSupport (K : Subgroup G) :
    totalDadeSupport ((K : Set G) \ {1}) (fun _ => (⊥ : Subgroup G)) = puncturedConjSupport K := by
  ext x
  rw [mem_totalDadeSupport_iff_exists_isConj, mem_puncturedConjSupport_iff]
  constructor
  · rintro ⟨a, ⟨haK, ha1⟩, y, hy, hconj⟩
    have hya : y = a := by simpa [mem_dadeCoset_iff, mul_inv_eq_one] using hy
    subst hya
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    refine ⟨⟨c⁻¹, ?_⟩, ?_⟩
    · have h2 : c⁻¹ * x * (c⁻¹)⁻¹ = y := by rw [← hc]; group
      rw [h2]; exact haK
    · intro hx1
      exact ha1 (by simpa [hx1] using hconj)
  · rintro ⟨⟨g, hg⟩, hx1⟩
    refine ⟨g * x * g⁻¹, ⟨hg, fun h => hx1 ?_⟩, g * x * g⁻¹, self_mem_dadeCoset _ _,
      isConj_iff.2 ⟨g⁻¹, by group⟩⟩
    have h1 : g * x * g⁻¹ = 1 := h
    have h2 : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [h2, h1]
    group

variable [Finite G] {I : Type*} [Finite I] [Nonempty I] {L H E : I → Subgroup G}

theorem exists_ne_one_notMem_puncturedConjSupport [∀ i, Group.IsSolvable ↥(H i)]
    (hodd : Odd (Nat.card G))
    (hnorm : ∀ i, L i ≤ normalizer ((H i : Set G)))
    (hmul : ∀ i, (H i : Set G) * (E i : Set G) = (L i : Set G))
    (hinf : ∀ i, H i ⊓ E i = ⊥)
    (hHbot : ∀ i, H i ≠ ⊥) (hEbot : ∀ i, E i ≠ ⊥)
    (hCfree : ∀ (i : I), ∀ u ∈ E i, u ≠ 1 → H i ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ (i : I) (g : G),
      (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) = (H i : Set G) \ {1} ↔ g ∈ L i)
    (hTIor : ∀ (i : I) (g : G),
      (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) = (H i : Set G) \ {1} ∨
        (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) ∩ ((H i : Set G) \ {1}) = ∅)
    (hcop : Pairwise fun i j => (Nat.card ↥(H i)).Coprime (Nat.card ↥(H j))) :
    ∃ x : G, x ≠ 1 ∧ ∀ i : I, x ∉ puncturedConjSupport (H i) := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  have hHL : ∀ i, H i ≤ L i := fun i => le_of_coe_mul_eq_left (hmul i)
  have hEL : ∀ i, E i ≤ L i := fun i => le_of_coe_mul_eq_right (hmul i)
  have hsup : ∀ i, H i ⊔ E i = L i := fun i => sup_eq_of_coe_mul_eq (hmul i)
  have _ : ∀ i, Fintype ↥(L i) := fun i => Fintype.ofFinite _
  have hLodd : ∀ i, Odd (Nat.card ↥(L i)) := fun i =>
    hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (L i))
  set A : I → Set G := fun i => (H i : Set G) \ {1} with hAdef
  set K : ∀ i, Subgroup ↥(L i) := fun i => (H i).subgroupOf (L i) with hKdef
  have _ : ∀ i, (K i).Normal := fun i => (normal_subgroupOf_iff_le_normalizer (hHL i)).2 (hnorm i)
  have _ : ∀ i, Group.IsSolvable ↥(K i) := fun i =>
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe (hHL i)).toMonoidHom)
      (by simpa using (subgroupOfEquivOfLe (hHL i)).injective)
  have hcompl : ∀ i, (K i).IsComplement' ((E i).subgroupOf (L i)) := fun i =>
    SibleyPGroupCoherence.isComplement'_subgroupOf (hHL i) (hEL i) (hnorm i) (hsup i) (hinf i)
  have hKbot : ∀ i, K i ≠ ⊥ := fun i =>
    SibleyNilpotentCoherence.subgroupOf_ne_bot (hHL i) (hHbot i)
  have hEbot' : ∀ i, (E i).subgroupOf (L i) ≠ ⊥ := fun i =>
    SibleyNilpotentCoherence.subgroupOf_ne_bot (hEL i) (hEbot i)
  have hC' : ∀ (i : I), ∀ u ∈ (E i).subgroupOf (L i), u ≠ 1 →
      K i ⊓ centralizer ({u} : Set ↥(L i)) = ⊥ := fun i => free_subgroupOf (hHL i) (hCfree i)
  have hKcard : ∀ i, Nat.card ↥(K i) = Nat.card ↥(H i) := fun i =>
    Nat.card_congr (subgroupOfEquivOfLe (hHL i)).toEquiv
  have isTI : ∀ i, IsTIWithNormalizer (A i) (L i) := fun i =>
    SibleyNilpotentCoherence.isTIWithNormalizer_sdiff (hHbot i) (hstab i) (hTIor i)
  set J : I → G → Subgroup G := fun _ _ => ⊥ with hJdef
  have hDade : ∀ i, IsDadeData (L i) (A i) (J i) := fun i => (isTI i).isDadeData
  set S : ∀ i, Set (↥(L i) → ℂ) := fun i => indFam (K i) (nonprincipalIrr ↥(K i)) with hSdef
  have hSfin : ∀ i, (S i).Finite := fun i =>
    indFam_finite _ (finite_nonprincipalIrr.subset fun _ h => h)
  have _ : ∀ i, Finite ↥(S i) := fun i => (hSfin i).to_subtype
  have hrange : ∀ i, Set.range (Subtype.val : ↥(S i) → (↥(L i) → ℂ)) = S i := fun i =>
    Subtype.range_coe
  have hinj : ∀ i, Function.Injective (Subtype.val : ↥(S i) → (↥(L i) → ℂ)) := fun _ =>
    Subtype.val_injective
  have hSIrr : ∀ i, S i ⊆ Irr ↥(L i) := fun i =>
    SibleyNilpotentCoherence.indFam_subgroupOf_subset_Irr (E := E i) (hHL i) (hEL i) (hnorm i)
      (hsup i) (hinf i) (hHbot i) (hCfree i)
  have hleS : ∀ i, charSpanZero (S i) ≤ dadeZDomain (L i) (A i) := fun i =>
    SibleyNilpotentCoherence.charSpanZero_le_dadeZDomain_sdiff (E := E i) (hHL i) (hEL i)
      (hnorm i) (hsup i) (hinf i) (hHbot i) (hCfree i)
  have hle : ∀ i, charSpanZero (Set.range (Subtype.val : ↥(S i) → (↥(L i) → ℂ)))
      ≤ dadeZDomain (L i) (A i) := fun i => by rw [hrange i]; exact hleS i
  set τ : ∀ i, charSpanZero (Set.range (Subtype.val : ↥(S i) → (↥(L i) → ℂ))) →+ virtualChars G :=
    fun i => (isTI i).indCharSpanZeroHom (hle i) with hτdef
  have hτcoe : ∀ (i : I) (f), ((τ i f : virtualChars G) : G → ℂ)
      = indClassFun (L i) (f : ↥(L i) → ℂ) := fun i =>
    IsTIWithNormalizer.coe_indCharSpanZeroHom _ _
  have hcohτ : ∀ i, IsCoherent (Set.range (Subtype.val : ↥(S i) → (↥(L i) → ℂ))) (τ i) := fun i => by
    refine FreeCentralSectionJointCoherence.isCoherent_of_eq_of_coe_eq
      (tau := indClassFun (L i)) (τ := (isTI i).indCharSpanZeroHom (hleS i)) (hrange i).symm
      (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)
      (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _) ?_
    exact SibleySolvableCoherence.isCoherent_indFam_nonprincipalIrr (E := E i) (hLodd i) (hHL i)
      (hEL i) (hnorm i) (hsup i) (hinf i) (hHbot i) (hEbot i) (hCfree i) (hstab i) (hTIor i) _
      (IsTIWithNormalizer.coe_indCharSpanZeroHom _ _)
  choose ν hν using fun i => isCoherent_iff.1 (hcohτ i)
  have hζ : ∀ i, ∃ z : ↥(S i), (z : ↥(L i) → ℂ) 1 = ((K i).index : ℂ) := fun i => by
    obtain ⟨θ, hθ, hθne, -, -, hdeg⟩ :=
      exists_mem_Irr_indClassFun_mem_Irr_index (E := (E i).subgroupOf (L i)) (hKbot i)
        (Subgroup.IsComplement.mul_eq (hcompl i)) (disjoint_iff.1 (hcompl i).disjoint) (hC' i)
    exact ⟨⟨_, indClassFun_mem_indFam _ (mem_nonprincipalIrr.2 ⟨hθ, hθne⟩)⟩, hdeg⟩
  choose k₀ hk₀ using hζ
  have hindex : ∀ i, 1 < (K i).index := fun i => by
    rw [index_eq_card_of_isComplement' (hcompl i)]
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr (hEbot' i)
  have hbound : ∀ i, 2 * (K i).index + 1 ≤ Nat.card ↥(K i) := fun i => by
    have h := two_mul_natCard_le_natCard_sub_one (L := ↥(L i)) (E := (E i).subgroupOf (L i))
      (V := K i) (hLodd i) (hKbot i) (hC' i)
    have hpos : 0 < Nat.card ↥(K i) := Nat.card_pos
    rw [index_eq_card_of_isComplement' (hcompl i)]
    omega
  have hpackets : ∀ i, totalDadeSupport (A i) (J i) = puncturedConjSupport (H i) := fun i =>
    totalDadeSupport_bot_eq_puncturedConjSupport (H i)
  have hdisj : Pairwise fun i j =>
      Disjoint (totalDadeSupport (A i) (J i)) (totalDadeSupport (A j) (J j)) := by
    intro i j hij
    rw [hpackets i, hpackets j]
    exact pairwise_disjoint_puncturedConjSupport hcop hij
  have hdistinct : Function.Injective fun i => Nat.card ↥(K i) := by
    intro i j hij
    have h : Nat.card ↥(H i) = Nat.card ↥(H j) := by
      rw [← hKcard i, ← hKcard j]; exact hij
    exact injective_natCard_of_pairwise_coprime hcop hHbot h
  have hτdade : ∀ (i : I) (f : charSpanZero (Set.range (Subtype.val : ↥(S i) → (↥(L i) → ℂ))))
      (F : dadeDomain (L i) (A i)), (f : ↥(L i) → ℂ) = (F : ↥(L i) → ℂ) →
      ((τ i f : virtualChars G) : G → ℂ)
        = ((dadeMap (hDade i) F : classFun G) : G → ℂ) := by
    intro i f F hfF
    have hkey := dadeMap_eq_indClassFun (hDade i) (isTI i) (subset_refl (A i))
      (F : ↥(L i) → ℂ) F.2
    have hFeq : (⟨(F : ↥(L i) → ℂ), dadeDomain_mono (subset_refl (A i)) F.2⟩ :
        dadeDomain (L i) (A i)) = F := Subtype.ext rfl
    rw [hFeq] at hkey
    rw [hτcoe i f, hfF, hkey]
  obtain ⟨x, hxmem, hx1⟩ :=
    CoherentFrobeniusUncovered.exists_mem_dadeCoverComplement_ne_one (Lsub := L) (A := A) (J := J)
      (H := K) (ξ := fun i => (Subtype.val : ↥(S i) → (↥(L i) → ℂ))) (k₀ := k₀) (τ := τ) (ν := ν)
      hodd hDade
      (fun i => by rw [hAdef]; exact coe_sdiff_eq_image_subgroupOf (hHL i))
      (fun i => by
        rw [hrange i]
        simp only [hSdef, nonprincipalIrr_eq_sdiff_singleton])
      (fun i => by rw [hrange i]; exact hSIrr i) hinj hν hτdade hk₀ hdisj hindex hbound hdistinct
  refine ⟨x, hx1, fun i => ?_⟩
  rw [← hpackets i]
  exact mem_dadeCoverComplement_iff.1 hxmem i

theorem exists_ne_one_notMem_conj_image [∀ i, Group.IsSolvable ↥(H i)]
    (hodd : Odd (Nat.card G))
    (hnorm : ∀ i, L i ≤ normalizer ((H i : Set G)))
    (hmul : ∀ i, (H i : Set G) * (E i : Set G) = (L i : Set G))
    (hinf : ∀ i, H i ⊓ E i = ⊥)
    (hHbot : ∀ i, H i ≠ ⊥) (hEbot : ∀ i, E i ≠ ⊥)
    (hCfree : ∀ (i : I), ∀ u ∈ E i, u ≠ 1 → H i ⊓ centralizer ({u} : Set G) = ⊥)
    (hstab : ∀ (i : I) (g : G),
      (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) = (H i : Set G) \ {1} ↔ g ∈ L i)
    (hTIor : ∀ (i : I) (g : G),
      (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) = (H i : Set G) \ {1} ∨
        (fun x => g⁻¹ * x * g) '' ((H i : Set G) \ {1}) ∩ ((H i : Set G) \ {1}) = ∅)
    (hcop : Pairwise fun i j => (Nat.card ↥(H i)).Coprime (Nat.card ↥(H j))) :
    ∃ x : G, x ≠ 1 ∧ ∀ (i : I) (g : G),
      x ∉ (fun y => g⁻¹ * y * g) '' ((H i : Set G) \ {1}) := by
  obtain ⟨x, hx1, hx⟩ := exists_ne_one_notMem_puncturedConjSupport (L := L) (E := E) hodd hnorm
    hmul hinf hHbot hEbot hCfree hstab hTIor hcop
  refine ⟨x, hx1, fun i g hmem => hx i ?_⟩
  rw [puncturedConjSupport_eq_iUnion]
  exact Set.mem_iUnion.2 ⟨g, hmem⟩

end FrobeniusMultipleKernel

end CFSG.FeitThompson

end
