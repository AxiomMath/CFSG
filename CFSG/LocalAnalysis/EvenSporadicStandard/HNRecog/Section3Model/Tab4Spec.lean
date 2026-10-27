module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.RowModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModelClass
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.Tab4Abstract
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.OrbitCountLe
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.TableMaps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import Certificates.Certificate441693
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIP

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open Subgroup CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3
  CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] noncomputable def tab4C (i : Fin 6) : ↥P1408 := (tab4Row i).rowP wordB

theorem natCard_z2_sym (n : ℕ) : Nat.card (Z 2 × Sym n) = 2 * n.factorial := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_perm,
    Nat.card_fin]

theorem tab4_mulEquiv_of_injective {X T : Type*} [Group X] [Group T] [Finite T]
    {f : X →* T} (hf : Function.Injective f) (hc : Nat.card T ≤ Nat.card X) : Nonempty (X ≃* T) :=
  ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le hc)⟩

section Cert


private theorem tab4_facts (hP : Nat.card ↥P1408 = 177408000) : Tab4Facts :=
  Certificates.certificate441693 hP

private theorem wordP_wordAZ' : wordP wordAZ = pA * pZ := Subtype.ext elemW_wordAZ

private theorem isConj_pB_pA_mul_pB (hP : Nat.card ↥P1408 = 177408000) : IsConj pB (pA * pB) :=
  (tab4_facts hP).ab

private theorem tab4C_mem_base (hP : Nat.card ↥P1408 = 177408000) (i : Fin 6) :
    tab4C i ∈ tab4Base pA pB pB :=
  ⟨isConj_wordP_rowP wordB (tab4Row i), ((tab4_facts hP).ne i).1, ((tab4_facts hP).ne i).2⟩

theorem tab4C_mem_set (hP : Nat.card ↥P1408 = 177408000) (i : Fin 6) :
    tab4C i ∈ tab4Set pA pZ pB pZ₁ pB i := by
  have F := tab4_facts hP
  have h0 := F.row0
  rw [wordP_wordAZ'] at h0
  fin_cases i
  · exact ⟨tab4C_mem_base hP 0, Or.inr (Or.inl h0)⟩
  · exact ⟨tab4C_mem_base hP 1, Or.inl F.row1⟩
  · exact ⟨tab4C_mem_base hP 2, F.row2⟩
  · exact ⟨tab4C_mem_base hP 3, Or.inl F.row3⟩
  · exact ⟨tab4C_mem_base hP 4, F.row4⟩
  · exact ⟨tab4C_mem_base hP 5, F.row5⟩

theorem tab4_base_ncard (hP : Nat.card ↥P1408 = 177408000) :
    (tab4Base pA pB pB).ncard = 2198 := by
  have hcl : {c : ↥P1408 | IsConj pB c}.ncard = 2200 := by
    rw [ncard_isConj_subtype P1408 pB]
    exact (invClasses_classSpec hP).2.2.1.class_ncard
  have hpA : pA ≠ 1 := fun h => by
    have := twoHSBasic_spec.1
    rw [show elemA = ((pA : ↥P1408) : Equiv.Perm (Fin 1408)) from rfl, h] at this
    simp at this
  have hne : pB ≠ pA * pB := fun h => hpA (by simpa using h.symm)
  have hsub : ({pB, pA * pB} : Set ↥P1408) ⊆ {c | IsConj pB c} := by
    rintro c (rfl | rfl)
    · exact IsConj.refl _
    · exact isConj_pB_pA_mul_pB hP
  have hset : tab4Base pA pB pB = {c | IsConj pB c} \ {pB, pA * pB} := by
    ext c
    simp only [tab4Base, Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or]
  rw [hset, Set.ncard_diff hsub (Set.toFinite _), hcl, Set.ncard_pair hne]

private theorem tab4_ord : orderOf pA = 2 ∧ orderOf pZ = 2 ∧ orderOf pB = 2 ∧ orderOf pZ₁ = 2 := by
  obtain ⟨hA, hZ, hB, hZ₁, -⟩ := twoHSBasic_spec
  exact ⟨(Subgroup.orderOf_coe pA).symm.trans hA, (Subgroup.orderOf_coe pZ).symm.trans hZ,
    (Subgroup.orderOf_coe pB).symm.trans hB, (Subgroup.orderOf_coe pZ₁).symm.trans hZ₁⟩

theorem tab4_card_stab (hP : Nat.card ↥P1408 = 177408000) (i : Fin 6) :
    Nat.card ↥(Gx pB ⊓ Gx (tab4C i)) = ![768, 768, 1440, 64, 240, 240] i := by
  have hK : Nat.card ↥(Gx pB) = 80640 := natCard_centralizer_pB hP
  refine stab_eq_of_le (Gx pB) (tab4Base pA pB pB) (tab4Set pA pZ pB pZ₁ pB) tab4C
    ![768, 768, 1440, 64, 240, 240]
    (by intro i x hx; fin_cases i <;> (simp [tab4Set] at hx; exact hx.1))
    (fun i j hij => tab4Set_disjoint pA_mem_center' tab4_ord (IsConj.refl pB) (not_isConj_inv hP)
      i j hij)
    (by
      intro i k hk x hx
      have hky : k * pB * k⁻¹ = pB := by rw [← mem_Gx.mp hk]; group
      have := (mem_tab4Set_conj pA_mem_center' pZ pB pZ₁ pB x k i).mpr hx
      rwa [hky] at this)
    (tab4C_mem_set hP) (tab4_facts hP).stab_le
    (by rw [hK]; intro i; fin_cases i <;> decide)
    (by rw [hK, tab4_base_ncard hP]; decide) i

theorem tab4_shape_4B (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeZ2TimesSym 6 ↥(Gx pB ⊓ Gx (tab4C 2)) := by
  obtain ⟨f, hf⟩ := (tab4_facts hP).inj2
  refine tab4_mulEquiv_of_injective hf ?_
  rw [natCard_z2_sym]
  exact le_of_eq (tab4_card_stab hP 2).symm

theorem tab4_shape_3A (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeZ2TimesSym 5 ↥(Gx pB ⊓ Gx (tab4C 4)) := by
  obtain ⟨f, hf⟩ := (tab4_facts hP).inj4
  refine tab4_mulEquiv_of_injective hf ?_
  rw [natCard_z2_sym]
  exact le_of_eq (tab4_card_stab hP 4).symm

theorem tab4_shape_6A (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeZ2TimesSym 5 ↥(Gx pB ⊓ Gx (tab4C 5)) := by
  obtain ⟨f, hf⟩ := (tab4_facts hP).inj5
  refine tab4_mulEquiv_of_injective hf ?_
  rw [natCard_z2_sym]
  exact le_of_eq (tab4_card_stab hP 5).symm

theorem tableIV_P (hP : Nat.card ↥P1408 = 177408000) : TableIVData pA pZ pB pZ₁ pB :=
  tableIV_of_reps pA_mem_center' tab4_ord (IsConj.refl pB) (not_isConj_inv hP)
    (natCard_centralizer_pB hP) (tab4_base_ncard hP) tab4C (tab4C_mem_set hP) (tab4_card_stab hP)
    (tab4_shape_4B hP) (tab4_shape_3A hP) (tab4_shape_6A hP)

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
