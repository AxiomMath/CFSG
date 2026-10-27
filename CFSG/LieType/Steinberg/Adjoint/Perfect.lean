module

public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Steinberg.Adjoint.Borel
public import CFSG.LieType.CurtisTits.Perfect
public import CFSG.LieType.TitsSimplicity.Simplicity
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate120

public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.TitsSimplicity
open scoped commutatorElement

variable {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K] {D : AdjData τ}

theorem rootGroup_single_le_commutator (hD : D.Valid) (hτ : NoG2 τ) {i l : Fin τ.rank}
    (hil : τ.cartan i l = -1) (hli : τ.cartan l i = -1) :
    rootGroup F K (Pi.single i 1) ≤ commutator ↥(adjointGroup τ K) := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (isRoot_single τ i) g).1 hg
  have hli' : l ≠ i := ne_of_cartan_eq_neg_one hil
  have hδ : IsRoot τ (Pi.single l 1 + Pi.single i 1) := isRoot_single_add_single hil
  have hγ : IsRoot τ (-Pi.single l 1) := isRoot_neg_single τ l
  have hsum : Pi.single l 1 + Pi.single i 1 + -Pi.single l 1 = (Pi.single i 1 : Fin τ.rank → ℤ) :=
    by abel
  have hne : (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) ≠ -Pi.single l 1 := fun h => by
    have := congrFun h i
    simp [hli'.symm] at this
  have hne' : (Pi.single l 1 + Pi.single i 1 : Fin τ.rank → ℤ) ≠ -(-Pi.single l 1) := fun h => by
    have := congrFun h i
    simp [hli'.symm] at this
  have h12 : ¬IsRoot τ (Pi.single l 1 + Pi.single i 1 + 2 • -Pi.single l 1) := by
    rw [show (Pi.single l 1 + Pi.single i 1 + 2 • -Pi.single l 1 : Fin τ.rank → ℤ) =
      Pi.single i 1 - Pi.single l 1 by rw [two_nsmul]; abel]
    exact not_isRoot_single_sub_single hli'.symm
  have h21 : ¬IsRoot τ (2 • (Pi.single l 1 + Pi.single i 1) + -Pi.single l 1) := by
    rw [show (2 • (Pi.single l 1 + Pi.single i 1) + -Pi.single l 1 : Fin τ.rank → ℤ) =
      Pi.single l 1 + (2 : ℤ) • Pi.single i 1 by rw [two_nsmul, two_zsmul]; abel]
    exact not_isRoot_single_add_two hil
  have hN : (RootOperatorFamily'.coeff11 F hD ⟨_, hδ⟩ ⟨_, hγ⟩).natAbs = 1 := by
    rw [RootOperatorFamily'.coeff11,
      RootOperatorFamily'.bracketCoeff_natAbs F hD (β := ⟨_, hδ⟩) (γ := ⟨_, hγ⟩)
        (fun h => hne' (by rw [show -Pi.single l 1 = -(Pi.single l 1 + Pi.single i 1) from h,
          neg_neg]))
        (show IsRoot τ (Pi.single l 1 + Pi.single i 1 + -Pi.single l 1) by
          rw [hsum]; exact isRoot_single τ i)]
    refine stringNorm_of_not_isRoot fun hr => not_isRoot_single_add_two hli ?_
    rw [show (Pi.single i 1 + (2 : ℤ) • Pi.single l 1 : Fin τ.rank → ℤ) =
      -(-Pi.single l 1 - (Pi.single l 1 + Pi.single i 1)) by rw [two_zsmul]; abel]
    exact isRoot_neg_iff.2 hr
  set N := RootOperatorFamily'.coeff11 F hD ⟨_, hδ⟩ ⟨_, hγ⟩
  have hNN : (N : K) * N = 1 := by
    rcases Int.natAbs_eq_iff.1 hN with h | h <;> rw [h] <;> push_cast <;> ring
  have h := commutator_xPar (F := F) hD hτ hδ hγ hne hne' ((N : K) * c) 1
  rw [xPar_of_not_isRoot h12, xPar_of_not_isRoot h21, mul_one, mul_one, hsum, mul_one,
    ← mul_assoc, hNN, one_mul] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem rootGroupCommutators_adjDatum :
    RootGroupCommutators (adjDatum F K) := by
  refine .of_divisible_eq_empty rfl fun γ hγ x hx y hy => ?_
  have hγ' : IsRoot τ γ := mem_adjDatum_roots.1 hγ
  obtain ⟨a, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
  obtain ⟨b, rfl⟩ := (mem_rootGroup_iff hγ' y).1 hy
  rw [Commute, SemiconjBy, ← xPar_add, ← xPar_add, add_comm]

variable (K)

theorem isPerfect_f4 : Group.IsPerfect ↥(adjointGroup .F4 K) :=
  CurtisTits.isPerfect_of_rootGroup_single_le_commutator (f4_isCTGroupDatum K)
    (f4_steinbergExtras K).two_smul_le fun i => by
      obtain ⟨l, hil, hli⟩ := neighbour_F4 i
      exact rootGroup_single_le_commutator f4Data_valid noG2_F4 hil hli

theorem rootGroupCommutators_f4 : RootGroupCommutators (f4Datum K) :=
  rootGroupCommutators_adjDatum

theorem nontrivial_f4 : Nontrivial ↥(adjointGroup .F4 K) := by
  have hr : (f4Datum K).rank = 4 := rfl
  have hmem : Pi.single (⟨0, by rw [hr]; norm_num⟩ : Fin (f4Datum K).rank) 1 ∈ (f4Datum K).roots :=
    Or.inl ⟨1, ⟨0, by rw [hr]; norm_num⟩, by simp⟩
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((f4_steinbergExtras K).ne_bot _ hmem)
  exact nontrivial_of_ne (x : ↥(adjointGroup .F4 K)) 1 fun h => hx (Subtype.ext h)

theorem isQuasisimple_f4 : IsQuasisimple ↥(adjointGroup .F4 K) := by
  have := nontrivial_f4 K
  exact TitsSimplicity.isQuasisimple (f4_isCTGroupDatum K) (f4_steinbergExtras K)
    (f4_bruhatExtras K) (rootGroupCommutators_f4 K)
    (by change IsIndecomposable (Tag.cartan .F4); decide +kernel) (isPerfect_f4 K)

theorem isPerfect_e8 : Group.IsPerfect ↥(adjointGroup .E8 K) :=
  CurtisTits.isPerfect_of_rootGroup_single_le_commutator (e8_isCTGroupDatum K)
    (e8_steinbergExtras K).two_smul_le fun i => by
      obtain ⟨l, hil, hli⟩ := neighbour_E8 i
      exact rootGroup_single_le_commutator e8Data_valid noG2_E8 hil hli

theorem rootGroupCommutators_e8 : RootGroupCommutators (e8Datum K) :=
  rootGroupCommutators_adjDatum

theorem nontrivial_e8 : Nontrivial ↥(adjointGroup .E8 K) := by
  have hr : (e8Datum K).rank = 8 := rfl
  have hmem : Pi.single (⟨0, by rw [hr]; norm_num⟩ : Fin (e8Datum K).rank) 1 ∈ (e8Datum K).roots :=
    Or.inl ⟨1, ⟨0, by rw [hr]; norm_num⟩, by simp⟩
  obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1
    ((e8_steinbergExtras K).ne_bot _ hmem)
  exact nontrivial_of_ne (x : ↥(adjointGroup .E8 K)) 1 fun h => hx (Subtype.ext h)

theorem isQuasisimple_e8 : IsQuasisimple ↥(adjointGroup .E8 K) := by
  have := nontrivial_e8 K
  exact TitsSimplicity.isQuasisimple (e8_isCTGroupDatum K) (e8_steinbergExtras K)
    (e8_bruhatExtras K) (rootGroupCommutators_e8 K)
    (by change IsIndecomposable (Tag.cartan .E8); decide +kernel) (isPerfect_e8 K)

end CFSG.LieType.Steinberg.Adjoint
