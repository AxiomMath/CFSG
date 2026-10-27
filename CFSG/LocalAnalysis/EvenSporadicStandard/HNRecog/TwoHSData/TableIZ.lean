module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableITrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeS5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Cert


theorem isShape_centralizer_z (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoSixS5 ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) := by
  have h1 := tableI1OK_true
  simp only [tableI1OK, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨hblk, himg⟩, hN⟩, htriv⟩, hcomm⟩, hma⟩, hmz⟩, hsq⟩ := h1
  obtain ⟨⟨-, hcard, hcl⟩, -, -, -⟩ := invClasses_classSpec hP
  obtain ⟨φ, hφ, hrange, hker⟩ := blkData_spec hblk
  have hg : gensOK = true := gensOK_of_blkDataOK hblk
  obtain ⟨-, hNw⟩ := enumW_gens_words hN
  obtain ⟨hNcard, hNenum⟩ := enumW_spec hN
  have hXeq : closure (elemW '' {w | w ∈ blkData1.gens}) =
      P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := hcl
  have hz2 : elemZ * elemZ = 1 := mul_self_eq_one_of_orderOf_eq_two twoHSBasic_spec.2.1
  have hNX : closure (elemW '' {w | w ∈ nWords1}) ≤ closure (elemW '' {w | w ∈ blkData1.gens}) := by
    rw [hXeq, closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.2 ⟨elemW_mem w, mem_centralizer_iff.2 ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ((commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hNw w hw)) rep_elemZ).1
      (List.all_eq_true.1 hcomm w hw)).symm
  have hVN : closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408))) ≤
      closure (elemW '' {w | w ∈ nWords1}) := by
    rw [closure_le]
    rintro v (rfl | hv)
    · exact (hNenum.memT_iff rep_elemA).1 hma
    · rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (hNenum.memT_iff rep_elemZ).1 hmz
  have hVcen : ∀ v ∈ closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408))),
      ∀ x ∈ closure (elemW '' {w | w ∈ blkData1.gens}), x * v = v * x := by
    intro v hv x hx
    have hx' : x ∈ P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))) := hXeq ▸ hx
    exact pair_central hx' v hv
  have hV : Nonempty (↥(closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408)))) ≃* Elem2 2) :=
    TwoHSData.nonempty_mulEquiv_elem2_closure_pair elemA_mul_self hz2 (elemA_comm elemZ_mem)
      (ne_one_of_orderOf_eq_two twoHSBasic_spec.1) (ne_one_of_orderOf_eq_two twoHSBasic_spec.2.1)
      (classes_distinct hP).1
  have hNker : ∀ (n : Equiv.Perm (Fin 1408)) (h : n ∈ closure (elemW '' {w | w ∈ nWords1})),
      φ ⟨n, hNX h⟩ = 1 := fun n h =>
    (hker ⟨n, hNX h⟩).2 (fun p => blkTriv_closure hg hNw htriv n h p)
  have hX : Nat.card ↥(closure (elemW '' {w | w ∈ blkData1.gens})) = 30720 := by
    rw [hXeq]
    exact hcard
  have hrange' : Nat.card ↥φ.range = 120 := by
    rw [hrange]
    exact blkImage_spec hblk (by show 5 < 2 ^ 32; norm_num) himg
  have hVenum : IsEnumSet 1408 (pair4 (idT 1408) (tabW wordA) (tabW wordZ) (tabW wordAZ))
      (closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408))) : Set (Equiv.Perm (Fin 1408))) :=
    isEnumSet_pair elemA_mul_self hz2 (elemA_comm elemZ_mem) rep_elemA rep_elemZ rep_elemAZ
  have hsq' : ∀ n ∈ closure (elemW '' {w | w ∈ nWords1}),
      n * n ∈ closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408))) := by
    refine (hNenum.forall_iff
      (fun s => memT 1408 (pair4 (idT 1408) (tabW wordA) (tabW wordZ) (tabW wordAZ))
        (compT 1408 s s))
      (fun g => g * g ∈ closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408)))) ?_).1 hsq
    intro x g hx
    exact hVenum.memT_iff (Rep.compT hx hx)
  have hshape := TwoHSData.isShapeTwoTwoSixS5_of_hom
    (closure (elemW '' {w | w ∈ blkData1.gens}))
    (closure ({elemA, elemZ} : Set (Equiv.Perm (Fin 1408))))
    (closure (elemW '' {w | w ∈ nWords1})) φ hVN hNX hVcen hV hNker hX hNcard hrange' hsq'
  rw [← hXeq]
  exact hshape

end Cert

end CFSG.EvenSporadicStandard.HNRecog
