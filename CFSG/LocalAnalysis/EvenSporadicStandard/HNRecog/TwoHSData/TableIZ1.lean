module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableITrue
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableISpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeA5
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

section Cert


private theorem rep_elemAZ₁ : Rep 1408 (tabW (wordA ++ wordZ₁)) (elemA * elemZ₁) := by
  have h := rep_elemW (wordA ++ wordZ₁) (by decide)
  rwa [elemW_append] at h

theorem isShape_centralizer_z₁ (hP : Nat.card ↥P1408 = 177408000) :
    IsShapeTwoTwoTimesTwoFourA5
      ↥(P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) := by
  have h3 := tableI3OK_true
  simp only [tableI3OK, Bool.and_eq_true, Bool.not_eq_true'] at h3
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hblk, himg⟩, hS⟩, hcomm⟩, hN⟩, htriv⟩, hmem⟩, hsq⟩, hnA⟩, hnZ⟩, hnAZ⟩ := h3
  obtain ⟨-, -, -, ⟨-, hcard, hcl⟩⟩ := invClasses_classSpec hP
  obtain ⟨φ, hφ, hrange, hker⟩ := blkData_spec hblk
  have hg : gensOK = true := gensOK_of_blkDataOK hblk
  obtain ⟨-, hSw⟩ := enumW_gens_words hS
  obtain ⟨-, hNw⟩ := enumW_gens_words hN
  obtain ⟨hScard, hSenum⟩ := enumW_spec hS
  obtain ⟨hNcard, hNenum⟩ := enumW_spec hN
  have hXeq : closure (elemW '' {w | w ∈ classz₁.centGens}) =
      P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) := hcl
  have hz2 : elemZ₁ * elemZ₁ = 1 := mul_self_eq_one_of_orderOf_eq_two twoHSBasic_spec.2.2.2.1
  have hSX : closure (elemW '' {w | w ∈ blkData3.gens}) ≤
      P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    refine Subgroup.mem_inf.2 ⟨elemW_mem w, mem_centralizer_iff.2 ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact ((commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hSw w hw)) rep_elemZ₁).1
      (List.all_eq_true.1 hcomm w hw)).symm
  have hNS : closure (elemW '' {w | w ∈ nWords3}) ≤
      closure (elemW '' {w | w ∈ blkData3.gens}) := by
    rw [closure_le]
    rintro _ ⟨w, hw, rfl⟩
    exact (hSenum.memT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hNw w hw))).1
      (List.all_eq_true.1 hmem w hw)
  have hVX : closure ({elemA, elemZ₁} : Set (Equiv.Perm (Fin 1408))) ≤
      P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) :=
    pair_le_centralizer elemZ₁_mem
  have hVcen : ∀ v ∈ closure ({elemA, elemZ₁} : Set (Equiv.Perm (Fin 1408))),
      ∀ x ∈ P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))), x * v = v * x :=
    fun v hv x hx => pair_central hx v hv
  have hV : Nonempty (↥(closure ({elemA, elemZ₁} : Set (Equiv.Perm (Fin 1408)))) ≃* Elem2 2) :=
    TwoHSData.nonempty_mulEquiv_elem2_closure_pair elemA_mul_self hz2 (elemA_comm elemZ₁_mem)
      (ne_one_of_orderOf_eq_two twoHSBasic_spec.1)
      (ne_one_of_orderOf_eq_two twoHSBasic_spec.2.2.2.1) (classes_distinct hP).2.2.2.1
  have hVS : ∀ v ∈ closure ({elemA, elemZ₁} : Set (Equiv.Perm (Fin 1408))),
      v ∈ closure (elemW '' {w | w ∈ blkData3.gens}) → v = 1 := by
    intro v hv hvS
    rcases (TwoHSData.mem_closure_pair_iff elemA_mul_self hz2 (elemA_comm elemZ₁_mem)).1 hv with
      h | h | h | h
    · exact h
    · rw [h] at hvS
      exact absurd ((hSenum.memT_iff rep_elemA).2 hvS) (by rw [hnA]; exact Bool.false_ne_true)
    · rw [h] at hvS
      exact absurd ((hSenum.memT_iff rep_elemZ₁).2 hvS) (by rw [hnZ]; exact Bool.false_ne_true)
    · rw [h] at hvS
      exact absurd ((hSenum.memT_iff rep_elemAZ₁).2 hvS) (by rw [hnAZ]; exact Bool.false_ne_true)
  have hNker : ∀ (n : Equiv.Perm (Fin 1408)) (h : n ∈ closure (elemW '' {w | w ∈ nWords3})),
      φ ⟨n, hNS h⟩ = 1 := fun n h =>
    (hker ⟨n, hNS h⟩).2 (fun p => blkTriv_closure hg hNw htriv n h p)
  have hX : Nat.card ↥(P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) = 3840 :=
    hcard
  have hrange' : Nat.card ↥φ.range = 60 := by
    rw [hrange]
    exact blkImage_spec hblk (by show 5 < 2 ^ 32; norm_num) himg
  exact TwoHSData.isShapeTwoTwoTimesTwoFourA5_of_hom
    (P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))))
    (closure ({elemA, elemZ₁} : Set (Equiv.Perm (Fin 1408))))
    (closure (elemW '' {w | w ∈ blkData3.gens})) (closure (elemW '' {w | w ∈ nWords3})) φ hVX hSX
    hVcen hV hVS hX hScard hNS hNker hNcard ((sqOneOK_iff hNenum).1 hsq) hrange'

end Cert

end CFSG.EvenSporadicStandard.HNRecog
