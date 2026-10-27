module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableIZ
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.InvClasses
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.Enum

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel27

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.HaradaModel

section Cert


theorem exists_hom_centralizer_z (hP : Nat.card ↥P1408 = 177408000) :
    ∃ φ : ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) →*
        Equiv.Perm (Fin 5),
      Function.Surjective φ ∧
      (∀ (x : ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408))))) (p : Fin 1408),
        blkF 5 blkData1.blk ((x : Equiv.Perm (Fin 1408)) p) =
          (blkF 5 blkData1.blk p).map (φ x)) ∧
      φ.ker = (closure (elemW '' {w | w ∈ nWords1})).subgroupOf
        (P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) := by
  have h1 := tableI1OK_true
  simp only [tableI1OK, Bool.and_eq_true] at h1
  obtain ⟨⟨⟨⟨⟨⟨⟨hblk, himg⟩, hN⟩, htriv⟩, hcomm⟩, hma⟩, hmz⟩, hsq⟩ := h1
  obtain ⟨⟨-, hcard, hcl⟩, -, -, -⟩ := invClasses_classSpec hP
  obtain ⟨φ, hφ, hrange, hker⟩ : ∃ φ : ↥(closure (elemW '' {w | w ∈ blkData1.gens})) →*
      Equiv.Perm (Fin 5),
      (∀ (x : ↥(closure (elemW '' {w | w ∈ blkData1.gens}))) (p : Fin 1408),
        blkF 5 blkData1.blk ((x : Equiv.Perm (Fin 1408)) p) =
          (blkF 5 blkData1.blk p).map (φ x)) ∧
      φ.range = genOf 5 blkData1.labs ∧
      (∀ x : ↥(closure (elemW '' {w | w ∈ blkData1.gens})),
        φ x = 1 ↔ ∀ p : Fin 1408,
          blkF 5 blkData1.blk ((x : Equiv.Perm (Fin 1408)) p) = blkF 5 blkData1.blk p) :=
    blkData_spec hblk
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
  have hNker : ∀ (n : Equiv.Perm (Fin 1408)) (h : n ∈ closure (elemW '' {w | w ∈ nWords1})),
      φ ⟨n, hNX h⟩ = 1 := fun n h =>
    (hker ⟨n, hNX h⟩).2 (fun p => blkTriv_closure hg hNw htriv n h p)
  have hX : Nat.card ↥(closure (elemW '' {w | w ∈ blkData1.gens})) = 30720 := by
    rw [hXeq]
    exact hcard
  have hrange' : Nat.card ↥φ.range = 120 := by
    rw [hrange]
    exact blkImage_spec hblk (by show 5 < 2 ^ 32; norm_num) himg
  have hcardK : Nat.card ↥φ.ker = 256 := by
    have h := Subgroup.card_ker_mul_card_range φ
    rw [hX, hrange'] at h
    omega
  haveI : Finite ↥φ.ker := Nat.finite_of_card_ne_zero (by rw [hcardK]; norm_num)
  have hNK : (closure (elemW '' {w | w ∈ nWords1})).subgroupOf
      (closure (elemW '' {w | w ∈ blkData1.gens})) ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    simpa using hNker (n : Equiv.Perm (Fin 1408)) (Subgroup.mem_subgroupOf.mp hn)
  have hcardN' : Nat.card ↥((closure (elemW '' {w | w ∈ nWords1})).subgroupOf
      (closure (elemW '' {w | w ∈ blkData1.gens}))) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv, hNcard]
  have hN'eqK : (closure (elemW '' {w | w ∈ nWords1})).subgroupOf
      (closure (elemW '' {w | w ∈ blkData1.gens})) = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hNK (by rw [hcardK, hcardN'])
  have hcardPerm : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num
  haveI : Finite ↥φ.range := Nat.finite_of_card_ne_zero (by rw [hrange']; norm_num)
  have hrange_top : φ.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq (G := Equiv.Perm (Fin 5)) (H := φ.range) ?_
    rw [hrange', hcardPerm]
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hrange_top
  let e : ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) ≃*
      ↥(closure (elemW '' {w | w ∈ blkData1.gens})) := MulEquiv.subgroupCongr hXeq.symm
  refine ⟨φ.comp e.toMonoidHom, hsurj.comp e.surjective, fun x p => hφ (e x) p, ?_⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ← hN'eqK,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  rfl

theorem exists_hom_centralizer_pZ (hP : Nat.card ↥P1408 = 177408000) :
    ∃ ψ : ↥(centralizer ({pZ} : Set ↥P1408)) →* Equiv.Perm (Fin 5),
      Function.Surjective ψ ∧
      ψ.ker = (wordSubgroupP nWords1).subgroupOf (centralizer ({pZ} : Set ↥P1408)) ∧
      ∀ (x : ↥(centralizer ({pZ} : Set ↥P1408))) (p : Fin 1408),
        blkF 5 blkData1.blk (((x : ↥P1408) : Equiv.Perm (Fin 1408)) p) =
          (blkF 5 blkData1.blk p).map (ψ x) := by
  obtain ⟨φ, hsurj, hact, hker⟩ := exists_hom_centralizer_z hP
  let e : ↥(centralizer ({pZ} : Set ↥P1408)) ≃*
      ↥(P1408 ⊓ centralizer ({elemZ} : Set (Equiv.Perm (Fin 1408)))) :=
    centralizerSubtypeEquiv P1408 pZ
  refine ⟨φ.comp e.toMonoidHom, hsurj.comp e.surjective, ?_, fun x p => hact (e x) p⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  rfl

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel27
