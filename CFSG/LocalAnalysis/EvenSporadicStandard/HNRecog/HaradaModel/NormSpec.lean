module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.ASpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog.HaradaModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.EvenSporadicStandard.HNRecog.HaradaLA

section Cert

variable
  (ι : Multiplicative V6 →* ↥P1408) (hι : ∀ v : V6, ι (Multiplicative.ofAdd v) = iotaFun v)

include hι

theorem wordSubgroupP_normGens_le_normalizer :
    wordSubgroupP normGens ≤ normalizer (ι.range : Set ↥P1408) := by
  have hlen : uWords.length = 6 := by decide
  have hnorm : wordSubgroup normGens ≤
      normalizer (wordSubgroup uWords : Set (Equiv.Perm (Fin 1408))) := by
    rw [wordSubgroup, closure_le]
    rintro g ⟨w, hw, rfl⟩
    refine Subgroup.mem_normalizer_fintype (fun x hx => ?_)
    have hle : wordSubgroup uWords ≤
        (wordSubgroup uWords).comap
          (MulAut.conj (elemW w) : Equiv.Perm (Fin 1408) →* Equiv.Perm (Fin 1408)) := by
      rw [wordSubgroup, closure_le]
      rintro x ⟨w', hw', rfl⟩
      obtain ⟨i, hi, hiw⟩ := List.mem_iff_getElem.1 hw'
      have hw'' : uWords.getD i [] = w' := by
        rw [List.getD_eq_getElem _ _ hi]
        exact hiw
      have hi6 : i < 6 := by rw [← hlen]; exact hi
      obtain ⟨k, -, e⟩ := aFacts.norm w hw i hi6
      have e' : elemW w * elemW (uWords.getD i []) * (elemW w)⁻¹ =
          ((iotaFun (vecOfCode k) : ↥P1408) : Equiv.Perm (Fin 1408)) := e
      refine Subgroup.mem_comap.mpr ?_
      change MulAut.conj (elemW w) (elemW w') ∈ wordSubgroup uWords
      rw [MulAut.conj_apply, ← hw'', e']
      exact iotaFun_mem (vecOfCode k)
    have hx' : MulAut.conj (elemW w) x ∈ wordSubgroup uWords := by
      have h : x ∈ (wordSubgroup uWords).comap
          (MulAut.conj (elemW w) : Equiv.Perm (Fin 1408) →* Equiv.Perm (Fin 1408)) := hle hx
      have h2 := Subgroup.mem_comap.mp h
      change MulAut.conj (elemW w) x ∈ wordSubgroup uWords at h2
      rwa [MulAut.conj_apply] at h2
    exact hx'
  rw [range_iota ι hι]
  intro x hx
  show x ∈ normalizer ((wordSubgroup uWords).subgroupOf P1408 : Set ↥P1408)
  rw [mem_normalizer_subgroupOf_P (wordSubgroup_le uWords)]
  exact hnorm hx

theorem card_centralizer_pZ₁ (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card (centralizer ({pZ₁} : Set ↥P1408)) = 3840 := by
  have hspec := (invClasses_classSpec hP).2.2.2
  have hcent : Nat.card ↥(P1408 ⊓
      centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))) = 3840 := hspec.cent_card
  have heq : centralizer ({pZ₁} : Set ↥P1408) =
      (P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))).subgroupOf P1408 := by
    ext y
    rw [mem_centralizer_singleton_P, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨y.2, by rw [coe_pZ₁] at h; exact h⟩
    · rintro ⟨-, h⟩
      rw [coe_pZ₁]; exact h
  rw [heq, card_subgroupOf_P inf_le_left]
  exact hcent

theorem centralizer_pZ₁_le_normGens (hP : Nat.card ↥P1408 = 177408000) :
    centralizer ({pZ₁} : Set ↥P1408) ≤ wordSubgroupP normGens := by
  have hspec := (invClasses_classSpec hP).2.2.2
  have hcl : closure (elemW '' {w | w ∈ classz₁.centGens}) =
      P1408 ⊓ centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408))) := hspec.cent_eq
  intro x hx
  show (x : Equiv.Perm (Fin 1408)) ∈ wordSubgroup normGens
  have hxmem : (x : Equiv.Perm (Fin 1408)) ∈
      closure (elemW '' {w | w ∈ classz₁.centGens}) := by
    rw [hcl]
    refine ⟨x.2, ?_⟩
    change (x : Equiv.Perm (Fin 1408)) ∈
      Subgroup.centralizer ({elemZ₁} : Set (Equiv.Perm (Fin 1408)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := (mem_centralizer_singleton_P (x := pZ₁) (y := x)).1 hx
    rwa [coe_pZ₁] at hcomm
  have hsub : closure (elemW '' {w | w ∈ classz₁.centGens}) ≤ wordSubgroup normGens := by
    rw [wordSubgroup]
    apply Subgroup.closure_mono
    rintro g ⟨w, hw, rfl⟩
    exact ⟨w, List.mem_append_left _ hw, rfl⟩
  exact hsub hxmem

theorem ncard_conjClass_normalizer_z₁ (hP : Nat.card ↥P1408 = 177408000) :
    (conjClass (normalizer (ι.range : Set ↥P1408)) pZ₁).ncard = 12 := by
  classical
  set S : Finset ℕ := (Finset.range 64).filter (fun k => typeIdx k = 2) with hS
  have hScard : S.card = 12 := by
    rw [hS]
    decide
  have hinj : Set.InjOn (fun k => iotaFun (vecOfCode k)) ↑S := by
    intro a ha b hb hab
    have ha' : a < 64 := Finset.mem_range.1 (Finset.mem_filter.1 ha).1
    have hb' : b < 64 := Finset.mem_range.1 (Finset.mem_filter.1 hb).1
    have h1 : ι (Multiplicative.ofAdd (vecOfCode a)) = ι (Multiplicative.ofAdd (vecOfCode b)) := by
      rw [hι, hι]
      exact hab
    have h2 := injective_iota ι hι h1
    rw [← codeOfVec_vecOfCode a ha', ← codeOfVec_vecOfCode b hb']
    exact congrArg codeOfVec (Multiplicative.ofAdd.injective h2)
  have hz1 : pZ₁ ∈ ι.range :=
    ⟨Multiplicative.ofAdd (vecOfCode 45), by rw [hι]; exact aFacts.iota_z₁⟩
  have heq : conjClass (normalizer (ι.range : Set ↥P1408)) pZ₁ =
      (fun k => iotaFun (vecOfCode k)) '' ↑S := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      have hxr : n * pZ₁ * n⁻¹ ∈ ι.range := (Subgroup.mem_set_normalizer_iff.1 hn pZ₁).1 hz1
      obtain ⟨v, hv⟩ := hxr
      have hk := codeOfVec_lt (Multiplicative.toAdd v)
      have hfk : iotaFun (vecOfCode (codeOfVec (Multiplicative.toAdd v))) = n * pZ₁ * n⁻¹ := by
        rw [vecOfCode_codeOfVec, ← hι]
        exact hv
      refine ⟨codeOfVec (Multiplicative.toAdd v),
        Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, ?_⟩, hfk⟩
      refine aFacts.conj_z₁ hP _ hk ((n⁻¹ : ↥P1408) : Equiv.Perm (Fin 1408)) (n⁻¹).2 ?_
      have h2 : (n⁻¹ * (n * pZ₁ * n⁻¹) * n⁻¹⁻¹ : ↥P1408) = pZ₁ := by group
      have h3 := congrArg (fun y : ↥P1408 => (y : Equiv.Perm (Fin 1408))) h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      rw [hfk]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact h3
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hk64, ht⟩ := Finset.mem_filter.1 hk
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact absurd ht (by decide)
      have hk16 : k ≠ 16 := by
        rintro rfl
        exact absurd ht (by decide)
      obtain ⟨n, hn, e⟩ := aFacts.fuse 45 (by norm_num) k (Finset.mem_range.1 hk64)
        (by norm_num) (by norm_num) hk0 hk16 (by rw [ht]; decide)
      refine ⟨⟨n, wordSubgroup_le normGens hn⟩,
        wordSubgroupP_normGens_le_normalizer ι hι (mem_wordSubgroupP.2 hn), ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← aFacts.iota_z₁]
      exact e.symm
  rw [heq, Set.InjOn.ncard_image hinj, Set.ncard_coe_finset, hScard]

theorem card_normalizer_A (hP : Nat.card ↥P1408 = 177408000) :
    Nat.card (normalizer (ι.range : Set ↥P1408)) = 46080 := by
  have hle : centralizer ({pZ₁} : Set ↥P1408) ≤ normalizer (ι.range : Set ↥P1408) :=
    (centralizer_pZ₁_le_normGens ι hι hP).trans (wordSubgroupP_normGens_le_normalizer ι hι)
  have hos := CFSG.Sporadic.SmallOddCore.ncard_conjClass_mul_card
    (normalizer (ι.range : Set ↥P1408)) pZ₁
  rw [ncard_conjClass_normalizer_z₁ ι hι hP, inf_eq_right.mpr hle,
    card_centralizer_pZ₁ ι hι hP] at hos
  norm_num at hos
  exact hos.symm

end Cert

end CFSG.EvenSporadicStandard.HNRecog.HaradaModel
