module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Exclusion
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.ClassicalInvolution.QuaternionStructure
public import CFSG.LocalAnalysis.ComponentClassification.TwoComponentConvention
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldPrimeOrderFixedSubfield
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OrderThreeNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2PSLRangeCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinUDecomposition
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTen
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationTenStructuralIdentities
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2FieldProjectionArithmetic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2OrderPSubgroupCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphReconstruction
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9

public section

namespace CFSG.ClassicalInvolution

open CFSG.Sporadic.Schreier (centralizerIn conjClass mem_centralizerIn)

variable {M : Type*} [Group M]

theorem NoNonsolvableClassicalAt.of_ambient_normal_pGroup (H : Subgroup M) [Finite H] (t : H)
    (U : Subgroup M) (hUK : U ≤ centralizerIn H (t : M))
    (hUn : centralizerIn H (t : M) ≤ Subgroup.normalizer (U : Set M)) (hU : IsPGroup 2 U)
    (hcon : centralizerIn H (t : M) ⊓ Subgroup.centralizer (U : Set M) ≤ U) :
    NoNonsolvableClassicalAt t := by
  have hUH : U ≤ H := fun x hx => ((mem_centralizerIn.1 (hUK hx)).1)
  refine NoNonsolvableClassicalAt.of_normal_pGroup_self_centralizing (U.subgroupOf H)
    (hU.comap_of_injective H.subtype H.subtype_injective) ?_ ?_ ?_
  · intro x hx
    have hxK := mem_centralizerIn.1 (hUK hx)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (by simpa using hxK.2)
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgK : (g : M) ∈ centralizerIn H (t : M) :=
      mem_centralizerIn.2 ⟨g.2, by
        simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)⟩
    have := Subgroup.mem_normalizer_iff.1 (hUn hgK) (x : M)
    simpa [Subgroup.mem_subgroupOf] using this
  · rintro g ⟨hg, hgU⟩
    have hgK : (g : M) ∈ centralizerIn H (t : M) :=
      mem_centralizerIn.2 ⟨g.2, by
        simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)⟩
    have hgC : (g : M) ∈ Subgroup.centralizer (U : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := Subgroup.mem_centralizer_iff.1 hgU ⟨u, hUH hu⟩
        (by simpa [Subgroup.mem_subgroupOf] using hu)
      exact congrArg Subtype.val this
    exact hcon ⟨hgK, hgC⟩

theorem NoNonsolvableClassicalAt.of_ambient_index_two (H : Subgroup M) [Finite H] (t : H)
    (N : Subgroup M) (hNK : N ≤ centralizerIn H (t : M))
    (hcard : Nat.card (centralizerIn H (t : M)) = 2 * Nat.card N) (htN : (t : M) ∉ N) :
    NoNonsolvableClassicalAt t := by
  set C : Subgroup H := Subgroup.centralizer ({t} : Set H) with hC
  set N'' : Subgroup C := (N.subgroupOf H).subgroupOf C with hN''
  have hmapC : C.map H.subtype = centralizerIn H (t : M) :=
    CFSG.Sporadic.Schreier.map_centralizer_subtype H t
  have hcardC : Nat.card C = Nat.card (centralizerIn H (t : M)) := by
    rw [← hmapC, Subgroup.card_map_of_injective H.subtype_injective]
  have hf : Function.Injective (H.subtype.comp C.subtype) :=
    H.subtype_injective.comp C.subtype_injective
  have hmapN : N''.map (H.subtype.comp C.subtype) = N := by
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact hc
    · intro hx
      have hxK := hNK hx
      rw [← hmapC] at hxK
      obtain ⟨y, hy, rfl⟩ := hxK
      exact ⟨⟨y, hy⟩, hx, rfl⟩
  have hcardN : Nat.card N'' = Nat.card N := by
    rw [← hmapN, Subgroup.card_map_of_injective hf]
  have hNH : N ≤ H := fun x hx => (mem_centralizerIn.1 (hNK hx)).1
  have : Finite N := Finite.of_injective (Subgroup.inclusion hNH) (Subgroup.inclusion_injective _)
  have hpos : 0 < Nat.card N := Nat.card_pos
  have hidx : N''.index = 2 := by
    have h := Subgroup.card_mul_index N''
    rw [hcardN, hcardC, hcard] at h
    have : Nat.card N * N''.index = Nat.card N * 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  refine NoNonsolvableClassicalAt.of_index_two (N.subgroupOf H) ?_ hidx ?_
  · exact Subgroup.normal_of_index_eq_two hidx
  · rw [Subgroup.mem_subgroupOf]
    exact htN

@[expose] def CentralizerGood (H : Subgroup M) (r : M) : Prop :=
  (∃ U : Subgroup M, U ≤ centralizerIn H r ∧ centralizerIn H r ≤ Subgroup.normalizer (U : Set M) ∧
      IsPGroup 2 U ∧ centralizerIn H r ⊓ Subgroup.centralizer (U : Set M) ≤ U) ∨
    ∃ N : Subgroup M, N ≤ centralizerIn H r ∧
      Nat.card (centralizerIn H r) = 2 * Nat.card N ∧ r ∉ N

theorem NoNonsolvableClassicalAt.of_centralizerGood (H : Subgroup M) [Finite H] (t : H)
    (h : CentralizerGood H (t : M)) : NoNonsolvableClassicalAt t := by
  rcases h with ⟨U, hUK, hUn, hU, hcon⟩ | ⟨N, hNK, hcard, htN⟩
  · exact NoNonsolvableClassicalAt.of_ambient_normal_pGroup H t U hUK hUn hU hcon
  · exact NoNonsolvableClassicalAt.of_ambient_index_two H t N hNK hcard htN

theorem noNonsolvableClassical_of_reps (H : Subgroup M) [Finite H] (reps : List M)
    (hreps : ∀ r ∈ reps, r ∈ H)
    (hcov : ∀ u ∈ H, orderOf u = 2 → ∃ r ∈ reps, ∃ c ∈ H, u = c * r * c⁻¹)
    (hgood : ∀ r ∈ reps, CentralizerGood H r) : NoNonsolvableClassical H := by
  refine NoNonsolvableClassical.of_conj_reps {x : H | ∃ r ∈ reps, (x : M) = r} ?_ ?_
  · intro z hz
    obtain ⟨r, hr, c, hc, hzr⟩ := hcov z z.2 (by rw [← Subgroup.orderOf_coe] at hz; exact hz)
    refine ⟨⟨r, hreps r hr⟩, ⟨r, hr, rfl⟩, ?_⟩
    rw [isConj_iff]
    refine ⟨⟨c, hc⟩, ?_⟩
    apply Subtype.ext
    simp [hzr]
  · rintro s ⟨r, hr, hsr⟩
    exact NoNonsolvableClassicalAt.of_centralizerGood H s (hsr ▸ hgood r hr)

section Lists

@[expose] def subgroupOfList (L : List M) (h1 : (1 : M) ∈ L)
    (hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L) (hinv : ∀ x ∈ L, x⁻¹ ∈ L) : Subgroup M where
  carrier := {x | x ∈ L}
  one_mem' := h1
  mul_mem' {x y} hx hy := hmul x hx y hy
  inv_mem' {x} hx := hinv x hx

theorem mem_subgroupOfList {L : List M} {h1 : (1 : M) ∈ L} {hmul : ∀ x ∈ L, ∀ y ∈ L, x * y ∈ L}
    {hinv : ∀ x ∈ L, x⁻¹ ∈ L} {x : M} : x ∈ subgroupOfList L h1 hmul hinv ↔ x ∈ L := Iff.rfl

variable [DecidableEq M]

@[expose] def twoConstrainedCheck (KL UL : List M) (k : ℕ) : Bool :=
  decide ((1 : M) ∈ UL) && UL.all (fun x => UL.all fun y => decide (x * y ∈ UL)) &&
    UL.all (fun x => decide (x⁻¹ ∈ UL)) && UL.all (fun u => decide (u ∈ KL)) &&
    UL.all (fun u => decide (u ^ 2 ^ k = 1)) &&
    KL.all (fun g => UL.all fun u => decide (g * u * g⁻¹ ∈ UL)) &&
    KL.all (fun g => !(UL.all fun u => decide (g * u = u * g)) || decide (g ∈ UL))

theorem exists_normal_pGroup_of_check (K : Subgroup M) (KL UL : List M)
    (hK : ∀ g, g ∈ KL ↔ g ∈ K) (k : ℕ) (h : twoConstrainedCheck KL UL k = true) :
    ∃ U : Subgroup M, U ≤ K ∧ K ≤ Subgroup.normalizer (U : Set M) ∧ IsPGroup 2 U ∧
      K ⊓ Subgroup.centralizer (U : Set M) ≤ U := by
  simp only [twoConstrainedCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hmul⟩, hinv⟩, hUK⟩, hpow⟩, hnorm⟩, hself⟩ := h
  have hmul' : ∀ x ∈ UL, ∀ y ∈ UL, x * y ∈ UL := fun x hx y hy => by
    simpa using hmul x hx y hy
  have hinv' : ∀ x ∈ UL, x⁻¹ ∈ UL := hinv
  let U := subgroupOfList UL h1 hmul' hinv'
  have hmemU : ∀ x, x ∈ U ↔ x ∈ UL := fun x => Iff.rfl
  refine ⟨U, fun u hu => (hK u).1 (hUK u hu), ?_, ?_, ?_⟩
  · intro g hg
    have hgL : g ∈ KL := (hK g).2 hg
    rw [Subgroup.mem_normalizer_iff]
    have hconj : ∀ g ∈ KL, ∀ x, x ∈ UL → g * x * g⁻¹ ∈ UL := fun g hg x hx => by
      simpa using hnorm g hg x hx
    intro x
    rw [hmemU, hmemU]
    refine ⟨fun hx => hconj g hgL x hx, fun hx => ?_⟩
    have hgi : g⁻¹ ∈ KL := (hK _).2 (inv_mem hg)
    have := hconj g⁻¹ hgi _ hx
    simpa [mul_assoc] using this
  · intro u
    have hu : u.1 ∈ UL := u.2
    exact ⟨k, Subtype.ext (by simpa using hpow u.1 hu)⟩
  · rintro g ⟨hg, hgU⟩
    have hgL : g ∈ KL := (hK g).2 hg
    have hcomm : ∀ u ∈ UL, g * u = u * g := fun u hu =>
      (Subgroup.mem_centralizer_iff.1 hgU u hu).symm
    have := hself g hgL
    rcases this with h | h
    · exfalso
      have htrue : (UL.all fun u => decide (g * u = u * g)) = true :=
        List.all_eq_true.2 fun u hu => decide_eq_true (hcomm u hu)
      rw [htrue] at h
      exact Bool.noConfusion h
    · exact (hmemU g).2 h

@[expose] def indexTwoCheck (r : M) (KL NL : List M) : Bool :=
  decide ((1 : M) ∈ NL) && NL.all (fun x => NL.all fun y => decide (x * y ∈ NL)) &&
    NL.all (fun x => decide (x⁻¹ ∈ NL)) && NL.all (fun u => decide (u ∈ KL)) &&
    decide (KL.length = 2 * NL.length) && decide NL.Nodup && !decide (r ∈ NL)

theorem exists_index_two_of_check (r : M) (K : Subgroup M) (KL NL : List M)
    (hK : ∀ g, g ∈ KL ↔ g ∈ K) (hKn : KL.Nodup) (h : indexTwoCheck r KL NL = true) :
    ∃ N : Subgroup M, N ≤ K ∧ Nat.card K = 2 * Nat.card N ∧ r ∉ N := by
  simp only [indexTwoCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, hmul⟩, hinv⟩, hNK⟩, hlen⟩, hnd⟩, hr⟩ := h
  have hmul' : ∀ x ∈ NL, ∀ y ∈ NL, x * y ∈ NL := fun x hx y hy => by
    simpa using hmul x hx y hy
  let N := subgroupOfList NL h1 hmul' hinv
  have hcardK : Nat.card K = KL.length := by
    have : (K : Set M) = {g | g ∈ KL} := by ext g; exact ((hK g).symm)
    classical
    rw [show Nat.card K = Nat.card (↥(KL.toFinset)) from ?_, Nat.card_eq_fintype_card,
      Fintype.card_coe, List.toFinset_card_of_nodup hKn]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simpa using (hK g).symm)
  have hcardN : Nat.card N = NL.length := by
    classical
    rw [show Nat.card N = Nat.card (↥(NL.toFinset)) from ?_, Nat.card_eq_fintype_card,
      Fintype.card_coe, List.toFinset_card_of_nodup hnd]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp [N, mem_subgroupOfList])
  refine ⟨N, fun u hu => (hK u).1 (hNK u hu), ?_, hr⟩
  rw [hcardK, hcardN]
  exact hlen

end Lists

end CFSG.ClassicalInvolution
