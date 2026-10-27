module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.Sporadic.Recognition.JankoWongPSLNine
public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix
public import CFSG.LocalAnalysis.EvenBN.Tits.I21Outer
public import CFSG.LocalAnalysis.EvenBN.Tits.I21LA6AutPgl
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoConstrained
public import CFSG.LocalAnalysis.EvenBN.Tits.Prelim.SecTwoQuotient
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.I21L

open Subgroup Equiv CFSG.GorensteinWalter
open scoped MatrixGroups

local notation "A₆" => alternatingGroup (Fin 6)

theorem a6aut_card_gf : Nat.card (GaloisField 3 2) = 9 := by
  rw [GaloisField.card 3 2 (by norm_num)]
  norm_num

theorem a6aut_nonempty_equiv_psl :
    Nonempty (alternatingGroup (Fin 6) ≃* PSL(2, GaloisField 3 2)) := by
  obtain ⟨φ⟩ :=
    CFSG.Sporadic.Recognition.JankoWong.nonempty_mulEquiv_alternatingGroup_six_of_card_nine
      (F := GaloisField 3 2) a6aut_card_gf
  exact ⟨φ.symm⟩

theorem isPSLTwo_nine_of_A6 {J : Type*} [Group J] (e : J ≃* alternatingGroup (Fin 6)) :
    IsPSLTwo J 9 := by
  obtain ⟨φ⟩ := a6aut_nonempty_equiv_psl
  exact ⟨GaloisField 3 2, inferInstance, inferInstance, a6aut_card_gf, ⟨e.trans φ⟩⟩

theorem A6_involutions_conj {J : Type*} [Group J] (e : J ≃* alternatingGroup (Fin 6)) {a b : J}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    ∃ g : J, g * a * g⁻¹ = b := by
  obtain ⟨φ⟩ := a6aut_nonempty_equiv_psl
  let e' : J ≃* PSL(2, GaloisField 3 2) := e.trans φ
  have hodd : IsOddPrimePower (Nat.card (GaloisField 3 2)) :=
    ⟨3, 2, Nat.prime_three, ⟨1, rfl⟩, by norm_num, by rw [a6aut_card_gf]; norm_num⟩
  have hinv : ∀ x : J, x * x = 1 → x ≠ 1 →
      CFSG.BenderSuzuki.PFAppendixIII.IsInvolution (e' x) := fun x hx hx1 =>
    ⟨fun h => hx1 (e'.injective (by rw [h, map_one])), by rw [pow_two, ← map_mul, hx, map_one]⟩
  obtain ⟨g, hg⟩ := psl2_involutions_conjugate_of_odd_prime_power (GaloisField 3 2) hodd (e' a)
    (e' b) (hinv a ha ha1) (hinv b hb hb1)
  exact ⟨e'.symm g, e'.injective (by simpa using hg)⟩

def a6autRep : alternatingGroup (Fin 6) :=
  ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.2 (by decide)⟩

theorem a6autRep_sq : a6autRep * a6autRep = 1 := by decide

theorem a6autRep_ne_one : a6autRep ≠ 1 := by decide

theorem a6aut_card_cent_rep :
    Nat.card {x : alternatingGroup (Fin 6) // x * a6autRep = a6autRep * x} = 8 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem a6aut_card_centralizer_congr {G H : Type*} [Group G] [Group H] (φ : G ≃* H) (g : G) :
    Nat.card (centralizer ({g} : Set G)) = Nat.card (centralizer ({φ g} : Set H)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun x => ?_)
  simp only [mem_centralizer_singleton_iff, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul]
  exact (φ.injective.eq_iff).symm

theorem a6aut_map_involution {J : Type*} [Group J] (e : J ≃* alternatingGroup (Fin 6)) {a : J}
    (ha : a * a = 1) (ha1 : a ≠ 1) : e a * e a = 1 ∧ e a ≠ 1 :=
  ⟨by rw [← map_mul, ha, map_one], fun h => ha1 (e.injective (by rw [h, map_one]))⟩

theorem a6aut_exists_equiv_rep {J : Type*} [Group J] (e : J ≃* alternatingGroup (Fin 6)) {a : J}
    (ha : a * a = 1) (ha1 : a ≠ 1) : ∃ ψ : J ≃* alternatingGroup (Fin 6), ψ a = a6autRep := by
  obtain ⟨ha', ha1'⟩ := a6aut_map_involution e ha ha1
  obtain ⟨g, hg⟩ := A6_involutions_conj (MulEquiv.refl (alternatingGroup (Fin 6))) ha' a6autRep_sq
    ha1' a6autRep_ne_one
  exact ⟨e.trans (MulAut.conj g), hg⟩

theorem A6_card_centralizer_involution {J : Type*} [Group J] [Finite J]
    (e : J ≃* alternatingGroup (Fin 6)) {a : J} (ha : a * a = 1) (ha1 : a ≠ 1) :
    Nat.card (centralizer ({a} : Set J)) = 8 := by
  obtain ⟨ψ, hψ⟩ := a6aut_exists_equiv_rep e ha ha1
  rw [a6aut_card_centralizer_congr ψ a, hψ, ← a6aut_card_cent_rep]
  exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun x => by
    simp [mem_centralizer_singleton_iff, eq_comm])

theorem a6aut_comm_of_sq_eq_one {G : Type*} [Group G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : (x * y) * (x * y) = 1) : x * y = y * x := by
  have h1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have h2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have h3 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right hxy
  calc x * y = (x * y)⁻¹ := h3.symm
    _ = y * x := by rw [mul_inv_rev, h1, h2]

theorem a6aut_perm_pow_four (g : Perm (Fin 6)) (h : g ^ 8 = 1) : g ^ 4 = 1 := by
  have hdvd : orderOf g ∣ 8 := orderOf_dvd_of_pow_eq_one h
  have hcycles : ∀ n ∈ g.cycleType, n ∣ 4 := by
    intro n hn
    have hbound : n ≤ 6 := (Multiset.le_sum_of_mem hn).trans (by simpa using g.sum_cycleType_le)
    have hn8 : n ∣ 8 := by
      have h1 := Multiset.dvd_lcm hn
      rw [g.lcm_cycleType] at h1
      exact h1.trans hdvd
    have hn2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    interval_cases n <;> omega
  have h4 : orderOf g ∣ 4 := by
    rw [← g.lcm_cycleType]
    exact Multiset.lcm_dvd.mpr hcycles
  exact orderOf_dvd_iff_pow_eq_one.1 h4

theorem a6aut_pow_four (x : alternatingGroup (Fin 6)) (h : x ^ 8 = 1) : x ^ 4 = 1 := by
  apply Subtype.ext
  exact a6aut_perm_pow_four x (by simpa using congrArg Subtype.val h)

theorem a6aut_conjNormal_injective {Y : Type*} [Group Y] (J : Subgroup Y) [J.Normal]
    (hC : centralizer (J : Set Y) = ⊥) :
    Function.Injective (MulAut.conjNormal (H := J) : Y →* MulAut J) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro y hy
  rw [MonoidHom.mem_ker] at hy
  have hmem : y ∈ centralizer (J : Set Y) := by
    rw [mem_centralizer_iff]
    intro j hj
    have h1 := congrArg (fun α : MulAut J => ((α ⟨j, hj⟩ : J) : Y)) hy
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    exact (mul_inv_eq_iff_eq_mul.1 h1).symm
  rw [hC] at hmem
  exact hmem

section OutSec

open CFSG.ComponentClassification.OuterAutomorphisms

theorem A6_out {Y : Type*} [Group Y] [Finite Y] (J : Subgroup Y) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 6)) (hC : centralizer (J : Set Y) = ⊥) :
    Nat.card (Y ⧸ J) ≤ 4 ∧ ∀ a b : Y, a * b * a⁻¹ * b⁻¹ ∈ J := by
  let θ : Y →* Outer A₆ :=
    (equivalence e).toMonoidHom.comp
      ((QuotientGroup.mk' (inner J)).comp (MulAut.conjNormal (H := J)))
  have hinj := a6aut_conjNormal_injective J hC
  have hker : ∀ y : Y, θ y = 1 ↔ y ∈ J := by
    intro y
    simp only [θ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨j, hj⟩
      have h1 : MulAut.conjNormal (H := J) (j : Y) = MulAut.conjNormal y := by
        rw [MulAut.conjNormal_val]
        exact hj
      rw [← hinj h1]
      exact j.2
    · intro hy
      exact ⟨⟨y, hy⟩, MulAut.conjNormal_val.symm⟩
  refine ⟨?_, fun a b => ?_⟩
  · have hkerJ : θ.ker = J := by
      ext y
      exact hker y
    have hle : Nat.card (Y ⧸ θ.ker) ≤ Nat.card (Outer A₆) :=
      Nat.card_le_card_of_injective _ (QuotientGroup.kerLift_injective θ)
    rw [Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkerJ).toEquiv] at hle
    exact hle.trans (CFSG.Sporadic.SchreierLemmas.outer_alternating_six).1
  · rw [← hker]
    have hcomm := isMulCommutative_iff.1
      (CFSG.Sporadic.SchreierLemmas.outer_alternating_six).2.1
    simp only [map_mul, map_inv]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm _ _

end OutSec

section OrderEight

open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix
  (inner_conjugation_injective)

theorem a6aut_card : Nat.card A₆ = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem a6aut_conj_conj {A : Type*} [Group A] (α : MulAut A) (a : A) :
    α * MulAut.conj a * α⁻¹ = MulAut.conj (α a) := by
  ext x
  simp [MulAut.conj_apply]

theorem a6aut_centralizer_trivial {α : MulAut A₆}
    (hα : α ∈ centralizer (((MulAut.conj : A₆ →* MulAut A₆).range : Subgroup _) : Set _)) :
    α = 1 := by
  refine MulEquiv.ext fun a => ?_
  have h1 : MulAut.conj a * α = α * MulAut.conj a :=
    mem_centralizer_iff.1 hα (MulAut.conj a) ⟨a, rfl⟩
  have h2 : MulAut.conj (α a) = MulAut.conj a := by
    rw [← a6aut_conj_conj, ← h1]
    simp
  rw [MulAut.one_apply]
  exact inner_conjugation_injective h2

theorem a6aut_order_eight_core {c : MulAut A₆} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hy : ∃ y : A₆, orderOf y = 5 ∧ c y = y) :
    ∃ σ : MulAut A₆, orderOf σ = 8 ∧
      σ ∈ Subgroup.closure (((MulAut.conj : A₆ →* MulAut A₆).range : Set (MulAut A₆)) ∪ {c}) := by
  obtain ⟨y, hy5, hcy⟩ := hy
  let J' : Subgroup (MulAut A₆) := (MulAut.conj : A₆ →* MulAut A₆).range
  haveI hJ'n : J'.Normal := inner_normal _
  let eJ : A₆ ≃* J' := MonoidHom.ofInjective inner_conjugation_injective
  have hJ360 : Nat.card J' = 360 := by
    rw [← Nat.card_congr eJ.toEquiv]
    exact a6aut_card
  have hPSL : IsPSLTwo J' 9 := isPSLTwo_nine_of_A6 eJ.symm
  have hCJ : centralizer (J' : Set (MulAut A₆)) = ⊥ := by
    rw [eq_bot_iff]
    intro α hα
    exact a6aut_centralizer_trivial hα
  have hcJ : c ∉ J' := by
    rintro ⟨b, hb⟩
    have hb2 : b * b = 1 := by
      apply inner_conjugation_injective
      rw [map_mul, hb, hc2, map_one]
    have hb1 : b ≠ 1 := by
      rintro rfl
      exact hc1 (by rw [← hb, map_one])
    have hyb : y ∈ centralizer ({b} : Set A₆) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : MulAut.conj b y = y := by rw [hb]; exact hcy
      rw [MulAut.conj_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.1 h1).symm
    have h8 := A6_card_centralizer_involution (MulEquiv.refl A₆) hb2 hb1
    have hdvd := orderOf_dvd_natCard (⟨y, hyb⟩ : ↥(centralizer ({b} : Set A₆)))
    rw [h8, ← Subgroup.orderOf_coe (⟨y, hyb⟩ : ↥(centralizer ({b} : Set A₆)))] at hdvd
    change orderOf y ∣ 8 at hdvd
    rw [hy5] at hdvd
    omega
  have hyc : MulAut.conj y ∈ J' ⊓ centralizer ({c} : Set (MulAut A₆)) := by
    refine ⟨⟨y, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := a6aut_conj_conj c y
    rw [hcy] at h1
    calc MulAut.conj y * c = c * MulAut.conj y * c⁻¹ * c := by rw [h1]
      _ = c * MulAut.conj y := by group
  have h5 : 5 ∣ Nat.card ↥(J' ⊓ centralizer ({c} : Set (MulAut A₆))) := by
    have hdvd := orderOf_dvd_natCard
      (⟨MulAut.conj y, hyc⟩ : ↥(J' ⊓ centralizer ({c} : Set (MulAut A₆))))
    rw [← Subgroup.orderOf_coe] at hdvd
    simpa [orderOf_injective _ inner_conjugation_injective, hy5] using hdvd
  have hpgl : PGLTwoSquareOuter J' c := by
    rcases sec622_outer_L2_nine hJ'n hCJ hPSL (t := c) (by rw [pow_two]; exact hc2) hcJ with
      ⟨_, h⟩ | h24
    · exact h
    · rw [h24] at h5
      omega
  obtain ⟨F, _, _, hF9, ⟨Φ⟩⟩ := pglP_iso J' hJ360 hc2 hcJ hpgl
  obtain ⟨x, hx⟩ := pglP_exists_orderOf_eight hF9
  refine ⟨((Φ.symm x : ↥(J' ⊔ Subgroup.zpowers c)) : MulAut A₆), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  · have hle : J' ⊔ Subgroup.zpowers c ≤ Subgroup.closure ((J' : Set (MulAut A₆)) ∪ {c}) := by
      refine sup_le (fun z hz => Subgroup.subset_closure (Or.inl hz)) ?_
      rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (Or.inr rfl)
    exact hle (Φ.symm x).2

theorem exists_aut_order_eight {J : Type*} [Group J] [Finite J]
    (e : J ≃* alternatingGroup (Fin 6)) {c : MulAut J} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hy : ∃ y : J, orderOf y = 5 ∧ c y = y) :
    ∃ σ : MulAut J, orderOf σ = 8 ∧
      σ ∈ Subgroup.closure (((MulAut.conj : J →* MulAut J).range : Set (MulAut J)) ∪ {c}) := by
  obtain ⟨y, hy5, hcy⟩ := hy
  obtain ⟨σ', h8, hmem⟩ := a6aut_order_eight_core (c := MulAut.congr e c)
    (by rw [← map_mul, hc2, map_one])
    (fun h => hc1 ((MulAut.congr e).injective (by rw [h, map_one])))
    ⟨e y, by rw [MulEquiv.orderOf_eq]; exact hy5, by simp [MulAut.congr_apply, hcy]⟩
  refine ⟨(MulAut.congr e).symm σ', by rw [MulEquiv.orderOf_eq]; exact h8, ?_⟩
  have hS : ((MulAut.conj : A₆ →* MulAut A₆).range : Set (MulAut A₆)) ∪ {MulAut.congr e c} ⊆
      (Subgroup.closure (((MulAut.conj : J →* MulAut J).range : Set (MulAut J)) ∪ {c})).map
        (MulAut.congr e).toMonoidHom := by
    rintro _ (⟨a, rfl⟩ | rfl)
    · obtain ⟨j, rfl⟩ := e.surjective a
      exact ⟨MulAut.conj j, Subgroup.subset_closure (Or.inl ⟨j, rfl⟩), congr_conj e j⟩
    · exact ⟨c, Subgroup.subset_closure (Or.inr rfl), rfl⟩
  obtain ⟨τ, hτ, hτσ⟩ := (Subgroup.closure_le _).2 hS hmem
  have : τ = (MulAut.congr e).symm σ' := by
    rw [← hτσ]
    exact ((MulAut.congr e).symm_apply_apply τ).symm
  rwa [← this]

end OrderEight

end CFSG.LocalAnalysis.EvenBN.Tits.I21L
