module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25Nu
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW1
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW2
public import CFSG.ClassicalInvolution.AschTight.S1911FusB
public import CFSG.ClassicalInvolution.AschTight.S1911FusD
public import CFSG.ClassicalInvolution.Asc77.AscSixModCent
public import CFSG.ClassicalInvolution.Asc77.AscC25V32
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutFrame
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerBlocks
public import CFSG.ClassicalInvolution.Q3.ClassicalFundamental
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911 CFSG.RankThreeCoreUniqueness
  CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

section Generic

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

theorem odd_natCard_ker_of_oddCoreOf {C : Subgroup G} {Φ : Type} [Group Φ] (ψ : ↥C →* Φ)
    (hker : ∀ x : ↥C, ψ x = 1 → (x : G) ∈ oddCoreOf K) : Odd (Nat.card ψ.ker) := by
  have hle : ψ.ker.map C.subtype ≤ oddCoreOf K := by
    rintro _ ⟨x, hx, rfl⟩
    exact hker x hx
  have hcard : Nat.card (ψ.ker.map C.subtype) = Nat.card ψ.ker :=
    (Nat.card_congr
      (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
  rw [← hcard]
  exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem nonempty_quotEquiv_of_surj_of_ker_le {C : Subgroup G} {Φ : Type} [Group Φ]
    (ψ : ↥C →* Φ) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥C, ψ x = 1 → (x : G) ∈ oddCoreOf K)
    (hΦ : classicalInvolutionOddCore Φ = ⊥) :
    Nonempty (↥C ⧸ classicalInvolutionOddCore ↥C ≃* Φ) :=
  nonempty_quotEquiv_of_surjective_of_odd ψ hψ (odd_natCard_ker_of_oddCoreOf ψ hker) hΦ

theorem nonempty_quotEquiv_perfectResidualOf_of_surj {C : Subgroup G} {Φ : Type} [Group Φ]
    [Group.IsPerfect Φ] (ψ : ↥C →* Φ) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥C, ψ x = 1 → (x : G) ∈ oddCoreOf K)
    (hΦ : classicalInvolutionOddCore Φ = ⊥) :
    Nonempty (↥(perfectResidualOf C) ⧸ classicalInvolutionOddCore ↥(perfectResidualOf C) ≃* Φ) := by
  let ψ' : ↥(perfectResidualOf C) →* Φ :=
    (ψ.comp (Helpers.perfectResidual ↥C).subtype).comp
      (Subgroup.equivMapOfInjective _ _ C.subtype_injective).symm.toMonoidHom
  have hcoe : ∀ x : ↥(perfectResidualOf C), ψ' x = ψ ⟨(x : G), perfectResidualOf_le C x.2⟩ := by
    intro x
    set y := (Subgroup.equivMapOfInjective _ _ C.subtype_injective).symm x with hy
    have hyx : (((y : ↥C)) : G) = x := by
      have h := congrArg Subtype.val (MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective _ _
        C.subtype_injective) x)
      rw [← hy] at h
      exact h
    change ψ ((Helpers.perfectResidual ↥C).subtype y) = _
    congr 1
    exact Subtype.ext hyx
  have hsurj : Function.Surjective ψ' := by
    have hmap := finite_perfectResidual_surjects_to_perfect_image ψ hψ
    intro b
    have hb : b ∈ (Helpers.perfectResidual ↥C).map ψ := by
      rw [hmap]
      trivial
    obtain ⟨y, hy, hyb⟩ := hb
    set E := Subgroup.equivMapOfInjective (Helpers.perfectResidual ↥C) C.subtype
      C.subtype_injective with hE
    refine ⟨E ⟨y, hy⟩, ?_⟩
    have e1 : ψ' (E ⟨y, hy⟩) = ψ y := by
      change ψ ((Helpers.perfectResidual ↥C).subtype (E.symm (E ⟨y, hy⟩))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    exact e1.trans hyb
  have hker' : ∀ x : ↥(perfectResidualOf C), ψ' x = 1 → (x : G) ∈ oddCoreOf K := by
    intro x hx
    rw [hcoe] at hx
    exact hker _ hx
  exact nonempty_quotEquiv_of_surjective_of_odd ψ' hsurj (odd_natCard_ker_of_oddCoreOf ψ' hker')
    hΦ

theorem mem_perfectResidualOf_of_surj {C : Subgroup G} {Φ : Type} [Group Φ] [Group.IsPerfect Φ]
    (ψ : ↥C →* Φ) (hψ : Function.Surjective ψ)
    (hker : ∀ x : ↥C, ψ x = 1 → (x : G) ∈ oddCoreOf K) {x : G} (hxC : x ∈ C)
    (hx2 : IsPGroup 2 (Subgroup.zpowers x)) : x ∈ perfectResidualOf C := by
  have hker' : ∀ n : ↥C, ψ n = 1 → Odd (orderOf n) := by
    intro n hn
    have h1 := hker n hn
    have h2 : orderOf (n : G) ∣ Nat.card ↥(oddCoreOf K) := Subgroup.orderOf_dvd_natCard _ h1
    rw [Subgroup.orderOf_coe] at h2
    exact Odd.of_dvd_nat (oddCoreOf_odd_natCard K) h2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := ↥(Subgroup.zpowers x))).mp hx2
  have hx2' : IsPGroup 2 (Subgroup.zpowers (⟨x, hxC⟩ : ↥C)) := by
    rw [IsPGroup.iff_card]
    refine ⟨k, ?_⟩
    have hoe : orderOf (⟨x, hxC⟩ : ↥C) = orderOf x := (Subgroup.orderOf_coe (⟨x, hxC⟩ : ↥C)).symm
    rw [Nat.card_zpowers, hoe]
    rw [Nat.card_zpowers] at hk
    exact hk
  have hres := C25V.mem_perfectResidual_of_isPGroup ψ hψ hker' hx2'
  exact Subgroup.mem_map.mpr ⟨_, hres, rfl⟩

end Generic

section Cover

variable {G : Type} [Group G] [Finite G] (K : Subgroup G) {b : G}
  (hb : b ∈ Subgroup.normalizer (K : Set G))

@[expose] noncomputable def a7FixHom : ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) →*
    ↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤) :=
  ((QuotientGroup.mk' (classicalInvolutionOddCore ↥K)).comp
    (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
    refine ⟨trivial, ?_⟩
    show oddQuotAut K (conjOn K b hb) (QuotientGroup.mk (Subgroup.inclusion inf_le_left c)) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_left c)
    rw [oddQuotAut_mk]
    congr 1
    apply Subtype.ext
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    show b * (c : G) * b⁻¹ = c
    rw [← hc]
    group

variable {K}

omit [Finite G] in
theorem a7FixHom_coe (c : ↥(K ⊓ Subgroup.centralizer ({b} : Set G))) :
    ((a7FixHom K hb c : ↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤)) : OddQuot K) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_left c) := rfl

omit [Finite G] in
theorem mem_oddCoreOf_of_a7FixHom_eq_one {c : ↥(K ⊓ Subgroup.centralizer ({b} : Set G))}
    (hc : a7FixHom K hb c = 1) : (c : G) ∈ oddCoreOf K := by
  have h1 : ((a7FixHom K hb c : ↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤)) : OddQuot K) = 1 :=
    congrArg Subtype.val hc
  rw [a7FixHom_coe] at h1
  rw [mem_oddCoreOf_iff]
  exact ⟨c.2.1, (QuotientGroup.eq_one_iff _).mp h1⟩

theorem a7FixHom_surjective (hb2 : b * b = 1) : Function.Surjective (a7FixHom K hb) := by
  rintro ⟨e, he⟩
  have he' : oddQuotAut K (conjOn K b hb) e = e := (mem_fixedIn.mp he).2
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective e
  have h1 : (QuotientGroup.mk (k⁻¹ * conjOn K b hb k) : OddQuot K) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : ((conjOn K b hb k : ↥K) : OddQuot K) = (k : OddQuot K) := he'
    rw [this, inv_mul_cancel]
  have h2 : (k : G)⁻¹ * (b * k * b⁻¹) ∈ oddCoreOf K := by
    rw [mem_oddCoreOf_iff]
    exact ⟨(k⁻¹ * conjOn K b hb k).2, (QuotientGroup.eq_one_iff _).mp h1⟩
  obtain ⟨o, ho, hko⟩ := exists_mul_mem_centralizer_of_odd (oddCoreOf_odd_natCard K) hb2
    (mem_normalizer_oddCore_of_mem_normalizer hb) h2
  have hoK : o ∈ K := oddCoreOf_le_self K ho
  have hoN : (⟨o, hoK⟩ : ↥K) ∈ classicalInvolutionOddCore ↥K := by
    obtain ⟨hK', h⟩ := mem_oddCoreOf_iff.mp ho
    exact h
  have hcb : (k : G) * o ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (k : G) * o * b = b * ((k : G) * o) * b⁻¹ * b := by rw [hko]
      _ = b * ((k : G) * o) := by group
  refine ⟨⟨(k : G) * o, (k * ⟨o, hoK⟩).2, hcb⟩, Subtype.ext ?_⟩
  show (QuotientGroup.mk (k * ⟨o, hoK⟩) : OddQuot K) = QuotientGroup.mk k
  rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (⟨o, hoK⟩ : ↥K)).mpr hoN, mul_one]

end Cover

section Weak

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {π : OddQuot K →* A7} {zE : OddQuot K}
  {b : G} (hb : b ∈ Subgroup.normalizer (K : Set G)) (cov : IsDoubleCoverA7 π zE)

include hb

omit [Finite G] in
theorem nuG_eq_autPerm : nuG cov b = cov.autPerm (oddQuotAut K (conjOn K b hb)) := by
  rw [nuG_of_mem cov hb]
  rfl

omit [Finite G] in
theorem a7_alpha_sq (hb2 : b * b = 1) :
    oddQuotAut K (conjOn K b hb) * oddQuotAut K (conjOn K b hb) = 1 :=
  oddQuotAut_mul_self K (conjOn_mul_self K hb hb2)

omit [Finite G] in
theorem a7_alpha_ne_one (hε : epsG cov b = -1) : oddQuotAut K (conjOn K b hb) ≠ 1 := by
  intro h
  have h1 : nuG cov b = 1 := by rw [nuG_eq_autPerm hb cov, h, map_one]
  rw [epsG, h1, map_one] at hε
  exact absurd hε (by decide)

omit [Finite G] in
theorem a7_nuG_sq (hb2 : b * b = 1) : nuG cov b * nuG cov b = 1 := by
  rw [nuG_eq_autPerm hb cov, ← map_mul, a7_alpha_sq hb hb2, map_one]

omit [Finite G] in
theorem a7_cycleType (hb2 : b * b = 1) (hε : epsG cov b = -1) :
    (nuG cov b).cycleType = {2} ∨ (nuG cov b).cycleType = {2, 2, 2} :=
  cycleType_of_odd_involution (a7_nuG_sq hb cov hb2) hε


theorem a7_fix_equiv_sl2_five [Fact (Nat.Prime 5)] (hb2 : b * b = 1) (hε : epsG cov b = -1)
    (hc : (nuG cov b).cycleType = {2}) :
    Nonempty (↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤) ≃* SL(2, GaloisField 5 1)) :=
  nonempty_fixedIn_equiv_sl2_five cov (oddQuotAut K (conjOn K b hb)) (a7_alpha_sq hb hb2)
    (a7_alpha_ne_one hb cov hε) (by rw [← nuG_eq_autPerm hb cov]; exact hc)

theorem a7_fix_equiv_sl2_three (hb2 : b * b = 1) (hε : epsG cov b = -1)
    (hc : (nuG cov b).cycleType = {2, 2, 2}) :
    Nonempty (↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤) ≃* SL(2, GaloisField 3 1)) :=
  nonempty_fixedIn_equiv_sl2_three cov (oddQuotAut K (conjOn K b hb)) (a7_alpha_sq hb hb2)
    (a7_alpha_ne_one hb cov hε) (by rw [← nuG_eq_autPerm hb cov]; exact hc)

theorem nonempty_centralizer_quotEquiv_sl2_three (hb2 : b * b = 1) (hε : epsG cov b = -1)
    (hc : (nuG cov b).cycleType = {2, 2, 2}) :
    Nonempty (↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ⧸
      classicalInvolutionOddCore ↥(K ⊓ Subgroup.centralizer ({b} : Set G)) ≃*
        SL(2, GaloisField 3 1)) := by
  obtain ⟨φ⟩ := a7_fix_equiv_sl2_three hb cov hb2 hε hc
  have hO : classicalInvolutionOddCore ↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤) = ⊥ := by
    have h3 : Nat.card (GaloisField 3 1) = 3 := by
      rw [GaloisField.card 3 1 (by norm_num)]
      norm_num
    obtain ⟨e'⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3
    exact CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_equiv (φ.trans e')
      CFSG.ClassicalInvolution.Q3.componentOddCore_sl2Three
  obtain ⟨ψ⟩ := nonempty_quotEquiv_of_surj_of_ker_le (a7FixHom K hb) (a7FixHom_surjective hb hb2)
    (fun x hx => mem_oddCoreOf_of_a7FixHom_eq_one hb hx) hO
  exact ⟨ψ.trans φ⟩

theorem a7_fix_isPerfect_five [Fact (Nat.Prime 5)] (hb2 : b * b = 1) (hε : epsG cov b = -1)
    (hc : (nuG cov b).cycleType = {2}) :
    Group.IsPerfect ↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤) := by
  obtain ⟨φ⟩ := a7_fix_equiv_sl2_five hb cov hb2 hε hc
  have hcard : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 (by norm_num)]
    norm_num
  have : Fintype (GaloisField 5 1) := Fintype.ofFinite _
  have h4 : ∃ s : Finset (GaloisField 5 1), s.card = 4 := by
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (GaloisField 5 1))) (n := 4)
      (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]; omega)
    exact ⟨s, hs⟩
  have : Group.IsPerfect SL(2, GaloisField 5 1) :=
    CFSG.LinearGroups.special_linear_isPerfect (K := GaloisField 5 1) (n := 2) le_rfl (Or.inr h4)
  exact Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective

theorem nonempty_perfectResidual_quotEquiv_sl2_five [Fact (Nat.Prime 5)] (hb2 : b * b = 1)
    (hε : epsG cov b = -1) (hc : (nuG cov b).cycleType = {2}) :
    Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G))) ≃*
        SL(2, GaloisField 5 1)) := by
  obtain ⟨φ⟩ := a7_fix_equiv_sl2_five hb cov hb2 hε hc
  have hperf := a7_fix_isPerfect_five hb cov hb2 hε hc
  have hcard : Nat.card (GaloisField 5 1) = 5 := by
    rw [GaloisField.card 5 1 (by norm_num)]
    norm_num
  have h2ne : (2 : GaloisField 5 1) ≠ 0 :=
    Ring.two_ne_zero (by rw [ringChar.eq (GaloisField 5 1) 5]; norm_num)
  have hO : classicalInvolutionOddCore ↥(fixedIn (oddQuotAut K (conjOn K b hb)) ⊤) = ⊥ :=
    CFSG.ClassicalInvolution.Q3.oddCore_eq_bot_of_equiv φ
      (CFSG.ClassicalInvolution.ModelFacts.LinearAut.oddCore_sl2_eq_bot h2ne (by rw [hcard]; omega))
  obtain ⟨ψ⟩ := nonempty_quotEquiv_perfectResidualOf_of_surj (a7FixHom K hb)
    (a7FixHom_surjective hb hb2) (fun x hx => mem_oddCoreOf_of_a7FixHom_eq_one hb hx) hO
  exact ⟨ψ.trans φ⟩

theorem mem_perfectResidualOf_of_isPGroup_five [Fact (Nat.Prime 5)] (hb2 : b * b = 1)
    (hε : epsG cov b = -1) (hc : (nuG cov b).cycleType = {2}) {x : G} (hxK : x ∈ K)
    (hxb : x ∈ Subgroup.centralizer ({b} : Set G)) (hx2 : IsPGroup 2 (Subgroup.zpowers x)) :
    x ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have := a7_fix_isPerfect_five hb cov hb2 hε hc
  exact mem_perfectResidualOf_of_surj (a7FixHom K hb) (a7FixHom_surjective hb hb2)
    (fun x hx => mem_oddCoreOf_of_a7FixHom_eq_one hb hx) ⟨hxK, hxb⟩ hx2

end Weak

end CFSG.ClassicalInvolution.Hat2A7
