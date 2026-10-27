module

import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
import CFSG.GH74.Uniqueness.SU.SU1Normal0
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.LocalAnalysis.GLTheoremB.TwoGroupTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.InnDiagThree
public import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.HardMathSupport.Solomon.LocalBalance
open scoped IsMulCommutative
open scoped commutatorElement
open CFSG.LocalAnalysis.GLTheoremB (quotAutHom quotAutHom_mk)

structure IsOmegaCentral {G : Type} [Group G] (P : Subgroup G) (z : G) : Prop where
  mem : z ∈ P
  central : ∀ y ∈ P, z * y = y * z
  order : orderOf z = 3
  unique : ∀ g ∈ P, (∀ y ∈ P, g * y = y * g) → g ^ 3 = 1 → g ∈ zpowers z

theorem normal_map_center_subtype {G : Type*} [Group G] (L : Subgroup G) [L.Normal] :
    ((center ↥L).map L.subtype).Normal := by
  constructor
  rintro _ ⟨c, hc, rfl⟩ g
  have hgL : g * (c : G) * g⁻¹ ∈ L := Subgroup.Normal.conj_mem inferInstance (c : G) c.2 g
  refine ⟨⟨g * (c : G) * g⁻¹, hgL⟩, Subgroup.mem_center_iff.mpr fun l => ?_, rfl⟩
  have hl : g⁻¹ * (l : G) * g ∈ L := by
    have := Subgroup.Normal.conj_mem inferInstance (l : G) l.2 g⁻¹
    simpa using this
  have hcc := Subgroup.mem_center_iff.mp hc ⟨g⁻¹ * (l : G) * g, hl⟩
  have hcc' : (c : G) * (g⁻¹ * (l : G) * g) = (g⁻¹ * (l : G) * g) * (c : G) :=
    congrArg Subtype.val hcc.symm
  apply Subtype.ext
  show (l : G) * (g * (c : G) * g⁻¹) = g * (c : G) * g⁻¹ * (l : G)
  calc (l : G) * (g * (c : G) * g⁻¹) = g * ((g⁻¹ * (l : G) * g) * (c : G)) * g⁻¹ := by group
    _ = g * ((c : G) * (g⁻¹ * (l : G) * g)) * g⁻¹ := by rw [hcc']
    _ = g * (c : G) * g⁻¹ * (l : G) := by group

theorem card_le_three_of_cyclic {W : Type*} [Group W] [Finite W] [IsCyclic W]
    (h3 : ∀ w : W, w ^ 3 = 1) : Nat.card W ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
  have hord : orderOf g = Nat.card W := orderOf_eq_card_of_forall_mem_zpowers hg
  have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (h3 g)
  rw [← hord]
  exact Nat.le_of_dvd (by norm_num) hdvd

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_normal_elementary_sq_of_not_isCyclic {S : Type} [Group S] [Finite S] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hS : IsPGroup p S) (C : Subgroup S) [hCn : C.Normal] (hC : ¬ IsCyclic C) :
    ∃ D : Subgroup S, D ≤ C ∧ D.Normal ∧ Nat.card D = p ^ 2 ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
  classical
  set 𝒜 : Set (Subgroup S) := {A | A ≤ C ∧ A.Normal ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x}
    with h𝒜
  have hbot : (⊥ : Subgroup S) ∈ 𝒜 :=
    ⟨bot_le, inferInstance, fun x hx y hy => by
      rw [mem_bot] at hx hy
      rw [hx, hy]⟩
  obtain ⟨A, hAmax⟩ := (Set.toFinite 𝒜).exists_maximal ⟨⊥, hbot⟩
  obtain ⟨hAC, hAn, hAcomm⟩ := hAmax.prop
  have hAX : A ≤ C ⊓ centralizer (A : Set S) :=
    le_inf hAC fun a ha => mem_centralizer_iff.mpr fun b hb => hAcomm b hb a ha
  have hCA : C ⊓ centralizer (A : Set S) ≤ A := by
    by_contra hle
    set X := C ⊓ centralizer (A : Set S) with hX
    have hXn : X.Normal := inferInstance
    set π := QuotientGroup.mk' A with hπ
    have hX'n : (X.map π).Normal := hXn.map π (QuotientGroup.mk'_surjective A)
    have hX'ne : X.map π ≠ ⊥ := by
      intro h
      apply hle
      intro x hx
      have hx' : π x ∈ X.map π := mem_map_of_mem π hx
      rw [h, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
      exact hx'
    obtain ⟨hdvd, -⟩ := CFSG.SectionRank.Ccomm.normal_inf_center_card (hS.to_quotient A) hX'ne
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X.map π ⊓ center (S ⧸ A))) p hdvd
    obtain ⟨hyX, hyZ⟩ := mem_inf.mp y.2
    obtain ⟨x, hxX, hxy⟩ := hyX
    have hxA : x ∉ A := by
      intro h
      have h1 : (y : S ⧸ A) = 1 := by
        rw [← hxy, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact h
      have h2 : y = 1 := Subtype.ext h1
      rw [h2, orderOf_one] at hy
      exact hp.out.one_lt.ne hy
    set B := A ⊔ zpowers x with hB
    have hxC : x ∈ C := (mem_inf.mp hxX).1
    have hxCA : x ∈ centralizer (A : Set S) := (mem_inf.mp hxX).2
    have hBC : B ≤ C := sup_le hAC (zpowers_le.mpr hxC)
    have hBc : B ≤ centralizer (B : Set S) := by
      have hxA' : zpowers x ≤ centralizer (A : Set S) := zpowers_le.mpr hxCA
      have h1 : A ≤ centralizer (B : Set S) := by
        rw [le_centralizer_iff]
        exact sup_le (le_inf_iff.mp hAX).2 hxA'
      have h2 : zpowers x ≤ centralizer (B : Set S) := by
        rw [le_centralizer_iff]
        refine sup_le ?_ ?_
        · rw [← le_centralizer_iff]
          exact hxA'
        · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
      exact sup_le h1 h2
    have hBn : B.Normal := by
      constructor
      intro b hb g
      have hle' : B ≤ B.comap (MulAut.conj g).toMonoidHom := by
        refine sup_le (fun a ha => ?_) (zpowers_le.mpr ?_)
        · exact mem_sup_left (hAn.conj_mem a ha g)
        ·
          change g * x * g⁻¹ ∈ B
          have hc : π (g * x * g⁻¹) = π x := by
            rw [map_mul, map_mul, map_inv, hxy, mem_center_iff.mp hyZ (π g), mul_inv_cancel_right]
          rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hc
          have hmem : (g * x * g⁻¹)⁻¹ * x ∈ A := hc
          have he : g * x * g⁻¹ = x * ((g * x * g⁻¹)⁻¹ * x)⁻¹ := by group
          rw [he]
          exact mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left (inv_mem hmem))
      exact hle' hb
    have hBA : B ≤ A := hAmax.2 ⟨hBC, hBn, fun u hu v hv => mem_centralizer_iff.mp (hBc hv) u hu⟩
      le_sup_left
    exact hxA (hBA (mem_sup_right (mem_zpowers x)))
  by_cases hAcyc : IsCyclic A
  ·
    let φ : C →* MulAut A := (MulAut.conjNormal : S →* MulAut A).comp C.subtype
    have hker : φ.ker = A.subgroupOf C := by
      ext c
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro h
        apply hCA
        refine mem_inf.mpr ⟨c.2, mem_centralizer_iff.mpr fun a ha => ?_⟩
        have h1 := congrArg (fun f : MulAut A => ((f ⟨a, ha⟩ : A) : S)) h
        change (c : S) * a * (c : S)⁻¹ = a at h1
        rw [mul_inv_eq_iff_eq_mul] at h1
        exact h1.symm
      · intro h
        refine MulEquiv.ext fun a => Subtype.ext ?_
        change (c : S) * a * (c : S)⁻¹ = a
        rw [hAcomm _ h _ a.2, mul_inv_cancel_right]
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp (hS.to_subgroup A)
    have hAut : IsCyclic (MulAut A) := by
      have h := ZMod.isCyclic_units_of_prime_pow p hp.out hp2 m
      rw [← hm] at h
      exact isCyclic_of_surjective (IsCyclic.mulAutMulEquiv A).symm.toMonoidHom
        (IsCyclic.mulAutMulEquiv A).symm.surjective
    have hquot : IsCyclic (C ⧸ A.subgroupOf C) := by
      have e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivRange φ)
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    have hAC' : IsCyclic (A.subgroupOf C) :=
      isCyclic_of_surjective (subgroupOfEquivOfLe hAC).symm.toMonoidHom
        (subgroupOfEquivOfLe hAC).symm.surjective
    obtain ⟨-, -, hT, -⟩ := CFSG.GroupTheory.SteinbergBK.odd_metacyclic_torsion_counts
      (hp.out.odd_of_ne_two hp2) (hS.to_subgroup C) (A.subgroupOf C) hAC' hquot
    obtain ⟨T, hTset, hTchar, hTel, hTcard, -⟩ := hT hC
    refine ⟨T.map C.subtype, map_subtype_le _, inferInstance, ?_, ?_, ?_⟩
    · rw [card_map_of_injective C.subtype_injective, hTcard]
    · rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ (T : Set C) := hx
      rw [hTset] at hx'
      exact congrArg Subtype.val hx'
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have := hTel.1
      exact congrArg Subtype.val (congrArg Subtype.val
        (mul_comm (⟨x, hx⟩ : T) ⟨y, hy⟩))
  ·
    let D : Subgroup S :=
      { carrier := {x | x ∈ A ∧ x ^ p = 1}
        mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
          rw [(Commute.mul_pow (hAcomm x hx.1 y hy.1) p), hx.2, hy.2, one_mul]⟩
        one_mem' := ⟨one_mem _, one_pow p⟩
        inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
    have hDA : D ≤ A := fun x hx => hx.1
    have hDn : D.Normal := ⟨fun x hx g => ⟨hAn.conj_mem x hx.1 g, by
      rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩
    have hDp : IsPGroup p D := fun x => ⟨1, Subtype.ext (by rw [pow_one]; exact x.2.2)⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hDp
    have : Fact (IsPGroup p A) := ⟨hS.to_subgroup A⟩
    obtain ⟨S₀, -, hS₀card, hS₀el⟩ := CFSG.lemma_4_5_a (R := A) hp2 hAcyc
    have hS₀D : S₀.map A.subtype ≤ D := by
      rintro _ ⟨x, hx, rfl⟩
      refine ⟨x.2, ?_⟩
      have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hS₀el.exponent_dvd_p ⟨x, hx⟩
      exact congrArg Subtype.val (congrArg Subtype.val h)
    have hk2 : 2 ≤ k := by
      have h := card_le_of_le hS₀D
      rw [card_map_of_injective A.subtype_injective, hS₀card, hk] at h
      exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h
    have hDel : CFSG.Open.IsElemAbelian p D :=
      ⟨⟨⟨fun x y => Subtype.ext (hAcomm x x.2.1 y y.2.1)⟩⟩, fun x hx => hx.2⟩
    have hcard : p ^ 2 ≤ Nat.card D := by
      rw [hk]
      exact Nat.pow_le_pow_right hp.out.pos hk2
    obtain ⟨E, hEn, hED, hEel, hEcard⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.exists_normal_Ep2 hp.out hS hDel hcard
    obtain ⟨hEcomm, hEexp⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mp hEel
    exact ⟨E, (hED.trans hDA).trans hAC, hEn, hEcard, hEexp, hEcomm⟩

theorem exists_normal_E9_of_type {S : Type} [Group S] [Finite S] (hS : IsPGroup 3 S)
    (C : Subgroup S) [C.Normal] (hC : ¬ IsCyclic C) :
    ∃ D : Subgroup S, D ≤ C ∧ D.Normal ∧ Nat.card D = 9 ∧ (∀ x ∈ D, x ^ 3 = 1) ∧
      ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨D, hDC, hDn, hDcard, hDexp, hDcomm⟩ :=
    exists_normal_elementary_sq_of_not_isCyclic (p := 3) (by norm_num) hS C hC
  exact ⟨D, hDC, hDn, hDcard.trans (by norm_num), hDexp, hDcomm⟩

theorem exists_normal_E9 {P N : Subgroup G} (hP : IsPGroup 3 P) (hNP : N ≤ P)
    (hnorm : P ≤ normalizer (N : Set G)) (hnc : ¬ IsCyclic N) :
    ∃ E : Subgroup G, E ≤ N ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      P ≤ normalizer (E : Set G) := by
  haveI hCn : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).2 hnorm
  have hC : ¬ IsCyclic (N.subgroupOf P) := fun h => by
    haveI := h
    exact hnc (isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hNP).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hNP).surjective)
  obtain ⟨D, hDC, hDn, hDcard, hDexp, hDcomm⟩ :=
    exists_normal_E9_of_type hP (N.subgroupOf P) hC
  refine ⟨D.map P.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hDC hd)
  · refine CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mpr ⟨?_, ?_⟩
    · rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
      exact congrArg Subtype.val (hDcomm d hd d' hd')
    · rintro _ ⟨d, hd, rfl⟩
      exact congrArg Subtype.val (hDexp d hd)
  · exact (Subgroup.card_map_of_injective P.subtype_injective).trans hDcard
  · intro g hg
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => ?_, fun hh => ?_⟩
    · obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hh
      exact Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : P) * d * (⟨g, hg⟩ : P)⁻¹, hDn.conj_mem d hd _, rfl⟩
    · obtain ⟨d, hd, hdh⟩ := Subgroup.mem_map.mp hh
      have hmem : (⟨g, hg⟩ : P)⁻¹ * d * ((⟨g, hg⟩ : P)⁻¹)⁻¹ ∈ D := hDn.conj_mem d hd _
      refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : P)⁻¹ * d * ((⟨g, hg⟩ : P)⁻¹)⁻¹, hmem, ?_⟩
      have h1 : (d : G) = g * h * g⁻¹ := hdh
      show g⁻¹ * (d : G) * g⁻¹⁻¹ = h
      rw [inv_inv, h1]
      group

end PGroups

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem IsOmegaCentral.mem_of_normal {P N : Subgroup G} {z : G} (hP : IsPGroup 3 P)
    (hz : IsOmegaCentral P z) (hNP : N ≤ P) (hnorm : P ≤ normalizer (N : Set G))
    (hN1 : N ≠ ⊥) : z ∈ N := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hP
  have hN' : (N.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hnorm
  have hN'1 : N.subgroupOf P ≠ ⊥ := by
    intro h
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hNP] at h
    exact hN1 h
  have hne : N.subgroupOf P ⊓ Subgroup.center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hN'1
  obtain ⟨y, hyN, hy1, hycomm⟩ : ∃ y : G, y ∈ N ∧ y ≠ 1 ∧ ∀ h ∈ P, h * y = y * h := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨haN, hac⟩ := Subgroup.mem_inf.mp a.2
    refine ⟨((a : ↥P) : G), Subgroup.mem_subgroupOf.mp haN,
      fun h => ha (Subtype.ext (Subtype.ext h)), fun h hh => ?_⟩
    have hcen := Subgroup.mem_center_iff.mp hac ⟨h, hh⟩
    exact congrArg Subtype.val hcen
  have hyP : y ∈ P := hNP hyN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨y, hyP⟩
  have hord : orderOf y = 3 ^ k := (Subgroup.orderOf_coe ⟨y, hyP⟩).trans hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hy1
    rw [← orderOf_eq_one_iff, hord, pow_zero]
  have h3 : 3 ∣ orderOf y := by
    rw [hord]
    exact dvd_pow_self 3 hk0
  have hord0 : orderOf y ≠ 0 := by
    rw [hord]
    exact pow_ne_zero _ (by norm_num)
  obtain ⟨g, hgN, hgP, hgord, hgc⟩ :
      ∃ g : G, g ∈ N ∧ g ∈ P ∧ orderOf g = 3 ∧ ∀ h ∈ P, g * h = h * g := by
    refine ⟨y ^ (orderOf y / 3), N.pow_mem hyN _, P.pow_mem hyP _,
      orderOf_pow_orderOf_div hord0 h3, ?_⟩
    intro h hh
    have hyh : Commute y h := (hycomm h hh).symm
    exact (hyh.pow_left (orderOf y / 3)).eq
  have hg3 : g ^ 3 = 1 := by
    rw [← hgord]
    exact pow_orderOf_eq_one g
  have hgz : g ∈ Subgroup.zpowers z := hz.unique g hgP hgc hg3
  have hle : Subgroup.zpowers g ≤ Subgroup.zpowers z := Subgroup.zpowers_le.mpr hgz
  have heq : Subgroup.zpowers g = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hgord, hz.order]))
  have hzg : z ∈ Subgroup.zpowers g := by
    rw [heq]
    exact Subgroup.mem_zpowers z
  exact (Subgroup.zpowers_le.mpr hgN) hzg

theorem pCore_le_sylow (P : Sylow 3 G) : CFSG.pCore 3 G ≤ (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pCore 3 G).Normal := CFSG.pCore_normal (p := 3) (G := G)
  exact IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 3) (G := G)) P

theorem le_center_of_normal_pGroup {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (N : Subgroup K) [N.Normal] (hN : IsPGroup 3 N) :
    N ≤ center K := by
  obtain ⟨hcomm, hsimple⟩ := hK
  haveI : Nontrivial (K ⧸ Subgroup.center K) := hsimple.toNontrivial
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set f : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective (Subgroup.center K)
  haveI hMn : (N.map f).Normal := Subgroup.Normal.map inferInstance f hfsurj
  rcases hsimple.eq_bot_or_eq_top_of_normal (N.map f) with hbot | htop
  ·
    intro n hn
    have hmem : f n ∈ N.map f := Subgroup.mem_map_of_mem f hn
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center K) n).mp hmem
  ·
    exfalso
    have hQ3 : IsPGroup 3 (K ⧸ Subgroup.center K) := by
      intro q
      have hq : q ∈ N.map f := by
        rw [htop]
        exact Subgroup.mem_top q
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hq
      obtain ⟨k, hk⟩ := hN ⟨n, hn⟩
      refine ⟨k, ?_⟩
      have hk' : n ^ 3 ^ k = 1 := congrArg Subtype.val hk
      rw [← map_pow, hk', map_one]
    have hcentQ : Subgroup.center (K ⧸ Subgroup.center K) = ⊤ :=
      (hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (K ⧸ Subgroup.center K))).resolve_left
        hQ3.bot_lt_center.ne'
    have hQcomm : ∀ a b : K ⧸ Subgroup.center K, a * b = b * a := by
      intro a b
      have ha : a ∈ Subgroup.center (K ⧸ Subgroup.center K) := by
        rw [hcentQ]
        exact Subgroup.mem_top a
      exact ((Subgroup.mem_center_iff.mp ha) b).symm
    have hcomm_le : commutator K ≤ Subgroup.center K := by
      show ⁅(⊤ : Subgroup K), ⊤⁆ ≤ Subgroup.center K
      rw [commutator_le]
      intro g _ h _
      have h1 : f ⁅g, h⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hQcomm (f g) (f h)
      exact (QuotientGroup.eq_one_iff (N := Subgroup.center K) ⁅g, h⁆).mp h1
    have htopK : ∀ k : K, k ∈ Subgroup.center K := by
      intro k
      apply hcomm_le
      rw [hcomm]
      exact Subgroup.mem_top k
    obtain ⟨q, hq⟩ := exists_ne (1 : K ⧸ Subgroup.center K)
    obtain ⟨k, rfl⟩ := hfsurj q
    exact hq ((QuotientGroup.eq_one_iff (N := Subgroup.center K) k).mpr (htopK k))

end PGroups

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem commute_of_inf_le_center {L O : Subgroup G} [L.Normal] [O.Normal]
    (hL : CFSG.Open.IsQuasisimple ↥L) (hLO : ∀ g ∈ L, g ∈ O → ∀ l ∈ L, l * g = g * l) :
    ∀ l ∈ L, ∀ o ∈ O, l * o = o * l := by
  intro l0 hl0 o ho
  have hcL : ∀ l ∈ L, l * o * l⁻¹ * o⁻¹ ∈ L := by
    intro l hl
    have h1 : o * l⁻¹ * o⁻¹ ∈ L := (‹L.Normal›).conj_mem _ (L.inv_mem hl) o
    have h2 : l * o * l⁻¹ * o⁻¹ = l * (o * l⁻¹ * o⁻¹) := by group
    rw [h2]
    exact L.mul_mem hl h1
  have hcO : ∀ l ∈ L, l * o * l⁻¹ * o⁻¹ ∈ O := by
    intro l hl
    have h1 : l * o * l⁻¹ ∈ O := (‹O.Normal›).conj_mem _ ho l
    exact O.mul_mem h1 (O.inv_mem ho)
  have key : ∀ a ∈ L, ∀ b ∈ L,
      (a * b) * o * (a * b)⁻¹ * o⁻¹ = (b * o * b⁻¹ * o⁻¹) * (a * o * a⁻¹ * o⁻¹) := by
    intro a ha b hb
    have hax : a * (b * o * b⁻¹ * o⁻¹) = (b * o * b⁻¹ * o⁻¹) * a :=
      hLO _ (hcL b hb) (hcO b hb) a ha
    calc (a * b) * o * (a * b)⁻¹ * o⁻¹ = a * (b * o * b⁻¹ * o⁻¹) * o * a⁻¹ * o⁻¹ := by group
      _ = (b * o * b⁻¹ * o⁻¹) * a * o * a⁻¹ * o⁻¹ := by rw [hax]
      _ = (b * o * b⁻¹ * o⁻¹) * (a * o * a⁻¹ * o⁻¹) := by group
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun l : ↥L => ⟨⟨(l : G) * o * (l : G)⁻¹ * o⁻¹, hcL l l.2⟩,
        Subgroup.mem_center_iff.2 fun g => Subtype.ext (hLO _ (hcL l l.2) (hcO l l.2) g g.2)⟩)
      (fun a b => by
        refine Subtype.ext (Subtype.ext ?_)
        exact (key (a : G) a.2 (b : G) b.2).trans
          (hLO _ (hcL (a : G) a.2) (hcO (a : G) a.2) _ (hcL (b : G) b.2)))
  have htop : (⊤ : Subgroup ↥L) ≤ f.ker := by
    rw [← hL.1]
    exact Abelianization.commutator_subset_ker f
  have h0 : (⟨l0, hl0⟩ : ↥L) ∈ f.ker := htop (Subgroup.mem_top _)
  have h1 : f ⟨l0, hl0⟩ = 1 := MonoidHom.mem_ker.1 h0
  have h2 : l0 * o * l0⁻¹ * o⁻¹ = 1 :=
    congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : G)) h1
  calc l0 * o = (l0 * o * l0⁻¹ * o⁻¹) * (o * l0) := by group
    _ = o * l0 := by rw [h2, one_mul]

theorem isElemAbelian_sup_card_27 {A B : Subgroup G} (hA : IsElemAbelian 3 A)
    (hB : IsElemAbelian 3 B) (hA9 : Nat.card A = 9) (hB9 : Nat.card B = 9)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hinf : Nat.card (A ⊓ B : Subgroup G) = 3) :
    IsElemAbelian 3 (A ⊔ B) ∧ Nat.card (A ⊔ B : Subgroup G) = 27 := by
  refine ⟨CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB, ?_⟩
  obtain ⟨h1, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB
  rw [hA9, hB9, hinf] at h1
  omega

end PGroups

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_centralizer_of_unipotent {x z : G} {V : Subgroup G}
    (hx : x ^ 3 = 1) (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) (hV : IsElemAbelian 3 V)
    (hV27 : Nat.card V = 27) (hzV : ∀ v ∈ V, z * v = v * z)
    (hxV : x ∈ normalizer (V : Set G)) (hcomm : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ zpowers z) :
    3 ≤ CFSG.Open.pRank 3 (centralizer ({x} : Set G)) := by
  clear hz1 hxV
  have hVcomm : ∀ a b : V, a * b = b * a := fun a b => hV.1.is_comm.comm a b
  have hVcommG : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw =>
    congrArg Subtype.val (hVcomm ⟨v, hv⟩ ⟨w, hw⟩)
  by_cases hxV' : x ∈ V
  ·
    have hVle : V ≤ centralizer ({x} : Set G) := by
      intro v hv
      exact mem_centralizer_singleton_iff.2 (hVcommG v hv x hxV')
    exact CFSG.SectionRank.le_pRank (by norm_num) hVle hV (k := 3) (hV27.trans (by norm_num))
  ·
    have hzc : ∀ c ∈ zpowers z, ∀ v ∈ V, v * c = c * v := by
      intro c hc v hv
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
      have hcv : Commute v z := (hzV v hv).symm
      exact (hcv.zpow_right k).eq
    obtain ⟨phi, hphi⟩ : ∃ phi : V →* ↥(zpowers z),
        ∀ v : V, ((phi v : ↥(zpowers z)) : G) = x * (v : G) * x⁻¹ * (v : G)⁻¹ := by
      refine ⟨MonoidHom.mk' (fun v : V =>
        (⟨x * (v : G) * x⁻¹ * (v : G)⁻¹, hcomm (v : G) v.2⟩ : ↥(zpowers z))) ?_, fun v => rfl⟩
      intro a b
      apply Subtype.ext
      change x * ((a : G) * (b : G)) * x⁻¹ * ((a : G) * (b : G))⁻¹
        = (x * (a : G) * x⁻¹ * (a : G)⁻¹) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)
      have hc : (a : G) * (x * (b : G) * x⁻¹ * (b : G)⁻¹)
          = (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G) :=
        hzc _ (hcomm (b : G) b.2) (a : G) a.2
      have key : x * ((a : G) * (b : G)) * x⁻¹ * ((a : G) * (b : G))⁻¹
          = (x * (a : G) * x⁻¹ * (a : G)⁻¹) *
            ((a : G) * (x * (b : G) * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹) := by
        group
      rw [key, hc]
      group
    have hrange : Nat.card phi.range ≤ 3 := by
      have h1 : Nat.card phi.range ≤ Nat.card (zpowers z) :=
        Subgroup.card_le_card_group phi.range
      have h2 : Nat.card (zpowers z) = orderOf z := Nat.card_zpowers z
      have h3 : orderOf z ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3)
      omega
    have hK : Nat.card phi.ker * Nat.card phi.range = 27 := by
      rw [Subgroup.card_ker_mul_card_range phi, hV27]
    have hK9 : 9 ≤ Nat.card phi.ker := by
      by_contra hlt
      have h8 : Nat.card phi.ker ≤ 8 := by omega
      have h24 := Nat.mul_le_mul h8 hrange
      omega
    obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = V ⊓ centralizer ({x} : Set G) := ⟨_, rfl⟩
    have hCV : C ≤ V := by
      rw [hC]
      exact inf_le_left
    have hCcent : ∀ c ∈ C, c * x = x * c := by
      intro c hc
      rw [hC] at hc
      exact mem_centralizer_singleton_iff.1 hc.2
    have hmemC : ∀ c ∈ V, c * x = x * c → c ∈ C := by
      intro c hc h
      rw [hC]
      exact ⟨hc, mem_centralizer_singleton_iff.2 h⟩
    have hKC : Nat.card phi.ker ≤ Nat.card C := by
      have hmap : Nat.card (phi.ker.map V.subtype) = Nat.card phi.ker :=
        Subgroup.card_map_of_injective V.subtype_injective
      rw [← hmap]
      apply Subgroup.card_le_of_le
      intro g hg
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hg
      refine hmemC (v : G) v.2 ?_
      have h0 := congrArg Subtype.val (MonoidHom.mem_ker.1 hv)
      rw [hphi v] at h0
      have h1 : x * (v : G) * x⁻¹ * (v : G)⁻¹ = 1 := h0
      have h2 : x * (v : G) * x⁻¹ = (v : G) := mul_inv_eq_one.1 h1
      calc (v : G) * x = (x * (v : G) * x⁻¹) * x := by rw [h2]
        _ = x * (v : G) := by group
    have hC9 : 9 ≤ Nat.card C := le_trans hK9 hKC
    have hdvd : Nat.card C ∣ 3 ^ 3 := by
      have h := Subgroup.card_dvd_of_le hCV
      rw [hV27] at h
      norm_num
      exact h
    obtain ⟨m, -, hCm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hm2 : 2 ≤ m := by
      by_contra hlt
      have hm1 : m ≤ 1 := by omega
      have h31 : Nat.card C ≤ 3 := by
        calc Nat.card C = 3 ^ m := hCm
          _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hm1
          _ = 3 := by norm_num
      omega
    have hxC : x ∉ C := fun h => hxV' (hCV h)
    have hcard : Nat.card ↥(C ⊔ zpowers x) = Nat.card C * 3 :=
      CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three C hx hxC hCcent
    have hCe : CFSG.IsElementaryAbelian 3 C :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 C).2 (hV.mono hCV)
    have hxe : CFSG.IsElementaryAbelian 3 (zpowers x) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx
    have hle : zpowers x ≤ centralizer (C : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun c hc => hCcent c hc
    have hY : CFSG.IsElementaryAbelian 3 ↥(C ⊔ zpowers x) :=
      CFSG.IsElementaryAbelian.sup_of_le_centralizer hle
    have hYel : CFSG.Open.IsElemAbelian 3 (C ⊔ zpowers x) :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 (C ⊔ zpowers x)).1 hY
    have hYle : C ⊔ zpowers x ≤ centralizer ({x} : Set G) := by
      refine sup_le ?_ ?_
      · intro c hc
        exact mem_centralizer_singleton_iff.2 (hCcent c hc)
      · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    have hYcard : Nat.card ↥(C ⊔ zpowers x) = 3 ^ (m + 1) := by
      rw [hcard, hCm, pow_succ]
    have hk := CFSG.SectionRank.le_pRank (by norm_num) hYle hYel hYcard
    omega

end PGroups

theorem centralizer_normal_of_normal {G : Type} [Group G] (L : Subgroup G) [L.Normal] :
    (centralizer (L : Set G)).Normal := by
  refine ⟨fun c hc g => ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have h := (inferInstance : L.Normal).conj_mem l hl g⁻¹
    rwa [inv_inv] at h
  have h := hc (g⁻¹ * l * g) hl'
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
    _ = g * c * g⁻¹ * l := by group

theorem card_sup_mul_card_inf_of_normal {X : Type} [Group X] (A B : Subgroup X) [A.Normal] :
    Nat.card (A ⊔ B : Subgroup X) * Nat.card (A ⊓ B : Subgroup X) = Nat.card A * Nat.card B := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := A ⊔ B)
  rw [Subgroup.relIndex_sup_left, inf_eq_left.mpr le_sup_left] at h1
  have h2 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [← h1, ← h2]
  ring

theorem exists_cover_subgroup {G : Type} [Group G] (E X Y : Subgroup G)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∃ S : Subgroup G, ∀ s, s ∈ S ↔ (s ∈ X ∧ ∃ y ∈ Y, s * y ∈ E) := by
  refine ⟨{ carrier := {s | s ∈ X ∧ ∃ y ∈ Y, s * y ∈ E}
            mul_mem' := ?_
            one_mem' := ?_
            inv_mem' := ?_ }, fun s => Iff.rfl⟩
  · intro a b ha hb
    obtain ⟨haX, c, hc, hac⟩ := ha
    obtain ⟨hbX, d, hd, hbd⟩ := hb
    refine ⟨X.mul_mem haX hbX, c * d, Y.mul_mem hc hd, ?_⟩
    have h : a * b * (c * d) = (a * c) * (b * d) := by
      calc a * b * (c * d) = a * (b * c) * d := by simp only [mul_assoc]
        _ = a * (c * b) * d := by rw [hXY b hbX c hc]
        _ = (a * c) * (b * d) := by simp only [mul_assoc]
    rw [h]
    exact E.mul_mem hac hbd
  · exact ⟨X.one_mem, 1, Y.one_mem, by rw [mul_one]; exact E.one_mem⟩
  · intro a ha
    obtain ⟨haX, c, hc, hac⟩ := ha
    refine ⟨X.inv_mem haX, c⁻¹, Y.inv_mem hc, ?_⟩
    have h : a⁻¹ * c⁻¹ = (a * c)⁻¹ := by
      rw [mul_inv_rev, hXY a⁻¹ (X.inv_mem haX) c⁻¹ (Y.inv_mem hc)]
    rw [h]
    exact E.inv_mem hac

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem exists_abelian_of_elemAbelian_cover {L E : Subgroup G} [L.Normal]
    (hLE : ∀ e ∈ E, ∃ l ∈ L, ∃ c ∈ centralizer (L : Set G), e = l * c)
    (hEC : Nat.card (E ⊓ centralizer (L : Set G) : Subgroup G) ≤ 3) (hE : Nat.card E = 27)
    (hEel : IsElemAbelian 3 E)
    (hZ : Nat.card (L ⊓ centralizer (L : Set G) : Subgroup G) = 3)
    (hC3 : ∀ B : Subgroup G, B ≤ centralizer (L : Set G) → IsPGroup 3 B →
      ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) :
    ∃ A : Subgroup G, A ≤ L ∧ IsPGroup 3 A ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
      27 ≤ Nat.card A := by
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup G, C = centralizer (L : Set G) := ⟨_, rfl⟩
  rw [← hCdef] at hLE hEC hZ hC3
  have hCnormal : C.Normal := by
    rw [hCdef]
    exact centralizer_normal_of_normal L
  have hCmem : ∀ c ∈ C, ∀ l ∈ L, l * c = c * l := by
    intro c hc l hl
    rw [hCdef] at hc
    exact Subgroup.mem_centralizer_iff.mp hc l hl
  have hEel' : IsMulCommutative E ∧ ∀ x ∈ E, x ^ 3 = 1 := hEel
  have hEexp : ∀ e ∈ E, e ^ 3 = 1 := hEel'.2
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    exact congrArg Subtype.val (hEel'.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
  have hZpow : ∀ z ∈ L ⊓ C, z ^ 3 = 1 := by
    intro z hz
    have h1 : (⟨z, hz⟩ : ↥(L ⊓ C)) ^ Nat.card ↥(L ⊓ C) = 1 := pow_card_eq_one'
    rw [hZ] at h1
    have h2 := congrArg Subtype.val h1
    simpa using h2
  have key9 : ∀ x ∈ L, ∀ y ∈ C, x * y ∈ E → x ^ 9 = 1 ∧ y ^ 9 = 1 := by
    intro x hx y hy hxy
    have h3 : (x * y) ^ 3 = 1 := hEexp _ hxy
    have hcomm : Commute x y := hCmem y hy x hx
    rw [hcomm.mul_pow] at h3
    have hx3eq : x ^ 3 = (y ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h3
    have hy3eq : y ^ 3 = (x ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h3
    have hx3L : x ^ 3 ∈ L := L.pow_mem hx 3
    have hy3L : y ^ 3 ∈ L := by
      rw [hy3eq]
      exact L.inv_mem hx3L
    have hx3C : x ^ 3 ∈ C := by
      rw [hx3eq]
      exact C.inv_mem (C.pow_mem hy 3)
    have hy3C : y ^ 3 ∈ C := C.pow_mem hy 3
    have hx9 : (x ^ 3) ^ 3 = 1 := hZpow _ (Subgroup.mem_inf.mpr ⟨hx3L, hx3C⟩)
    have hy9 : (y ^ 3) ^ 3 = 1 := hZpow _ (Subgroup.mem_inf.mpr ⟨hy3L, hy3C⟩)
    rw [← pow_mul] at hx9 hy9
    exact ⟨hx9, hy9⟩
  obtain ⟨A, hA⟩ := exists_cover_subgroup E L C (fun x hx y hy => hCmem y hy x hx)
  obtain ⟨B, hB⟩ := exists_cover_subgroup E C L (fun x hx y hy => (hCmem x hx y hy).symm)
  have hAL : ∀ a ∈ A, a ∈ L := fun a ha => ((hA a).mp ha).1
  have hAC : ∀ a ∈ A, ∃ c ∈ C, a * c ∈ E := fun a ha => ((hA a).mp ha).2
  have hBC : B ≤ C := by
    intro c hc
    exact ((hB c).mp hc).1
  have hBL : ∀ c ∈ B, ∃ l ∈ L, l * c ∈ E := by
    intro c hc
    obtain ⟨hcC, l, hl, hcl⟩ := (hB c).mp hc
    refine ⟨l, hl, ?_⟩
    rw [hCmem c hcC l hl]
    exact hcl
  have hAp : IsPGroup 3 A := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    obtain ⟨c, hc, hgc⟩ := hAC (g : G) g.2
    have h9 := (key9 (g : G) (hAL (g : G) g.2) c hc hgc).1
    simpa using h9
  have hBp : IsPGroup 3 B := by
    intro g
    refine ⟨2, ?_⟩
    apply Subtype.ext
    obtain ⟨l, hl, hgl⟩ := hBL (g : G) g.2
    have h9 := (key9 l hl (g : G) ((hB (g : G)).mp g.2).1 hgl).2
    simpa using h9
  have hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a₁ ha₁ a₂ ha₂
    obtain ⟨c₁, hc₁, h₁⟩ := hAC a₁ ha₁
    obtain ⟨c₂, hc₂, h₂⟩ := hAC a₂ ha₂
    have hc₁B : c₁ ∈ B := by
      refine (hB c₁).mpr ⟨hc₁, a₁, hAL a₁ ha₁, ?_⟩
      rw [← hCmem c₁ hc₁ a₁ (hAL a₁ ha₁)]
      exact h₁
    have hc₂B : c₂ ∈ B := by
      refine (hB c₂).mpr ⟨hc₂, a₂, hAL a₂ ha₂, ?_⟩
      rw [← hCmem c₂ hc₂ a₂ (hAL a₂ ha₂)]
      exact h₂
    have hcc : c₁ * c₂ = c₂ * c₁ := hC3 B hBC hBp c₁ hc₁B c₂ hc₂B
    have e1 : (a₁ * c₁) * (a₂ * c₂) = (a₂ * c₂) * (a₁ * c₁) := hEcomm _ h₁ _ h₂
    have ec1 : c₁ * a₂ = a₂ * c₁ := (hCmem c₁ hc₁ a₂ (hAL a₂ ha₂)).symm
    have ec2 : c₂ * a₁ = a₁ * c₂ := (hCmem c₂ hc₂ a₁ (hAL a₁ ha₁)).symm
    have eq1 : (a₁ * c₁) * (a₂ * c₂) = (a₁ * a₂) * (c₁ * c₂) := by
      calc (a₁ * c₁) * (a₂ * c₂) = a₁ * (c₁ * a₂) * c₂ := by simp only [mul_assoc]
        _ = a₁ * (a₂ * c₁) * c₂ := by rw [ec1]
        _ = (a₁ * a₂) * (c₁ * c₂) := by simp only [mul_assoc]
    have eq2 : (a₂ * c₂) * (a₁ * c₁) = (a₂ * a₁) * (c₂ * c₁) := by
      calc (a₂ * c₂) * (a₁ * c₁) = a₂ * (c₂ * a₁) * c₁ := by simp only [mul_assoc]
        _ = a₂ * (a₁ * c₂) * c₁ := by rw [ec2]
        _ = (a₂ * a₁) * (c₂ * c₁) := by simp only [mul_assoc]
    rw [eq1, eq2, hcc] at e1
    exact mul_right_cancel e1
  have hsubAC : L ⊓ C ≤ A ⊓ C := by
    intro z hz
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨(hA z).mpr ⟨hzL, z⁻¹, C.inv_mem hzC, ?_⟩, hzC⟩
    rw [mul_inv_cancel]
    exact E.one_mem
  have hcardZ : 3 ≤ Nat.card ↥(A ⊓ C) := by
    have h := Subgroup.card_le_of_le hsubAC
    rw [hZ] at h
    exact h
  have hEAC : E ⊔ C ≤ A ⊔ C := by
    refine sup_le ?_ le_sup_right
    intro e he
    obtain ⟨l, hl, c, hc, rfl⟩ := hLE _ he
    have hlA : l ∈ A := (hA l).mpr ⟨hl, c, hc, he⟩
    exact (A ⊔ C).mul_mem ((le_sup_left : A ≤ A ⊔ C) hlA) ((le_sup_right : C ≤ A ⊔ C) hc)
  have hcardEAC : Nat.card ↥(E ⊔ C) ≤ Nat.card ↥(A ⊔ C) := Subgroup.card_le_of_le hEAC
  have hprodA : Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) = Nat.card ↥C * Nat.card ↥A := by
    have h := card_sup_mul_card_inf_of_normal C A
    rw [sup_comm, inf_comm] at h
    exact h
  have hprodE : Nat.card ↥(E ⊔ C) * Nat.card ↥(E ⊓ C) = Nat.card ↥C * 27 := by
    have h := card_sup_mul_card_inf_of_normal C E
    rw [sup_comm, inf_comm, hE] at h
    exact h
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have step1 : Nat.card ↥(E ⊔ C) * Nat.card ↥(E ⊓ C) ≤ Nat.card ↥(A ⊔ C) * 3 :=
    Nat.mul_le_mul hcardEAC hEC
  have step2 : 27 * Nat.card ↥C ≤ Nat.card ↥(A ⊔ C) * 3 := by
    linarith
  have step3 : 9 * Nat.card ↥C ≤ Nat.card ↥(A ⊔ C) := by
    omega
  have step4 : 9 * Nat.card ↥C * 3 ≤ Nat.card ↥(A ⊔ C) * Nat.card ↥(A ⊓ C) :=
    Nat.mul_le_mul step3 hcardZ
  have step5 : 27 * Nat.card ↥C ≤ Nat.card ↥A * Nat.card ↥C := by
    linarith
  have h27 : 27 ≤ Nat.card ↥A := Nat.le_of_mul_le_mul_right step5 hCpos
  exact ⟨A, fun a ha => hAL a ha, hAp, hAab, h27⟩

end PGroups

section PGroups

variable {G : Type} [Group G] [Finite G]

theorem IsOmegaCentral.commutator_mem {P E : Subgroup G} {z : G} (hP : IsPGroup 3 P)
    (hz : IsOmegaCentral P z) (hEP : E ≤ P) (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (hzE : z ∈ E) (hnorm : P ≤ normalizer (E : Set G)) :
    ∀ g ∈ P, ∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ zpowers z := by
  intro g hg e he
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  let _ : CommGroup E := { (inferInstance : Group E) with mul_comm := hcomm }
  let N : Subgroup E := (zpowers z).subgroupOf E
  haveI hNn : N.Normal := Subgroup.normal_of_comm N
  let ρ : ↥P →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  have hρapp : ∀ (γ : ↥P) (a : ↥E), ((ρ γ a : E) : G) = (γ : G) * (a : G) * (γ : G)⁻¹ :=
    fun _ _ => rfl
  have hzfix : ∀ (γ : ↥P), (γ : G) * z * (γ : G)⁻¹ = z := by
    intro γ
    have h := hz.central γ γ.2
    rw [mul_inv_eq_iff_eq_mul]
    exact h.symm
  have hfix : ∀ (γ : ↥P) (n : E), n ∈ N → ρ γ n = n := by
    intro γ n hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hn)
    apply Subtype.ext
    rw [hρapp, ← hk, ← conj_zpow, hzfix γ]
  have hρN : ∀ γ : ↥P, N.map (ρ γ).toMonoidHom = N := by
    intro γ
    ext m
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      have := hfix γ n hn
      change ρ γ n ∈ N
      rw [this]
      exact hn
    · intro hm
      exact ⟨m, hm, hfix γ m hm⟩
  let ρ' : ↥P →* MulAut (↥E ⧸ N) := quotAutHom N ρ hρN
  have hNcard : Nat.card N = 3 := by
    have h1 : Nat.card N = Nat.card (zpowers z) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (zpowers_le.2 hzE)).toEquiv
    rw [h1, Nat.card_zpowers, hz.order]
  have hQcard : Nat.card (↥E ⧸ N) = 3 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hE9, hNcard] at h
    omega
  haveI : IsCyclic (↥E ⧸ N) := isCyclic_of_prime_card (p := 3) hQcard
  have hAut : Nat.card (MulAut (↥E ⧸ N)) = 2 := by
    rw [IsCyclic.card_mulAut, hQcard, Nat.totient_prime Nat.prime_three]
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨g, hg⟩
  have hdvd3 : orderOf (ρ' ⟨g, hg⟩) ∣ 3 ^ a := by
    rw [← ha]
    exact orderOf_map_dvd ρ' _
  have hdvd2 : orderOf (ρ' ⟨g, hg⟩) ∣ 2 := by
    rw [← hAut]
    exact orderOf_dvd_natCard _
  have hone : orderOf (ρ' ⟨g, hg⟩) = 1 := by
    have hcop : Nat.Coprime (3 ^ a) 2 := Nat.Coprime.pow_left a (by norm_num)
    exact Nat.eq_one_of_dvd_coprimes hcop hdvd3 hdvd2
  have htriv : ρ' ⟨g, hg⟩ = 1 := orderOf_eq_one_iff.mp hone
  have hmk := quotAutHom_mk N ρ hρN ⟨g, hg⟩ ⟨e, he⟩
  rw [htriv, MulAut.one_apply] at hmk
  have hmem : (⟨e, he⟩ : E)⁻¹ * ρ ⟨g, hg⟩ ⟨e, he⟩ ∈ N := QuotientGroup.eq.mp hmk
  have hmem' := Subgroup.mem_subgroupOf.mp hmem
  have hge : g * e * g⁻¹ ∈ E := by
    have := (ρ ⟨g, hg⟩ ⟨e, he⟩).2
    rwa [hρapp] at this
  have hcomm' : (g * e * g⁻¹) * e⁻¹ = e⁻¹ * (g * e * g⁻¹) := by
    have := hcomm ⟨g * e * g⁻¹, hge⟩ ⟨e⁻¹, E.inv_mem he⟩
    exact congrArg Subtype.val this
  rw [hcomm']
  simpa [hρapp] using hmem'

end PGroups

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29
