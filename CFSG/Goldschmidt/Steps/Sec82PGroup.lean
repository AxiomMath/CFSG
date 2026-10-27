module

import CFSG.GroupTheory.SteinbergBKOddMetacyclicTorsion
import CFSG.LocalAnalysis.SectionRank.Ccomm.PGroupBasics
import CFSG.Goldschmidt.Steps.Sec82Tools
import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.Goldschmidt.Sec82

open Subgroup
open scoped IsMulCommutative commutatorElement

section Plane

variable {S : Type*} [Group S] [Finite S]

theorem exists_normal_plane_le_aux {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hS : IsPGroup p S)
    {A C : Subgroup S} (hAC : A ≤ C) (hAn : A.Normal)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAcyc : ¬ IsCyclic A) :
    ∃ D : Subgroup S, D ≤ C ∧ D.Normal ∧ Nat.card D = p ^ 2 ∧ (∀ x ∈ D, x ^ p = 1) ∧
      ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
  classical
  let D₀ : Subgroup S :=
    { carrier := {x | x ∈ A ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        rw [(Commute.mul_pow (hAcomm x hx.1 y hy.1) p), hx.2, hy.2, one_mul]⟩
      one_mem' := ⟨one_mem _, one_pow p⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩ }
  have hDA : D₀ ≤ A := fun x hx => hx.1
  have : Fact (IsPGroup p A) := ⟨hS.to_subgroup A⟩
  obtain ⟨S₀, -, hS₀card, hS₀el⟩ := CFSG.lemma_4_5_a (R := A) hp2 hAcyc
  have hS₀D : S₀.map A.subtype ≤ D₀ := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hS₀el.exponent_dvd_p ⟨x, hx⟩
    exact congrArg Subtype.val (congrArg Subtype.val h)
  have hcardD : p ^ 2 ≤ Nat.card D₀ := by
    have h := card_le_of_le hS₀D
    rwa [card_map_of_injective A.subtype_injective, hS₀card] at h
  have hDn : D₀.Normal := ⟨fun x hx g => ⟨hAn.conj_mem x hx.1 g, by
    rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩⟩
  have hD0 : D₀ ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcardD
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  have hpdvd := (CFSG.SectionRank.Ccomm.normal_inf_center_card hS hD0).1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(D₀ ⊓ center S)) p hpdvd
  have hyD : (y : S) ∈ D₀ := y.2.1
  have hyZ : (y : S) ∈ center S := y.2.2
  have hyord : orderOf (y : S) = p := by rw [Subgroup.orderOf_coe]; exact hy
  set U := zpowers (y : S) with hU
  have hUcard : Nat.card U = p := by rw [hU, Nat.card_zpowers, hyord]
  have hUn : U.Normal := normal_of_le_center (zpowers_le.2 hyZ)
  have hUD : U < D₀ := by
    refine lt_of_le_of_ne (zpowers_le.2 hyD) fun h => ?_
    rw [← h, hUcard] at hcardD
    have : p < p ^ 2 := by nlinarith [hp.out.one_lt]
    omega
  obtain ⟨b, hbD, -, -, B, hBn, hUB, hBD, -, hform, -⟩ :=
    CFSG.SectionRank.Ccomm.exists_central_extension hS hUD
  have hbp : b ^ p = 1 := hbD.2
  have hBle : B ≤ zpowers b ⊔ U := fun x hx => by
    obtain ⟨k, u, hu, rfl⟩ := hform x hx
    exact mul_mem (mem_sup_left (zpow_mem (mem_zpowers b) k)) (mem_sup_right hu)
  have hUN : zpowers b ≤ normalizer (U : Set S) := by
    rw [normalizer_eq_top_iff.mpr hUn]
    exact le_top
  have hcard1 : Nat.card B ≤ p ^ 2 := by
    have h3 : Nat.card (zpowers b) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.out.pos (orderOf_dvd_of_pow_eq_one hbp)
    calc Nat.card B ≤ Nat.card (zpowers b ⊔ U : Subgroup S) := card_le_of_le hBle
      _ ≤ Nat.card (zpowers b) * Nat.card U := card_sup_le_mul_of_le_normalizer hUN
      _ ≤ p * p := Nat.mul_le_mul h3 hUcard.le
      _ = p ^ 2 := (sq p).symm
  have hcard2 : p ^ 2 ≤ Nat.card B := by
    obtain ⟨j, hj⟩ := (hS.to_subgroup B).exists_card_eq
    have hlt : Nat.card U < Nat.card B := card_lt_of_lt hUB
    rw [hUcard, hj] at hlt
    have hj2 : 2 ≤ j := by
      have h1 : p ^ 1 < p ^ j := by rwa [pow_one]
      exact (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp h1
    rw [hj]
    exact Nat.pow_le_pow_right hp.out.pos hj2
  exact ⟨B, hBD.trans (hDA.trans hAC), hBn, le_antisymm hcard1 hcard2,
    fun x hx => (hBD hx).2, fun x hx z hz => hAcomm x (hDA (hBD hx)) z (hDA (hBD hz))⟩

theorem exists_normal_plane_le {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (hS : IsPGroup p S)
    (C : Subgroup S) [hCn : C.Normal] (hC : ¬ IsCyclic C) :
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
        · change g * x * g⁻¹ ∈ B
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
  · exact exists_normal_plane_le_aux hp2 hS hAC hAn hAcomm hAcyc

theorem plane_stability {p : ℕ} [hp : Fact p.Prime] (hS : IsPGroup p S) (V : Subgroup S)
    [hVn : V.Normal] (hVc : Nat.card V = p ^ 2) :
    (∀ x y : S, x * y * x⁻¹ * y⁻¹ ∈ centralizer (V : Set S)) ∧
      ∀ X : Subgroup S, X ⊓ centralizer (V : Set S) = ⊥ → Nat.card X ≤ p := by
  classical
  have hV0 : V ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hVc
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.out.one_lt
    omega
  by_cases hVZ : V ≤ center S
  ·
    have hall : ∀ g : S, g ∈ centralizer (V : Set S) := fun g =>
      mem_centralizer_iff.mpr fun v hv => (mem_center_iff.mp (hVZ hv) g).symm
    refine ⟨fun x y => hall _, fun X hX => ?_⟩
    have hXb : X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [← hX]
      exact ⟨hx, hall x⟩
    rw [hXb, card_bot]
    exact hp.out.one_lt.le
  set U := V ⊓ center S with hU
  have hple := (CFSG.SectionRank.Ccomm.normal_inf_center_card hS hV0).2
  have hUV : U < V := lt_of_le_of_ne inf_le_left fun h => hVZ (h ▸ inf_le_right)
  have hUcard : Nat.card U = p := by
    obtain ⟨j, hj⟩ := (hS.to_subgroup U).exists_card_eq
    have hlt : Nat.card U < Nat.card V := card_lt_of_lt hUV
    rw [hj, hVc] at hlt
    have hj2 : j < 2 := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp hlt
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [← hU, hj, pow_zero] at hple
      exact absurd hple (not_le.mpr hp.out.one_lt)
    rw [hj, show j = 1 by omega, pow_one]
  have hUn : U.Normal := normal_of_le_center inf_le_right
  obtain ⟨b, -, -, -, B, -, hUB, hBV, hbB, hform, hcomm⟩ :=
    CFSG.SectionRank.Ccomm.exists_central_extension hS hUV
  have hBeq : B = V := by
    refine Subgroup.eq_of_le_of_card_ge hBV ?_
    obtain ⟨j, hj⟩ := (hS.to_subgroup B).exists_card_eq
    have hlt : Nat.card U < Nat.card B := card_lt_of_lt hUB
    rw [hUcard, hj] at hlt
    have hj2 : 2 ≤ j := (Nat.pow_lt_pow_iff_right hp.out.one_lt).mp (by rwa [pow_one])
    rw [hVc, hj]
    exact Nat.pow_le_pow_right hp.out.pos hj2
  have hfU : ∀ g : S, g * b * g⁻¹ * b⁻¹ ∈ U := fun g => by
    have e : g * b * g⁻¹ * b⁻¹ = ⁅b, g⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact U.inv_mem (hcomm b hbB g)
  have hcen : ∀ g x : S, x * (g * b * g⁻¹ * b⁻¹) = (g * b * g⁻¹ * b⁻¹) * x := fun g x =>
    mem_center_iff.mp (hfU g).2 x
  let f : S →* S :=
    { toFun := fun g => g * b * g⁻¹ * b⁻¹
      map_one' := by group
      map_mul' := fun x y => by
        calc x * y * b * (x * y)⁻¹ * b⁻¹ = x * (y * b * y⁻¹ * b⁻¹) * b * x⁻¹ * b⁻¹ := by group
          _ = (y * b * y⁻¹ * b⁻¹) * x * b * x⁻¹ * b⁻¹ := by rw [hcen y x]
          _ = (y * b * y⁻¹ * b⁻¹) * (x * b * x⁻¹ * b⁻¹) := by group
          _ = (x * b * x⁻¹ * b⁻¹) * (y * b * y⁻¹ * b⁻¹) := (hcen y _).symm }
  have hf : ∀ g : S, f g = g * b * g⁻¹ * b⁻¹ := fun _ => rfl
  have hker : ∀ g : S, f g = 1 → g ∈ centralizer (V : Set S) := by
    intro g hg
    rw [hf] at hg
    have hgb : Commute g b := by
      calc g * b = g * b * g⁻¹ * b⁻¹ * (b * g) := by group
        _ = b * g := by rw [hg, one_mul]
    refine mem_centralizer_iff.mpr fun v hv => ?_
    rw [← hBeq] at hv
    obtain ⟨k, u, hu, rfl⟩ := hform v hv
    have hgu : g * u = u * g := mem_center_iff.mp hu.2 g
    have hgbk : g * b ^ k = b ^ k * g := (hgb.zpow_right k).eq
    calc b ^ k * u * g = b ^ k * (g * u) := by rw [mul_assoc, hgu]
      _ = (g * b ^ k) * u := by rw [← mul_assoc, hgbk]
      _ = g * (b ^ k * u) := by group
  refine ⟨fun x y => hker _ ?_, fun X hX => ?_⟩
  · have huw : f x * f y = f y * f x := by rw [hf x, hf y]; exact hcen y _
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, huw]
    group
  ·
    let ψ : X → U := fun x => ⟨f x, hfU x⟩
    have hψ : Function.Injective ψ := by
      intro x y hxy
      have h1 : f x = f y := congrArg Subtype.val hxy
      have h2 : f ((x : S)⁻¹ * y) = 1 := by rw [map_mul, map_inv, h1, inv_mul_cancel]
      have h3 : (x : S)⁻¹ * y ∈ X ⊓ centralizer (V : Set S) :=
        ⟨X.mul_mem (X.inv_mem x.2) y.2, hker _ h2⟩
      rw [hX, mem_bot] at h3
      exact Subtype.ext (inv_mul_eq_one.mp h3)
    calc Nat.card X ≤ Nat.card U := Nat.card_le_card_of_injective ψ hψ
      _ = p := hUcard

end Plane

section Ambient

variable {G : Type*} [Group G] [Finite G]

theorem exists_normal_plane_le_of_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T R : Subgroup G}
    (hT : IsPGroup p T) (hRT : R ≤ T) (hTR : T ≤ normalizer (R : Set G)) (hRc : ¬ IsCyclic R) :
    ∃ V : Subgroup G, V ≤ R ∧ T ≤ normalizer (V : Set G) ∧ Nat.card V = p ^ 2 ∧
      (∀ v ∈ V, v ^ p = 1) ∧ ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := by
  have : Fact p.Prime := ⟨hp⟩
  have hRn : (R.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hRT).mpr hTR
  have hRc' : ¬ IsCyclic (R.subgroupOf T) := fun h =>
    hRc (isCyclic_of_surjective (subgroupOfEquivOfLe hRT).toMonoidHom
      (subgroupOfEquivOfLe hRT).surjective)
  obtain ⟨D, hDR, hDn, hDc, hDp, hDab⟩ := exists_normal_plane_le hp2 hT (R.subgroupOf T) hRc'
  refine ⟨D.map T.subtype, ?_, fun t ht => ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    exact hDR hd
  · refine Sec82.mem_normalizer_of_conj_mem ?_
    rintro _ ⟨d, hd, rfl⟩
    exact ⟨⟨t, ht⟩ * d * ⟨t, ht⟩⁻¹, hDn.conj_mem d hd ⟨t, ht⟩, by simp⟩
  · rw [card_map_of_injective T.subtype_injective, hDc]
  · rintro _ ⟨d, hd, rfl⟩
    have h := hDp d hd
    exact congrArg Subtype.val h
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (hDab x hx y hy)

theorem plane_stability_of_le {p : ℕ} (hp : p.Prime) {T V : Subgroup G} (hT : IsPGroup p T)
    (hVT : V ≤ T) (hTV : T ≤ normalizer (V : Set G)) (hVc : Nat.card V = p ^ 2) :
    (∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ centralizer (V : Set G)) ∧
      ∀ X : Subgroup G, X ≤ T → X ⊓ centralizer (V : Set G) = ⊥ → Nat.card X ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hVn : (V.subgroupOf T).Normal := (normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hVc' : Nat.card (V.subgroupOf T) = p ^ 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVT).toEquiv, hVc]
  obtain ⟨h1, h2⟩ := plane_stability hT (V.subgroupOf T) hVc'
  have htr : ∀ z : T, z ∈ centralizer ((V.subgroupOf T : Subgroup T) : Set T) →
      (z : G) ∈ centralizer (V : Set G) := by
    intro z hz
    refine mem_centralizer_iff.mpr fun v hv => ?_
    have := mem_centralizer_iff.mp hz ⟨v, hVT hv⟩ hv
    exact congrArg Subtype.val this
  refine ⟨fun x hx y hy => htr _ (h1 ⟨x, hx⟩ ⟨y, hy⟩), fun X hXT hX => ?_⟩
  have hX' : X.subgroupOf T ⊓ centralizer ((V.subgroupOf T : Subgroup T) : Set T) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, hz2⟩
    have hz : (z : G) ∈ X ⊓ centralizer (V : Set G) := ⟨hz1, htr z hz2⟩
    rw [hX, mem_bot] at hz
    exact mem_bot.mpr (Subtype.ext hz)
  have h3 := h2 _ hX'
  rwa [Nat.card_congr (subgroupOfEquivOfLe hXT).toEquiv] at h3

omit [Finite G] in
theorem not_isCyclic_of_card_sq {p : ℕ} (hp : p.Prime) {V : Subgroup G}
    (hVc : Nat.card V = p ^ 2) (hVp : ∀ v ∈ V, v ^ p = 1) : ¬ IsCyclic V := by
  intro hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := V)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hVp g g.2))
  rw [hg, hVc] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

theorem not_isCyclic_of_two_le_pRank {p : ℕ} (hp : p.Prime) {R : Subgroup G}
    (h : 2 ≤ CFSG.Open.pRank p R) : ¬ IsCyclic R := by
  intro hcyc
  obtain ⟨E, hER, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt R
  have hEc' : IsCyclic E := by
    have : IsCyclic (E.subgroupOf R) := inferInstance
    exact isCyclic_of_surjective (subgroupOfEquivOfLe hER).toMonoidHom
      (subgroupOfEquivOfLe hER).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := E)
  have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hE.2 g g.2))
  rw [hg, hEc] at h1
  have h2 := Nat.le_of_dvd hp.pos h1
  have h3 : p ^ 2 ≤ p ^ CFSG.Open.pRank p R := Nat.pow_le_pow_right hp.pos h
  have h4 : p < p ^ 2 := by nlinarith [hp.one_lt]
  omega

theorem isCyclic_of_card_le {p : ℕ} (hp : p.Prime) {Q : Subgroup G} (hQ : IsPGroup p Q)
    (hc : Nat.card Q ≤ p) : IsCyclic Q := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    have : Subsingleton Q := (Nat.card_eq_one_iff_unique.mp hk).1
    exact isCyclic_of_subsingleton
  · have hk1 : k = 1 := by
      by_contra hk1
      have h1 : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
      have h2 : p < p ^ 2 := by nlinarith [hp.one_lt]
      omega
    rw [hk1, pow_one] at hk
    exact isCyclic_of_prime_card hk

omit [Finite G] in
theorem commutator_sup_le_of_le_centralizer {X Y : Subgroup G}
    (hXY : X ≤ centralizer (Y : Set G)) : ⁅X ⊔ Y, X ⊔ Y⁆ ≤ ⁅X, X⁆ ⊔ ⁅Y, Y⁆ := by
  have hc : ∀ x ∈ X, ∀ y ∈ Y, Commute x y := fun x hx y hy =>
    (mem_centralizer_iff.mp (hXY hx) y hy).symm
  have hdec : ∀ g ∈ X ⊔ Y, ∃ x ∈ X, ∃ y ∈ Y, x * y = g := fun g hg => by
    have hYX : Y ≤ normalizer (X : Set G) := fun y hy =>
      centralizer_le_normalizer X (mem_centralizer_iff.mpr fun x hx => (hc x hx y hy).eq)
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left X Y hYX] at hg
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hg
    exact ⟨x, hx, y, hy, rfl⟩
  rw [commutator_le]
  intro g₁ hg₁ g₂ hg₂
  obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := hdec g₁ hg₁
  obtain ⟨x₂, hx₂, y₂, hy₂, rfl⟩ := hdec g₂ hg₂
  have hw : y₁ * y₂ * y₁⁻¹ ∈ Y := Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)
  have hw' : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ Y := Y.mul_mem hw (Y.inv_mem hy₂)
  have e : ⁅x₁ * y₁, x₂ * y₂⁆ = ⁅x₁, x₂⁆ * ⁅y₁, y₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    calc x₁ * y₁ * (x₂ * y₂) * (x₁ * y₁)⁻¹ * (x₂ * y₂)⁻¹
        = x₁ * (y₁ * x₂) * y₂ * y₁⁻¹ * x₁⁻¹ * y₂⁻¹ * x₂⁻¹ := by group
      _ = x₁ * (x₂ * y₁) * y₂ * y₁⁻¹ * x₁⁻¹ * y₂⁻¹ * x₂⁻¹ := by rw [(hc x₂ hx₂ y₁ hy₁).eq]
      _ = x₁ * x₂ * ((y₁ * y₂ * y₁⁻¹) * x₁⁻¹) * y₂⁻¹ * x₂⁻¹ := by group
      _ = x₁ * x₂ * (x₁⁻¹ * (y₁ * y₂ * y₁⁻¹)) * y₂⁻¹ * x₂⁻¹ := by
          rw [(hc x₁⁻¹ (X.inv_mem hx₁) _ hw).eq]
      _ = x₁ * x₂ * x₁⁻¹ * ((y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * x₂⁻¹) := by group
      _ = x₁ * x₂ * x₁⁻¹ * (x₂⁻¹ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)) := by
          rw [(hc x₂⁻¹ (X.inv_mem hx₂) _ hw').eq]
      _ = x₁ * x₂ * x₁⁻¹ * x₂⁻¹ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group
  rw [e]
  exact mul_mem (mem_sup_left (commutator_mem_commutator hx₁ hx₂))
    (mem_sup_right (commutator_mem_commutator hy₁ hy₂))

end Ambient

end CFSG.Goldschmidt.Sec82
