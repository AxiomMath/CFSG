module

public import CFSG.LocalAnalysis.OddStandard.AltStdWeakTop
public import CFSG.LocalAnalysis.OddStandard.AltStdSecTwoRoot

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Quot

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem weakShape_quotient_central {x t : H} [(zpowers x).Normal]
    (hxc : x ∈ Subgroup.center H) (hx2 : x * x = 1) (ht : orderOf t = 2) (htx : t ∉ zpowers x)
    {B : Subgroup H} {m : ℕ} (hm : 5 ≤ m) (eB : B ≃* alternatingGroup (Fin m))
    (hBt : B ≤ centralizer ({t} : Set H))
    (hfus : ∀ y : H, (y * t * y⁻¹)⁻¹ * t ∈ zpowers x → y * t * y⁻¹ = t)
    (hnorm : centralizer ({t} : Set H) ≤ normalizer (B : Set H))
    (hcc : ∀ c ∈ centralizer (B : Set H) ⊓ centralizer ({t} : Set H), ∀ k : ℕ, c ^ 2 ^ k = 1 →
      c ∈ zpowers t ⊔ zpowers x) :
    WeakShape (QuotientGroup.mk t : H ⧸ zpowers x) (B.map (QuotientGroup.mk' (zpowers x))) m := by
  classical
  set P := zpowers x with hPdef
  have hPc : P ≤ Subgroup.center H := zpowers_le.2 hxc
  have hBP : B ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hbB, hbP⟩
    have hbc : (⟨b, hbB⟩ : B) ∈ Subgroup.center B := by
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      exact Subgroup.mem_center_iff.1 (hPc hbP) c
    rw [center_eq_bot_of_alt (by omega) eB, Subgroup.mem_bot] at hbc
    exact congrArg Subtype.val hbc
  have hinj : Function.Injective ((QuotientGroup.mk' P).domRestrict B) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    have hb1 : (QuotientGroup.mk' P) (b : H) = 1 := hb
    have : (b : H) ∈ B ⊓ P := ⟨b.2, (QuotientGroup.eq_one_iff _).1 hb1⟩
    rw [hBP] at this
    exact Subtype.ext this
  have hconj : ∀ c ∈ normalizer (B : Set H), ∀ y : H ⧸ P,
      y ∈ B.map (QuotientGroup.mk' P) ↔
        (c : H ⧸ P) * y * (c : H ⧸ P)⁻¹ ∈ B.map (QuotientGroup.mk' P) := by
    intro c hc y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    constructor
    · rintro ⟨b, hb, hby⟩
      refine ⟨c * b * c⁻¹, (mem_normalizer_iff.1 hc b).1 hb, ?_⟩
      rw [← hby]
      simp
    · rintro ⟨b, hb, hby⟩
      refine ⟨c⁻¹ * b * c, ?_, ?_⟩
      · have := (mem_normalizer_iff.1 (inv_mem hc) b).1 hb
        simpa using this
      · have h1 : (b : H ⧸ P) = (c : H ⧸ P) * y * (c : H ⧸ P)⁻¹ := hby
        have : ((c⁻¹ * b * c : H) : H ⧸ P) = (c : H ⧸ P)⁻¹ * b * (c : H ⧸ P) := by simp
        simp only [QuotientGroup.mk'_apply, this, h1]
        group
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply orderOf_eq_prime
    · have h2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
      rw [← QuotientGroup.mk_pow, h2]
      rfl
    · intro h1
      exact htx ((QuotientGroup.eq_one_iff t).1 h1)
  · exact ⟨(ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective
      (QuotientGroup.mk' P) B hinj).symm.trans eB⟩
  · rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hBt hb)
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]
  · intro y hy
    obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage_central hfus hy
    rw [mem_normalizer_iff]
    exact hconj c (hnorm hc)
  · rintro y ⟨hyB, hyt⟩ k hyk
    obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage_central hfus hyt
    have hcN : c ∈ normalizer (B : Set H) := hnorm hc
    have hcB : c ∈ centralizer (B : Set H) := by
      rw [mem_centralizer_iff]
      intro b hb
      have hcomm : (b : H ⧸ P) * (c : H ⧸ P) = (c : H ⧸ P) * (b : H ⧸ P) :=
        mem_centralizer_iff.1 hyB (b : H ⧸ P) ⟨b, hb, rfl⟩
      have h1 : c * b * c⁻¹ * b⁻¹ ∈ B :=
        mul_mem ((mem_normalizer_iff.1 hcN b).1 hb) (inv_mem hb)
      have h2 : c * b * c⁻¹ * b⁻¹ ∈ P := by
        rw [← QuotientGroup.eq_one_iff]
        have : ((c * b * c⁻¹ * b⁻¹ : H) : H ⧸ P) =
            (c : H ⧸ P) * b * (c : H ⧸ P)⁻¹ * (b : H ⧸ P)⁻¹ := by simp
        rw [this, ← hcomm]
        group
      have h3 : c * b * c⁻¹ * b⁻¹ ∈ B ⊓ P := ⟨h1, h2⟩
      rw [hBP] at h3
      have h4 : c * b * c⁻¹ * b⁻¹ = 1 := h3
      calc b * c = (c * b * c⁻¹ * b⁻¹)⁻¹ * (c * b) := by group
        _ = c * b := by rw [h4]; group
    have hck : c ^ 2 ^ (k + 1) = 1 := by
      have h1 : c ^ 2 ^ k ∈ P :=
        (QuotientGroup.eq_one_iff _).1 (by rw [QuotientGroup.mk_pow]; exact hyk)
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
      calc c ^ 2 ^ (k + 1) = (c ^ 2 ^ k) * (c ^ 2 ^ k) := by rw [pow_succ, pow_mul, sq]
        _ = x ^ j * x ^ j := by rw [hj]
        _ = 1 := by
          rcases lookup_zpow_eq_one_or_self hx2 j with h2 | h2
          · rw [h2, one_mul]
          · rw [h2, hx2]
    have hmem := hcc c ⟨hcB, hc⟩ (k + 1) hck
    have := Subgroup.mem_map_of_mem (QuotientGroup.mk' P) hmem
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq]
      at this

end Quot

section Rho

variable {G : Type} [Group G] {L : Subgroup G} {n : ℕ} (e : L ≃* alternatingGroup (Fin n))
  (hn : 8 ≤ n)

theorem comm_of_mem_corr_of_rho_fix {x : G} (hxN : x ∈ normalizer (L : Set G))
    {F : Finset (Fin n)} (hF : ∀ i ∈ F, rho e hn ⟨x, hxN⟩ i = i) {w : G}
    (hw : w ∈ corr (X := G) e (altSub F)) : x * w = w * x := by
  obtain ⟨hwL, hwT⟩ := mem_corr.1 hw
  have hxw : x * w * x⁻¹ ∈ L := (mem_normalizer_iff.1 hxN w).1 hwL
  have h1 := rho_conj_apply e hn hxN ⟨w, hwL⟩ ⟨x * w * x⁻¹, hxw⟩ rfl
  have hfix : rho e hn ⟨x, hxN⟩ ∈ fixSub F := hF
  have h2 := comm_altSub_fixSub hwT hfix
  have h3 : (e ⟨x * w * x⁻¹, hxw⟩ : alternatingGroup (Fin n)) = e ⟨w, hwL⟩ := by
    apply Subtype.ext
    rw [← h1, ← h2]
    simp
  have h4 := e.injective h3
  have h5 : x * w * x⁻¹ = w := congrArg Subtype.val h4
  calc x * w = (x * w * x⁻¹) * x := by group
    _ = w * x := by rw [h5]

theorem mem_normalizer_corr_fixFin_of_rho {a y : G} (haN : a ∈ normalizer (L : Set G))
    (hyN : y ∈ normalizer (L : Set G)) (hay : y * a = a * y) :
    y ∈ normalizer (corr (X := G) e (altSub (fixFin (rho e hn ⟨a, haN⟩))) : Set G) := by
  refine mem_normalizer_corr e hn hyN (mem_normalizer_altSub fun i => ?_)
  have hcomm : rho e hn ⟨y, hyN⟩ * rho e hn ⟨a, haN⟩ = rho e hn ⟨a, haN⟩ * rho e hn ⟨y, hyN⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hay
  have h2 := congrArg (fun f : Perm (Fin n) => f i) hcomm
  simp only [Perm.mul_apply] at h2
  rw [mem_fixFin, mem_fixFin]
  constructor
  · intro hi
    rw [← h2, hi]
  · intro hi
    have h3 : rho e hn ⟨y, hyN⟩ (rho e hn ⟨a, haN⟩ i) = rho e hn ⟨y, hyN⟩ i := by rw [h2, hi]
    exact (rho e hn ⟨y, hyN⟩).injective h3

end Rho

section TwoSecWeak

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

theorem weakShape_twoSec (hstd : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 8 ≤ n) {Q : Subgroup G} (d : Cyc L Q z)
    (hQ2 : Nat.card Q = 2) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hxN : x ∈ normalizer (L : Set G)) (hτ : (rho e hn ⟨x, hxN⟩).IsSwap) (hx2 : x * x = 1)
    (hfus : ¬ IsConj z (z * x)) (hzx : z ∈ centralizer ({x} : Set G)) :
    WeakShape (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
      (twoSecComp e x (fixFin (rho e hn ⟨x, hxN⟩))) (n - 2) := by
  classical
  have hnorm' := CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
    hstd (d.le d.mem) d.order
  have hCN : centralizer ({z} : Set G) ≤ normalizer (L : Set G) := hnorm'.1
  have hLz : L ≤ centralizer ({z} : Set G) := hnorm'.2.1
  have hz2 : z * z = 1 := d.mul_self
  set τ := rho e hn ⟨x, hxN⟩ with hτdef
  set F : Finset (Fin n) := fixFin τ with hF
  have hFcard : F.card = n - 2 := card_fixFin_of_isSwap hτ
  set C := centralizer ({x} : Set G) with hC
  set R := corr (X := G) e (altSub F) with hR
  have hRx : R ≤ C := by
    intro w hw
    rw [hC, mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_rho_fix e hn hxN (fun i hi => mem_fixFin.1 hi) hw).symm
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) e F
  have eB : R.subgroupOf C ≃* alternatingGroup (Fin (n - 2)) :=
    ((Subgroup.subgroupOfEquivOfLe hRx).trans φ).trans
      (Equiv.altCongrHom (finCongr hFcard))
  have hτ1 : τ ≠ 1 := by
    obtain ⟨p, q, hpq, hτe⟩ := hτ
    intro h1
    have := congrArg (fun f : Perm (Fin n) => f p) (hτe.symm.trans h1)
    simp only [swap_apply_left, Perm.one_apply] at this
    exact hpq this.symm
  have hxz : x ≠ z := by
    intro hxz
    apply hτ1
    have : (⟨x, hxN⟩ : normalizer (L : Set G)) = ⟨z, hxz ▸ hxN⟩ := Subtype.ext hxz
    rw [hτdef, this]
    exact (rho_eq_one_iff e hn _).2 (d.le d.mem)
  refine weakShape_quotient_central (selfC_mem_center x) (Subtype.ext hx2) ?_ ?_ (by omega) eB
    ?_ ?_ ?_ ?_
  · rw [Subgroup.orderOf_mk]; exact d.order
  · intro hzP
    rcases (mem_zpowers_selfC_iff hx2).1 hzP with h1 | h1
    · have := d.order
      rw [show z = 1 from h1, orderOf_one] at this
      exact absurd this (by decide)
    · exact hxz (show x = z from h1.symm)
  · intro b hb
    rw [mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.1 (hLz (corr_le e _ (Subgroup.mem_subgroupOf.1 hb)))
  · intro y hy
    rcases (mem_zpowers_selfC_iff hx2).1 hy with h1 | h1
    · apply Subtype.ext
      have h1' : ((y : G) * z * (y : G)⁻¹)⁻¹ * z = 1 := by simpa using h1
      have := inv_mul_eq_one.1 h1'
      simpa using this
    · exfalso
      apply hfus
      have h1' : ((y : G) * z * (y : G)⁻¹)⁻¹ * z = x := by simpa using h1
      have h2 : (y : G) * z * (y : G)⁻¹ = z * x := by
        have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
        calc (y : G) * z * (y : G)⁻¹ = z * (((y : G) * z * (y : G)⁻¹)⁻¹ * z)⁻¹ := by group
          _ = z * x := by rw [h1', hxinv]
      exact isConj_iff.2 ⟨(y : G), h2⟩
  · intro y hy
    have hyz : (y : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hy ⊢
      exact congrArg Subtype.val hy
    have hyx : (y : G) * x = x * y := mem_centralizer_singleton_iff.1 y.2
    have hN := mem_normalizer_corr_fixFin_of_rho e hn hxN (hCN hyz) hyx
    rw [mem_normalizer_iff]
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact mem_normalizer_iff.1 hN b
  · rintro y ⟨hyB, hyt⟩ k hyk
    have hyt' : y ∈ centralizer ({(⟨z, hzx⟩ : ↥C)} : Set ↥C) := hyt
    have hyB' : y ∈ centralizer ((R.subgroupOf C : Subgroup ↥C) : Set ↥C) := hyB
    have hyz : (y : G) ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff] at hyt' ⊢
      exact congrArg Subtype.val hyt'
    have hyR : (y : G) ∈ centralizer (R : Set G) := by
      rw [mem_centralizer_iff]
      intro w hw
      have := mem_centralizer_iff.1 hyB' ⟨w, hRx hw⟩ (Subgroup.mem_subgroupOf.2 hw)
      exact congrArg Subtype.val this
    have hyN : (y : G) ∈ normalizer (L : Set G) := hCN hyz
    have hρ := rho_mem_centralizer e hn (altSub_le_alternatingGroup F) hyN hyR
    have hfix : ∀ i ∈ F, rho e hn ⟨y, hyN⟩ i = i :=
      (mem_centralizer_altSub_iff (by omega)).1 hρ
    obtain ⟨p, q, hpq, hτe⟩ := hτ
    have hcomp : ∀ i, i ≠ p → i ≠ q → rho e hn ⟨y, hyN⟩ i = i := by
      intro i hip hiq
      refine hfix i ?_
      rw [hF, mem_fixFin, hτe, swap_apply_of_ne_of_ne hip hiq]
    have hyk' : (y : G) ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hyk
      simpa using this
    have hzt : (⟨z, hzx⟩ : ↥C) ∈ zpowers (⟨z, hzx⟩ : ↥C) ⊔ zpowers (selfC x) :=
      mem_sup_left (mem_zpowers _)
    have hxt : selfC x ∈ zpowers (⟨z, hzx⟩ : ↥C) ⊔ zpowers (selfC x) :=
      mem_sup_right (mem_zpowers _)
    rcases eq_one_or_eq_of_fixes_compl hpq hcomp with hp1 | hpτ
    · have hyK : (y : G) ∈ centralizer (L : Set G) := (rho_eq_one_iff e hn ⟨y, hyN⟩).1 hp1
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (mem_zpowers_of_two_element d hQ2 ⟨hyK, hyz⟩ hyk')
      have : y = (⟨z, hzx⟩ : ↥C) ^ j := Subtype.ext (by simpa using hj.symm)
      rw [this]
      exact zpow_mem hzt j
    · have hρyx : rho e hn ⟨(y : G) * x, mul_mem hyN hxN⟩ = 1 := by
        have : (⟨(y : G) * x, mul_mem hyN hxN⟩ : normalizer (L : Set G)) =
            ⟨y, hyN⟩ * ⟨x, hxN⟩ := rfl
        rw [this, map_mul, hpτ, ← hτdef, hτe, swap_mul_self]
      have hyx : (y : G) * x = x * y := mem_centralizer_singleton_iff.1 y.2
      have hyxK : (y : G) * x ∈ centralizer (L : Set G) := (rho_eq_one_iff e hn _).1 hρyx
      have hyxz : (y : G) * x ∈ centralizer ({z} : Set G) := mul_mem hyz hx
      have hyxk : ((y : G) * x) ^ 2 ^ (k + 1) = 1 := by
        rw [(Commute.mul_pow (show Commute (y : G) x from hyx) _), pow_succ, pow_mul, hyk',
          one_pow, one_mul, pow_mul', sq, hx2, one_pow]
      obtain ⟨j, hj⟩ := mem_zpowers_iff.1
        (mem_zpowers_of_two_element d hQ2 ⟨hyxK, hyxz⟩ hyxk)
      have : y = (⟨z, hzx⟩ : ↥C) ^ j * selfC x := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_zpow]
        change (y : G) = z ^ j * x
        calc (y : G) = ((y : G) * x) * x := by rw [mul_assoc, hx2, mul_one]
          _ = z ^ j * x := by rw [hj]
      rw [this]
      exact mul_mem (zpow_mem hzt j) hxt

end TwoSecWeak

section TwoSecExact

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {z : G}

omit [Finite G] in
theorem centralizer_singleton_ne_top_of_simple (hsimple : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {x : G} (hx1 : x ≠ 1) :
    centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  have hZ : center G = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (center G) with h1 | h1
    · exact h1
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.1 (h1 ▸ mem_top b) a)
  have hc : x ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({x} : Set G) := htop ▸ Subgroup.mem_top g
    exact mem_centralizer_singleton_iff.1 this
  rw [hZ, Subgroup.mem_bot] at hc
  exact hx1 hc

theorem exactShape_twoSecO (hlookup : AltComponentLookup)
    (hHN : CFSG.ComponentClassification.RestrictedStd.Spor.HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : CFSG.ComponentClassification.RestrictedStd.Spor.FourExactOuterInput)
    (hS : StandardSetting G L) (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n)
    {Q : Subgroup G} (d : Cyc L Q z) (hQ2 : Nat.card Q = 2) {x : G}
    (hx : x ∈ centralizer ({z} : Set G)) (hxN : x ∈ normalizer (L : Set G))
    (hτ : (rho e (by omega) ⟨x, hxN⟩).IsSwap) (hx2 : x * x = 1) (hfus : ¬ IsConj z (z * x))
    (hzx : z ∈ centralizer ({x} : Set G)) :
    ExactShape
      (QuotientGroup.mk (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) :
        TwoSec x ⧸ CFSG.oddCore (TwoSec x))
      ((twoSecComp e x (fixFin (rho e (by omega) ⟨x, hxN⟩))).map
        (QuotientGroup.mk' (CFSG.oddCore (TwoSec x)))) (n - 2) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    obtain ⟨p, q, hpq, hτe⟩ := hτ
    have h1 : rho e (by omega) ⟨1, hxN⟩ = 1 := map_one _
    have := congrArg (fun f : Perm (Fin n) => f p) (hτe.symm.trans h1)
    simp only [swap_apply_left, Perm.one_apply] at this
    exact hpq this.symm
  have hKC : CFSG.SectionRank.IsKGroupCat (TwoSec x ⧸ CFSG.oddCore (TwoSec x)) :=
    (((isKGroupCat_of_kProper hS.kProper _
      (centralizer_singleton_ne_top_of_simple hS.simple hS.nonab hx1)).quotient _).quotient _)
  exact exactShape_of_weakShape hlookup hHN hOut hFour hKC
    (ClassicalInvolution.QuaternionStructure.oddCore_quotient_oddCore_eq_bot _)
    (weakShape_quotient_oddCore
      (weakShape_twoSec hS.standard e (by omega) d hQ2 hx hxN hτ hx2 hfus hzx) (by omega))
    (by omega)

end TwoSecExact

end CFSG.OddStandard.AltStdSec
