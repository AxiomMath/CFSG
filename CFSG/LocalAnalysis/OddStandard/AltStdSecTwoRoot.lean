module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecPartNear
public import CFSG.GroupTheory.QuasiDihedralFusion.CharPowerBasic
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootSec

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Quot

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem exists_centralizer_preimage_central {x t : H} [(zpowers x).Normal]
    (hfus : ∀ y : H, (y * t * y⁻¹)⁻¹ * t ∈ zpowers x → y * t * y⁻¹ = t)
    {c : H ⧸ zpowers x}
    (hc : c ∈ centralizer ({(QuotientGroup.mk t : H ⧸ zpowers x)} : Set (H ⧸ zpowers x))) :
    ∃ y ∈ centralizer ({t} : Set H), (QuotientGroup.mk y : H ⧸ zpowers x) = c := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨y, ?_, rfl⟩
  rw [mem_centralizer_singleton_iff] at hc ⊢
  have h1 : ((y * t * y⁻¹ : H) : H ⧸ zpowers x) = (t : H ⧸ zpowers x) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hc]
    group
  have h2 := hfus y (QuotientGroup.eq.1 h1)
  calc y * t = (y * t * y⁻¹) * y := by group
    _ = t * y := by rw [h2]

omit [Finite H] in
theorem exactShape_quotient_central {x t : H} [(zpowers x).Normal]
    (hxc : x ∈ Subgroup.center H) (ht : orderOf t = 2) (htx : t ∉ zpowers x)
    {B : Subgroup H} {m : ℕ} (hm : 5 ≤ m) (eB : B ≃* alternatingGroup (Fin m))
    (hBt : B ≤ centralizer ({t} : Set H))
    (hfus : ∀ y : H, (y * t * y⁻¹)⁻¹ * t ∈ zpowers x → y * t * y⁻¹ = t)
    (hnorm : centralizer ({t} : Set H) ≤ normalizer (B : Set H))
    (hcc : centralizer (B : Set H) ⊓ centralizer ({t} : Set H) ≤ zpowers t ⊔ zpowers x) :
    ExactShape (QuotientGroup.mk t : H ⧸ zpowers x) (B.map (QuotientGroup.mk' (zpowers x))) m := by
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
  ·
    apply orderOf_eq_prime
    · have h2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
      rw [← QuotientGroup.mk_pow, h2]
      rfl
    · intro h1
      exact htx ((QuotientGroup.eq_one_iff t).1 h1)
  · exact ⟨(ClassicalInvolution.QuaternionStructure.mulEquivMapOfInjective
      (QuotientGroup.mk' P) B hinj).symm.trans eB⟩
  ·
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.1 (hBt hb)
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]
  ·
    intro y hy
    obtain ⟨c, hc, rfl⟩ := exists_centralizer_preimage_central hfus hy
    rw [mem_normalizer_iff]
    exact hconj c (hnorm hc)
  ·
    apply le_antisymm
    · rintro y ⟨hyB, hyt⟩
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
      have hmem : c ∈ zpowers t ⊔ P := hcc ⟨hcB, hc⟩
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' P) hmem
      rwa [Subgroup.map_sup, MonoidHom.map_zpowers, QuotientGroup.map_mk'_self, sup_bot_eq]
        at this
    · refine le_inf ?_ ?_
      · rw [zpowers_le, mem_centralizer_iff]
        rintro _ ⟨b, hb, rfl⟩
        have := mem_centralizer_singleton_iff.1 (hBt hb)
        simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, this]
      · rw [zpowers_le, mem_centralizer_singleton_iff]

end Quot

section TwoSec

variable {G : Type} [Group G]

@[expose] def selfC (x : G) : ↥(centralizer ({x} : Set G)) :=
  ⟨x, mem_centralizer_singleton_iff.2 rfl⟩

theorem selfC_mem_center (x : G) : selfC x ∈ Subgroup.center ↥(centralizer ({x} : Set G)) := by
  rw [Subgroup.mem_center_iff]
  intro c
  apply Subtype.ext
  exact mem_centralizer_singleton_iff.1 c.2

instance normal_zpowers_selfC (x : G) : (zpowers (selfC x)).Normal :=
  Subgroup.normal_of_le_center (zpowers_le.2 (selfC_mem_center x))

abbrev TwoSec (x : G) : Type := ↥(centralizer ({x} : Set G)) ⧸ zpowers (selfC x)

theorem mem_zpowers_selfC_iff {x : G} (hx : x * x = 1) {c : ↥(centralizer ({x} : Set G))} :
    c ∈ zpowers (selfC x) ↔ (c : G) = 1 ∨ (c : G) = x := by
  constructor
  · intro hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hx
    have key : x ^ k = x ^ (k % 2) := zpow_eq_zpow_emod k hx2
    show ((selfC x ^ k : ↥(centralizer ({x} : Set G))) : G) = 1 ∨ _
    rw [Subgroup.coe_zpow]
    change x ^ k = 1 ∨ x ^ k = x
    rw [key]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left; rw [h0, zpow_zero]
    · right; rw [h1, zpow_one]
  · rintro (h1 | h1)
    · have : c = 1 := Subtype.ext h1
      rw [this]
      exact one_mem _
    · have : c = selfC x := Subtype.ext h1
      rw [this]
      exact mem_zpowers _

end TwoSec

section Exact

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

@[expose] noncomputable def twoSecComp (e : L ≃* alternatingGroup (Fin n)) (x : G)
    (F : Finset (Fin n)) : Subgroup (TwoSec x) :=
  ((corr (X := G) e (altSub F)).subgroupOf (centralizer ({x} : Set G))).map
    (QuotientGroup.mk' (zpowers (selfC x)))

omit [Finite G] in
theorem card_fixFin_add_card_support (σ : Perm (Fin n)) : (fixFin σ).card + σ.support.card = n := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => σ i = i)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hs : σ.support = Finset.univ.filter (fun i => ¬ σ i = i) := by
    ext i
    simp [Perm.mem_support]
  rw [hs]
  exact h

omit [Finite G] in
theorem card_fixFin_of_isSwap {σ : Perm (Fin n)} (hσ : σ.IsSwap) : (fixFin σ).card = n - 2 := by
  have h := card_fixFin_add_card_support σ
  rw [Perm.card_support_eq_two.2 hσ] at h
  omega

theorem permOf_self (h : Setting G L n) (d : Cyc L Q z) (e : L ≃* alternatingGroup (Fin n))
    (hz : z ∈ centralizer ({z} : Set G)) : permOf h d e hz = 1 :=
  (rho_eq_one_iff e h.hn _).2 (d.le d.mem)

theorem swap_elt_facts (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) : x * x = 1 ∧ x ≠ z ∧ x ≠ 1 := by
  have hz2 : z * z = 1 := d.mul_self
  have hτ2 : permOf h d e hx * permOf h d e hx = 1 := by
    obtain ⟨p, q, _, hpq⟩ := hτ
    rw [hpq, swap_mul_self]
  have hsq : swapIota h d T e (permOf h d e hx) * swapIota h d T e (permOf h d e hx) = 1 := by
    rw [← map_mul, hτ2, map_one]
  have hs2 : (swapIota h d T e (permOf h d e hx) : G) * swapIota h d T e (permOf h d e hx) = 1 :=
    congrArg Subtype.val hsq
  have hsz : (swapIota h d T e (permOf h d e hx) : G) * z =
      z * swapIota h d T e (permOf h d e hx) :=
    mem_centralizer_singleton_iff.1 (swapIota_mem_centralizer h d T e _)
  have hτ1 : permOf h d e hx ≠ 1 := by
    obtain ⟨p, q, hpq, he⟩ := hτ
    intro h1
    rw [h1] at he
    have := congrArg (fun f : Perm (Fin n) => f p) he
    simp only [Perm.one_apply, swap_apply_left] at this
    exact hpq this
  refine ⟨?_, ?_, ?_⟩
  · rcases eq_swapIota_or h d T e hx with h1 | h1
    · rw [h1]; exact hs2
    · rw [h1]
      calc z * (swapIota h d T e (permOf h d e hx) : G) * (z * swapIota h d T e (permOf h d e hx))
          = z * (swapIota h d T e (permOf h d e hx) * z) * swapIota h d T e (permOf h d e hx) := by
            group
        _ = z * (z * swapIota h d T e (permOf h d e hx)) * swapIota h d T e (permOf h d e hx) := by
            rw [hsz]
        _ = (z * z) * ((swapIota h d T e (permOf h d e hx) : G) *
            swapIota h d T e (permOf h d e hx)) := by group
        _ = 1 := by rw [hz2, hs2, one_mul]
  · intro hxz
    subst hxz
    exact hτ1 (permOf_self h d e hx)
  · intro hx1
    subst hx1
    apply hτ1
    have : permOf h d e hx = permOf h d e (one_mem _) := rfl
    rw [this]
    unfold permOf
    have h1 : (⟨1, AltStdBal.centralizer_le_normalizer h d (one_mem _)⟩ :
        normalizer (L : Set G)) = 1 := rfl
    rw [h1, map_one]

theorem exactShape_twoSec (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 7 ≤ n) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) (hfus : ¬ IsConj z (z * x))
    (hzx : z ∈ centralizer ({x} : Set G)) :
    ExactShape (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x)
      (twoSecComp e x (fixFin (permOf h d e hx))) (n - 2) := by
  classical
  obtain ⟨hx2, hxz, hx1⟩ := swap_elt_facts h d T e hx hτ
  have hz2 : z * z = 1 := d.mul_self
  have hzxc : z * x = x * z := mem_centralizer_singleton_iff.1 hzx
  set F : Finset (Fin n) := fixFin (permOf h d e hx) with hF
  have hFcard : F.card = n - 2 := card_fixFin_of_isSwap hτ
  set C := centralizer ({x} : Set G) with hC
  set R := corr (X := G) e (altSub F) with hR
  have hRx : R ≤ C := by
    intro w hw
    rw [hC, mem_centralizer_singleton_iff]
    exact (comm_of_mem_corr_of_permOf_fix h d e hx (fun i hi => mem_fixFin.1 hi) hw).symm
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) e F
  have eB : R.subgroupOf C ≃* alternatingGroup (Fin (n - 2)) :=
    ((Subgroup.subgroupOfEquivOfLe hRx).trans φ).trans
      (Equiv.altCongrHom (finCongr hFcard))
  refine exactShape_quotient_central (selfC_mem_center x) ?_ ?_ (by omega) eB ?_ ?_ ?_ ?_
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
    exact mem_centralizer_singleton_iff.1
      (le_centralizer_single h d (corr_le e _ (Subgroup.mem_subgroupOf.1 hb)))
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
    have hN := mem_normalizer_corr_fixFin h d e hx hyz hyx
    rw [mem_normalizer_iff]
    intro b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact mem_normalizer_iff.1 hN b
  · rintro y ⟨hyB, hyt⟩
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
    have hyN : (y : G) ∈ normalizer (L : Set G) := AltStdBal.centralizer_le_normalizer h d hyz
    have hρ := rho_mem_centralizer e h.hn (altSub_le_alternatingGroup F) hyN hyR
    have hfix : ∀ i ∈ F, permOf h d e hyz i = i :=
      (mem_centralizer_altSub_iff (by omega)).1 hρ
    obtain ⟨p, q, hpq, hτe⟩ := hτ
    have hpF : p ∉ F := by
      rw [hF, mem_fixFin, hτe, swap_apply_left]; exact hpq.symm
    have hqF : q ∉ F := by
      rw [hF, mem_fixFin, hτe, swap_apply_right]; exact hpq
    have hcomp : ∀ i, i ≠ p → i ≠ q → permOf h d e hyz i = i := by
      intro i hip hiq
      refine hfix i ?_
      rw [hF, mem_fixFin, hτe, swap_apply_of_ne_of_ne hip hiq]
    have hzt : (⟨z, hzx⟩ : ↥C) ∈ zpowers (⟨z, hzx⟩ : ↥C) ⊔ zpowers (selfC x) :=
      mem_sup_left (mem_zpowers _)
    have hxt : selfC x ∈ zpowers (⟨z, hzx⟩ : ↥C) ⊔ zpowers (selfC x) :=
      mem_sup_right (mem_zpowers _)
    rcases eq_one_or_eq_of_fixes_compl hpq hcomp with hp1 | hpτ
    ·
      have hι1 : (swapIota h d T e (permOf h d e hyz) : G) = 1 := by
        rw [hp1, map_one]; rfl
      rcases eq_swapIota_or h d T e hyz with h1 | h1
      · rw [hι1] at h1
        have : y = 1 := Subtype.ext h1
        rw [this]; exact one_mem _
      · rw [hι1, mul_one] at h1
        have : y = ⟨z, hzx⟩ := Subtype.ext h1
        rw [this]; exact hzt
    ·
      have hpe : permOf h d e hyz = permOf h d e hx := hpτ.trans hτe.symm
      have hιe : (swapIota h d T e (permOf h d e hyz) : G) =
          swapIota h d T e (permOf h d e hx) := by rw [hpe]
      set s : G := (swapIota h d T e (permOf h d e hx) : G) with hs
      set s' : G := (swapIota h d T e (permOf h d e hyz) : G) with hs'
      rcases eq_swapIota_or h d T e hx with hx' | hx'
      · rcases eq_swapIota_or h d T e hyz with h1 | h1
        · have : y = selfC x := Subtype.ext (h1.trans (hιe.trans hx'.symm))
          rw [this]; exact hxt
        · have : y = ⟨z, hzx⟩ * selfC x := by
            apply Subtype.ext
            rw [Subgroup.coe_mul]
            change (y : G) = z * x
            calc (y : G) = z * s' := h1
              _ = z * s := by rw [hιe]
              _ = z * x := (congrArg (z * ·) hx').symm
          rw [this]; exact mul_mem hzt hxt
      · rcases eq_swapIota_or h d T e hyz with h1 | h1
        · have : y = ⟨z, hzx⟩ * selfC x := by
            apply Subtype.ext
            rw [Subgroup.coe_mul]
            change (y : G) = z * x
            calc (y : G) = s' := h1
              _ = s := hιe
              _ = z * (z * s) := by rw [← mul_assoc, hz2, one_mul]
              _ = z * x := (congrArg (z * ·) hx').symm
          rw [this]; exact mul_mem hzt hxt
        · have : y = selfC x := by
            apply Subtype.ext
            change (y : G) = x
            calc (y : G) = z * s' := h1
              _ = z * s := by rw [hιe]
              _ = x := hx'.symm
          rw [this]; exact hxt

theorem centralizer_singleton_ne_top (h : Setting G L n) {x : G} (hx1 : x ≠ 1) :
    centralizer ({x} : Set G) ≠ ⊤ := by
  intro htop
  have hc : x ∈ center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ centralizer ({x} : Set G) := htop ▸ Subgroup.mem_top g
    exact mem_centralizer_singleton_iff.1 this
  rw [center_eq_bot_of_simple_nonabelian h.std.simple h.std.nonab, Subgroup.mem_bot] at hc
  exact hx1 hc

theorem isKGroupCat_twoSec (h : Setting G L n) {x : G} (hx1 : x ≠ 1) :
    CFSG.SectionRank.IsKGroupCat (TwoSec x) :=
  (isKGroupCat_of_kProper h.std.kProper _ (centralizer_singleton_ne_top h hx1)).quotient _

theorem oddCore_twoSec_eq_bot (h : Setting G L n) {x : G} (hx : orderOf x = 2) :
    CFSG.oddCore (TwoSec x) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine QuasiDihedralFusion.oddCore_quotient_eq_bot_of_le_center (h.bal x hx) _
    (zpowers_le.2 (selfC_mem_center x)) ?_
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers]
  unfold selfC
  rw [Subgroup.orderOf_mk, hx, pow_one]

omit [Finite G] in
theorem comm_of_mk_comm {x : G} (hx2 : x * x = 1) (hfus : ¬ IsConj z (z * x))
    (hzx : z ∈ centralizer ({x} : Set G)) {w : G} (hw : w ∈ centralizer ({x} : Set G))
    (h1 : (QuotientGroup.mk ⟨w, hw⟩ * QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) =
      QuotientGroup.mk ⟨z, hzx⟩ * QuotientGroup.mk ⟨w, hw⟩) : w * z = z * w := by
  have h2 : ((⟨w, hw⟩ * ⟨z, hzx⟩ * (⟨w, hw⟩ : ↥(centralizer ({x} : Set G)))⁻¹ :
      ↥(centralizer ({x} : Set G))) : TwoSec x) = QuotientGroup.mk ⟨z, hzx⟩ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h1]
    group
  have h3 := (mem_zpowers_selfC_iff hx2).1 (QuotientGroup.eq.1 h2)
  rcases h3 with h3 | h3
  · have h3' : (w * z * w⁻¹)⁻¹ * z = 1 := by simpa using h3
    have := inv_mul_eq_one.1 h3'
    calc w * z = (w * z * w⁻¹) * w := by group
      _ = z * w := by rw [this]
  · exfalso
    apply hfus
    have h3' : (w * z * w⁻¹)⁻¹ * z = x := by simpa using h3
    have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have h4 : w * z * w⁻¹ = z * x := by
      calc w * z * w⁻¹ = z * ((w * z * w⁻¹)⁻¹ * z)⁻¹ := by group
        _ = z * x := by rw [h3', hxinv]
    exact isConj_iff.2 ⟨w, h4⟩

omit [Finite G] in
theorem centralizer_le_of_mem_center {x : G} (hx2 : x * x = 1) (hfus : ¬ IsConj z (z * x))
    (hzx : z ∈ centralizer ({x} : Set G))
    (hc : (QuotientGroup.mk ⟨z, hzx⟩ : TwoSec x) ∈ Subgroup.center (TwoSec x)) :
    centralizer ({x} : Set G) ≤ centralizer ({z} : Set G) := by
  intro y hy
  rw [mem_centralizer_singleton_iff]
  exact comm_of_mk_comm hx2 hfus hzx hy ((Subgroup.mem_center_iff.1 hc) (QuotientGroup.mk ⟨y, hy⟩))

end Exact

end CFSG.OddStandard.AltStdSec
