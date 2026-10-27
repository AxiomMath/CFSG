module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightAut
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly
open Equiv

private instance instDecEqPermFinFive : DecidableEq (Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

theorem s5_exists_invariant_four : ∀ σ : Perm (Fin 5), (σ * σ = 1 ∧ Perm.sign σ ≠ 1) →
    ∃ a : Perm (Fin 5), (Perm.sign a = 1 ∧ a * a = 1 ∧ a ≠ 1) ∧
    ∃ b : Perm (Fin 5), (Perm.sign b = 1 ∧ b * b = 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * b = b * a ∧
      (σ * a * σ⁻¹ = a ∨ σ * a * σ⁻¹ = b ∨ σ * a * σ⁻¹ = a * b) ∧
      (σ * b * σ⁻¹ = a ∨ σ * b * σ⁻¹ = b ∨ σ * b * σ⁻¹ = a * b)) := by
  decide +kernel

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hH : ∀ h ∈ H, g * h * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨h, hh, rfl⟩
    exact hH h hh
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem eq_normalizer_of_le {K : Type*} [Group K] [Finite K] (hK : Nat.card K = 60)
    {F B : Subgroup K} (hF : Nat.card F = 4) (hNB : Subgroup.normalizer (F : Set K) ≤ B)
    (hB : B ≠ ⊤) {d : K} (hdN : d ∈ Subgroup.normalizer (F : Set K)) (hd3 : d * d * d = 1)
    (hd1 : d ≠ 1) : B = Subgroup.normalizer (F : Set K) := by
  set N := Subgroup.normalizer (F : Set K) with hN
  have h4 : 4 ∣ Nat.card N := by
    have := Subgroup.card_dvd_of_le (Subgroup.le_normalizer (H := F))
    rwa [hF] at this
  have h3 : 3 ∣ Nat.card N := by
    have hord : orderOf (⟨d, hdN⟩ : N) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (by rw [pow_three, ← mul_assoc, hd3]) hd1
    rw [← hord]
    exact orderOf_dvd_natCard _
  have h12 : 12 ∣ Nat.card N := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h4
  have hB60 : Nat.card B ∣ 60 := hK ▸ Subgroup.card_subgroup_dvd_card _
  have hBne : Nat.card B ≠ 60 := fun h60 =>
    hB (by rw [← Subgroup.card_eq_iff_eq_top, h60, hK])
  have h12B : 12 ∣ Nat.card B := h12.trans (Subgroup.card_dvd_of_le hNB)
  have hB12 : Nat.card B = 12 := by
    obtain ⟨k, hk⟩ := h12B
    obtain ⟨l, hl⟩ := hB60
    rw [hk] at hl hBne
    have hkl : k * l = 5 := by
      have h60 : 12 * (k * l) = 12 * 5 := by rw [← mul_assoc, ← hl]
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) h60
    rcases (Nat.dvd_prime (by norm_num)).mp (⟨l, hkl.symm⟩ : k ∣ 5) with hk1 | hk1
    · rw [hk, hk1]
    · exact absurd (by rw [hk1]) hBne
  have hN12 : 12 ≤ Nat.card N := Nat.le_of_dvd Nat.card_pos h12
  exact (Subgroup.eq_of_le_of_card_ge hNB (by rw [hB12]; exact hN12)).symm

variable {X : Type} [Group X] [Finite X]

namespace OneComponent

variable {Y : Subgroup X} {e v : X} {L : Subgroup X}

theorem map_comap_le_of_stable [L.Normal] (hL : OneComponent Y e v L) (hc : BaseConfig Y e)
    {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2) (hxe : x ≠ e)
    {F : Subgroup (L ⧸ Subgroup.center L)} (hF : ∀ y ∈ F, y * y = 1)
    (hFx : ∀ y ∈ F, quotientConj L x y ∈ F) :
    (F.comap (QuotientGroup.mk' (Subgroup.center L))).map L.subtype ≤ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center L) with hπdef
  set Qx := (F.comap π).map L.subtype with hQx
  have hF2 : IsPGroup 2 F := fun y => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two]
    exact hF y y.2)⟩
  have hker2 : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact hL.center_isPGroup hc
  have hQx2 : IsPGroup 2 Qx := (hF2.comap_of_ker_isPGroup π hker2).map _
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hconj : ∀ q : L, π q ∈ F → x * q * x⁻¹ ∈ Qx := by
    intro q hq
    refine ⟨MulAut.conjNormal x q, ?_, by simp [MulAut.conjNormal_apply]⟩
    change ((MulAut.conjNormal x q : L) : L ⧸ Subgroup.center L) ∈ F
    rw [← quotientConj_mk]
    exact hFx _ hq
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer (Qx : Set X) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hconj q hq
    · rintro ⟨q, hq, hqw⟩
      have h := hconj q hq
      have hq' : (q : X) = x * w * x⁻¹ := hqw
      rwa [hq', hxinv, show x * (x * w * x) * x = x * x * w * (x * x) by group, hxx, one_mul,
        mul_one] at h
  have hD2 : IsPGroup 2 (Qx ⊔ Subgroup.zpowers x : Subgroup X) :=
    hQx2.to_sup_of_normal_left' (IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, hx, pow_one])) hnorm
  have heQx : e ∈ Qx := ⟨⟨e, hL.mem⟩, by
    change ((⟨e, hL.mem⟩ : L) : L ⧸ Subgroup.center L) ∈ F
    rw [(QuotientGroup.eq_one_iff _).mpr (hL.mem_center hc)]
    exact F.one_mem, rfl⟩
  have hrank : 2 ≤ CFSG.Open.pRank 2 ((Qx ⊔ Subgroup.zpowers x) ⊓ Y) :=
    two_le_pRank_of_commuting_involutions ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers x), hxY⟩
      ⟨Subgroup.mem_sup_left heQx, hc.center_mem⟩ hx hc.order hxe (hc.commute_center x)
  exact le_sup_left.trans (hc.le_of_two_le_pRank_inf hD2 hrank)

theorem mem_of_normalizes (hL : OneComponent Y e v L) (hc : BaseConfig Y e) (hv : v * v = e)
    (hvn : (Subgroup.zpowers v).Normal) (hZ : Nat.card (Subgroup.center L) = 2)
    {F : Subgroup (L ⧸ Subgroup.center L)} (hF : ∀ y ∈ F, y * y = 1)
    (hQY : (F.comap (QuotientGroup.mk' (Subgroup.center L))).map L.subtype ≤ Y) {q : L}
    (hqF : (q : L ⧸ Subgroup.center L) ∈ F) (hq1 : (q : L ⧸ Subgroup.center L) ≠ 1) {l : L}
    (hl : ∀ y ∈ F, (l : L ⧸ Subgroup.center L) * y * (l : L ⧸ Subgroup.center L)⁻¹ ∈ F) :
    (l : X) ∈ Y := by
  have hvY : v ∈ Y := hc.twoCore_le (hc.mem_twoCore_of_sq hv hvn)
  have hvc : ∀ g : L, (g : X) * v = v * g := fun g =>
    Subgroup.mem_centralizer_iff.mp hL.mem_centralizer g g.2
  have hqZ : q ∉ Subgroup.center L := fun h => hq1 ((QuotientGroup.eq_one_iff q).mpr h)
  have hqq : q * q ∈ Subgroup.center L := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
    exact hF _ hqF
  have hqY : (q : X) ∈ Y := hQY ⟨q, hqF, rfl⟩
  have hlq : (l : X) * q * (l : X)⁻¹ ∈ Y := by
    have h := hQY ⟨l * q * l⁻¹, by
      change ((l * q * l⁻¹ : L) : L ⧸ Subgroup.center L) ∈ F
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hl _ hqF, rfl⟩
    simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] using h
  obtain ⟨t, htY, ht2, hte, hltY⟩ :
      ∃ t ∈ Y, orderOf t = 2 ∧ t ≠ e ∧ (l : X) * t * (l : X)⁻¹ ∈ Y := by
    rcases hL.eq_one_or_eq_of_card_two hc hZ hqq with h1 | he
    · refine ⟨q, hqY, ?_, fun h => hqZ ?_, hlq⟩
      · rw [Subgroup.orderOf_coe]
        exact orderOf_eq_prime (by rw [pow_two]; exact h1) fun h => hqZ (h ▸ Subgroup.one_mem _)
      · rw [show q = ⟨e, hL.mem⟩ from Subtype.ext h]
        exact hL.mem_center hc
    · obtain ⟨hvq2, hvqe⟩ := hL.mul_involution_of_card_two hc hv hZ q.2 he
      refine ⟨v * q, Y.mul_mem hvY hqY, hvq2, hvqe, ?_⟩
      have hconj : (l : X) * (v * q) * (l : X)⁻¹ = v * ((l : X) * q * (l : X)⁻¹) := by
        calc (l : X) * (v * q) * (l : X)⁻¹ = (l : X) * v * q * (l : X)⁻¹ := by group
          _ = v * l * q * (l : X)⁻¹ := by rw [hvc l]
          _ = v * ((l : X) * q * (l : X)⁻¹) := by group
      rw [hconj]
      exact Y.mul_mem hvY hlq
  have h := hc.mem_of_conj_mem (m := (l : X)⁻¹) htY ht2 hte (by rwa [inv_inv])
  simpa using Y.inv_mem h

theorem mem_of_fixed [L.Normal] (hL : OneComponent Y e v L) (hc : BaseConfig Y e) {x : X}
    (hxY : x ∈ Y) (hx : orderOf x = 2) (hxe : x ≠ e) {l : L}
    (hl : quotientConj L x (l : L ⧸ Subgroup.center L) = (l : L ⧸ Subgroup.center L)) :
    (l : X) ∈ Y := by
  rw [quotientConj_mk, QuotientGroup.eq] at hl
  have hζ := Subgroup.mem_subgroupOf.mp (hL.center_le_subgroupOf hc hl)
  have hxx : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have h : (l : X)⁻¹ * x * l = x * (((MulAut.conjNormal x l)⁻¹ * l : L) : X) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    calc (l : X)⁻¹ * x * l = (l : X)⁻¹ * x⁻¹ * l := by rw [hxinv]
      _ = x * x * ((l : X)⁻¹ * x⁻¹ * l) := by rw [hxx, one_mul]
      _ = x * ((x * l * x⁻¹)⁻¹ * l) := by group
  exact hc.mem_of_conj_mem hxY hx hxe (h ▸ Y.mul_mem hxY hζ)

end OneComponent

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
