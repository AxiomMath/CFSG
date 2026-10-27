module

public import CFSG.ClassicalInvolution.Balance.Prop311
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved
import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.ClassicalInvolution.Balance.LocalBalance

open CFSG CFSG.LocalCores CFSG.Open

section Parity

variable {Y : Type*} [Group Y] [Finite Y]

theorem even_card_inf_centralizer_of_even {K : Subgroup Y} {t : Y} (ht : t * t = 1)
    (hK : ∀ x ∈ K, t * x * t⁻¹ ∈ K) (hev : Even (Nat.card K)) :
    Even (Nat.card (K ⊓ Subgroup.centralizer ({t} : Set Y) : Subgroup Y)) := by
  classical
  let _ : Fintype Y := Fintype.ofFinite Y
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  let σ : Function.End K := fun x => ⟨t * x * t⁻¹, hK x x.2⟩
  have hσ : σ ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    change t * (t * (x : Y) * t⁻¹) * t⁻¹ = x
    calc t * (t * (x : Y) * t⁻¹) * t⁻¹ = (t * t) * (x : Y) * (t * t)⁻¹ := by group
      _ = x := by rw [ht]; group
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hσ
  have hcard : Nat.card (K ⊓ Subgroup.centralizer ({t} : Set Y) : Subgroup Y) =
      Fintype.card (Function.fixedPoints (σ : K → K)) := by
    rw [← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun y => ⟨⟨y.1, y.2.1⟩, ?_⟩, fun x => ⟨x.1.1, x.1.2, ?_⟩, ?_, ?_⟩
    · have h := Subgroup.mem_centralizer_singleton_iff.mp y.2.2
      apply Subtype.ext
      change t * (y : Y) * t⁻¹ = y
      rw [← h]
      group
    · have h := congrArg Subtype.val x.2
      change t * (x.1 : Y) * t⁻¹ = x.1 at h
      rw [mul_inv_eq_iff_eq_mul] at h
      exact Subgroup.mem_centralizer_singleton_iff.mpr h.symm
    · intro y; rfl
    · intro x; rfl
  rw [hcard]
  have h1 : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  rw [h1] at hmod
  have : Nat.card K % 2 = Fintype.card (Function.fixedPoints (σ : K → K)) % 2 := hmod
  rw [Nat.even_iff] at hev ⊢
  omega

end Parity

section Normalizes

variable {X : Type*} [Group X] [Finite X]

theorem mem_centralizer_layer_of_central {L : Subgroup X} (hL : IsComponent L) {a : X} (ha : a ∈ L)
    (hcen : ∀ w ∈ L, w * a = a * w) : a ∈ Subgroup.centralizer (layer X : Set X) :=
  CFSG.WholeGroup.mem_centralizer_layer_of_mem_component hL ha hcen

theorem conjSub_eq_of_mem_involutionOddCore {L : Subgroup X} (hL : IsComponent L) {f d : X}
    (hf2 : f * f = 1) (hfL : conjSub f L = L)
    (hd : d ∈ CFSG.Assembly.Dichotomy.involutionOddCore f) : conjSub d L = L := by
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL₂ : IsComponent (conjSub d L) := isComponent_map_mulEquiv (MulAut.conj d) hL
  have hcomm : ∀ a ∈ L, ∀ b ∈ conjSub d L, a * b = b * a :=
    commute_of_isComponent_of_ne hL hL₂ (fun h => hne h.symm)
  have hEn : (layer X).Normal := by
    have : (layer X).Characteristic := layer_characteristic
    infer_instance
  set CE : Subgroup X := Subgroup.centralizer (layer X : Set X) with hCE
  have hCEn : CE.Normal := Subgroup.normal_centralizer
  let π : X →* X ⧸ CE := QuotientGroup.mk' CE
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective CE
  have hLE : L ≤ layer X := component_le_layer hL
  have hinter : ∀ a ∈ L, ∀ b ∈ conjSub d L, π a = π b → π a = 1 := by
    intro a ha b hb hab
    have hmem : a⁻¹ * b ∈ CE := QuotientGroup.eq.mp hab
    have hc : ∀ w ∈ L, w * a = a * w := by
      intro w hw
      have h1 : w * (a⁻¹ * b) = (a⁻¹ * b) * w := Subgroup.mem_centralizer_iff.mp hmem w (hLE hw)
      have h2 : w * b = b * w := hcomm w hw b hb
      have h3 : w * a⁻¹ = a⁻¹ * w := by
        have h4 : w * a⁻¹ * b = a⁻¹ * w * b := by
          calc w * a⁻¹ * b = w * (a⁻¹ * b) := by group
            _ = (a⁻¹ * b) * w := h1
            _ = a⁻¹ * (b * w) := by group
            _ = a⁻¹ * (w * b) := by rw [h2]
            _ = a⁻¹ * w * b := by group
        exact mul_right_cancel h4
      calc w * a = a * (a⁻¹ * w) * a := by group
        _ = a * (w * a⁻¹) * a := by rw [h3]
        _ = a * w := by group
    exact (QuotientGroup.eq_one_iff a).mpr (mem_centralizer_layer_of_central hL ha hc)
  set Lb : Subgroup (X ⧸ CE) := L.map π with hLb
  have hperf : Group.IsPerfect Lb := by
    have : Group.IsPerfect L := hL.1.1
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap L) (π.subgroupMap_surjective L)
  have hnontriv : Nontrivial Lb := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    have hker : L ≤ CE := by
      have := (Subgroup.map_eq_bot_iff _).mp hbot
      rwa [QuotientGroup.ker_mk'] at this
    obtain ⟨a, ha, b, hb, hab⟩ := exists_noncomm_of_isQuasisimple hL.1
    exact hab (Subgroup.mem_centralizer_iff.mp (hker ha) b (hLE hb)).symm
  have hev : Even (Nat.card Lb) := by
    by_contra hodd
    have hsolv : Group.IsSolvable Lb :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.not_even_iff_odd.mp hodd)
    exact Group.IsPerfect.not_isSolvable Lb hsolv
  have ht2 : π f * π f = 1 := by rw [← map_mul, hf2, map_one]
  have hLbn : ∀ y ∈ Lb, π f * y * (π f)⁻¹ ∈ Lb := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨f * x * f⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    have : f * x * f⁻¹ ∈ conjSub f L := conj_mem_conjSub hx
    rwa [hfL] at this
  have hevC := even_card_inf_centralizer_of_even ht2 hLbn hev
  obtain ⟨xc, hxc⟩ := exists_prime_orderOf_dvd_card'
    (G := (Lb ⊓ Subgroup.centralizer ({π f} : Set (X ⧸ CE)) : Subgroup (X ⧸ CE))) 2
    (even_iff_two_dvd.mp hevC)
  set xb : X ⧸ CE := (xc : X ⧸ CE) with hxb
  have hxord : orderOf xb = 2 := by rw [hxb, Subgroup.orderOf_coe, hxc]
  have hxbL : xb ∈ Lb := xc.2.1
  have hxbC : xb ∈ Subgroup.centralizer ({π f} : Set (X ⧸ CE)) := xc.2.2
  obtain ⟨x, hx, hxπ⟩ := hxbL
  have hpg : IsPGroup 2 (Subgroup.zpowers f) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    have h2 : orderOf f ∣ 2 ^ 1 := by
      rw [pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [sq, hf2])
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
    exact ⟨i, hi⟩
  have hdb : π d ∈ CFSG.Assembly.Dichotomy.involutionOddCore (π f) :=
    map_involutionOddCore_le π hπ hpg ⟨d, hd, rfl⟩
  have hcmem : xb⁻¹ * (π d * xb * (π d)⁻¹) ∈
      CFSG.Assembly.Dichotomy.involutionOddCore (π f) := by
    have h1 := conj_mem_involutionOddCore (a := π f) (c := xb⁻¹) (u := π d)
      (inv_mem hxbC) hdb
    have : xb⁻¹ * (π d * xb * (π d)⁻¹) = (xb⁻¹ * π d * xb⁻¹⁻¹) * (π d)⁻¹ := by group
    rw [this]
    exact mul_mem h1 (inv_mem hdb)
  have hcodd : ¬ 2 ∣ orderOf (xb⁻¹ * (π d * xb * (π d)⁻¹)) := by
    obtain ⟨r, hr, hrc⟩ := hcmem
    rw [← hrc]
    exact not_two_dvd_orderOf_of_mem_oddCore hr
  have hy : d * x * d⁻¹ ∈ conjSub d L := conj_mem_conjSub hx
  have hyb : π d * xb * (π d)⁻¹ = π (d * x * d⁻¹) := by
    rw [← hxπ]
    simp only [map_mul, map_inv]
  have hxy : Commute (π x) (π (d * x * d⁻¹)) := by
    have := congrArg π (hcomm x hx _ hy)
    rwa [map_mul, map_mul] at this
  set n := orderOf (xb⁻¹ * (π d * xb * (π d)⁻¹)) with hn
  have hcn : (xb⁻¹ * (π d * xb * (π d)⁻¹)) ^ n = 1 := pow_orderOf_eq_one _
  have hcomm' : Commute xb⁻¹ (π (d * x * d⁻¹)) := by
    rw [← hxπ]
    exact hxy.inv_left
  have hkey : (xb⁻¹ * (π d * xb * (π d)⁻¹)) ^ n = xb⁻¹ ^ n * (π (d * x * d⁻¹)) ^ n := by
    rw [hyb]
    exact hcomm'.mul_pow n
  rw [hkey, inv_pow, inv_mul_eq_one] at hcn
  have h1 : π (x ^ n) = π ((d * x * d⁻¹) ^ n) := by
    rw [map_pow, map_pow, hxπ]
    exact hcn
  have h2 := hinter (x ^ n) (pow_mem hx n) ((d * x * d⁻¹) ^ n) (pow_mem hy n) h1
  rw [map_pow, hxπ] at h2
  have h3 : orderOf xb ∣ n := orderOf_dvd_of_pow_eq_one h2
  rw [hxord] at h3
  exact hcodd h3

end Normalizes

end CFSG.ClassicalInvolution.Balance.LocalBalance
