module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCard
import CFSG.Mathlib.GroupTheory.PermCommute
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3Model

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

theorem isNonsplitDoubleCoverOfS5_inf_Gx {G : Type} [Group G] {y c : G} (hy : y * y = 1)
    (hc : c * c = 1) (hx : orderOf (y * c) = 5) (hX : IsShapeCentralizerFiveC ↥(Gx (y * c)))
    (hS : Nat.card ↥(Gx y ⊓ Gx c) = 240) : IsNonsplitDoubleCoverOfS5 ↥(Gx y ⊓ Gx c) := by
  have hXcard : Nat.card ↥(Gx (y * c)) = 1200 := IsShapeCentralizerFiveC.card_eq hX
  obtain ⟨Y, hYgrp, hYns, ⟨e⟩⟩ := hX
  letI : Group Y := hYgrp
  set S : Subgroup G := Gx y ⊓ Gx c with hSdef
  have hScard : Nat.card ↥S = 240 := by rw [hSdef]; exact hS
  haveI : Finite ↥(Gx (y * c)) := Nat.finite_of_card_ne_zero (by rw [hXcard]; norm_num)
  have hYcard : Nat.card Y = 240 := by
    have he : Nat.card ↥(Gx (y * c)) = Nat.card (Multiplicative (ZMod 5) × Y) :=
      Nat.card_congr e.toEquiv
    rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] at he
    omega
  haveI : Finite Y := Nat.finite_of_card_ne_zero (by rw [hYcard]; norm_num)
  have hSX : S ≤ Gx (y * c) := by
    intro s hs
    rw [hSdef, Subgroup.mem_inf] at hs
    obtain ⟨hsy, hsc⟩ := hs
    rw [mem_Gx] at hsy hsc ⊢
    calc (y * c) * s = y * (c * s) := by group
      _ = y * (s * c) := by rw [hsc]
      _ = y * s * c := by group
      _ = s * y * c := by rw [hsy]
      _ = s * (y * c) := by group
  let x' : ↥(Gx (y * c)) := GxSelf (y * c)
  have hx'cen : ∀ w : ↥(Gx (y * c)), x' * w = w * x' := by
    intro w
    apply Subtype.ext
    simpa [x', GxSelf] using mem_Gx.mp w.2
  have hecen : ∀ w : ↥(Gx (y * c)), e x' * e w = e w * e x' := by
    intro w
    rw [← map_mul, ← map_mul, hx'cen w]
  let π : ↥(Gx (y * c)) →* Y :=
    (MonoidHom.snd (Multiplicative (ZMod 5)) Y).comp e.toMonoidHom
  let γ : Y := π x'
  have hγcen : ∀ g : Y, γ * g = g * γ := by
    intro g
    have h := hecen (e.symm (1, g))
    have h2 : e x' * (1, g) = (1, g) * e x' := by simpa using h
    have h3 := congrArg Prod.snd h2
    change (e x').2 * g = g * (e x').2
    simpa [Prod.snd_mul] using h3
  have hYnsKeep : IsNonsplitDoubleCoverOfS5 Y := hYns
  obtain ⟨Z, hZn, hZcard, ⟨isoQ⟩, hnsplit⟩ := hYns
  haveI : Z.Normal := hZn
  let q : Y →* Y ⧸ Z := QuotientGroup.mk' Z
  let φ : Y →* Equiv.Perm (Fin 5) := isoQ.toMonoidHom.comp q
  have hφcen : ∀ g : Y, φ γ * φ g = φ g * φ γ := by
    intro g
    rw [← map_mul, ← map_mul, hγcen g]
  have hφsurj : Function.Surjective φ := by
    intro σ
    obtain ⟨w, hw⟩ := isoQ.surjective σ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z w
    exact ⟨g, by simpa [φ, q] using hw⟩
  have hφγ : φ γ = 1 := CFSG.perm_eq_one_of_forall_commute (by simp) fun σ => by
    obtain ⟨g, rfl⟩ := hφsurj σ
    exact hφcen g
  have hγZ : γ ∈ Z := by
    have hq : q γ = 1 := isoQ.injective (hφγ.trans (map_one isoQ).symm)
    have : (γ : Y ⧸ Z) = 1 := by simpa [q] using hq
    exact (QuotientGroup.eq_one_iff γ).mp this
  have hx5 : (y * c) ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one (y * c)
  have hx'5 : x' ^ 5 = 1 := by
    apply Subtype.ext
    simpa [x', GxSelf, hx5]
  have hγ5 : γ ^ 5 = 1 := by
    change (π x') ^ 5 = 1
    rw [← map_pow, hx'5, map_one]
  have hγ1 : γ = 1 := by
    have h2 : orderOf γ ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard Z hγZ
      rwa [hZcard] at this
    have h5 : orderOf γ ∣ 5 := orderOf_dvd_iff_pow_eq_one.mpr hγ5
    have h1 : orderOf γ ∣ 1 := by
      have := Nat.dvd_gcd h2 h5
      rwa [show Nat.gcd 2 5 = 1 by norm_num] at this
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hπsurj : Function.Surjective π := by
    intro g
    exact ⟨e.symm (1, g), by simp [π]⟩
  have hπx' : π x' = 1 := hγ1
  have hkercard : Nat.card π.ker = 5 := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := π) hπsurj
    rw [hYcard, hXcard] at h
    omega
  have hx'ord : orderOf x' = 5 := by
    change orderOf (GxSelf (y * c)) = 5
    exact (Subgroup.orderOf_mk (y * c) (self_mem_Gx (y * c))).trans hx
  have hzpcard : Nat.card (Subgroup.zpowers x') = 5 := by
    rw [Nat.card_zpowers, hx'ord]
  have hker_eq : Subgroup.zpowers x' = π.ker := by
    apply Subgroup.eq_of_le_of_card_ge
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]; exact hπx'
    · rw [hkercard, hzpcard]
  have hmap : (Subgroup.zpowers x').map (Gx (y * c)).subtype = Subgroup.zpowers (y * c) := by
    rw [MonoidHom.map_zpowers]; rfl
  have hSx_bot : S ⊓ Subgroup.zpowers (y * c) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    rw [Subgroup.mem_inf] at hs
    obtain ⟨hsS, hszp⟩ := hs
    rw [hSdef, Subgroup.mem_inf] at hsS
    obtain ⟨hsy, hsc⟩ := hsS
    rw [mem_Gx] at hsy
    have hys : y * s * y⁻¹ = s := by rw [hsy]; group
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hszp
    have hyinv : y⁻¹ = y := mul_eq_one_iff_inv_eq.mp hy
    have hcinv : c⁻¹ = c := mul_eq_one_iff_inv_eq.mp hc
    have hyx : y * (y * c) * y⁻¹ = (y * c)⁻¹ := by
      rw [mul_inv_rev, hyinv, hcinv]
      rw [show y * (y * c) * y = y * y * c * y from by group, hy, one_mul]
    have hsi : s = s⁻¹ := by
      have h2 : y * s * y⁻¹ = ((y * c) ^ i)⁻¹ := by
        rw [← hi, ← conj_zpow, hyx, inv_zpow]
      calc s = y * s * y⁻¹ := hys.symm
        _ = ((y * c) ^ i)⁻¹ := h2
        _ = s⁻¹ := by rw [hi]
    have hss : s * s = 1 := mul_eq_one_iff_eq_inv.mpr hsi
    refine orderOf_eq_one_iff.mp (Nat.dvd_one.mp ?_)
    have h2 : orderOf s ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hss
    have h5 : orderOf s ∣ 5 := by
      have := orderOf_dvd_of_mem_zpowers hszp
      rwa [hx] at this
    have h1 : orderOf s ∣ 1 := by
      have := Nat.dvd_gcd h2 h5
      rwa [show Nat.gcd 2 5 = 1 by norm_num] at this
    exact h1
  have hker : (π.comp (Subgroup.inclusion hSX)).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hmem : Subgroup.inclusion hSX s ∈ π.ker := hs
    rw [← hker_eq] at hmem
    have hmemG : (s : G) ∈ Subgroup.zpowers (y * c) := by
      rw [← hmap]
      simpa using Subgroup.mem_map_of_mem (Gx (y * c)).subtype hmem
    have hmemS : (s : G) ∈ S := s.2
    have hbot : (s : G) ∈ (⊥ : Subgroup G) := by
      rw [← hSx_bot]
      exact ⟨hmemS, hmemG⟩
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext hbot
  have hinj : Function.Injective (π.comp (Subgroup.inclusion hSX)) :=
    (MonoidHom.ker_eq_bot_iff _).mp hker
  have hbij : Function.Bijective (π.comp (Subgroup.inclusion hSX)) :=
    hinj.bijective_of_nat_card_le (by rw [hYcard, hScard])
  let e' : ↥S ≃* Y := MulEquiv.ofBijective (π.comp (Subgroup.inclusion hSX)) hbij
  have hfinal : IsNonsplitDoubleCoverOfS5 ↥S :=
    IsNonsplitDoubleCoverOfS5.of_mulEquiv e'.symm hYnsKeep
  rwa [hSdef] at hfinal

end CFSG.EvenSporadicStandard.HNRecog.Section3Model
