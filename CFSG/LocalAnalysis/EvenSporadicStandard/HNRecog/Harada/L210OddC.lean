module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210QDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210OddA
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.L210OddB

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] [Finite G] {t z z₁ : G} {ι : Elem2 6 →* G} {zv : V6}
  {R0 F : Subgroup G} (h : Setting25 G t z z₁ ι zv R0 F)

private def gElt (t n : G) : G := n * t * n⁻¹ * t⁻¹

private lemma map_conj_closure_le {s : Set G} {m : G} {B : Subgroup G}
    (h : ∀ x ∈ s, m * x * m⁻¹ ∈ B) :
    (Subgroup.closure s).map (MulAut.conj m).toMonoidHom ≤ B := by
  rw [MonoidHom.map_closure]
  exact (Subgroup.closure_le B).mpr (by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using h x hx)

private lemma conj_mem_closure_of {s : Set G} {m : G} {B : Subgroup G}
    (h : ∀ x ∈ s, m * x * m⁻¹ ∈ B) {b : G} (hb : b ∈ Subgroup.closure s) :
    m * b * m⁻¹ ∈ B := by
  have hle := map_conj_closure_le (B := B) h
  have hmem : (MulAut.conj m).toMonoidHom b ∈ B :=
    hle (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
  simpa [MulAut.conj_apply] using hmem

private lemma inf_centralizer_t_eq_bot {U : Subgroup G}
    (hD2 : HData2 G t z z₁ ι zv R0 F)
    (hU : U ≤ Mgrp z) (hn : ∀ m ∈ Mgrp z, ∀ u ∈ U, m * u * m⁻¹ ∈ U)
    (hodd : Odd (Nat.card U)) :
    U ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ := by
  have hW : U ⊓ Subgroup.centralizer ({t} : Set G) ≤
      Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro w hw
    rw [Subgroup.mem_inf] at hw ⊢
    exact ⟨hw.2, hU hw.1⟩
  have hWn : ∀ c ∈ Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
      ∀ u ∈ U ⊓ Subgroup.centralizer ({t} : Set G),
        c * u * c⁻¹ ∈ U ⊓ Subgroup.centralizer ({t} : Set G) := by
    intro c hc u hu
    rw [Subgroup.mem_inf] at hc hu ⊢
    exact ⟨hn c hc.2 u hu.1, mul_mem (mul_mem hc.1 hu.2) (inv_mem hc.1)⟩
  have hWo : Odd (Nat.card (U ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G)) :=
    hodd.of_dvd_nat
      (Subgroup.card_dvd_of_le
        (inf_le_left : U ⊓ Subgroup.centralizer ({t} : Set G) ≤ U))
  exact eq_bot_of_odd_normal_centralizer hD2 hW hWn hWo

private lemma inf_centralizer_conj_t_eq_bot {U : Subgroup G} {n t' : G}
    (hUn : ∀ u ∈ U, n⁻¹ * u * n ∈ U)
    (h : U ⊓ Subgroup.centralizer ({t'} : Set G) = ⊥) :
    U ⊓ Subgroup.centralizer ({n * t' * n⁻¹} : Set G) = ⊥ := by
  have hmap : (U ⊓ Subgroup.centralizer ({n * t' * n⁻¹} : Set G)).map
      (MulAut.conj n⁻¹).toMonoidHom ≤ U ⊓ Subgroup.centralizer ({t'} : Set G) := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Subgroup.mem_inf] at hy ⊢
    refine ⟨?_, ?_⟩
    · simpa [MulAut.conj_apply, inv_inv] using hUn y hy.1
    · rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      show n⁻¹ * y * (n⁻¹)⁻¹ * t' = t' * (n⁻¹ * y * (n⁻¹)⁻¹)
      have hy' : y * (n * t' * n⁻¹) = (n * t' * n⁻¹) * y := hy.2
      calc n⁻¹ * y * (n⁻¹)⁻¹ * t'
          = n⁻¹ * y * (n * t' * n⁻¹) * n := by group
        _ = n⁻¹ * (y * (n * t' * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * t' * n⁻¹) * y) * n := by rw [hy']
        _ = t' * (n⁻¹ * y * (n⁻¹)⁻¹) := by group
  have hbot : (U ⊓ Subgroup.centralizer ({n * t' * n⁻¹} : Set G)).map
      (MulAut.conj n⁻¹).toMonoidHom = ⊥ :=
    le_bot_iff.mp (hmap.trans (le_of_eq h))
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := U ⊓ Subgroup.centralizer ({n * t' * n⁻¹} : Set G))
    (f := (MulAut.conj n⁻¹).toMonoidHom) (MulAut.conj n⁻¹).injective).mp hbot

theorem eq_bot_of_odd_normal_Mgrp (hzt : ¬ IsConj t z) (htz : IsConj t (t * z))
    (hirr : ∀ B : Subgroup G, B ≤ Rgrp h → z ∈ B →
      (∀ n ∈ normalizer (Rgrp h : Set G), ∀ b ∈ B, n * b * n⁻¹ ∈ B) →
        B = zpowers z ∨ B = Rgrp h)
    {U : Subgroup G} (hU : U ≤ Mgrp z) (hn : ∀ m ∈ Mgrp z, ∀ u ∈ U, m * u * m⁻¹ ∈ U)
    (hodd : Odd (Nat.card U)) : U = ⊥ := by
  have htM : t ∈ Mgrp z := Rgrp_le_Mgrp h (Setting25.t_mem_Rgrp h)
  have ht2 : t * t = 1 := by simpa [pow_two] using h.t_sq
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht2
  have hzord : orderOf z = 2 := orderOf_eq_prime h.z_sq h.z_ne_one
  have hbase : U ⊓ Subgroup.centralizer ({t} : Set G) = ⊥ :=
    inf_centralizer_t_eq_bot h.hD2 hU hn hodd
  have hg_cent : ∀ n ∈ normalizer (Rgrp h : Set G),
      gElt t n ∈ Subgroup.centralizer (U : Set G) := by
    intro n hnN
    have hnM : n ∈ Mgrp z := normalizer_Rgrp_le_Mgrp h hnN
    have hninvM : n⁻¹ ∈ Mgrp z := normalizer_Rgrp_le_Mgrp h (inv_mem hnN)
    have hUn : ∀ u ∈ U, n⁻¹ * u * n ∈ U := by
      intro u hu
      simpa using hn n⁻¹ hninvM u hu
    have hfix' : U ⊓ Subgroup.centralizer ({n * t * n⁻¹} : Set G) = ⊥ :=
      inf_centralizer_conj_t_eq_bot hUn hbase
    have ht'2 : (n * t * n⁻¹) * (n * t * n⁻¹) = 1 := by
      calc (n * t * n⁻¹) * (n * t * n⁻¹) = n * (t * t) * n⁻¹ := by group
        _ = n * 1 * n⁻¹ := by rw [ht2]
        _ = 1 := by group
    have hUn' : ∀ u ∈ U, (n * t * n⁻¹) * u * (n * t * n⁻¹)⁻¹ ∈ U := by
      intro u hu
      exact hn (n * t * n⁻¹) (mul_mem (mul_mem hnM htM) (inv_mem hnM)) u hu
    have hconj' : ∀ u ∈ U, (n * t * n⁻¹) * u * (n * t * n⁻¹)⁻¹ = u⁻¹ :=
      conj_eq_inv_of_inf_centralizer_eq_bot ht'2 hUn' hfix'
    have hUn_t : ∀ u ∈ U, t * u * t⁻¹ ∈ U := fun u hu => hn t htM u hu
    have hconj_t : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ :=
      conj_eq_inv_of_inf_centralizer_eq_bot ht2 hUn_t hbase
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hg_conj : gElt t n * u * (gElt t n)⁻¹ = u := by
      have ht_inv : t⁻¹ * u * t = u⁻¹ := by
        simpa [htinv] using hconj_t u hu
      simp only [gElt]
      calc (n * t * n⁻¹ * t⁻¹) * u * (n * t * n⁻¹ * t⁻¹)⁻¹
          = (n * t * n⁻¹) * (t⁻¹ * u * t) * (n * t * n⁻¹)⁻¹ := by group
        _ = (n * t * n⁻¹) * u⁻¹ * (n * t * n⁻¹)⁻¹ := by rw [ht_inv]
        _ = ((n * t * n⁻¹) * u * (n * t * n⁻¹)⁻¹)⁻¹ := by group
        _ = (u⁻¹)⁻¹ := by rw [hconj' u hu]
        _ = u := inv_inv u
    have hgu : gElt t n * u = u * gElt t n := by
      have h := congrArg (fun x => x * gElt t n) hg_conj
      calc gElt t n * u = (gElt t n * u * (gElt t n)⁻¹) * gElt t n := by group
        _ = u * gElt t n := h
    exact hgu.symm
  let S : Set G := {x | (∃ n ∈ normalizer (Rgrp h : Set G), x = gElt t n) ∨ x = z}
  have hSmem : ∀ x : G, x ∈ S ↔
      (∃ n ∈ normalizer (Rgrp h : Set G), x = gElt t n) ∨ x = z := fun x => Iff.rfl
  have hgen_mem : ∀ n ∈ normalizer (Rgrp h : Set G), gElt t n ∈ Subgroup.closure S :=
    fun n hnN => Subgroup.subset_closure (Or.inl ⟨n, hnN, rfl⟩)
  have hzS : z ∈ Subgroup.closure S := Subgroup.subset_closure (Or.inr rfl)
  have hBS_le_R : Subgroup.closure S ≤ Rgrp h := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [hSmem x] at hx
    rcases hx with ⟨n, hnN, hxn⟩ | hxz
    · rw [hxn]
      have hntn : n * t * n⁻¹ ∈ Rgrp h :=
        (Subgroup.mem_set_normalizer_iff.mp hnN t).mp (Setting25.t_mem_Rgrp h)
      exact mul_mem hntn (inv_mem (Setting25.t_mem_Rgrp h))
    · rw [hxz]
      exact z_mem_Rgrp h
  have hBS_inv : ∀ m ∈ normalizer (Rgrp h : Set G), ∀ b ∈ Subgroup.closure S,
      m * b * m⁻¹ ∈ Subgroup.closure S := by
    intro m hmN b hb
    have hgen : ∀ x ∈ S, m * x * m⁻¹ ∈ Subgroup.closure S := by
      intro x hx
      rw [hSmem x] at hx
      rcases hx with ⟨n, hnN, hxn⟩ | hxz
      · rw [hxn]
        have hmn : m * n ∈ normalizer (Rgrp h : Set G) := mul_mem hmN hnN
        have hid : m * gElt t n * m⁻¹ = gElt t (m * n) * (gElt t m)⁻¹ := by
          simp only [gElt]; group
        rw [hid]
        exact mul_mem (hgen_mem (m * n) hmn) (inv_mem (hgen_mem m hmN))
      · rw [hxz, conj_z_of_mem_normalizer_Rgrp h hmN]
        exact hzS
    exact conj_mem_closure_of hgen hb
  have hBS_ne : Subgroup.closure S ≠ zpowers z := by
    intro hBSz
    let Vg : Subgroup G := Subgroup.closure ({t, z} : Set G)
    have hVgmem : ∀ x : G, x ∈ ({t, z} : Set G) ↔ x = t ∨ x = z := fun x => by simp
    have htVg : t ∈ Vg := Subgroup.subset_closure (by simp)
    have hzVg : z ∈ Vg := Subgroup.subset_closure (by simp)
    have hVg_le_R : Vg ≤ Rgrp h := by
      change Subgroup.closure ({t, z} : Set G) ≤ Rgrp h
      rw [Subgroup.closure_le]
      intro x hx
      rw [hVgmem x] at hx
      rcases hx with hxt | hxz
      · rw [hxt]; exact Setting25.t_mem_Rgrp h
      · rw [hxz]; exact z_mem_Rgrp h
    have hzp_le_Vg : Subgroup.zpowers z ≤ Vg := Subgroup.zpowers_le.mpr hzVg
    have hVg_inv : ∀ m ∈ normalizer (Rgrp h : Set G), ∀ b ∈ Vg, m * b * m⁻¹ ∈ Vg := by
      intro m hmN b hb
      have hgen : ∀ x ∈ ({t, z} : Set G), m * x * m⁻¹ ∈ Vg := by
        intro x hx
        rw [hVgmem x] at hx
        rcases hx with hxt | hxz
        · rw [hxt]
          have hgm : gElt t m ∈ Subgroup.zpowers z := by
            rw [← hBSz]; exact hgen_mem m hmN
          have hid : m * t * m⁻¹ = gElt t m * t := by simp only [gElt]; group
          rw [hid]
          exact mul_mem (hzp_le_Vg hgm) htVg
        · rw [hxz, conj_z_of_mem_normalizer_Rgrp h hmN]
          exact hzVg
      exact conj_mem_closure_of hgen hb
    rcases hirr Vg hVg_le_R hzVg hVg_inv with hVgz | hVgR
    · have ht_zp : t ∈ Subgroup.zpowers z := hVgz ▸ htVg
      rcases Subgroup.mem_zpowers_iff.mp ht_zp with ⟨k, hk⟩
      rw [← zpow_mod_orderOf z k, hzord] at hk
      norm_num only [Nat.cast_ofNat] at hk
      rcases Int.emod_two_eq_zero_or_one k with hk2 | hk2
      · rw [hk2] at hk
        simp at hk
        have ht1 : t = 1 := hk.symm
        have h1 : IsConj (1 : G) z := by simpa [ht1] using htz
        exact h.z_ne_one (isConj_one_right.mp h1)
      · rw [hk2] at hk
        have htz_eq : t = z := by simpa only [zpow_one] using hk.symm
        exact hzt (by simpa [htz_eq] using IsConj.refl z)
    · have habel : IsMulCommutative Vg := by
        change IsMulCommutative (Subgroup.closure ({t, z} : Set G))
        exact Subgroup.isMulCommutative_closure (by
          intro a ha b hb hab
          rw [hVgmem a] at ha
          rw [hVgmem b] at hb
          rcases ha with hat | haz <;> rcases hb with hbt | hbz
          · exact absurd (hat.trans hbt.symm) hab
          · rw [hat, hbz]; exact h.t_mul_z_comm
          · rw [haz, hbt]; exact h.t_mul_z_comm.symm
          · exact absurd (haz.trans hbz.symm) hab)
      have hR_le_cent : Rgrp h ≤ Subgroup.centralizer (Rgrp h : Set G) := by
        rw [← hVgR]
        exact Subgroup.le_centralizer Vg
      have hcard : Nat.card (Rgrp h) ≤ Nat.card (Subgroup.centralizer (Rgrp h : Set G)) :=
        Subgroup.card_le_of_le hR_le_cent
      rw [centralizer_Rgrp_eq h, Nat.card_zpowers, hzord, card_Rgrp h] at hcard
      norm_num at hcard
  have hBS_eq_R : Subgroup.closure S = Rgrp h := by
    rcases hirr (Subgroup.closure S) hBS_le_R hzS hBS_inv with hBSz | hBSR
    · exact absurd hBSz hBS_ne
    · exact hBSR
  have hU_le_zp : U ≤ Subgroup.zpowers z := by
    have hU_le_cB : U ≤ Subgroup.centralizer (Subgroup.closure S : Set G) := by
      rw [Subgroup.le_centralizer_iff]
      rw [Subgroup.closure_le]
      intro x hx
      rw [hSmem x] at hx
      rcases hx with ⟨n, hnN, hxn⟩ | hxz
      · rw [hxn]; exact hg_cent n hnN
      · rw [hxz]
        exact Subgroup.mem_centralizer_iff.mpr
          (fun u hu => Subgroup.mem_centralizer_singleton_iff.mp (hU hu))
    rw [hBS_eq_R, centralizer_Rgrp_eq h] at hU_le_cB
    exact hU_le_cB
  have hcardU : Nat.card U ≤ 2 := by
    have h := Subgroup.card_le_of_le hU_le_zp
    rwa [Nat.card_zpowers, hzord] at h
  obtain ⟨k, hk⟩ := hodd
  have hUcard : Nat.card U = 1 := by omega
  exact Subgroup.eq_bot_of_card_eq U hUcard

end CFSG.EvenSporadicStandard.HNRecog.Harada
