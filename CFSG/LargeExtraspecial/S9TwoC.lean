module

public import CFSG.LargeExtraspecial.S8CorB
public import CFSG.LargeExtraspecial.S5Five
public import CFSG.LargeExtraspecial.S6ThreeC

public section

namespace CFSG.LargeExtraspecial.S9

open Subgroup CFSG.Open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

theorem exists_normal_odd_of_isolated {X : Type u} [Group X] [Finite X] {t : X} (ht1 : t ≠ 1)
    (htt : t * t = 1)
    (hiso : ∀ y : X, (y * t * y⁻¹) * t = t * (y * t * y⁻¹) → y * t * y⁻¹ = t) :
    ∃ K : Subgroup X, K.Normal ∧ Odd (Nat.card K) ∧ ∀ y : X, y * t * y⁻¹ * t⁻¹ ∈ K := by
  set e : Shrink.{0} X ≃* X := Shrink.mulEquiv with he
  have : Fintype (Shrink.{0} X) := Fintype.ofFinite _
  set t' : Shrink.{0} X := e.symm t with ht'
  have het : e t' = t := e.apply_symm_apply t
  have ht'1 : t' ≠ 1 := fun h => ht1 (by rw [← het, h, map_one])
  have ht'2 : t' * t' = 1 := e.injective (by rw [map_mul, het, htt, map_one])
  have hiso' : ∀ y : Shrink.{0} X, (y * t' * y⁻¹) * t' = t' * (y * t' * y⁻¹) →
      y * t' * y⁻¹ = t' := by
    intro y hy
    apply e.injective
    have h1 := congrArg e hy
    simp only [map_mul, map_inv, het] at h1
    have h2 := hiso (e y) h1
    simpa only [map_mul, map_inv, het] using h2
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar (Shrink.{0} X) t' ht'1 ht'2 hiso'
  refine ⟨N.map (e : Shrink.{0} X →* X), hN.map _ e.surjective, ?_, fun y => ?_⟩
  · rw [card_map_of_injective e.injective]
    exact hNodd
  · have h := mem_map_of_mem (e : Shrink.{0} X →* X) (hNt (e.symm y))
    simpa only [MonoidHom.coe_ofClass, map_mul, map_inv, het, MulEquiv.apply_symm_apply] using h

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem N0bar_le_zpowers_of_isolated (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hn : 4 < S.width) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hiso : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t) :
    N0bar S g t ≤ zpowers t := by
  have haQ := H.conj_mem
  have htt : t * t = 1 := mul_self_of_mem_Lbar S haQ ht
  have htM : t ∈ S.Mbar := S.Lbar_le_Mbar g ht
  set tX : S.Mbar := ⟨t, htM⟩ with htX
  have hisoX : ∀ y : S.Mbar, (y * tX * y⁻¹) * tX = tX * (y * tX * y⁻¹) →
      y * tX * y⁻¹ = tX := by
    intro y hy
    apply Subtype.ext
    exact hiso y y.2 (congrArg Subtype.val hy)
  have htX1 : tX ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have htXX : tX * tX = 1 := Subtype.ext htt
  obtain ⟨K, hKN, hKodd, hK⟩ := exists_normal_odd_of_isolated htX1 htXX hisoX
  have hKO : K ≤ timmesfeldOddCore S.Mbar := le_sSup ⟨hKN, hKodd⟩
  have hO3 := S5.card_oddCore_dvd_three H hNo C hn
  have hOn' := S5.timmesfeldOddCore_normal S.Mbar
  refine S8.le_zpowers_of_conj_mem (X := S.Mbar) (O := (timmesfeldOddCore S.Mbar).map
    S.Mbar.subtype) (L := S.Lbar g) (R := Rbar S g t) (N := N0bar S g t) htM htt ht1
    (fun P hP h2 => S5.eq_bot_of_isSubnormal_Mbar S hP h2) (map_subtype_le _) ?_ ?_ ?_
    (S.Lbar_le_Mbar g) (fun a ha b hb => Lbar_comm S haQ ha hb)
    (fun l hl => mul_self_of_mem_Lbar S haQ hl) ht ?_ ?_ (N0bar_le_Nbar.trans Nbar_le_Rbar) ?_
    (isPGroup_N0bar H ht) (Lbar_inf_Nbar_le_N0bar (mem_inf.mpr ⟨ht, self_mem_Nbar H ht⟩))
  · intro x hx o' ho'
    obtain ⟨o, ho, ho'o⟩ := Subgroup.mem_map.mp ho'
    have h1 : (⟨x, hx⟩ : S.Mbar) * o * (⟨x, hx⟩ : S.Mbar)⁻¹ ∈ timmesfeldOddCore S.Mbar :=
      hOn'.conj_mem o ho _
    have h2 := Subgroup.mem_map_of_mem S.Mbar.subtype h1
    rw [map_mul, map_mul, map_inv, ho'o] at h2
    exact h2
  · rw [Subgroup.card_map_of_injective S.Mbar.subtype_injective]
    exact hO3
  · intro x hx
    have h1 : (⟨x, hx⟩ : S.Mbar) * tX * (⟨x, hx⟩ : S.Mbar)⁻¹ ∈
        timmesfeldOddCore S.Mbar ⊔ zpowers tX := by
      have hc := hKO (hK ⟨x, hx⟩)
      have e : (⟨x, hx⟩ : S.Mbar) * tX * (⟨x, hx⟩ : S.Mbar)⁻¹ =
          ((⟨x, hx⟩ : S.Mbar) * tX * (⟨x, hx⟩ : S.Mbar)⁻¹ * tX⁻¹) * tX := by group
      rw [e]
      exact mul_mem (mem_sup_left hc) (mem_sup_right (mem_zpowers tX))
    have h2 := Subgroup.mem_map_of_mem S.Mbar.subtype h1
    rw [Subgroup.map_sup, MonoidHom.map_zpowers] at h2
    simpa only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk,
      map_mul, map_inv] using h2
  · refine sSup_le fun Z hZ => ?_
    obtain ⟨h, rfl, htZ⟩ := mem_Dset.mp hZ
    exact le_sSup ⟨S.ρ h, ⟨h, rfl⟩, Lbar_mul S h g, (Lbar_mul S h g) ▸ htZ⟩
  · rintro x ⟨h, rfl⟩ htZ
    rw [← Lbar_mul S h g] at htZ ⊢
    exact Lbar_mul_le_Rbar htZ
  · intro r hr n hn
    exact conj_mem_N0bar haQ hr hn

theorem Lbar_inf_Nbar_eq_zpowers_of_isolated (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
    (hn : 4 < S.width) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hiso : ∀ x ∈ S.Mbar, x * t * x⁻¹ * t = t * (x * t * x⁻¹) → x * t * x⁻¹ = t) :
    S.Lbar g ⊓ Nbar S g t = zpowers t :=
  le_antisymm (Lbar_inf_Nbar_le_N0bar.trans (N0bar_le_zpowers_of_isolated H hNo C hn ht ht1 hiso))
    ((zpowers_le).mpr (mem_inf.mpr ⟨ht, self_mem_Nbar H ht⟩))

end CFSG.LargeExtraspecial.S9
