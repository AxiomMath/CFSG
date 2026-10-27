module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P6Tail1

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6

open Subgroup CFSG.Open
open CFSG.LocalAnalysis.EvenBN.Tits.N

variable {G : Type} [Group G] [Finite G]
variable (d : Data G)

@[expose] noncomputable def alphaJp (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) :
    ↥(Jp d) →* MulAut ↥(Ws d) :=
  (alphaHom d hW).comp (Subgroup.inclusion (Jp_le_Hg d))

theorem alphaJp_apply (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) (g : ↥(Jp d)) :
    alphaJp d hW g = alpha d (g : G) := rfl

theorem card_range_dvd (z₀ : G) (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (h19 : img d (Wg d z₀) = Ws d) (hWab : IsElemAbelian 2 (Ws d)) :
    Nat.card (alphaJp d hW).range ∣ (Wg d z₀).relIndex (Jp d) := by
  have hle : (Wg d z₀).subgroupOf (Jp d) ≤ (alphaJp d hW).ker := fun g hg =>
    (alphaJp d hW).mem_ker.2 (alpha_eq_one_of_mem_Wg d z₀ h19 hWab (Subgroup.mem_subgroupOf.1 hg))
  have h1 := Subgroup.index_dvd_of_le hle
  rwa [Subgroup.index_ker] at h1

theorem range_conj_mem (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) {i l : MulAut ↥(Ws d)}
    (hi : i ∈ Ialpha d) (hl : l ∈ (alphaJp d hW).range) : i * l * i⁻¹ ∈ (alphaJp d hW).range := by
  obtain ⟨h, hh, rfl⟩ := exists_alpha_eq_of_mem_Ialpha d hi
  obtain ⟨x, rfl⟩ := hl
  have hxH := Jp_le_Hg d x.2
  refine ⟨⟨h * (x : G) * h⁻¹, Jp_conj_mem d hh x.2⟩, ?_⟩
  rw [alphaJp_apply]
  exact alpha_conj hh hxH (star_mem_normalizer_Ws d hW hh) (star_mem_normalizer_Ws d hW hxH)

theorem Ja_le_range (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d) (hX : Xg d ≤ Hg d) :
    Ja d ≤ (alphaJp d hW).range := by
  have hnormal : ((alphaJp d hW).range.subgroupOf (Ialpha d)).Normal :=
    ⟨fun l hl i => Subgroup.mem_subgroupOf.2
      (range_conj_mem d hW i.2 (Subgroup.mem_subgroupOf.1 hl))⟩
  have h1 : Subgroup.normalClosure (((Alpha d (Xg d)).subgroupOf (Ialpha d) :
      Subgroup ↥(Ialpha d)) : Set ↥(Ialpha d)) ≤ (alphaJp d hW).range.subgroupOf (Ialpha d) := by
    refine Subgroup.normalClosure_le_normal fun σ hσ => Subgroup.mem_subgroupOf.2 ?_
    obtain ⟨k, hk, hkH, hkσ⟩ := (mem_Alpha_iff d hW).1 (Subgroup.mem_subgroupOf.1 hσ)
    refine ⟨⟨k, Jg_le_Jp d (Xg_le_Jg d hX hk)⟩, ?_⟩
    rw [alphaJp_apply]
    exact hkσ
  intro σ hσ
  obtain ⟨σ', hσ', rfl⟩ := hσ
  exact Subgroup.mem_subgroupOf.1 (h1 hσ')

theorem nine_dvd_card_range (z₀ : G) (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (h19 : img d (Wg d z₀) = Ws d) (hWab : IsElemAbelian 2 (Ws d)) (hX : Xg d ≤ Hg d)
    (h360 : (Wg d z₀).relIndex (Jp d) = 360)
    (hdich : Nonempty (↥(Ja d) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(Ja d) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5))) :
    9 ∣ Nat.card (alphaJp d hW).range := by
  have hJa : Nat.card (Ja d) ∣ Nat.card (alphaJp d hW).range :=
    Subgroup.card_dvd_of_le (Ja_le_range d hW hX)
  have hdvd : Nat.card (alphaJp d hW).range ∣ 360 := h360 ▸ card_range_dvd d z₀ hW h19 hWab
  rcases hdich with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have h1 : Nat.card (Ja d) = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    rw [h1] at hJa
    exact (show 9 ∣ 360 by norm_num).trans hJa
  · exfalso
    have h1 : Nat.card (Ja d) = 25 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    rw [h1] at hJa
    have := hJa.trans hdvd
    norm_num at this

theorem exists_three_element_C (z₀ : G) (hW : ∀ h ∈ Hs d, ∀ w ∈ Ws d, h * w * h⁻¹ ∈ Ws d)
    (hN : ((H0 d z₀).subgroupOf (Hg d)).Normal) (hZV : Zz d z₀ ≤ d.s56V)
    (hJ : Jg d ≤ H0 d z₀) (h19 : img d (Wg d z₀) = Ws d) (hWab : IsElemAbelian 2 (Ws d))
    (hX : Xg d ≤ Hg d) (h360 : (Wg d z₀).relIndex (Jp d) = 360)
    (hdich : Nonempty (↥(Ja d) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (↥(Ja d) ≃* Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))
    (hE1 : Nat.card (Ialpha d) ∣ 2 ^ 5 * 3 ^ 2 * 5 ^ 2) {y : G} (hyH : y ∈ Hg d)
    (hy3 : IsPGroup 3 (zpowers y)) (hyH0 : y ∉ H0 d z₀) :
    ∃ o : G, o ∈ Hg d ∧ IsPGroup 3 (zpowers o) ∧ o ∉ H0 d z₀ ∧
      star d o ∈ centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) := by
  have h9 := nine_dvd_card_range d z₀ hW h19 hWab hX h360 hdich
  have hJp0 : Jp d ≤ H0 d z₀ := Jp_le_H0 d z₀ hZV hJ
  have hyI : alpha d y ∈ Ialpha d := alpha_mem_Ialpha d hW hyH
  obtain ⟨b, hb⟩ := hy3 ⟨y, mem_zpowers y⟩
  have hyb : y ^ 3 ^ b = 1 := congrArg Subtype.val hb
  have hαy3 : IsPGroup 3 (zpowers (alpha d y)) := by
    refine IsPGroup.of_card_dvd_pow (n := b) ?_
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    have h1 : alpha d y ^ 3 ^ b = alphaHom d hW (⟨y, hyH⟩ ^ 3 ^ b) := by rw [map_pow]; rfl
    have h2 : (⟨y, hyH⟩ : ↥(Hg d)) ^ 3 ^ b = 1 := Subtype.ext hyb
    rw [h1, h2, map_one]
  have hΛI : (alphaJp d hW).range ≤ Ialpha d := by
    rintro _ ⟨x, rfl⟩
    exact alpha_mem_Ialpha d hW (Jp_le_Hg d x.2)
  have hyΛ : alpha d y ∈ (alphaJp d hW).range :=
    mem_of_isPGroup_three_of_card hΛI (fun i hi l hl => range_conj_mem d hW hi hl) h9 hE1 hyI hαy3
  obtain ⟨x, hx⟩ := hyΛ
  have hjJ : (x : G) ∈ Jp d := x.2
  have hjH0 : (x : G) ∈ H0 d z₀ := hJp0 hjJ
  have hjH : (x : G) ∈ Hg d := Jp_le_Hg d hjJ
  have hαj : alpha d (x : G) = alpha d y := hx
  have hcH : (x : G)⁻¹ * y ∈ Hg d := mul_mem (inv_mem hjH) hyH
  have hαc : alpha d ((x : G)⁻¹ * y) = 1 := by
    have e : alpha d ((x : G)⁻¹ * y) = (alpha d (x : G))⁻¹ * alpha d y := by
      have := map_mul (alphaHom d hW) (⟨(x : G), hjH⟩⁻¹) ⟨y, hyH⟩
      rw [map_inv] at this
      exact this
    rw [e, hαj, inv_mul_cancel]
  have hcC : star d ((x : G)⁻¹ * y) ∈
      centralizer ((Ws d : Subgroup (MulAut ↥d.s56V)) : Set (MulAut ↥d.s56V)) :=
    (actFun_eq_one_iff (Ws d) (star_mem_normalizer_Ws d hW hcH)).1 hαc
  haveI := hN
  obtain ⟨m, e, hm3, hcm, hcmK⟩ := exists_isPGroup_three_not_mem (K := H0 d z₀) (H := Hg d) hyH
    inf_le_left hjH0 hy3 hyH0
  refine ⟨((x : G)⁻¹ * y) ^ m, pow_mem hcH m, ?_, hcmK, ?_⟩
  · refine IsPGroup.of_card_dvd_pow (n := e) ?_
    rw [Nat.card_zpowers]
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← pow_mul]
    exact hcm
  · show actFun d.s56V (((x : G)⁻¹ * y) ^ m) ∈ _
    rw [actFun_pow d.s56V hcH m]
    exact pow_mem hcC m

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6
