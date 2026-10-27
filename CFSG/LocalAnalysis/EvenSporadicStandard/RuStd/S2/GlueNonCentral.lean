module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.Cen
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueThree

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem t_noncentral_of (hc : Config G L t) (hF : RuFacts L) (h3 : RuThreeFacts L)
    (hZ : center M10 = ⊥) {r : G} (hrL : r ∈ L) (hr3 : orderOf r = 3) :
    (QuotientGroup.mk (tCen hc hrL) : CenG r ⧸ CFSG.oddCore (CenG r)) ∉
      center (CenG r ⧸ CFSG.oddCore (CenG r)) := by
  intro hcen
  have hrL3 : orderOf (⟨r, hrL⟩ : L) = 3 := by rw [Subgroup.orderOf_mk]; exact hr3
  obtain ⟨v, hvC, hv2, hvA⟩ := h3.inv2A ⟨r, hrL⟩ hrL3
  obtain ⟨g, hg⟩ := isConj_iff.1 (hc.isConj_mul_of_classA hF hv2 hvA)
  have hvr : (v : G) * r = r * (v : G) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 hvC)
  have hrt : r * t = t * r := hc.comm r hrL
  have htvr : (t * (v : G)) * r = r * (t * (v : G)) := by
    calc t * (v : G) * r = t * ((v : G) * r) := mul_assoc _ _ _
      _ = t * (r * (v : G)) := by rw [hvr]
      _ = (t * r) * (v : G) := (mul_assoc _ _ _).symm
      _ = (r * t) * (v : G) := by rw [hrt]
      _ = r * (t * (v : G)) := mul_assoc _ _ _
  set O := CFSG.oddCore (CenG r) with hO
  let τ₁ : CenG r := tCen hc hrL
  let τ₂ : CenG r := ⟨t * (v : G), mem_centralizer_singleton_iff.2 htvr⟩
  let vX : CenG r := ⟨(v : G), mem_centralizer_singleton_iff.2 hvr⟩
  have hgtv : (g * t * g⁻¹) * r = r * (g * t * g⁻¹) := by rw [hg]; exact htvr
  have hr't : (g⁻¹ * r * g) * t = t * (g⁻¹ * r * g) := by
    calc (g⁻¹ * r * g) * t = g⁻¹ * (r * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * r) * g := by rw [hgtv]
      _ = t * (g⁻¹ * r * g) := by group
  have hr'3 : orderOf (g⁻¹ * r * g) = 3 := by
    rw [← hr3]
    exact SemiconjBy.orderOf_eq g (show SemiconjBy g (g⁻¹ * r * g) r by
      simp [SemiconjBy, mul_assoc])
  have hr'L : g⁻¹ * r * g ∈ L := mem_of_odd_orderOf hc hr't (by rw [hr'3]; decide)
  have hr'L3 : orderOf (⟨g⁻¹ * r * g, hr'L⟩ : L) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hr'3
  have hn₁ : Nat.card (centralizer ({τ₁} : Set (CenG r))) = 3 * 1440 := by
    have h := card_cenT hc hrL
    rw [h3.card ⟨r, hrL⟩ hrL3] at h
    exact h.trans (by norm_num)
  have hn₂ : Nat.card (centralizer ({τ₂} : Set (CenG r))) = 3 * 1440 := by
    have e1 : Nat.card (centralizer ({τ₂} : Set (CenG r))) =
        Nat.card (centralizer ({r, t * (v : G)} : Set G)) := by
      rw [card_cen_eq, centralizer_pair_eq_inf]
    have e2 : Nat.card (centralizer ({g⁻¹ * r * g, t} : Set G)) =
        Nat.card (centralizer ({tCen hc hr'L} : Set (CenG (g⁻¹ * r * g)))) := by
      rw [card_cen_eq, centralizer_pair_eq_inf]
      rfl
    have e3 : Nat.card (centralizer ({r, t * (v : G)} : Set G)) =
        Nat.card (centralizer ({g⁻¹ * r * g, t} : Set G)) := by
      have h := card_centralizer_conj_image g ({g⁻¹ * r * g, t} : Set G)
      rw [Set.image_pair] at h
      have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
      rw [e, hg] at h
      exact h
    have e4 := card_cenT hc hr'L
    rw [h3.card ⟨g⁻¹ * r * g, hr'L⟩ hr'L3] at e4
    rw [e1, e3, e2]
    exact e4.trans (by norm_num)
  have hρO : rCen r ∈ O := rCen_mem_oddCore hr3
  have hodd : ∀ x ∈ O, Odd (orderOf x) := fun x hx => odd_orderOf_of_mem_oddCore hx
  have hρ3 : orderOf (rCen r) = 3 := by rw [orderOf_rCen]; exact hr3
  have hO₁ : ∀ x ∈ O, x * τ₁ = τ₁ * x → x ∈ zpowers (rCen r) := by
    intro x hx hxτ
    refine cen_odd_of hc h3 hrL hr3 x hx ?_
    calc tCen hc hrL * x * (tCen hc hrL)⁻¹ = (x * tCen hc hrL) * (tCen hc hrL)⁻¹ := by
          rw [hxτ]
      _ = x := by group
  have hO₂ : ∀ x ∈ O, x * τ₂ = τ₂ * x → x ∈ zpowers (rCen r) := by
    intro x hx hxτ
    have hxG : (x : G) * (g * t * g⁻¹) = (g * t * g⁻¹) * (x : G) := by
      rw [hg]
      exact congrArg Subtype.val hxτ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (cen_odd_le_conj hc h3 hr'L hr3 (oddCoreCen_le r)
      (fun y hy n hn => oddCoreCen_norm r hy hn) (odd_card_oddCoreCen r)
      ((mem_oddCoreCen_iff x).2 hx) hxG)
    exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa [rCen] using hk)⟩
  have hρ₁ : rCen r * τ₁ = τ₁ * rCen r := (mem_center_iff.1 (rCen_mem_center r) τ₁).symm
  have hρ₂ : rCen r * τ₂ = τ₂ * rCen r := (mem_center_iff.1 (rCen_mem_center r) τ₂).symm
  have hτ₂c := noncentral_aux (O := O) hodd hρ3 hρO hρ₁ hρ₂ (tCen_mul_self hc hrL) hO₁ hO₂
    hn₁ hn₂ hcen
  have hvX : (QuotientGroup.mk vX : CenG r ⧸ O) ∈ center (CenG r ⧸ O) := by
    have hv : vX = τ₁ * τ₂ := Subtype.ext (by
      show (v : G) = t * (t * (v : G))
      rw [← mul_assoc, hc.z_sq, one_mul])
    rw [hv, QuotientGroup.mk_mul]
    exact mul_mem hcen hτ₂c
  refine false_of_central_mod h3 hZ hrL3 ⟨v, hvC⟩ hv2 ?_
  intro m
  have hmr : ((m : L) : G) * r = r * ((m : L) : G) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.1 m.2)
  let wX : CenG r := ⟨((m : L) : G), mem_centralizer_singleton_iff.2 hmr⟩
  have hcX : vX * wX * vX⁻¹ * wX⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h : (vX : CenG r ⧸ O) * (wX : CenG r ⧸ O) = (wX : CenG r ⧸ O) * (vX : CenG r ⧸ O) :=
      (mem_center_iff.1 hvX (wX : CenG r ⧸ O)).symm
    calc (vX : CenG r ⧸ O) * (wX : CenG r ⧸ O) * (vX : CenG r ⧸ O)⁻¹ * (wX : CenG r ⧸ O)⁻¹
        = ((wX : CenG r ⧸ O) * (vX : CenG r ⧸ O)) * (vX : CenG r ⧸ O)⁻¹ *
            (wX : CenG r ⧸ O)⁻¹ := by rw [h]
      _ = 1 := by group
  have hcv : Commute (v : G) t := hc.comm v v.2
  have hcm : Commute ((m : L) : G) t := hc.comm _ (m : L).2
  have hct : tCen hc hrL * (vX * wX * vX⁻¹ * wX⁻¹) * (tCen hc hrL)⁻¹ =
      vX * wX * vX⁻¹ * wX⁻¹ := by
    rw [mul_inv_eq_iff_eq_mul]
    refine Subtype.ext ?_
    exact (((hcv.mul_left hcm).mul_left hcv.inv_left).mul_left hcm.inv_left).eq.symm
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (cen_odd_of hc h3 hrL hr3 _ hcX hct)
  refine mem_zpowers_iff.2 ⟨k, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hk
  simpa [rCen, vX, wX] using h

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
