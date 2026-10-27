module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRCoord

public section

namespace CFSG.ComponentClassification.GMS78.RuN

open Subgroup CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.GMS78RuS
open CFSG.ComponentClassification.GMS78.RuSimCode CFSG.ComponentClassification.GMS78.RuSModel

section D

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

theorem linId_of_linApply {r : Lin8} (h : ∀ t, linApply r t = t) : r = linId := by
  have e1 := h 1
  have e2 := h 2
  have e4 := h 4
  rw [linApply_one] at e1
  rw [linApply_two] at e2
  rw [linApply_four] at e4
  exact Prod.ext e1 (Prod.ext e2 e4)

theorem sMul_D (d e : Fin 8) : sMul false (0, 0, d) (0, 0, e) = (0, 0, dMul d e) := by
  simp only [sMul, dPart_zero, gam_zero_left, linApply_zero, Bool.false_and, Bool.false_eq_true,
    ↓reduceIte, fin8_xor_zero, Nat.zero_xor]

theorem exists_dInv : ∀ d : Fin 8, ∃ e : Fin 8, dMul e d = 0 := by decide

@[expose] noncomputable def dSub (hS : Sec3.SzR.SModel L T R μ ν false Φ) : Subgroup G where
  carrier := {g | ∃ d : Fin 8, Φ (0, 0, d) = g}
  mul_mem' := by
    rintro _ _ ⟨d, rfl⟩ ⟨e, rfl⟩
    exact ⟨dMul d e, by rw [← hS.mul, sMul_D]⟩
  one_mem' := ⟨0, sModel_one_eq hS⟩
  inv_mem' := by
    rintro _ ⟨d, rfl⟩
    obtain ⟨e, he⟩ := exists_dInv d
    refine ⟨e, ?_⟩
    rw [eq_inv_iff_mul_eq_one, ← hS.mul, sMul_D, he, sModel_one_eq hS]

theorem card_dSub (hS : Sec3.SzR.SModel L T R μ ν false Φ) : Nat.card (dSub hS) = 8 := by
  let F : Fin 8 → dSub hS := fun d => ⟨Φ (0, 0, d), d, rfl⟩
  have hF : Function.Bijective F := by
    refine ⟨fun d e h => ?_, fun g => ?_⟩
    · have := hS.inj (0, 0, d) (0, 0, e) (by norm_num) (by norm_num)
        (congrArg Subtype.val h)
      simpa using this
    · obtain ⟨d, hd⟩ := g.2
      exact ⟨d, Subtype.ext hd⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem dSub_inf_R (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) : dSub hS ⊓ R = ⊥ := by
  refine eq_bot_iff.mpr fun g hg => ?_
  obtain ⟨⟨d, rfl⟩, hgR⟩ := hg
  have hcode : ∀ t, linApply (dCode d) t = t := by
    intro t
    obtain ⟨b, hb, hbt⟩ := hM.ν_surj t
    have := hS.code (0, 0, d) b hb
    rw [hM.central _ hgR b hb, mul_inv_cancel_right, hbt] at this
    exact this.symm
  have hd : d = 0 := dCode_injective d 0 (linId_of_linApply hcode)
  rw [hd, mem_bot]
  exact sModel_one_eq hS

theorem dSub_le_normalizer (hS : Sec3.SzR.SModel L T R μ ν false Φ) :
    dSub hS ≤ normalizer (R : Set G) := by
  rintro _ ⟨d, rfl⟩
  exact hS.mem _

end D

section Cert

variable {G : Type} [Group G] {L T R : Subgroup G} {μ : G → ℕ} {ν : G → Fin 8}
  {Φ : ℕ × Fin 8 × Fin 8 → G}

@[expose] noncomputable def actN (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) : ↥(normalizer (R : Set G)) →* MulAut RuR where
  toFun n := conjR hM hS n.2
  map_one' := MulEquiv.ext fun x => (conjR_eq_iff hM hS _ _ _).mpr (by
    change 1 * thetaR hS x * 1⁻¹ = thetaR hS x
    group)
  map_mul' n n' := conjR_mul hM hS n.2 n'.2

theorem actN_apply (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (n : ↥(normalizer (R : Set G))) (x : RuR) :
    thetaR hS (actN hM hS n x) = (n : G) * thetaR hS x * (n : G)⁻¹ :=
  thetaR_conjR hM hS n.2 x

theorem actN_code (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (n : ↥(normalizer (R : Set G))) :
    ∃ r ∈ glList, (∀ b ∈ gmsA L T, ν ((n : G) * b * (n : G)⁻¹) = linApply r (ν b)) ∧
      (∀ x, (actN hM hS n x).m = (nAut r x).m) ∧
        ∀ t, actN hM hS n ⟨0, t⟩ = ⟨0, linApply r t⟩ := by
  obtain ⟨r, hr, hA, hR⟩ := hM.act n n.2
  exact ⟨r, hr, hA, conjR_code hM hS n.2 hA hR⟩

theorem exists_actN_code (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (hidx : R.relIndex (normalizer (R : Set G)) = 168) [Finite G] {r : Lin8} (hr : r ∈ glList) :
    ∃ n : ↥(normalizer (R : Set G)), (∀ x, (actN hM hS n x).m = (nAut r x).m) ∧
      ∀ t, actN hM hS n ⟨0, t⟩ = ⟨0, linApply r t⟩ := by
  obtain ⟨g, hg, hA, hR⟩ := hM.exists_code_eq hNC hidx hr
  exact ⟨⟨g, hg⟩, conjR_code hM hS hg hA hR⟩

theorem actN_thetaR (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (y : RuR) :
    actN hM hS ⟨thetaR hS y, le_normalizer (thetaR_mem hS y)⟩ = MulAut.conj y :=
  conjR_thetaR hM hS y

theorem actN_D (hM : Sec3.SzR.MaskCoords L T R μ ν) (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (d : Fin 8) (x : RuR) : actN hM hS ⟨Φ (0, 0, d), hS.mem _⟩ x = nAut (dCode d) x :=
  conjR_D hM hS d x

theorem mem_R_of_actN (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (n : ↥(normalizer (R : Set G))) (hn : ∀ t, actN hM hS n ⟨0, t⟩ = ⟨0, t⟩) : (n : G) ∈ R := by
  obtain ⟨r, -, hA, -, hA'⟩ := actN_code hM hS n
  have hr : r = linId := linId_of_linApply fun t => by
    have := congrArg RuR.t ((hA' t).symm.trans (hn t))
    exact this
  refine hM.mem_of_code_eq_linId hNC n.2 fun b hb => ?_
  rw [hA b hb, hr]

theorem exists_eq_conj (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (n : ↥(normalizer (R : Set G))) (hn : ∀ t, actN hM hS n ⟨0, t⟩ = ⟨0, t⟩) :
    ∃ y : RuR, actN hM hS n = MulAut.conj y := by
  have hR := mem_R_of_actN hM hS hNC n hn
  obtain ⟨y, hy⟩ : (n : G) ∈ (thetaR hS).range := by
    rw [range_thetaR hM hS]
    exact hR
  refine ⟨y, ?_⟩
  rw [← actN_thetaR hM hS y]
  congr 1
  exact Subtype.ext hy.symm

theorem mem_A_of_actN_eq_one (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ)
    (hNC : normalizer (R : Set G) ⊓ centralizer (gmsA L T : Set G) = R)
    (n : ↥(normalizer (R : Set G))) (hn : actN hM hS n = 1) : (n : G) ∈ gmsA L T := by
  have hR := mem_R_of_actN hM hS hNC n (fun t => by rw [hn]; rfl)
  obtain ⟨y, hy⟩ : (n : G) ∈ (thetaR hS).range := by
    rw [range_thetaR hM hS]
    exact hR
  have h1 : actN hM hS ⟨thetaR hS y, le_normalizer (thetaR_mem hS y)⟩ = 1 := by
    rw [← hn]
    congr 1
    exact Subtype.ext hy
  rw [actN_thetaR] at h1
  have hyc : y ∈ center RuR := mem_center_iff.mpr fun z => by
    have := congrArg (fun f : MulAut RuR => f z) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc z * y = y * z * y⁻¹ * y := by rw [this]
      _ = y * z := by group
  rw [center_RuR] at hyc
  have hy0 : y = ⟨0, y.t⟩ := RuR.ext hyc rfl
  rw [← hy, hy0]
  exact (thetaR_A1 hS y.t).1

theorem actN_eq_one_of_mem_A (hM : Sec3.SzR.MaskCoords L T R μ ν)
    (hS : Sec3.SzR.SModel L T R μ ν false Φ) (n : ↥(normalizer (R : Set G)))
    (hn : (n : G) ∈ gmsA L T) : actN hM hS n = 1 := by
  refine MulEquiv.ext fun x => (thetaR_injective hS) ?_
  rw [actN_apply, MulAut.one_apply, ← hM.central _ (thetaR_mem hS x) _ hn, mul_inv_cancel_right]

end Cert

end CFSG.ComponentClassification.GMS78.RuN
