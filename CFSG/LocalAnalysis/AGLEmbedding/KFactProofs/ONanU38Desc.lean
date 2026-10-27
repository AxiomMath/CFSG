module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Galois
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanU38Model
public import CFSG.RankThree.PartTwo.Sec6.BThreeCensusU3

public section

namespace CFSG.AGLEmbedding.ChevOuter.U38

open CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter CFSG.AGLEmbedding.ChevOuter.GF64
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec6.BThreeCensus

theorem hq2 : 2 < 2 ^ 3 := by norm_num

section Act

variable {X : Type*} [Group X] (K : Subgroup X) [K.Normal]

@[expose] noncomputable def actOn {G : Type*} [Group G] (e : K ≃* G) : X →* MulAut G :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem coe_actOn_symm {G : Type*} [Group G] (e : K ≃* G) (x : X) (g : G) :
    ((e.symm (actOn K e x g) : K) : X) = x * ((e.symm g : K) : X) * x⁻¹ := by
  simp [actOn, MulAut.congr_apply]

theorem actOn_trans {G H : Type*} [Group G] [Group H] (e : K ≃* G) (γ : G ≃* H) (x : X) :
    actOn K (e.trans γ) x = γ.symm.trans ((actOn K e x).trans γ) := by
  refine MulEquiv.ext fun h => ?_
  apply (e.trans γ).symm.injective
  apply Subtype.ext
  rw [coe_actOn_symm]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_trans_apply, MulEquiv.symm_apply_apply]
  have := coe_actOn_symm K e x (γ.symm h)
  simpa using this.symm

theorem actOn_trans_mul {G : Type*} [Group G] (e : K ≃* G) (γ : MulAut G) (x : X) :
    actOn K (e.trans γ) x = γ * actOn K e x * γ⁻¹ := by
  rw [actOn_trans]
  refine MulEquiv.ext fun g => ?_
  rfl

theorem actOn_coe {G : Type*} [Group G] (e : K ≃* G) (k : K) :
    actOn K e (k : X) = MulAut.conj (e k) := by
  refine MulEquiv.ext fun g => ?_
  apply e.symm.injective
  apply Subtype.ext
  rw [coe_actOn_symm]
  simp [MulAut.conj_apply]

end Act

theorem mulAut_conj_eq_suConj' (x : SU) :
    MulAut.conj x = suConj hU ⟨x, unitarySU_le_unitaryIsom3 x.2⟩ := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.conj_apply, coe_suConj]
  rfl

section Desc

variable {X : Type*} [Group X] (K : Subgroup X) [K.Normal]

theorem exists_sigma_model_su (e : K ≃* SU) {x : X} (hx : x ^ 3 = 1)
    (hD : actOn K e x ∉ (suConj hU).range) :
    ∃ (e' : K ≃* SU) (y : X), (y = x ∨ y = x⁻¹) ∧ actOn K e' y = sigSU := by
  set β := actOn K e x with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hx, map_one]
  have hα3 : suDescend hU hq2 β ^ 3 = 1 := by rw [← map_pow, hβ3, map_one]
  have hαD : suDescend hU hq2 β ∉ (psuConj hU).range := by
    rintro ⟨A, hA⟩
    apply hD
    refine ⟨A, ?_⟩
    apply eq_of_suDescend_eq hU hq2
    rw [suDescend_suConj]
    exact hA
  obtain ⟨σ, hσ3, H, hαH⟩ := unitary_order_three_field_descent hq2 _ hα3 hαD
  have hβH : β = suConj hU H * suField hU σ * (suConj hU H)⁻¹ := by
    apply eq_of_suDescend_eq hU hq2
    rw [map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suField]
    exact hαH
  have key : ∀ y : X, actOn K (e.trans (suConj hU H)⁻¹) y =
      (suConj hU H)⁻¹ * actOn K e y * suConj hU H := by
    intro y
    rw [actOn_trans_mul, inv_inv]
  rcases eq_sigma2_or_inv_of_orderOf_eq_three σ hσ3 with rfl | rfl
  · refine ⟨e.trans (suConj hU H)⁻¹, x, Or.inl rfl, ?_⟩
    rw [key, ← hβ, hβH]
    show _ = suField hU sigma2Equiv
    group
  · refine ⟨e.trans (suConj hU H)⁻¹, x⁻¹, Or.inr rfl, ?_⟩
    rw [key, map_inv, ← hβ, hβH, map_inv]
    show _ = suField hU sigma2Equiv
    group

theorem exists_sigma_model_psu (e : K ≃* unitaryPSU hU 3) {x : X} (hx : x ^ 3 = 1)
    (hD : actOn K e x ∉ (psuConj hU).range) :
    ∃ (e' : K ≃* unitaryPSU hU 3) (y : X), (y = x ∨ y = x⁻¹) ∧
      actOn K e' y = psuField hU sigma2Equiv := by
  set β := actOn K e x with hβ
  have hβ3 : β ^ 3 = 1 := by rw [hβ, ← map_pow, hx, map_one]
  obtain ⟨σ, hσ3, H, hβH⟩ := unitary_order_three_field_descent hq2 _ hβ3 hD
  have key : ∀ y : X, actOn K (e.trans (psuConj hU H)⁻¹) y =
      (psuConj hU H)⁻¹ * actOn K e y * psuConj hU H := by
    intro y
    rw [actOn_trans_mul, inv_inv]
  rcases eq_sigma2_or_inv_of_orderOf_eq_three σ hσ3 with rfl | rfl
  · refine ⟨e.trans (psuConj hU H)⁻¹, x, Or.inl rfl, ?_⟩
    rw [key, ← hβ, hβH]
    group
  · refine ⟨e.trans (psuConj hU H)⁻¹, x⁻¹, Or.inr rfl, ?_⟩
    rw [key, map_inv, ← hβ, hβH, map_inv]
    group

end Desc

end CFSG.AGLEmbedding.ChevOuter.U38
