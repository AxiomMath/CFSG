module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL319Conj

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups
open scoped commutatorElement

private def fzl_fzZ : Subgroup FzUT where
  carrier := {x | FzInZ x}
  mul_mem' := by
    rintro x y ⟨hxa, hxb⟩ ⟨hya, hyb⟩
    exact ⟨by simp [UT3.mul_def, hxa, hya], by simp [UT3.mul_def, hxb, hyb]⟩
  one_mem' := by simp [FzInZ, UT3.one_def]
  inv_mem' := by
    rintro x ⟨hxa, hxb⟩
    exact ⟨by simp [UT3.inv_def, hxa], by simp [UT3.inv_def, hxb]⟩

private noncomputable def fzl_fzZEquiv : {x : FzUT // FzInZ x} ≃ L23.F4c where
  toFun x := x.1.c
  invFun c := ⟨⟨0, 0, c⟩, by simp [FzInZ]⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨ha, hb⟩ := x.2
    exact UT3.ext ha.symm hb.symm rfl
  right_inv c := rfl

private theorem fzl_sq_central (x : FzUT) : FzInZ (x * x) := by
  revert x
  simp only [FzInZ]
  decide +kernel

private noncomputable def fzl_comapEquiv {G : Type} [Group G] {P : Subgroup G}
    (φ : ↥P ≃* FzUT) :
    ↥(fzl_fzZ.comap φ.toMonoidHom) ≃ {x : FzUT // FzInZ x} where
  toFun y := ⟨φ y.1, y.2⟩
  invFun x := ⟨φ.symm x.1, by
    rw [Subgroup.mem_comap]
    show φ (φ.symm x.1) ∈ fzl_fzZ
    rw [MulEquiv.apply_symm_apply]
    exact x.2⟩
  left_inv y := Subtype.ext (by simp)
  right_inv x := Subtype.ext (by simp)

variable {G : Type} [Group G] [Finite G]
variable {t tau lam rho : G} {Z E W Q R T P : Subgroup G}
  (D : Fz319Data t tau lam rho Z E W Q R T P)

namespace Fz319Data

theorem Z_iff (p : ↥P) : (p : G) ∈ Z ↔ FzInZ (D.φ p) := by
  have hZcenter : ∀ q : ↥P, (q : G) ∈ Z → FzInZ (D.φ q) := by
    intro q hq
    obtain ⟨e, heE, he2⟩ := D.str.Z_sqrt (q : G) hq
    have heP : e ∈ P := D.pf.EP heE
    have hqeq : q = (⟨e, heP⟩ : ↥P) ^ 2 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact he2.symm
    have hφ : D.φ q = (D.φ ⟨e, heP⟩) ^ 2 := by rw [hqeq, map_pow]
    rw [hφ, pow_two]
    exact fzl_sq_central (D.φ ⟨e, heP⟩)
  constructor
  · exact hZcenter p
  · intro hp
    have hZP : Z ≤ P := fun z hz => D.pf.EP (D.str.ZE hz)
    have hcardZP : Nat.card (Z.subgroupOf P) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, D.str.card_Z]
    have hcardS : Nat.card (fzl_fzZ.comap D.φ.toMonoidHom) = 4 := by
      rw [Nat.card_congr ((fzl_comapEquiv D.φ).trans fzl_fzZEquiv), Nat.card_eq_fintype_card]
      decide +kernel
    have hle : Z.subgroupOf P ≤ fzl_fzZ.comap D.φ.toMonoidHom := by
      intro q hq
      rw [Subgroup.mem_comap]
      show FzInZ (D.φ q)
      exact hZcenter q (Subgroup.mem_subgroupOf.mp hq)
    have heq : Z.subgroupOf P = fzl_fzZ.comap D.φ.toMonoidHom :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardZP, hcardS])
    have hpS : p ∈ fzl_fzZ.comap D.φ.toMonoidHom := by
      rw [Subgroup.mem_comap]
      show FzInZ (D.φ p)
      exact hp
    exact Subgroup.mem_subgroupOf.mp (heq.symm ▸ hpS)

theorem E_iff (p : ↥P) : (p : G) ∈ E ↔ (D.cT) (D.φ p) = D.φ p := by
  constructor
  · intro hp
    have hconj : t * (p : G) * t⁻¹ = (p : G) := by
      rw [D.str.W_comm t D.str.t_mem (p : G) (D.str.EW hp)]
      group
    have h1 := D.cT_coe (D.φ p)
    rw [MulEquiv.symm_apply_apply] at h1
    rw [hconj] at h1
    have h2 : D.φ.symm ((D.cT) (D.φ p)) = p := Subtype.ext h1
    have := congrArg D.φ h2
    simpa using this
  · intro h
    have hconj : t * (p : G) * t⁻¹ = (p : G) := by
      have h1 := D.cT_coe (D.φ p)
      rw [h, MulEquiv.symm_apply_apply] at h1
      exact h1.symm
    have hpt : (p : G) * t = t * (p : G) := by
      have h2 : t * (p : G) = (p : G) * t := by
        have := congrArg (fun x => x * t) hconj
        simpa [mul_assoc] using this
      exact h2.symm
    have hcomm : (p : G) * t * (p : G)⁻¹ = t := by
      rw [hpt]; group
    have hpQ : (p : G) ∈ Q := D.pf.PQ p.2
    by_cases hpW : (p : G) ∈ W
    · exact D.pf.PW (p : G) p.2 hpW
    · exact absurd hcomm (D.str.Q_t (p : G) hpQ hpW)

end Fz319Data

end CFSG.OddStandard.SmallF3.FritzII
