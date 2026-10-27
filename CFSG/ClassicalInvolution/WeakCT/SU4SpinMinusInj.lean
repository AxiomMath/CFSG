module

public import CFSG.ClassicalInvolution.WeakCT.SU4SpinMinusRep
public import CFSG.LieType.Universal.SpinOmega.Kernel

public section

namespace CFSG.ClassicalInvolution.WeakCT.SU4

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra QuadraticMap
open scoped Matrix

namespace KleinData

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}
  (D : KleinData F K σ₀ b c)

theorem δ_ne_zero : D.δ ≠ 0 := by
  intro h
  have := D.δ_mul_ε
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem ε_ne_zero : D.ε ≠ 0 := by
  intro h
  have := D.δ_mul_ε
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem Xmat_eq_zero {v : Vm 3 F} (h : D.Xmat v = 0) : v = 0 := by
  have h01 : algebraMap F K (v (.inl iZ)) = 0 := by
    simpa [Xmat, skew6] using congrFun (congrFun h 0) 1
  have h23 : algebraMap F K (v (.inr (.inl iZ))) = 0 := by
    simpa [Xmat, skew6] using congrFun (congrFun h 2) 3
  have h02 : D.δ * algebraMap F K (v (.inl iO)) = 0 := by
    simpa [Xmat, skew6] using congrFun (congrFun h 0) 2
  have h13 : D.ε * algebraMap F K (v (.inr (.inl iO))) = 0 := by
    simpa [Xmat, skew6] using congrFun (congrFun h 1) 3
  have h03 : algebraMap F K (v (.inr (.inr 0))) - algebraMap F K (v (.inr (.inr 1))) * D.ω = 0 := by
    simpa [Xmat, skew6] using congrFun (congrFun h 0) 3
  have h12 : algebraMap F K (v (.inr (.inr 0))) + algebraMap F K (v (.inr (.inr 1))) *
      algebraMap F K b + algebraMap F K (v (.inr (.inr 1))) * D.ω = 0 := by
    simpa [Xmat, skew6] using congrFun (congrFun h 1) 2
  have hw : algebraMap F K (v (.inr (.inr 1))) = 0 := by
    have h3 : algebraMap F K (v (.inr (.inr 1))) * D.δ = 0 := by
      unfold δ
      linear_combination h12 - h03
    exact (mul_eq_zero.mp h3).resolve_right D.δ_ne_zero
  have hu : algebraMap F K (v (.inr (.inr 0))) = 0 := by
    rw [hw, zero_mul, sub_zero] at h03
    exact h03
  funext x
  rcases x with i | i | t
  · fin_cases i
    · exact (map_eq_zero _).mp h01
    · exact (map_eq_zero _).mp ((mul_eq_zero.mp h02).resolve_left D.δ_ne_zero)
  · fin_cases i
    · exact (map_eq_zero _).mp h23
    · exact (map_eq_zero _).mp ((mul_eq_zero.mp h13).resolve_left D.ε_ne_zero)
  · fin_cases t
    · exact (map_eq_zero _).mp hu
    · exact (map_eq_zero _).mp hw

theorem gam_eq_zero {v : Vm 3 F} (h : D.gam v = 0) : v = 0 := by
  apply D.Xmat_eq_zero
  ext i j
  have h1 := congrFun (congrArg (fun T : Module.End F (Fin 4 → K) => T (D.rv (Pi.single j 1))) h) i
  simp only [gam_apply, rv_rv, Matrix.mulVec_single_one, LinearMap.zero_apply] at h1
  simpa using h1

theorem gam_injective : Function.Injective D.gam := fun v w h => by
  have h1 : D.gam (v - w) = 0 := by
    rw [← gamLin_apply, map_sub, gamLin_apply, gamLin_apply, h, sub_self]
  exact sub_eq_zero.mp (D.gam_eq_zero h1)

theorem mem_ker_spinAction_of_PhiMon_eq_one {s : spinGroup (quadMinus 3 F b c)}
    (h : D.PhiMon s = 1) : s ∈ (spinAction (quadMinus 3 F b c)).ker := by
  have hs : D.Psi (s : CliffordAlgebra (quadMinus 3 F b c)) = 1 :=
    LinearMap.ext fun x => by rw [Psi_spin, h, Matrix.one_mulVec]; rfl
  have hi : D.Psi ((s⁻¹ : spinGroup (quadMinus 3 F b c)) : CliffordAlgebra (quadMinus 3 F b c)) =
      1 := by
    have h1 : D.Psi ((s : CliffordAlgebra (quadMinus 3 F b c)) *
        ((s⁻¹ : spinGroup (quadMinus 3 F b c)) : CliffordAlgebra (quadMinus 3 F b c))) = 1 := by
      rw [coe_mul_coe_inv, map_one]
    rwa [map_mul, hs, one_mul] at h1
  rw [MonoidHom.mem_ker]
  refine LinearEquiv.ext fun v => ?_
  have h1 := congrArg D.Psi (ι_spinAction (quadMinus 3 F b c) s v)
  rw [Psi_ι, map_mul, map_mul, hs, hi, Psi_ι, one_mul, mul_one] at h1
  exact D.gam_injective h1

theorem PhiMon_of_coe_eq {s : spinGroup (quadMinus 3 F b c)} {r : F} {a a' : Vm 3 F}
    (h : (s : CliffordAlgebra (quadMinus 3 F b c)) =
      1 + r • (ι (quadMinus 3 F b c) a * ι (quadMinus 3 F b c) a')) :
    D.PhiMon s = 1 + r • (D.Xmat a * D.Hs (D.Xmat a')) := by
  have h1 : (⟨(s : CliffordAlgebra (quadMinus 3 F b c)), spinGroup.mem_even s.2⟩ :
      CliffordAlgebra.even (quadMinus 3 F b c)) =
      1 + r • (CliffordAlgebra.even.ι (quadMinus 3 F b c)).bilin a a' := Subtype.ext h
  rw [PhiMon_apply, h1, map_add, map_one, map_smul, PhiAlg_ι]

theorem PhiMon_injective [Finite F] (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective D.PhiMon := by
  rw [injective_iff_map_eq_one]
  intro s hs
  have hcent := isCentral_cliffordAlgebra_quadMinus 3 b c hirr
  rcases (mem_ker_spinAction_iff_of_isCentral _ s).1 (D.mem_ker_spinAction_of_PhiMon_eq_one hs) with
    h | h
  · exact h
  · exfalso
    have h1 : (⟨(s : CliffordAlgebra (quadMinus 3 F b c)), spinGroup.mem_even s.2⟩ :
        CliffordAlgebra.even (quadMinus 3 F b c)) = -1 := Subtype.ext h
    have h2 : D.PhiMon s = -1 := by rw [PhiMon_apply, h1, map_neg, map_one]
    rw [hs] at h2
    have h3 := congrFun (congrFun h2 0) 0
    simp only [Matrix.one_apply_eq, Matrix.neg_apply] at h3
    apply D.two_ne
    linear_combination h3

end KleinData

end CFSG.ClassicalInvolution.WeakCT.SU4
