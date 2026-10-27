module

public import CFSG.GH74.Generic.S1.KL3SL3
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3WASTSign

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.Generic (Commutes)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair pair_normalize blockSL
  coe_blockSL_three_one coe_blockSL_three_zero)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups


section Spin

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}
  {𝔉 : Set (Subgroup (spinGroup Q))}

theorem exists_involution_of_fam3 (S : ModelFacts.SpinCtx3 3 1 Q 𝔉) {R : Subgroup (spinGroup Q)}
    (hR : R ∈ 𝔉) : ∃ c ∈ R, orderOf c = 2 := by
  have hodd := S.odd_card
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨i, hI⟩ := S.map R hR
  obtain ⟨c, hcR, hc⟩ := hI.mem
  have hcc : c * c = 1 := S.inj R hR (c * c) (R.mul_mem hcR hcR)
    (by rw [map_mul, hc]; exact hI.mul_self)
  have hc1 : c ≠ 1 := fun h => hI.ne_one hodd (by rw [← hc, h, map_one])
  exact ⟨c, hcR, orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1⟩

theorem eq_of_involutions_fam3 (S : ModelFacts.SpinCtx3 3 1 Q 𝔉) {R : Subgroup (spinGroup Q)}
    (hR : R ∈ 𝔉) {c c' : spinGroup Q} (hc : c ∈ R) (hc' : c' ∈ R) (ho : orderOf c = 2)
    (ho' : orderOf c' = 2) : c = c' := by
  obtain ⟨i, hI⟩ := S.map R hR
  have e1 := S.map_eq_of_orderOf hR hc ho hI
  have e2 := S.map_eq_of_orderOf hR hc' ho' hI
  have h1 : c * c'⁻¹ = 1 := S.inj R hR _ (R.mul_mem hc (R.inv_mem hc'))
    (by rw [map_mul, map_inv, e1, e2, mul_inv_cancel])
  exact mul_inv_eq_one.mp h1

theorem linear_pair_of_chain3 (S : ModelFacts.SpinCtx3 3 1 Q 𝔉)
    {R₁ R₂ R₃ : Subgroup (spinGroup Q)} (h₁ : R₁ ∈ 𝔉) (h₂ : R₂ ∈ 𝔉) (h₃ : R₃ ∈ 𝔉)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₁ R₂) (h13 : Commutes R₁ R₃)
    (hn32 : ¬ Commutes R₃ R₂) (hne32 : R₃ ≠ R₂) {c₂ : spinGroup Q} (hc₂ : c₂ ∈ R₂)
    (ho₂ : orderOf c₂ = 2) (hnorm : ∀ x ∈ R₃, c₂ * x * c₂⁻¹ ∈ R₃) :
    ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₂ R₃ := by
  have hodd := S.odd_card
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨W, hW⟩ := hlin
  obtain ⟨c₁, hc₁, ho₁⟩ := exists_involution_of_fam3 S h₁
  obtain ⟨c₃, hc₃, ho₃⟩ := exists_involution_of_fam3 S h₃
  have hc₃c : c₂ * c₃ * c₂⁻¹ = c₃ := by
    refine eq_of_involutions_fam3 S h₃ (hnorm c₃ hc₃) hc₃ ?_ ho₃
    have h := orderOf_injective (MulAut.conj c₂).toMonoidHom (MulAut.conj c₂).injective c₃
    simpa [MulAut.conj_apply, ho₃] using h
  have h₃₂ : c₃ * c₂ = c₂ * c₃ := by
    have := hc₃c
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have h₁₂ : c₁ * c₂ = c₂ * c₁ := standardPair_involutions_commute h2 hW hc₁ hc₂ ho₁ ho₂
  have h₁₃ : c₁ * c₃ = c₃ * c₁ := h13 c₁ hc₁ c₃ hc₃
  rcases Q3W.spinCtx3_sign S h₁ h₂ h₃ hc₁ hc₂ hc₃ ho₁ ho₂ ho₃ h₁₂ h₃₂ h₁₃ h13
    (ne_of_linearBlockStandardPair hW) hne32 (not_commutes_of_linearBlockStandardPair hW) hn32
    with ⟨-, hl⟩ | ⟨hu, -⟩
  · exact hl
  · exact (Q3W.false_of_linear_of_unitary3 ⟨W, hW⟩ hu).elim

end Spin

theorem sq_eq_one_of_comm_pair3 {X : Type} [Group X] {W N L : Subgroup X}
    (h : LinearBlockStandardPair (GaloisField 3 1) W N L) {v : X} (hv : v ∈ N)
    (hv2 : orderOf v = 2) {y : X} (hy : y ∈ L)
    (hc : y * v * y⁻¹ * v⁻¹ ∈ Subgroup.center X) : y * y = 1 := by
  classical
  obtain ⟨θ, -, hker, hN, hL⟩ := pair_normalize h
  have h2 : (2 : GaloisField 3 1) ≠ 0 := Q3W.two_ne_zero_gf3
  have hcenter : Subgroup.center SL(3, GaloisField 3 1) = ⊥ :=
    GH74.Generic.S1.kl3_center_sl3 Q3W.card_gf3
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro s hs
    have := hker (MonoidHom.mem_ker.mpr hs)
    rwa [hcenter, Subgroup.mem_bot] at this
  rw [← hN] at hv
  rw [← hL] at hy
  have hvθ := eq_block_neg_one h2 hker (by omega : 0 + 2 ≤ 3) hv hv2
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hy
  set b : SL(3, GaloisField 3 1) := blockSL (GaloisField 3 1) 3 2 1 (by omega) A with hb
  set d : SL(3, GaloisField 3 1) := blockSL (GaloisField 3 1) 3 2 0 (by omega) (-1) with hd
  have hcθ : θ (b * d * b⁻¹ * d⁻¹) ∈ Subgroup.center X := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hvθ]
    exact hc
  have hz : b * d * b⁻¹ * d⁻¹ ∈ Subgroup.center SL(3, GaloisField 3 1) := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply hθinj
    rw [map_mul θ s (b * d * b⁻¹ * d⁻¹), map_mul θ (b * d * b⁻¹ * d⁻¹) s]
    exact Subgroup.mem_center_iff.mp hcθ (θ s)
  rw [hcenter, Subgroup.mem_bot] at hz
  have hbd : b * d = d * b :=
    commutatorElement_eq_one_iff_mul_comm.mp (by rw [commutatorElement_def]; exact hz)
  have hbdm : (b : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) * d =
      (d : Matrix (Fin 3) (Fin 3) (GaloisField 3 1)) * b := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hbd]
  have e12 := congrFun (congrFun hbdm 1) 2
  have e21 := congrFun (congrFun hbdm 2) 1
  simp [hb, hd, coe_blockSL_three_one, coe_blockSL_three_zero, Matrix.mul_apply,
    Fin.sum_univ_three] at e12 e21
  have hA01 : (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) 0 1 = 0 := by
    have : (2 : GaloisField 3 1) * A 0 1 = 0 := by linear_combination e12
    exact (mul_eq_zero.mp this).resolve_left h2
  have hA10 : (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) 1 0 = 0 := by
    have : (2 : GaloisField 3 1) * A 1 0 = 0 := by linear_combination -e21
    exact (mul_eq_zero.mp this).resolve_left h2
  have hdet : (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) 0 0 * A 1 1 = 1 := by
    have := A.2
    rw [Matrix.det_fin_two] at this
    rw [hA01, hA10] at this
    linear_combination this
  have hsqF : ∀ a : GaloisField 3 1, a ≠ 0 → a * a = 1 := fun a ha => by
    have : Fintype (GaloisField 3 1) := Fintype.ofFinite _
    have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [← Nat.card_eq_fintype_card, Q3W.card_gf3] at h1
    simpa [pow_two] using h1
  have h00 : (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) 0 0 ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at hdet
    exact zero_ne_one hdet
  have h11 : (A : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) 1 1 ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hdet
    exact zero_ne_one hdet
  have hsq : A * A = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hA01, hA10, hsqF _ h00, hsqF _ h11]
  calc θ (blockSL (GaloisField 3 1) 3 2 1 (by omega) A) *
        θ (blockSL (GaloisField 3 1) 3 2 1 (by omega) A) =
      θ (blockSL (GaloisField 3 1) 3 2 1 (by omega) (A * A)) := by rw [← map_mul, ← map_mul]
    _ = 1 := by rw [hsq, map_one, map_one]

end CFSG.ClassicalInvolution.Q3.Q3E6T
