module

public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.M11OddCore
public import CFSG.GH74.KGroups.M11

public section

namespace CFSG.ClassicalInvolution.Q3.Q3NM

open CFSG.Open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Q3 CFSG.Blueprint

theorem FixedOddFree.of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : FixedOddFree A) : FixedOddFree B := by
  intro τ hτ
  have hρ : MulAut.congr e.symm τ * MulAut.congr e.symm τ = 1 := by
    rw [← map_mul, hτ, map_one]
  have h1 := oddCoreIn_fixed_congr_eq_bot' e (MulAut.congr e.symm τ) (h _ hρ)
  have : MulAut.congr e (MulAut.congr e.symm τ) = τ := by
    ext x
    simp [MulAut.congr_apply]
  rwa [this] at h1

theorem m11_aut_inner (φ : MulAut ↥NativeSporadic.M11) :
    ∃ k : ↥NativeSporadic.M11, φ = MulAut.conj k := by
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.KGroups.M11.autModel (K := ↥NativeSporadic.M11)
    ⟨MulEquiv.refl _⟩
  have hPA : M.P = M.A := hP.trans hA.symm
  have hmem : ((M.Φ φ : M.A) : Equiv.Perm (Fin 11)) ∈ M.P := by
    rw [hPA]
    exact (M.Φ φ).2
  obtain ⟨k, hk⟩ := M.e.surjective ⟨_, hmem⟩
  refine ⟨k, MulEquiv.ext fun x => ?_⟩
  apply M.e.injective
  apply Subtype.ext
  rw [M.spec φ x]
  have hk' : ((M.e k : M.P) : Equiv.Perm (Fin 11)) = (M.Φ φ : Equiv.Perm (Fin 11)) :=
    congrArg Subtype.val hk
  show _ = ((M.e (k * x * k⁻¹) : M.P) : Equiv.Perm (Fin 11))
  rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hk']

theorem fixedOddFree_m11 : FixedOddFree ↥NativeSporadic.M11 := by
  have hM := m11Facts
  have : Finite ↥NativeSporadic.M11 := Nat.finite_of_card_ne_zero (by rw [hM.2]; norm_num)
  have hcenter := center_m11_eq_bot hM
  have hOF : OddCoreFree ↥NativeSporadic.M11 :=
    oddCoreFree_of_m11 hM m11OddCentralizerFree (MonoidHom.id _) Function.surjective_id
      (by simp)
  intro σ hσ
  obtain ⟨k, rfl⟩ := m11_aut_inner σ
  have hk : k * k = 1 := by
    have h1 : MulAut.conj (k * k) = 1 := by rw [map_mul]; exact hσ
    have h2 : k * k ∈ Subgroup.center ↥NativeSporadic.M11 := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun α : MulAut ↥NativeSporadic.M11 => α g) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      have h3 : k * k * g = g * (k * k) := by
        calc k * k * g = (k * k * g * (k * k)⁻¹) * (k * k) := by group
          _ = g * (k * k) := by rw [this]
      exact h3.symm
    rw [hcenter, Subgroup.mem_bot] at h2
    exact h2
  rw [fixedSubgroup_conj]
  exact hOF k hk

theorem fixedOddFree_m11_quotient :
    FixedOddFree (↥NativeSporadic.M11 ⧸ Subgroup.center ↥NativeSporadic.M11) := by
  have hcenter := center_m11_eq_bot m11Facts
  exact FixedOddFree.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
    fixedOddFree_m11

end CFSG.ClassicalInvolution.Q3.Q3NM
