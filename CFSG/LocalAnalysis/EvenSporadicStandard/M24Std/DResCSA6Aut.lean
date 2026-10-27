module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import Certificates.Certificate25770

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.DoubleA3

theorem card_fix_involution_alt6 {K : Type*} [Group K]
    (e₀ : K ≃* alternatingGroup (Fin 6)) (α : MulAut K) (hα : α * α = 1) :
    Nat.card {k : K // α k = k} = 360 ∨ Nat.card {k : K // α k = k} = 8 ∨
      Nat.card {k : K // α k = k} = 24 ∨ Nat.card {k : K // α k = k} = 10 := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e₀.trans ψ.symm
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ α
  have hα2 : ∀ k, α (α k) = k := fun k => by
    simpa using congrArg (fun f : MulAut K => f k) hα
  have hb2 : b * b = 1 := by
    have hc : b * b ∈ A6Models.autA6 := A6Models.autA6.mul_mem hbA hbA
    refine centralizer_psl29 hc fun x hx => ?_
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1 := hb k
    have h2 := hb (α k)
    rw [hα2 k, h1, hk] at h2
    calc b * b * x = (b * (b * x * b⁻¹) * b⁻¹) * (b * b) := by group
      _ = x * (b * b) := by rw [← h2]
  have hfix : Nat.card {k : K // α k = k} =
      Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({b} : Set P10)) := by
    refine Nat.card_congr
      { toFun := fun k => ⟨((φ k.1 : ↥A6Models.psl29) : P10), (φ k.1).2, ?_⟩
        invFun := fun y => ⟨φ.symm ⟨y.1, (Subgroup.mem_inf.1 y.2).1⟩, ?_⟩
        left_inv := fun k => by simp
        right_inv := fun y => by apply Subtype.ext; simp }
    · show ((φ k.1 : ↥A6Models.psl29) : P10) ∈ Subgroup.centralizer ({b} : Set P10)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hb k.1
      rw [k.2] at h1
      calc ((φ k.1 : ↥A6Models.psl29) : P10) * b
          = (b * ((φ k.1 : ↥A6Models.psl29) : P10) * b⁻¹) * b := by rw [← h1]
        _ = b * ((φ k.1 : ↥A6Models.psl29) : P10) := by group
    · have hy := Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 y.2).2
      apply φ.injective
      apply Subtype.ext
      rw [hb, MulEquiv.apply_symm_apply]
      calc b * y.1 * b⁻¹ = (y.1 * b) * b⁻¹ := by rw [hy]
        _ = y.1 := by group
  rw [hfix, card_psl29_centralizer]
  exact Certificates.certificate25770 (code b) (code_mem_autL hbA)
    (by rw [← code_mul, hb2, code_one])

end CFSG.EvenSporadicStandard.M24Std.DRes
