module

public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Sp6B
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4tModel

public section

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25T

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Q3.TL4
open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
open CFSG.ClassicalInvolution.Q3.TL4.E4Sp6

@[expose] def E4Sp6NC4Model : Prop :=
  ∀ (M : Type) [Group M] [Finite M], CFSG.Blueprint.LieModel M .PSp 3 2 1 →
    ∀ (K : Subgroup M) (s : M), Nonempty (↥K ≃* QuaternionGroup 2) → IsUniqueInvolution K s →
      (∀ c ∈ Subgroup.centralizer ({s} : Set M), conjSub c K = K ∨
        ∀ x ∈ K, ∀ y ∈ conjSub c K, x * y = y * x) →
      ∃ y ∈ K, orderOf y = 4 ∧
        ∃ g : M, g * s * g⁻¹ ≠ y * y ∧ (g * s * g⁻¹) * y = y * (g * s * g⁻¹)

namespace NC4Sp6

@[expose] def witWord : List ℤ := [2, 2, 2, 2, 1, 2, 1, 2, 1]

@[expose] def witW : Equiv.Perm (Fin 36) := evalCodes sp6Gens witWord

@[expose] def witX : Equiv.Perm (Fin 36) := witW * sp6Rep2 * witW⁻¹

theorem witX_ne : witX ≠ sp6Rep2 := by decide +kernel

theorem witX_comm : witX * rho () = rho () * witX := by decide +kernel

theorem rho_mul_rho : rho () * rho () = sp6Rep2 := by decide +kernel

theorem orderOf_rho : orderOf (rho ()) = 4 := by
  have h2 : ¬ rho () ^ 2 ^ 1 = 1 := by decide +kernel
  have h4 : rho () ^ 2 ^ (1 + 1) = 1 := by decide +kernel
  simpa using orderOf_eq_prime_pow h2 h4

theorem witW_mem :
    witW ∈ co3X36 := by
  rw [← sp6Q_originalSubgroup]
  exact evalCodes_mem _ sp6Gens_mem witWord

end NC4Sp6

theorem e4Sp6NC4Model_of_certs :
    E4Sp6NC4Model := by
  intro M _ _ hM K s hq hinv htw
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hM
  obtain ⟨φ, hφ, hrange, hKφ⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.exists_emb_of_ident e
      (fun K s hd => E4Sp6.ident_ambient hd) hq hinv htw
  have hs : φ s = sp6Rep2 :=
    E4Sp6.eq_rep_of_isUniqueInvolution (hKφ ▸ Vtx.isUniqueInvolution_map φ hφ hinv)
  have hρ : rho () ∈ K.map φ := hKφ ▸ Subgroup.subset_closure (Set.mem_insert _ _)
  obtain ⟨y, hyK, hy⟩ := hρ
  obtain ⟨g, hg⟩ : NC4Sp6.witW ∈ φ.range := hrange ▸ NC4Sp6.witW_mem
  have hX : φ (g * s * g⁻¹) = NC4Sp6.witX := by
    rw [map_mul φ (g * s) g⁻¹, map_mul φ g s, map_inv φ g, hg, hs]
    rfl
  have hyy : φ (y * y) = sp6Rep2 := by
    rw [map_mul φ y y, hy, NC4Sp6.rho_mul_rho]
  refine ⟨y, hyK, ?_, g, ?_, ?_⟩
  · rw [← orderOf_injective φ hφ y, hy]
    exact NC4Sp6.orderOf_rho
  · intro h
    apply NC4Sp6.witX_ne
    rw [← hX, h, hyy]
  · apply hφ
    rw [map_mul φ (g * s * g⁻¹) y, map_mul φ y (g * s * g⁻¹), hX, hy]
    exact NC4Sp6.witX_comm

end CFSG.ClassicalInvolution.Q8P.Asc77.P25T
