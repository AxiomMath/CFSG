module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5M1TDiag
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5FrameType
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5Cov3Frame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem sec5m1t_aux_exists_k (i j : Fin 6) (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4)
    (hij : i ≠ j) : ∃ k : Fin 6, (k : ℕ) < 4 ∧ i ≠ k ∧ j ≠ k := by
  decide +kernel +revert

private theorem sec5m1t_aux_swap3 (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (Equiv.swap i j * Equiv.swap j k) ^ 3 = 1 := by
  decide +kernel +revert

private theorem sec5m1t_aux_alt (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Equiv.swap i j * Equiv.swap j k ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr hij) (Equiv.Perm.swap_isSwap_iff.mpr hjk)

private theorem sec5m1t_aux_preserve (i j k : Fin 6) (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4)
    (hk : (k : ℕ) < 4) :
    ({0, 1, 2, 3} : Finset (Fin 6)).map (Equiv.swap i j * Equiv.swap j k).toEmbedding =
      {0, 1, 2, 3} := by
  decide +kernel +revert

private theorem sec5m1t_aux_symm (i j k : Fin 6) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    symmDiff ({i, j} : Finset (Fin 6))
        (({i, j} : Finset (Fin 6)).map (Equiv.swap i j * Equiv.swap j k).toEmbedding) =
      ((({i, j} : Finset (Fin 6)).map
        (Equiv.swap i j * Equiv.swap j k).toEmbedding)).map
        (Equiv.swap i j * Equiv.swap j k).toEmbedding := by
  decide +kernel +revert

private theorem sec5m1t_aux_c012_alt : sec5m1tC012 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (0 : Fin 6) ≠ 1))
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (1 : Fin 6) ≠ 2))

private theorem sec5m1t_aux_c012_pow3 : sec5m1tC012 ^ 3 = 1 := by
  decide +kernel

private theorem sec5m1t_aux_c012_preserve :
    ({0, 1, 2, 3} : Finset (Fin 6)).map sec5m1tC012.toEmbedding = {0, 1, 2, 3} := by
  decide +kernel

private theorem sec5m1t_aux_c123_alt : sec5m1tC123 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mul_mem_alternatingGroup_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (1 : Fin 6) ≠ 2))
    (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (2 : Fin 6) ≠ 3))

private theorem sec5m1t_aux_c123_pow3 : sec5m1tC123 ^ 3 = 1 := by
  decide +kernel

private theorem sec5m1t_aux_c123_preserve :
    ({0, 1, 2, 3} : Finset (Fin 6)).map sec5m1tC123.toEmbedding = {0, 1, 2, 3} := by
  decide +kernel

private theorem sec5m1t_aux_comm_twoRes (hQ : Q.Nondegenerate) {c : ZMod 3}
    (fr : NFrame Q (Fin 6) c) {y : V ≃ₗ[ZMod 3] V}
    (hy : ∀ h ∈ omegaGroup hQ,
      h * fr.signChange {0, 1, 2, 3} = fr.signChange {0, 1, 2, 3} * h → Odd (orderOf h) →
        y * (h : V ≃ₗ[ZMod 3] V) = (h : V ≃ₗ[ZMod 3] V) * y) :
    ∀ g ∈ twoRes (omegaGroup hQ ⊓ Subgroup.centralizer
        ({fr.signChange {0, 1, 2, 3}} : Set (OGroup Q))),
      y * (g : V ≃ₗ[ZMod 3] V) = (g : V ≃ₗ[ZMod 3] V) * y := by
  classical
  let S : Subgroup (OGroup Q) :=
    (Subgroup.centralizer ({y} : Set (V ≃ₗ[ZMod 3] V))).comap
      (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
  have hS : ∀ g : OGroup Q, g ∈ S ↔
      y * (g : V ≃ₗ[ZMod 3] V) = (g : V ≃ₗ[ZMod 3] V) * y := by
    intro g
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    constructor
    · intro h; exact h y (Set.mem_singleton y)
    · intro h z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact h
  have hle : twoRes (omegaGroup hQ ⊓ Subgroup.centralizer
      ({fr.signChange {0, 1, 2, 3}} : Set (OGroup Q))) ≤ S := by
    rw [twoRes, Subgroup.closure_le]
    rintro g ⟨hgH, hgodd⟩
    exact (hS g).mpr (hy g hgH.1 (Subgroup.mem_centralizer_singleton_iff.mp hgH.2) hgodd)
  intro g hg
  exact (hS g).mp (hle hg)

private theorem sec5m1t_aux_pair_mem_twoRes (hQ : Q.Nondegenerate) {c : ZMod 3}
    (fr : NFrame Q (Fin 6) c) {i j : Fin 6} (hi : (i : ℕ) < 4) (hj : (j : ℕ) < 4)
    (hij : i ≠ j) :
    fr.signChange ({i, j} : Finset (Fin 6)) ∈
      twoRes (omegaGroup hQ ⊓ Subgroup.centralizer
        ({fr.signChange {0, 1, 2, 3}} : Set (OGroup Q))) := by
  obtain ⟨k, hk4, hki, hkj⟩ := sec5m1t_aux_exists_k i j hi hj hij
  let σ : Equiv.Perm (Fin 6) := Equiv.swap i j * Equiv.swap j k
  have hσ3 : σ ^ 3 = 1 := sec5m1t_aux_swap3 i j k hij hki hkj
  have hσalt : σ ∈ alternatingGroup (Fin 6) := sec5m1t_aux_alt i j k hij hki hkj
  have hσpres : ({0, 1, 2, 3} : Finset (Fin 6)).map σ.toEmbedding = {0, 1, 2, 3} :=
    sec5m1t_aux_preserve i j k hi hj hk4
  have hσsymm : symmDiff ({i, j} : Finset (Fin 6))
      (({i, j} : Finset (Fin 6)).map σ.toEmbedding) =
      ((({i, j} : Finset (Fin 6)).map σ.toEmbedding)).map σ.toEmbedding :=
    sec5m1t_aux_symm i j k hij hki hkj
  have hp : fr.permOrth σ ∈ omegaGroup hQ ⊓ Subgroup.centralizer
      ({fr.signChange {0, 1, 2, 3}} : Set (OGroup Q)) :=
    ⟨fr.permOrth_mem_omegaGroup hQ hσalt,
      Subgroup.mem_centralizer_singleton_iff.mpr (fr.permOrth_comm_signChange hσpres)⟩
  have ht : fr.signChange ({i, j} : Finset (Fin 6)) ∈ omegaGroup hQ ⊓
      Subgroup.centralizer ({fr.signChange {0, 1, 2, 3}} : Set (OGroup Q)) :=
    ⟨fr.signChange_mem_omegaGroup hQ _ (by rw [Finset.card_pair hij]; decide),
      Subgroup.mem_centralizer_singleton_iff.mpr (fr.signChange_comm _ _)⟩
  exact NFrame.signChange_mem_twoRes fr hσ3 hp ht hσsymm

private theorem sec5m1t_aux_threeCycle_mem_twoRes (hQ : Q.Nondegenerate) {c : ZMod 3}
    (fr : NFrame Q (Fin 6) c) {σ : Equiv.Perm (Fin 6)} (hσ3 : σ ^ 3 = 1)
    (hσalt : σ ∈ alternatingGroup (Fin 6))
    (hσpres : ({0, 1, 2, 3} : Finset (Fin 6)).map σ.toEmbedding = {0, 1, 2, 3}) :
    fr.permOrth σ ∈ twoRes (omegaGroup hQ ⊓ Subgroup.centralizer
        ({fr.signChange {0, 1, 2, 3}} : Set (OGroup Q))) := by
  refine subset_closure ⟨⟨fr.permOrth_mem_omegaGroup hQ hσalt,
    Subgroup.mem_centralizer_singleton_iff.mpr (fr.permOrth_comm_signChange hσpres)⟩, ?_⟩
  have hp3 : (fr.permOrth σ) ^ 3 = 1 := by
    rw [pow_three, ← fr.permOrth_mul, ← fr.permOrth_mul, ← pow_three, hσ3, fr.permOrth_one]
  exact Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hp3)

theorem sec5m1t_diag_of_odd (hQ : Q.Nondegenerate) {c : ZMod 3} (fr : NFrame Q (Fin 6) c)
    {y : V ≃ₗ[ZMod 3] V}
    (hy : ∀ h ∈ omegaGroup hQ,
      h * fr.signChange {0, 1, 2, 3} = fr.signChange {0, 1, 2, 3} * h → Odd (orderOf h) →
        y * (h : V ≃ₗ[ZMod 3] V) = (h : V ≃ₗ[ZMod 3] V) * y) :
    ∃ a : ZMod 3, a ≠ 0 ∧ ∀ l : Fin 6, (l : ℕ) < 4 → y (fr.b l) = a • fr.b l := by
  have hcomm := sec5m1t_aux_comm_twoRes hQ fr hy
  have ht : ∀ i j : Fin 6, (i : ℕ) < 4 → (j : ℕ) < 4 → i ≠ j →
      y * ((fr.signChange {i, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) =
        ((fr.signChange {i, j} : OGroup Q) : V ≃ₗ[ZMod 3] V) * y :=
    fun i j hi hj hij => hcomm _ (sec5m1t_aux_pair_mem_twoRes hQ fr hi hj hij)
  have hp₁ : y * ((fr.permOrth sec5m1tC012 : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((fr.permOrth sec5m1tC012 : OGroup Q) : V ≃ₗ[ZMod 3] V) * y :=
    hcomm _ (sec5m1t_aux_threeCycle_mem_twoRes hQ fr sec5m1t_aux_c012_pow3
      sec5m1t_aux_c012_alt sec5m1t_aux_c012_preserve)
  have hp₂ : y * ((fr.permOrth sec5m1tC123 : OGroup Q) : V ≃ₗ[ZMod 3] V) =
      ((fr.permOrth sec5m1tC123 : OGroup Q) : V ≃ₗ[ZMod 3] V) * y :=
    hcomm _ (sec5m1t_aux_threeCycle_mem_twoRes hQ fr sec5m1t_aux_c123_pow3
      sec5m1t_aux_c123_alt sec5m1t_aux_c123_preserve)
  exact sec5m1t_diag fr ht hp₁ hp₂

end CFSG.OddStandard.SmallF3.Omega
