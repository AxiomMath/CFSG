module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Odd
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Core
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6ToralA5

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar rootChar_add
  rootChar_zero)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem rootChar_zsmul {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ) (n : ℤ)
    (v : Fin τ.rank → ℤ) : rootChar a (n • v) = rootChar a v ^ n := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul, mul_comm]

theorem rootChar_list_sum_eq_one {τ : Tag} {K : Type} [Field K] (a : Fin τ.rank → Kˣ)
    (l : List ((Fin τ.rank → ℤ) × ℤ)) (h : ∀ x ∈ l, rootChar a x.1 = 1) :
    rootChar a ((l.map fun x => x.2 • x.1).sum) = 1 := by
  induction l with
  | nil => exact rootChar_zero a
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, rootChar_add, rootChar_zsmul, h x List.mem_cons_self,
      one_zpow, one_mul, ih fun y hy => h y (List.mem_cons_of_mem x hy)]

@[expose] def e6BurgDataA : Fin (Tag.rank .E6) → List ((Fin (Tag.rank .E6) → ℤ) × ℤ) :=
  ![[(![1, 0, 0, 0, 0, 0], 2)],
    [(![1, 2, 2, 3, 2, 1], 1), (![1, 0, 0, 0, 0, 0], -1), (![0, 0, 1, 0, 0, 0], -2),
      (![0, 0, 0, 1, 0, 0], -3), (![0, 0, 0, 0, 1, 0], -2), (![0, 0, 0, 0, 0, 1], -1)],
    [(![0, 0, 1, 0, 0, 0], 2)],
    [(![0, 0, 0, 1, 0, 0], 2)],
    [(![0, 0, 0, 0, 1, 0], 2)],
    [(![0, 0, 0, 0, 0, 1], 2)]]

theorem e6BurgDataA_check :
    (∀ j, ∀ x ∈ e6BurgDataA j ++ e6BurgDataA j, x.1 ∈ rootFinset .E6 ∧
      maskChar (listMask (τ := .E6) [false, true, false, false, false, false])
        (Multiplicative.ofAdd x.1) = 1) ∧
    (∀ j, ((e6BurgDataA j).map fun x => x.2 • x.1).sum = (2 : ℤ) • Pi.single j 1) ∧
    (∀ i j, 2 * Tag.E6.cartan i j =
      ((e6BurgDataA i).map fun x => x.2 * corootPair x.1 (Pi.single j 1)).sum) := by
  decide +kernel

@[expose] def e6Gamma2 : List ((Fin (Tag.rank .E6) → ℤ) × ℤ) :=
  [(![1, 0, 0, 0, 0, 0], 1), (![0, 0, 1, 0, 0, 0], 1), (![0, 0, 0, 1, 0, 0], 4),
    (![0, 0, 0, 0, 1, 0], 1), (![0, 0, 0, 0, 0, 1], 5), (![1, 2, 2, 3, 2, 1], 3)]

theorem e6Gamma2_reg : ∀ α ∈ rootFinset .E6,
    (∑ j, regCoweight e6Gamma2 j * α j) ≠ 0 ∧ (∑ j, regCoweight e6Gamma2 j * α j).natAbs < 12 := by
  decide +kernel

theorem e6Gamma2_kernel : ∀ y ∈ e6Gamma2, y.1 ∈ rootFinset .E6 ∧
    maskChar (listMask (τ := .E6) [false, true, false, false, false, false])
      (Multiplicative.ofAdd y.1) = 1 := by
  decide +kernel


theorem burgCoreFor_E6_t2 {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) :
    BurgCoreFor (rootDiagAut .E6 K (bitsTuple e6BitsA5)) := by
  obtain ⟨hd, h1, h2⟩ := e6BurgDataA_check
  have hm : e6BitsA5 = listMask (τ := .E6) [false, true, false, false, false, false] := rfl
  have hker := rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem (K := K) e6BitsA5)
  rw [signTupleBits_bitsTuple hK2] at hker
  have hmemk : ∀ γ, γ ∈ rootFinset .E6 →
      maskChar (listMask (τ := .E6) [false, true, false, false, false, false])
        (Multiplicative.ofAdd γ) = 1 → γ ∈ rootCharKernel (bitsTuple (K := K) e6BitsA5) := by
    intro γ hγ hχ
    rw [hker, hm]
    exact ⟨mem_rootFinset.1 hγ, hχ⟩
  refine ⟨pPrimeCore_fixedSubgroup_rootDiagAut (by
    rw [hm]
    exact pPrimeCore_toralCentralizer_bits_eq_bot hK2 _ e6BurgDataA e6BurgDataA hd h1 h2),
    fun β hβ _ hfix => ?_⟩
  have hb0 : bitsTuple (K := K) e6BitsA5 (e6Node 0) = 1 := by
    simp [bitsTuple, show e6BitsA5 (e6Node 0) = false from by decide]
  obtain ⟨e, rfl⟩ := exists_eq_rootDiagAut_of_odd_fix (Or.inl rfl) hK2 hβ (e6Node 0)
    (fun x hx => hfix x (rankOne_le_fixedSubgroup_rootDiagAut' hb0 hx)) e6Gamma2
    (fun y hy => mem_rootFinset.1 (e6Gamma2_kernel y hy).1)
    (fun y hy u hu => hfix u (rootPair_le_fixedSubgroup
      (hmemk _ (e6Gamma2_kernel y hy).1 (e6Gamma2_kernel y hy).2) hu))
    12 (fun α hα => e6Gamma2_reg α (mem_rootFinset.2 hα))
  have hγ : ∀ γ ∈ rootCharKernel (bitsTuple (K := K) e6BitsA5), rootChar e γ = 1 := by
    intro γ hγ
    refine rootChar_eq_one_of_fix_pinnedX hγ.1 (hfix _ (rootPair_le_fixedSubgroup hγ ?_))
    exact le_sup_left (a := rootSubgroup .E6 K γ) (Subgroup.subset_closure ⟨1, rfl⟩)
  have he2 : e ^ 2 = 1 := by
    funext j
    have hsum := rootChar_list_sum_eq_one e (e6BurgDataA j) fun x hx =>
      hγ _ (hmemk _ (hd j x (List.mem_append_left _ hx)).1 (hd j x (List.mem_append_left _ hx)).2)
    rw [h1 j, rootChar_zsmul, rootChar_single'] at hsum
    exact hsum
  have hsq : rootDiagAut .E6 K e ^ 2 = 1 := by
    change rootDiagAutHom .E6 K e ^ 2 = 1
    rw [← map_pow, he2, map_one]
  have hd2 : orderOf (rootDiagAut .E6 K e) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have h1' : orderOf (rootDiagAut .E6 K e) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hd2 with h | h
    · exact h
    · rw [h] at hβ
      exact absurd hβ (by decide)
  exact orderOf_eq_one_iff.1 h1'

end CFSG.ComponentClassification.Burgoyne.E2
