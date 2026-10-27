module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPW
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPGen

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {X : Type} [Group X] {t z : G} {T : Subgroup G}
  {π : ↥(centralizer ({z} : Set G)) →* X}

theorem sec5op_final_of_odd (hyp : Sec5OPHyp t z T π) {K : Subgroup G}
    (hKH : K ≤ centralizer ({z} : Set G)) (hgen : twoRes K = K)
    (hodd : ∀ k ∈ K, Odd (orderOf k) → k ∈ sec5op_kerG z T π) :
    ⁅K, sec5op_Y t z⁆ ≤ oddCoreIn (sec5op_Y t z) := by
  let P : Subgroup G :=
    { carrier := {k | k ∈ centralizer ({z} : Set G) ∧
        ∀ y ∈ sec5op_Y t z, k * y * k⁻¹ * y⁻¹ ∈ oddCoreIn (sec5op_Y t z)}
      one_mem' := by
        refine ⟨Subgroup.one_mem _, ?_⟩
        intro y hy
        simpa using Subgroup.one_mem (oddCoreIn (sec5op_Y t z))
      mul_mem' := by
        rintro k₁ k₂ ⟨hk₁H, hk₁⟩ ⟨hk₂H, hk₂⟩
        refine ⟨Subgroup.mul_mem _ hk₁H hk₂H, ?_⟩
        intro y hy
        have h₁ : k₁ * (k₂ * y * k₂⁻¹ * y⁻¹) * k₁⁻¹ ∈ oddCoreIn (sec5op_Y t z) :=
          sec5op_oddCore_Y_normal hyp hk₁H (hk₂ y hy)
        have h₂ : k₁ * y * k₁⁻¹ * y⁻¹ ∈ oddCoreIn (sec5op_Y t z) := hk₁ y hy
        have heq : (k₁ * k₂) * y * (k₁ * k₂)⁻¹ * y⁻¹ =
            (k₁ * (k₂ * y * k₂⁻¹ * y⁻¹) * k₁⁻¹) * (k₁ * y * k₁⁻¹ * y⁻¹) := by
          group
        rw [heq]
        exact Subgroup.mul_mem _ h₁ h₂
      inv_mem' := by
        rintro k ⟨hkH, hk⟩
        refine ⟨Subgroup.inv_mem _ hkH, ?_⟩
        intro y hy
        have hci : (k * y * k⁻¹ * y⁻¹)⁻¹ ∈ oddCoreIn (sec5op_Y t z) :=
          Subgroup.inv_mem _ (hk y hy)
        have hconj := sec5op_oddCore_Y_normal hyp (Subgroup.inv_mem _ hkH) hci
        have heq : k⁻¹ * y * k⁻¹⁻¹ * y⁻¹ =
            k⁻¹ * (k * y * k⁻¹ * y⁻¹)⁻¹ * (k⁻¹)⁻¹ := by
          group
        rw [heq]
        exact hconj }
  have hgenP : ∀ k ∈ K, Odd (orderOf k) → k ∈ P := by
    intro k hkK hkodd
    have hkH : k ∈ centralizer ({z} : Set G) := hKH hkK
    have hker : k ∈ sec5op_kerG z T π := hodd k hkK hkodd
    refine ⟨hkH, ?_⟩
    intro y hy
    have hW : k * y * k⁻¹ * y⁻¹ ∈ sec5op_W hyp := sec5op_comm_mem_W hyp hker hy
    obtain ⟨e, n, hnN, hen⟩ := sec5op_W_decomp hyp hW
    have hz2 : z * z = 1 := by
      simpa [hyp.hz, pow_two] using pow_orderOf_eq_one z
    have hkz : k * z = z * k := Subgroup.mem_centralizer_singleton_iff.mp hkH
    have hNz : ∀ n ∈ sec5op_N hyp, n * z = z * n := fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mp (sec5op_N_le_H hyp hn)
    have hNy : ∀ n ∈ sec5op_N hyp, k * n * k⁻¹ ∈ sec5op_N hyp := fun n hn =>
      sec5op_N_normal hyp hkH hn
    have hmem := sec5op_odd_comm_trick (z := z) (y := k) (h := y) (N := sec5op_N hyp)
      hz2 hkz hNz hNy (sec5op_N_odd hyp) hkodd ⟨e, n, hnN, hen⟩
    exact sec5op_N_le_oddCore hyp hmem
  have hKP : K ≤ P := by
    rw [← hgen]
    change Subgroup.closure {g | g ∈ K ∧ Odd (orderOf g)} ≤ P
    rw [Subgroup.closure_le]
    intro k hk
    exact hgenP k hk.1 hk.2
  refine (Subgroup.commutator_le).mpr (fun k hkK y hy => ?_)
  simpa only [commutatorElement_def] using (hKP hkK).2 y hy

end CFSG.OddStandard.SmallF3.Omega
