module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Frames
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.FrameCentralizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.OuterSL

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false

theorem exists_units_zpow_ne_one (K : Type) [Field K] [Finite K] (hq : 4 ≤ Nat.card K) :
    ∃ t : Kˣ, ∀ m : ℤ, m ≠ 0 → |m| ≤ 2 → t ^ m ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨t, fun m hm0 hm2 h => ?_⟩
  have hord : orderOf t = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers ht
  have hcard : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have hK : 4 ≤ Nat.card K := hq
  have hdvd : (orderOf t : ℤ) ∣ |m| := (dvd_abs _ _).2 (orderOf_dvd_iff_zpow_eq_one.2 h)
  have hle := Int.le_of_dvd (abs_pos.2 hm0) hdvd
  rw [hord, hcard] at hle
  omega

def frameThetaF4 : Fin (Tag.rank .F4) → ℤ := ![2, 3, 4, 2]

theorem frameThetaF4_mem : frameThetaF4 ∈ rootFinset .F4 := by decide +kernel

def frameThetaE8 : Fin (Tag.rank .E8) → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

theorem frameThetaE8_mem : frameThetaE8 ∈ rootFinset .E8 := by decide +kernel

theorem cartan_pairing_F4 : ∀ α ∈ rootFinset .F4, ∃ k : Fin Tag.F4.rank, k ≠ ⟨1, by decide⟩ ∧
    (∑ j, Tag.F4.cartan k j * α j) ∈ ({1, -1, 2, -2} : Finset ℤ) := by
  decide +kernel

theorem cartan_pairing_E8 : ∀ α ∈ rootFinset .E8, ∃ k : Fin Tag.E8.rank, k ≠ ⟨4, by decide⟩ ∧
    (∑ j, Tag.E8.cartan k j * α j) ∈ ({1, -1, 2, -2} : Finset ℤ) := by
  decide +kernel


theorem commute_of_mem_centralizer_cosetRoots {τ : Tag} {K : Type} [Field K] [Finite K]
    (hq : 4 ≤ Nat.card K) {i₀ : Fin τ.rank} {n : ℕ} {θ : Fin τ.rank → ℤ} (hθ : IsRoot τ θ)
    (hθp : 0 < height θ) (hθn : (n : ℤ) ∣ θ i₀) (hθ0 : θ i₀ ≠ 0)
    (hker : ∀ α ∈ rootFinset τ, ∃ k, k ≠ i₀ ∧
      (∑ j, τ.cartan k j * α j) ∈ ({1, -1, 2, -2} : Finset ℤ))
    {c d : ModGL τ K}
    (hc : c ∈ Subgroup.centralizer (rootSpan τ K (cosetRoots τ i₀ n) : Set (ModGL τ K)) ⊓
      adjointGroup τ K)
    (hd : d ∈ Subgroup.centralizer (rootSpan τ K (cosetRoots τ i₀ n) : Set (ModGL τ K)) ⊓
      adjointGroup τ K) :
    Commute c d := by
  classical
  obtain ⟨t, ht⟩ := exists_units_zpow_ne_one K hq
  have hsingle : ∀ k, k ≠ i₀ → (Pi.single k 1 : Fin τ.rank → ℤ) i₀ = 0 := fun k hk => by
    simp [Ne.symm hk]
  have hJ : ∀ k ∈ {k : Fin τ.rank | k ≠ i₀},
      (Pi.single k 1 : Fin τ.rank → ℤ) ∈ cosetRoots τ i₀ n ∧
        (-Pi.single k 1 : Fin τ.rank → ℤ) ∈ cosetRoots τ i₀ n := by
    intro k hk
    refine ⟨⟨IsRoot.basis k, ?_⟩, ⟨isRoot_neg_single τ k, ?_⟩⟩
    · rw [hsingle k hk]
      exact dvd_zero _
    · rw [Pi.neg_apply, hsingle k hk, neg_zero]
      exact dvd_zero _
  have hker' : ∀ α, IsRoot τ α → ∃ k ∈ {k : Fin τ.rank | k ≠ i₀}, ∃ s : Kˣ,
      s ^ (∑ j, τ.cartan k j * α j) ≠ 1 := by
    intro α hα
    obtain ⟨k, hk, hm⟩ := hker α (mem_rootFinset.2 hα)
    refine ⟨k, hk, t, ht _ ?_ ?_⟩
    · intro h0
      rw [h0] at hm
      simp at hm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hm
      rcases hm with h | h | h | h <;> rw [h] <;> norm_num
  set R : Set (Fin τ.rank → ℤ) := {α | (∃ k, k ≠ i₀ ∧ α = Pi.single k 1) ∨ α = θ} with hR
  have hRS : R ⊆ cosetRoots τ i₀ n := by
    rintro α (⟨k, hk, rfl⟩ | rfl)
    · exact (hJ k hk).1
    · exact ⟨hθ, hθn⟩
  have hRpos : ∀ α ∈ R, IsRoot τ α ∧ 0 < height α := by
    rintro α (⟨k, hk, rfl⟩ | rfl)
    · refine ⟨IsRoot.basis k, ?_⟩
      simp [height, Finset.sum_pi_single']
    · exact ⟨hθ, hθp⟩
  have hRw : ∀ w : WeylGroup τ, (∀ α ∈ R, w • α = α) → w = 1 := by
    intro w hw
    exact eq_one_of_smul_single_of_smul (i₀ := i₀) (fun k hk => hw _ (Or.inl ⟨k, hk, rfl⟩))
      (hw θ (Or.inr rfl)) hθ0
  have hT : ∀ {g : ModGL τ K},
      g ∈ Subgroup.centralizer (rootSpan τ K (cosetRoots τ i₀ n) : Set (ModGL τ K)) ⊓
        adjointGroup τ K → g ∈ torusGroup τ K := fun {g} hg =>
    mem_torusGroup_of_mem_centralizer_rootSpan {k | k ≠ i₀} hJ hker' R hRS hRpos hRw hg.2 hg.1
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (hT hc)
  rw [ha]
  exact rootDiagUnit_mul_comm_of_mem_torusGroup a (hT hd)


theorem frameNormalizerSolvable_F4 (K : Type) [Field K] [Finite K] (hq : 4 ≤ Nat.card K) :
    FrameNormalizerSolvable .F4 K (cosetRoots .F4 1 3) := by
  intro P hPG hPN hPX
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_F4 K
  rw [← hrange] at hPN hPX
  refine isSolvable_of_le_normalizer_frame (isQuasisimple_SL (by norm_num))
    (isSolvable_out_SL (by norm_num)) hA hB hcomm (Gh := adjointGroup .F4 K)
    (hrange ▸ rootSpan_le_adjointGroup K _) (fun c hc d hd => ?_) hPG hPN hPX
  rw [hrange] at hc hd
  exact commute_of_mem_centralizer_cosetRoots hq (mem_rootFinset.1 frameThetaF4_mem)
    (by decide) (by decide) (by decide) cartan_pairing_F4 hc hd

theorem frameNormalizerSolvable_E8
    (K : Type) [Field K] [Finite K] (hq : 4 ≤ Nat.card K) :
    FrameNormalizerSolvable .E8 K (cosetRoots .E8 4 5) := by
  intro P hPG hPN hPX
  obtain ⟨ψA, ψB, hA, hB, hcomm, hrange⟩ := exists_splitFrame_E8 K
  rw [← hrange] at hPN hPX
  refine isSolvable_of_le_normalizer_frame (isQuasisimple_SL (by norm_num))
    (isSolvable_out_SL (by norm_num)) hA hB hcomm (Gh := adjointGroup .E8 K)
    (hrange ▸ rootSpan_le_adjointGroup K _) (fun c hc d hd => ?_) hPG hPN hPX
  rw [hrange] at hc hd
  exact commute_of_mem_centralizer_cosetRoots hq (mem_rootFinset.1 frameThetaE8_mem)
    (by decide) (by decide) (by decide) cartan_pairing_E8 hc hd

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame
