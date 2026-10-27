module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G]

theorem gamma_center_eq {M : Subgroup G} (hM : IsShapeTwoTwoTimesA8 ↥M) {b y : G} (hbM : b ∈ M)
    (hyM : y ∈ M) (hbc : ∀ g ∈ M, b * g = g * b) (hyc : ∀ g ∈ M, y * g = g * y) (hb1 : b ≠ 1)
    (hy1 : y ≠ 1) (hby1 : b * y ≠ 1) (hne : b ≠ y) :
    (Subgroup.center ↥M : Set ↥M) = {1, ⟨y, hyM⟩, ⟨b, hbM⟩, ⟨y, hyM⟩ * ⟨b, hbM⟩} := by
  have hycenter : (⟨y, hyM⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hyc (g : G) g.property).symm
  have hbcenter : (⟨b, hbM⟩ : ↥M) ∈ Subgroup.center ↥M := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hbc (g : G) g.property).symm
  have hsub : ({1, ⟨y, hyM⟩, ⟨b, hbM⟩, ⟨y, hyM⟩ * ⟨b, hbM⟩} : Set ↥M) ⊆
      (Subgroup.center ↥M : Set ↥M) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact hycenter
    · exact hbcenter
    · exact Subgroup.mul_mem _ hycenter hbcenter
  have hS : ({1, ⟨y, hyM⟩, ⟨b, hbM⟩, ⟨y, hyM⟩ * ⟨b, hbM⟩} : Set ↥M).ncard = 4 := by
    refine Set.ncard_eq_four.mpr ⟨1, ⟨y, hyM⟩, ⟨b, hbM⟩,
      ⟨y, hyM⟩ * ⟨b, hbM⟩, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · intro h
      exact hy1 (by simpa using (congrArg Subtype.val h).symm)
    · intro h
      exact hb1 (by simpa using (congrArg Subtype.val h).symm)
    · intro h
      apply hby1
      have hv : (1 : G) = y * b := by simpa using congrArg Subtype.val h
      rw [← hyc b hbM]
      exact hv.symm
    · intro h
      exact hne (congrArg Subtype.val h).symm
    · intro h
      apply hb1
      have hv : y = y * b := congrArg Subtype.val h
      have h1 : y * 1 = y * b := by rw [mul_one]; exact hv
      exact (mul_left_cancel h1).symm
    · intro h
      apply hy1
      have hv : b = y * b := congrArg Subtype.val h
      have h1 : y * b = 1 * b := by rw [one_mul]; exact hv.symm
      exact mul_right_cancel h1
  have hcard : Nat.card ↥(Subgroup.center ↥M) = 4 := by
    obtain ⟨e⟩ := hM
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    rw [Subgroup.center_prod]
    rw [Nat.card_congr (Subgroup.prodEquiv (Subgroup.center (Elem2 2))
      (Subgroup.center (alternatingGroup (Fin 8)))).toEquiv]
    rw [Nat.card_prod]
    have hE : Nat.card ↥(Subgroup.center (Elem2 2)) = 4 := by
      have e : ↥(Subgroup.center (Elem2 2)) ≃ Elem2 2 :=
        { toFun := fun x => x.1
          invFun := fun x => ⟨x, by
            rw [Subgroup.mem_center_iff]
            intro y
            exact mul_comm y x⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
      rw [Nat.card_congr e]
      change Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      norm_num
    have hA : Nat.card ↥(Subgroup.center (alternatingGroup (Fin 8))) = 1 := by
      rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 8))]
      exact Subgroup.card_bot
    rw [hE, hA, mul_one]
  have hcenter : (Subgroup.center ↥M : Set ↥M).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcenter, hS])).symm

theorem gamma_inf_center_eq {M L : Subgroup G} {b y w : G} (hbM : b ∈ M) (hyM : y ∈ M)
    (hwM : w ∈ M) (hw : w = y ∨ w = b)
    (hZ : (Subgroup.center ↥M : Set ↥M) = {1, ⟨y, hyM⟩, ⟨b, hbM⟩, ⟨y, hyM⟩ * ⟨b, hbM⟩})
    (h : L ⊓ Subgroup.closure {b, y} = Subgroup.zpowers w) :
    L.subgroupOf M ⊓ Subgroup.center ↥M = Subgroup.zpowers ⟨w, hwM⟩ := by
  ext g
  rw [Subgroup.mem_inf]
  constructor
  · intro hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hgL : (g : G) ∈ L := hg.1
    have hval_mem : (g : G) ∈ Subgroup.closure ({b, y} : Set G) := by
      obtain ⟨_, hgZ⟩ := hg
      change g ∈ (Subgroup.center ↥M : Set ↥M) at hgZ
      rw [hZ] at hgZ
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgZ
      rcases hgZ with rfl | rfl | rfl | rfl
      · exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.subset_closure (by simp)
      · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))
    have hzw : (g : G) ∈ Subgroup.zpowers w := by
      have hinf : (g : G) ∈ L ⊓ Subgroup.closure ({b, y} : Set G) := ⟨hgL, hval_mem⟩
      rwa [h] at hinf
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzw
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    apply Subtype.ext
    exact hk
  · intro hg
    have hwcenter : (⟨w, hwM⟩ : ↥M) ∈ Subgroup.center ↥M := by
      change (⟨w, hwM⟩ : ↥M) ∈ (Subgroup.center ↥M : Set ↥M)
      rw [hZ]
      rcases hw with rfl | rfl <;> simp
    refine ⟨?_, (Subgroup.zpowers_le.mpr hwcenter) hg⟩
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hzw : (g : G) ∈ Subgroup.zpowers w := by
      rw [Subgroup.mem_zpowers_iff]
      refine ⟨k, ?_⟩
      have hv := congrArg Subtype.val hk
      simpa using hv
    rw [← h] at hzw
    exact hzw.1

end CFSG.EvenSporadicStandard.HNRecog.Section3
