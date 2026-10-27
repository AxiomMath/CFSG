module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Layer
public import CFSG.GroupTheory.SwappedFactorsOffenders
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.SeitzReduction.SymplecticPilot CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2] {q : ℕ} {ζ : Fˣ}

section SplitTorus

variable {n : ℕ}

private theorem rootTorusHom_orderOf (k : Fin n) (u : Fˣ) :
    orderOf (rootTorusHom F n k u) = orderOf u :=
  orderOf_injective (rootTorusHom F n k) (rootTorusHom_injective k) u

theorem commute_rootTorusHom_of_ne {i j : Fin n} (hij : i ≠ j) (u v : Fˣ) :
    Commute (rootTorusHom F n i u) (rootTorusHom F n j v) := by
  have h₁ : rootTorusHom F n i u ∈ suppGroup (coords j)ᶜ := by
    refine mem_suppGroup.2 (suppGroup_mono ?_ (isSupp_rootTorusHom i u))
    intro a ha
    rw [Set.mem_compl_iff]
    intro haj
    rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 haj with h | h
    · exact hij (Sum.inl_injective h)
    · exact Sum.inl_ne_inr h
    · exact Sum.inr_ne_inl h
    · exact hij (Sum.inr_injective h)
  have h₂ : rootTorusHom F n j v ∈ suppGroup ((coords j)ᶜ)ᶜ := by
    simpa using mem_suppGroup.2 (isSupp_rootTorusHom j v)
  exact commute_suppGroup_compl h₁ h₂

theorem rootTorusHom_mem_symplecticQTorus_gen {i : Fin n} {ζ : Fˣ}
    (hζ : orderOf ζ = q) :
    rootTorusHom F n i ζ ∈ symplecticQTorus (F := F) (ℓ := n) q := by
  refine (mem_symplecticQTorus (F := F) (ℓ := n)).2
    ⟨Pi.mulSingle i ζ, ?_, rootTorusHom_apply ..⟩
  intro j
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same, ← hζ]
    exact pow_orderOf_eq_one ζ
  · rw [Pi.mulSingle_eq_of_ne hj]
    simp

theorem rootTorusHom_mem_complSp_of_ne_gen {i j : Fin n} (hij : i ≠ j)
    (u : Fˣ) :
    rootTorusHom F n i u ∈ complSp F j := by
  refine suppGroup_mono ?_ (isSupp_rootTorusHom i u)
  intro a ha
  rw [Set.mem_compl_iff]
  intro haj
  rcases mem_coords.1 ha with rfl | rfl <;> rcases mem_coords.1 haj with h | h
  · exact hij (Sum.inl_injective h)
  · exact Sum.inl_ne_inr h
  · exact Sum.inr_ne_inl h
  · exact hij (Sum.inr_injective h)

private theorem rootTorusSp_le_complSp_of_ne {i j : Fin n} (hij : i ≠ j) :
    rootTorusSp F i ≤ complSp F j :=
  fun _ hx => by
    obtain ⟨u, rfl⟩ := hx
    exact rootTorusHom_mem_complSp_of_ne_gen hij u

private theorem disjoint_rootTorusSp_of_ne {i j : Fin n} (hij : i ≠ j) :
    Disjoint (rootTorusSp F i) (rootTorusSp F j) :=
  (disjoint_longRootSp2_complSp (K := F) (k := i)).mono
    (rootTorusSp_le_longRootSp2 i) (rootTorusSp_le_complSp_of_ne (Ne.symm hij))

@[expose] noncomputable def symplecticE2Torus (i j : Fin n) (ζ : Fˣ) :
    Subgroup (StatedSp n F) :=
  Subgroup.zpowers (rootTorusHom F n i ζ) ⊔
    Subgroup.zpowers (rootTorusHom F n j ζ)

theorem rootTorusHom_mem_symplecticE2Torus_left (i j : Fin n) (ζ : Fˣ) :
    rootTorusHom F n i ζ ∈ symplecticE2Torus (F := F) (n := n) i j ζ :=
  Subgroup.mem_sup_left (Subgroup.mem_zpowers _)

theorem rootTorusHom_mem_symplecticE2Torus_right (i j : Fin n) (ζ : Fˣ) :
    rootTorusHom F n j ζ ∈ symplecticE2Torus (F := F) (n := n) i j ζ :=
  Subgroup.mem_sup_right (Subgroup.mem_zpowers _)

theorem card_symplecticE2Torus {i j : Fin n} (hq : q.Prime)
    (hij : i ≠ j) {ζ : Fˣ} (hζ : orderOf ζ = q) :
    Nat.card (symplecticE2Torus (F := F) (n := n) i j ζ) = q ^ 2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard_i : Nat.card (Subgroup.zpowers (rootTorusHom F n i ζ)) = q := by
    rw [Nat.card_zpowers, rootTorusHom_orderOf, hζ]
  have hcard_j : Nat.card (Subgroup.zpowers (rootTorusHom F n j ζ)) = q := by
    rw [Nat.card_zpowers, rootTorusHom_orderOf, hζ]
  have hdisj : Disjoint (Subgroup.zpowers (rootTorusHom F n i ζ))
      (Subgroup.zpowers (rootTorusHom F n j ζ)) :=
    (disjoint_rootTorusSp_of_ne hij).mono
      (Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp i ζ))
      (Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp j ζ))
  have hnorm : Subgroup.zpowers (rootTorusHom F n j ζ) ≤
      Subgroup.normalizer (Subgroup.zpowers (rootTorusHom F n i ζ) : Set _) := by
    refine Subgroup.le_normalizer_iff.2 fun b hb a ha => ?_
    obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hc : Commute ((rootTorusHom F n i ζ) ^ r)
        ((rootTorusHom F n j ζ) ^ s) :=
      ((commute_rootTorusHom_of_ne hij ζ ζ).zpow_left r).zpow_right s
    have hconj : (rootTorusHom F n j ζ) ^ s * (rootTorusHom F n i ζ) ^ r *
        ((rootTorusHom F n j ζ) ^ s)⁻¹ = (rootTorusHom F n i ζ) ^ r := by
      rw [hc.symm.eq]
      group
    rw [hconj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) r
  rw [symplecticE2Torus,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (G := StatedSp n F) _ _ hnorm hdisj, hcard_i, hcard_j]
  ring

theorem symplecticE2Torus_le_symplecticQTorus {i j : Fin n} {ζ : Fˣ}
    (hζ : orderOf ζ = q) :
    symplecticE2Torus (F := F) (n := n) i j ζ ≤
      symplecticQTorus (F := F) (ℓ := n) q :=
  sup_le (Subgroup.zpowers_le.2 (rootTorusHom_mem_symplecticQTorus_gen hζ))
    (Subgroup.zpowers_le.2 (rootTorusHom_mem_symplecticQTorus_gen hζ))

end SplitTorus

section E3

variable {m : ℕ}

theorem rootTorusHom_mem_symplecticQTorus {i : Fin (m + 1)} {ζ : Fˣ}
    (hζ : orderOf ζ = q) :
    rootTorusHom F (m + 1) i ζ ∈ symplecticQTorus (F := F) (ℓ := m + 1) q :=
  rootTorusHom_mem_symplecticQTorus_gen (F := F) (n := m + 1) hζ

@[expose] noncomputable def symplecticE3Torus (i j k : Fin (m + 1)) (ζ : Fˣ) :
    Subgroup (StatedSp (m + 1) F) :=
  (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
    Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)) ⊔
      Subgroup.zpowers (rootTorusHom F (m + 1) k ζ)

theorem rootTorusHom_mem_symplecticE3Torus (i j k : Fin (m + 1)) (ζ : Fˣ) :
    rootTorusHom F (m + 1) i ζ ∈ symplecticE3Torus (F := F) (m := m) i j k ζ :=
  Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))

theorem isElemAbelian_symplecticE3Torus {i j k : Fin (m + 1)} (hq : q.Prime)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {ζ : Fˣ} (hζ : orderOf ζ = q) :
    IsElemAbelian q (symplecticE3Torus (F := F) (m := m) i j k ζ) := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hord_i : orderOf (rootTorusHom F (m + 1) i ζ) = q := by
    rw [rootTorusHom_orderOf, hζ]
  have hord_j : orderOf (rootTorusHom F (m + 1) j ζ) = q := by
    rw [rootTorusHom_orderOf, hζ]
  have hord_k : orderOf (rootTorusHom F (m + 1) k ζ) = q := by
    rw [rootTorusHom_orderOf, hζ]
  have hXi : IsElemAbelian q
      (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ)) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hord_i]; exact pow_orderOf_eq_one _)
  have hXj : IsElemAbelian q
      (Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hord_j]; exact pow_orderOf_eq_one _)
  have hXk : IsElemAbelian q
      (Subgroup.zpowers (rootTorusHom F (m + 1) k ζ)) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hord_k]; exact pow_orderOf_eq_one _)
  have hcomm_ij : ∀ a ∈ Subgroup.zpowers (rootTorusHom F (m + 1) i ζ),
      ∀ b ∈ Subgroup.zpowers (rootTorusHom F (m + 1) j ζ), a * b = b * a := by
    intro a ha b hb
    obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (((commute_rootTorusHom_of_ne hij ζ ζ).zpow_left r).zpow_right s).eq
  have hXij := hXi.sup_of_commute hXj hcomm_ij
  have hcomm_ijk : ∀ a ∈ (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
      Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)),
      ∀ b ∈ Subgroup.zpowers (rootTorusHom F (m + 1) k ζ), a * b = b * a := by
    intro a ha b hb
    obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hsupC : (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
        Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)) ≤
        Subgroup.centralizer ({rootTorusHom F (m + 1) k ζ} : Set (StatedSp (m + 1) F)) :=
      sup_le
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
          (commute_rootTorusHom_of_ne hik ζ ζ).eq))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_singleton_iff.2
          (commute_rootTorusHom_of_ne hjk ζ ζ).eq))
    have hcomm : Commute a (rootTorusHom F (m + 1) k ζ) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hsupC ha)
    exact (hcomm.zpow_right s).eq
  exact hXij.sup_of_commute hXk hcomm_ijk

theorem card_symplecticE3Torus {i j k : Fin (m + 1)} (hq : q.Prime)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {ζ : Fˣ} (hζ : orderOf ζ = q) :
    Nat.card (symplecticE3Torus (F := F) (m := m) i j k ζ) = q ^ 3 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hcard_i : Nat.card (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ)) = q := by
    rw [Nat.card_zpowers, rootTorusHom_orderOf, hζ]
  have hcard_j : Nat.card (Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)) = q := by
    rw [Nat.card_zpowers, rootTorusHom_orderOf, hζ]
  have hcard_k : Nat.card (Subgroup.zpowers (rootTorusHom F (m + 1) k ζ)) = q := by
    rw [Nat.card_zpowers, rootTorusHom_orderOf, hζ]
  have hdisj_ij : Disjoint (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ))
      (Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)) :=
    (disjoint_rootTorusSp_of_ne hij).mono
      (Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp i ζ))
      (Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp j ζ))
  have hnorm_j : Subgroup.zpowers (rootTorusHom F (m + 1) j ζ) ≤
      Subgroup.normalizer (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) : Set _) := by
    refine Subgroup.le_normalizer_iff.2 fun b hb a ha => ?_
    obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have hc : Commute ((rootTorusHom F (m + 1) i ζ) ^ r)
        ((rootTorusHom F (m + 1) j ζ) ^ s) :=
      ((commute_rootTorusHom_of_ne hij ζ ζ).zpow_left r).zpow_right s
    have hconj : (rootTorusHom F (m + 1) j ζ) ^ s * (rootTorusHom F (m + 1) i ζ) ^ r *
        ((rootTorusHom F (m + 1) j ζ) ^ s)⁻¹ = (rootTorusHom F (m + 1) i ζ) ^ r := by
      rw [hc.symm.eq]
      group
    rw [hconj]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) r
  have hcard_ij : Nat.card (↥(Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
      Subgroup.zpowers (rootTorusHom F (m + 1) j ζ))) = q * q := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (G := StatedSp (m + 1) F) _ _ hnorm_j hdisj_ij, hcard_i, hcard_j]
  have hdisj_ijk : Disjoint
      (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
        Subgroup.zpowers (rootTorusHom F (m + 1) j ζ))
      (Subgroup.zpowers (rootTorusHom F (m + 1) k ζ)) := by
    refine disjoint_iff_inf_le.mpr ?_
    have hle : (Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
        Subgroup.zpowers (rootTorusHom F (m + 1) j ζ)) ⊓
        Subgroup.zpowers (rootTorusHom F (m + 1) k ζ) ≤
        complSp F k ⊓ longRootSp2 F (m + 1) k :=
      inf_le_inf
        (sup_le
          ((Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp i ζ)).trans
            (rootTorusSp_le_complSp_of_ne hik))
          ((Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp j ζ)).trans
            (rootTorusSp_le_complSp_of_ne hjk)))
        ((Subgroup.zpowers_le.2 (rootTorusHom_mem_rootTorusSp k ζ)).trans
          (rootTorusSp_le_longRootSp2 k))
    refine hle.trans ?_
    exact le_of_eq (disjoint_iff.mp (disjoint_longRootSp2_complSp (K := F) (k := k)).symm)
  have hnorm_k : Subgroup.zpowers (rootTorusHom F (m + 1) k ζ) ≤
      Subgroup.normalizer
        ((Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
          Subgroup.zpowers (rootTorusHom F (m + 1) j ζ) :
            Subgroup (StatedSp (m + 1) F)) : Set _) := by
    have hkC : Subgroup.zpowers (rootTorusHom F (m + 1) k ζ) ≤
        Subgroup.centralizer
          ((Subgroup.zpowers (rootTorusHom F (m + 1) i ζ) ⊔
            Subgroup.zpowers (rootTorusHom F (m + 1) j ζ) : Subgroup _) : Set _) := by
      rw [CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer
        (A := Subgroup.zpowers (rootTorusHom F (m + 1) i ζ))
        (B := Subgroup.zpowers (rootTorusHom F (m + 1) j ζ))]
      exact le_inf
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun a ha => by
          obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
          exact ((commute_rootTorusHom_of_ne hik ζ ζ).zpow_left r).eq))
        (Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun a ha => by
          obtain ⟨r, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
          exact ((commute_rootTorusHom_of_ne hjk ζ ζ).zpow_left r).eq))
    refine Subgroup.le_normalizer_iff.2 fun b hb a ha => ?_
    have hba : a * b = b * a := Subgroup.mem_centralizer_iff.1 (hkC hb) a ha
    have hconj : b * a * b⁻¹ = a := by
      rw [hba.symm]
      group
    rw [hconj]
    exact ha
  rw [symplecticE3Torus,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer
      (G := StatedSp (m + 1) F) _ _ hnorm_k hdisj_ijk, hcard_ij, hcard_k]
  ring

theorem symplecticE3Torus_le_symplecticQTorus {i j k : Fin (m + 1)} {ζ : Fˣ}
    (hζ : orderOf ζ = q) :
    symplecticE3Torus (F := F) (m := m) i j k ζ ≤
      symplecticQTorus (F := F) (ℓ := m + 1) q :=
  sup_le (sup_le (Subgroup.zpowers_le.2 (rootTorusHom_mem_symplecticQTorus hζ))
    (Subgroup.zpowers_le.2 (rootTorusHom_mem_symplecticQTorus hζ)))
    (Subgroup.zpowers_le.2 (rootTorusHom_mem_symplecticQTorus hζ))

end E3

section Block

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ} {q : ℕ} {ζ : Fˣ}

private theorem fin_zero_val (m : ℕ) : (0 : Fin (m + 1)).val = 0 := rfl

private theorem fin_one_val (hm : 3 ≤ m) : (1 : Fin (m + 1)).val = 1 := by
  show 1 % (m + 1) = 1
  exact Nat.mod_eq_of_lt (by omega)

private theorem fin_two_val (hm : 3 ≤ m) : (2 : Fin (m + 1)).val = 2 := by
  show 2 % (m + 1) = 2
  exact Nat.mod_eq_of_lt (by omega)

private def blockEmbed (m : ℕ) : Fin (m - 2) → Fin (m + 1) :=
  fun i => ⟨i.val + 3, by have h := i.isLt; omega⟩

private theorem blockEmbed_val (m : ℕ) (i : Fin (m - 2)) :
    (blockEmbed (m := m) i).val = i.val + 3 := rfl

private theorem blockEmbed_injective (m : ℕ) : Function.Injective (blockEmbed (m := m)) := by
  intro i j h
  have h' := congrArg Fin.val h
  simp only [blockEmbed_val] at h'
  exact Fin.ext (by omega)

private noncomputable def blockSp (m : ℕ) : Subgroup (StatedSp (m + 1) F) :=
  (spEmbed (blockEmbed m) (blockEmbed_injective m)).range

private theorem exists_blockEmbed_eq_iff (hm : 3 ≤ m) (i : Fin (m + 1)) :
    (∃ j : Fin (m - 2), blockEmbed (m := m) j = i) ↔
      i ≠ (0 : Fin (m + 1)) ∧ i ≠ (1 : Fin (m + 1)) ∧ i ≠ (2 : Fin (m + 1)) := by
  have hv0 : (0 : Fin (m + 1)).val = 0 := rfl
  have hv1 : (1 : Fin (m + 1)).val = 1 := by
    show 1 % (m + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hv2 : (2 : Fin (m + 1)).val = 2 := by
    show 2 % (m + 1) = 2
    exact Nat.mod_eq_of_lt (by omega)
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨?_, ?_, ?_⟩ <;> intro h
    · have h' := congrArg Fin.val h
      rw [hv0, blockEmbed_val] at h'
      omega
    · have h' := congrArg Fin.val h
      rw [hv1, blockEmbed_val] at h'
      omega
    · have h' := congrArg Fin.val h
      rw [hv2, blockEmbed_val] at h'
      omega
  · rintro ⟨h0, h1, h2⟩
    have hi0 : i.val ≠ 0 := fun h => h0 (Fin.ext (by rw [hv0]; exact h))
    have hi1 : i.val ≠ 1 := fun h => h1 (Fin.ext (by rw [hv1]; exact h))
    have hi2 : i.val ≠ 2 := fun h => h2 (Fin.ext (by rw [hv2]; exact h))
    have hi : 3 ≤ i.val := by omega
    refine ⟨⟨i.val - 3, by omega⟩, Fin.ext ?_⟩
    show i.val - 3 + 3 = i.val
    omega

private theorem range_blockEmbed (hm : 3 ≤ m) :
    Set.range (Sum.map (blockEmbed (m := m)) (blockEmbed (m := m))) =
      (coords (0 : Fin (m + 1)) ∪ coords (1 : Fin (m + 1)) ∪
        coords (2 : Fin (m + 1)))ᶜ := by
  ext a
  rcases a with i | i
  · simpa [Sum.map, exists_blockEmbed_eq_iff hm i, mem_coords, and_assoc]
  · simpa [Sum.map, exists_blockEmbed_eq_iff hm i, mem_coords, and_assoc]

theorem suppGroup_inf {n : ℕ} {K : Type} [Field K]
    (S T : Set (Fin n ⊕ Fin n)) :
    suppGroup (K := K) S ⊓ suppGroup (K := K) T = suppGroup (K := K) (S ∩ T) := by
  ext x
  rw [Subgroup.mem_inf, mem_suppGroup (K := K), mem_suppGroup (K := K),
    mem_suppGroup (K := K)]
  constructor
  · rintro ⟨hS, hT⟩ r t hrt
    by_cases h : r ∈ S ∧ t ∈ S
    · exact hT r t fun h' => hrt ⟨⟨h.1, h'.1⟩, ⟨h.2, h'.2⟩⟩
    · exact hS r t h
  · intro h
    exact ⟨fun r t hrt => h r t fun h' => hrt ⟨h'.1.1, h'.2.1⟩,
      fun r t hrt => h r t fun h' => hrt ⟨h'.1.2, h'.2.2⟩⟩

private theorem blockSp_eq_inf (hm : 3 ≤ m) :
    blockSp (F := F) (m := m) =
      complSp F (0 : Fin (m + 1)) ⊓ complSp F (1 : Fin (m + 1)) ⊓
        complSp F (2 : Fin (m + 1)) := by
  rw [blockSp, range_spEmbed, range_blockEmbed hm, complSp, complSp, complSp,
    suppGroup_inf, suppGroup_inf]
  congr 1
  ext a
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]
  tauto

private theorem blockSp_le_inf_centralizer (hm : 3 ≤ m) :
    blockSp (F := F) (m := m) ≤
      complSp F (0 : Fin (m + 1)) ⊓ Subgroup.centralizer
        (symplecticE3Torus (F := F) (m := m) (0 : Fin (m + 1)) (1 : Fin (m + 1))
          (2 : Fin (m + 1)) ζ : Set (StatedSp (m + 1) F)) := by
  have hL : blockSp (F := F) (m := m) =
      complSp F (0 : Fin (m + 1)) ⊓ complSp F (1 : Fin (m + 1)) ⊓
        complSp F (2 : Fin (m + 1)) := blockSp_eq_inf hm
  have hL0 : blockSp (F := F) (m := m) ≤ complSp F (0 : Fin (m + 1)) := by
    rw [hL]; exact inf_le_left.trans inf_le_left
  have hL1 : blockSp (F := F) (m := m) ≤ complSp F (1 : Fin (m + 1)) := by
    rw [hL]; exact inf_le_left.trans inf_le_right
  have hL2 : blockSp (F := F) (m := m) ≤ complSp F (2 : Fin (m + 1)) := by
    rw [hL]; exact inf_le_right
  refine le_inf hL0 ?_
  rw [symplecticE3Torus, CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer,
    CFSG.GroupTheory.centralizer_sup_eq_inf_centralizer]
  refine le_inf (le_inf ?_ ?_) ?_
  · exact hL0.trans
      ((complSp_le_centralizer_rootTorusSp (K := F) (0 : Fin (m + 1))).trans
        (Subgroup.centralizer_le (Subgroup.zpowers_le.2
          (rootTorusHom_mem_rootTorusSp 0 ζ))))
  · exact hL1.trans
      ((complSp_le_centralizer_rootTorusSp (K := F) (1 : Fin (m + 1))).trans
        (Subgroup.centralizer_le (Subgroup.zpowers_le.2
          (rootTorusHom_mem_rootTorusSp 1 ζ))))
  · exact hL2.trans
      ((complSp_le_centralizer_rootTorusSp (K := F) (2 : Fin (m + 1))).trans
        (Subgroup.centralizer_le (Subgroup.zpowers_le.2
          (rootTorusHom_mem_rootTorusSp 2 ζ))))

private theorem isQuasisimple_blockSp (hm : 3 ≤ m) (hF : 4 ≤ Nat.card F) :
    CFSG.IsQuasisimple (blockSp (F := F) (m := m)) := by
  have hN : 1 ≤ m - 2 := by omega
  have hQ : CFSG.IsQuasisimple (StatedSp (m - 2) F) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple (m - 2) F hN (Or.inl (Or.inr hF))
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (MonoidHom.ofInjective (spEmbed_injective (blockEmbed_injective m))) hQ

private theorem dvd_card_blockSp (hm : 3 ≤ m) (hq : q.Prime)
    (hqdvd : q ∣ Nat.card F - 1) :
    q ∣ Nat.card (blockSp (F := F) (m := m)) := by
  haveI : NeZero (m - 2) := ⟨by omega⟩
  have hcard : Nat.card (blockSp (F := F) (m := m)) =
      Nat.card (StatedSp (m - 2) F) :=
    Nat.card_congr
      (MonoidHom.ofInjective (spEmbed_injective (blockEmbed_injective m))).toEquiv.symm
  rw [hcard]
  have hrt : q ∣ Nat.card (rootTorusSp F (0 : Fin (m - 2))) := by
    rw [card_rootTorusSp]
    exact hqdvd
  exact hrt.trans (Subgroup.card_subgroup_dvd_card _)

private theorem center_blockSp (hm : 3 ≤ m) :
    Subgroup.center (blockSp (F := F) (m := m)) = ⊥ := by
  haveI : NeZero (m - 2) := ⟨by omega⟩
  exact (center_eq_bot_congr
    (MonoidHom.ofInjective (spEmbed_injective (blockEmbed_injective m)))).2
    (center_statedSp_eq_bot (m - 2))

private theorem blockSp_normal_inf_centralizer (hm : 3 ≤ m) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqdvd : q ∣ Nat.card F - 1) (hζ : orderOf ζ = q) :
    ((blockSp (F := F) (m := m)).subgroupOf
      (complSp F (0 : Fin (m + 1)) ⊓ Subgroup.centralizer
        (symplecticE3Torus (F := F) (m := m) (0 : Fin (m + 1)) (1 : Fin (m + 1))
          (2 : Fin (m + 1)) ζ : Set (StatedSp (m + 1) F)))).Normal := by
  have hζ2 : ζ * ζ ≠ 1 := by
    intro h
    have h2 : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    have hpq : q ∣ 2 := hζ ▸ h2
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hpq)
  have h10 : (1 : Fin (m + 1)) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_one_val hm, fin_zero_val] at h'
    omega
  have h12 : (1 : Fin (m + 1)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_one_val hm, fin_two_val hm] at h'
    omega
  have h20 : (2 : Fin (m + 1)) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_two_val hm, fin_zero_val] at h'
    omega
  have h21 : (2 : Fin (m + 1)) ≠ 1 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_two_val hm, fin_one_val hm] at h'
    omega
  have hL : blockSp (F := F) (m := m) =
      complSp F (0 : Fin (m + 1)) ⊓ complSp F (1 : Fin (m + 1)) ⊓
        complSp F (2 : Fin (m + 1)) := blockSp_eq_inf hm
  have hL0 : blockSp (F := F) (m := m) ≤ complSp F (0 : Fin (m + 1)) := by
    rw [hL]; exact inf_le_left.trans inf_le_left
  have hL1 : blockSp (F := F) (m := m) ≤ complSp F (1 : Fin (m + 1)) := by
    rw [hL]; exact inf_le_left.trans inf_le_right
  have hL2 : blockSp (F := F) (m := m) ≤ complSp F (2 : Fin (m + 1)) := by
    rw [hL]; exact inf_le_right
  have hLH := blockSp_le_inf_centralizer (F := F) (m := m) (ζ := ζ) hm
  refine (Subgroup.normal_subgroupOf_iff hLH).2 ?_
  intro l g hl hg
  obtain ⟨hgJ, hgC⟩ := hg
  have h1E : rootTorusHom F (m + 1) 1 ζ ∈
      symplecticE3Torus (F := F) (m := m) (0 : Fin (m + 1)) (1 : Fin (m + 1))
        (2 : Fin (m + 1)) ζ :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have h2E : rootTorusHom F (m + 1) 2 ζ ∈
      symplecticE3Torus (F := F) (m := m) (0 : Fin (m + 1)) (1 : Fin (m + 1))
        (2 : Fin (m + 1)) ζ :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hg1 : g * rootTorusHom F (m + 1) 1 ζ = rootTorusHom F (m + 1) 1 ζ * g :=
    (Subgroup.mem_centralizer_iff.1 hgC _ h1E).symm
  obtain ⟨u1, y1, hy1, hg_eq⟩ :=
    exists_eq_mul_of_commute_rootTorusHom (k := (1 : Fin (m + 1))) hζ2 hg1
  set a1 : StatedSp (m + 1) F := rootTorusHom F (m + 1) 1 u1 with ha1
  have hu1J : a1 ∈ complSp F (0 : Fin (m + 1)) :=
    rootTorusHom_mem_complSp_of_ne h10 u1
  have hy1J : y1 ∈ complSp F (0 : Fin (m + 1)) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu1J) hgJ
    rw [hg_eq, ha1] at h
    simpa using h
  have hg2 : Commute g (rootTorusHom F (m + 1) 2 ζ) :=
    (Subgroup.mem_centralizer_iff.1 hgC _ h2E).symm
  have hu12 : Commute a1 (rootTorusHom F (m + 1) 2 ζ) :=
    commute_rootTorusHom_of_ne h12 u1 ζ
  have hy1_eq : y1 = a1⁻¹ * g := by
    rw [hg_eq]
    group
  have hy1_comm : y1 * rootTorusHom F (m + 1) 2 ζ =
      rootTorusHom F (m + 1) 2 ζ * y1 := by
    rw [hy1_eq]
    calc a1⁻¹ * g * rootTorusHom F (m + 1) 2 ζ
        = a1⁻¹ * (g * rootTorusHom F (m + 1) 2 ζ) := by group
      _ = a1⁻¹ * (rootTorusHom F (m + 1) 2 ζ * g) := by rw [hg2.eq]
      _ = (a1⁻¹ * rootTorusHom F (m + 1) 2 ζ) * g := by group
      _ = (rootTorusHom F (m + 1) 2 ζ * a1⁻¹) * g := by rw [hu12.inv_left.eq]
      _ = rootTorusHom F (m + 1) 2 ζ * (a1⁻¹ * g) := by group
  obtain ⟨u2, y2, hy2, hy1_eq2⟩ :=
    exists_eq_mul_of_commute_rootTorusHom (k := (2 : Fin (m + 1))) hζ2 hy1_comm
  set a2 : StatedSp (m + 1) F := rootTorusHom F (m + 1) 2 u2 with ha2
  have hu2J0 : a2 ∈ complSp F (0 : Fin (m + 1)) :=
    rootTorusHom_mem_complSp_of_ne h20 u2
  have hu2J1 : a2 ∈ complSp F (1 : Fin (m + 1)) :=
    rootTorusHom_mem_complSp_of_ne h21 u2
  have hy2_0 : y2 ∈ complSp F (0 : Fin (m + 1)) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu2J0) hy1J
    rw [hy1_eq2, ha2] at h
    simpa using h
  have hy2_1 : y2 ∈ complSp F (1 : Fin (m + 1)) := by
    have h := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu2J1) hy1
    rw [hy1_eq2, ha2] at h
    simpa using h
  have hy2L : y2 ∈ blockSp (F := F) (m := m) := by
    rw [hL]
    exact ⟨⟨hy2_0, hy2_1⟩, hy2⟩
  have hl' : l ∈ complSp F (0 : Fin (m + 1)) ⊓ complSp F (1 : Fin (m + 1)) ⊓
      complSp F (2 : Fin (m + 1)) := hL ▸ hl
  have hu1l : Commute a1 l :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 1 ⟨u1, rfl⟩) hl'.1.2
  have hu2l : Commute a2 l :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 2 ⟨u2, rfl⟩) hl'.2
  have hz : y2 * l * y2⁻¹ ∈ blockSp (F := F) (m := m) :=
    Subgroup.mul_mem _
      (Subgroup.mul_mem _ hy2L hl) (Subgroup.inv_mem _ hy2L)
  have hz1mem : y2 * l * y2⁻¹ ∈ complSp F (1 : Fin (m + 1)) := (hL ▸ hz).1.2
  have hz2mem : y2 * l * y2⁻¹ ∈ complSp F (2 : Fin (m + 1)) := (hL ▸ hz).2
  have hz1 : Commute a1 (y2 * l * y2⁻¹) :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 1 ⟨u1, rfl⟩) hz1mem
  have hz2 : Commute a2 (y2 * l * y2⁻¹) :=
    commute_of_mem_longRootSp2_of_mem_complSp
      (rootTorusSp_le_longRootSp2 2 ⟨u2, rfl⟩) hz2mem
  have hconj : g * l * g⁻¹ = y2 * l * y2⁻¹ := by
    rw [hg_eq, hy1_eq2]
    have hz2' : a2 * (y2 * l * y2⁻¹) * a2⁻¹ = y2 * l * y2⁻¹ := by
      rw [hz2.eq]
      group
    have hz1' : a1 * (y2 * l * y2⁻¹) * a1⁻¹ = y2 * l * y2⁻¹ := by
      rw [hz1.eq]
      group
    calc (a1 * (a2 * y2)) * l * (a1 * (a2 * y2))⁻¹
        = a1 * (a2 * (y2 * l * y2⁻¹) * a2⁻¹) * a1⁻¹ := by group
      _ = a1 * (y2 * l * y2⁻¹) * a1⁻¹ := by rw [hz2']
      _ = y2 * l * y2⁻¹ := hz1'
  rw [hconj]
  exact hz

theorem exists_e3_statedSp {F : Type} [Field F] [Finite F] [CharP F 2]
    {m n q : ℕ} {ζ : Fˣ} (hm : 3 ≤ m) (hn : 2 ≤ n) (hcard : Nat.card F = 2 ^ n)
    (hq : q.Prime) (hq2 : q ≠ 2) (hqdvd : q ∣ Nat.card F - 1) (hζ : orderOf ζ = q) :
    ∃ E : Subgroup (StatedSp (m + 1) F),
      E ≤ symplecticQTorus (F := F) (ℓ := m + 1) q ∧ IsElemAbelian q E ∧
        Nat.card E = q ^ 3 ∧ rootTorusHom F (m + 1) 0 ζ ∈ E ∧
        GLAPLayer q (complSp F (0 : Fin (m + 1)) ⊓
          Subgroup.centralizer (E : Set (StatedSp (m + 1) F))) ≠ ⊥ := by
  have hF4 : 4 ≤ Nat.card F := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h01 : (0 : Fin (m + 1)) ≠ 1 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_zero_val, fin_one_val hm] at h'
    omega
  have h02 : (0 : Fin (m + 1)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_zero_val, fin_two_val hm] at h'
    omega
  have h12 : (1 : Fin (m + 1)) ≠ 2 := by
    intro h
    have h' := congrArg Fin.val h
    rw [fin_one_val hm, fin_two_val hm] at h'
    omega
  have hqL : q ∣ Nat.card (↥(blockSp (F := F) (m := m)) ⧸
      Subgroup.center ↥(blockSp (F := F) (m := m))) := by
    have h := dvd_card_blockSp (F := F) (m := m) hm hq hqdvd
    have hc := center_blockSp (F := F) (m := m) hm
    have hquot : Nat.card (↥(blockSp (F := F) (m := m)) ⧸
        Subgroup.center ↥(blockSp (F := F) (m := m))) =
        Nat.card (blockSp (F := F) (m := m)) := by
      rw [hc]
      exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
    rwa [hquot]
  have hQ := isQuasisimple_blockSp (F := F) (m := m) hm hF4
  refine ⟨symplecticE3Torus (F := F) (m := m) (0 : Fin (m + 1)) (1 : Fin (m + 1))
    (2 : Fin (m + 1)) ζ, ?_, ?_, ?_, ?_, ?_⟩
  · exact symplecticE3Torus_le_symplecticQTorus hζ
  · exact isElemAbelian_symplecticE3Torus hq h01 h02 h12 hζ
  · exact card_symplecticE3Torus hq h01 h02 h12 hζ
  · exact rootTorusHom_mem_symplecticE3Torus 0 1 2 ζ
  · refine glaPLayer_ne_bot_of_normal_quasisimple hq ?_
      (blockSp_normal_inf_centralizer hm hq hq2 hqdvd hζ) ?_ hqL
    · exact blockSp_le_inf_centralizer (F := F) (m := m) hm
    · exact ⟨hQ.1.commutator_eq_top, hQ.2.1⟩

end Block

end CFSG.LocalAnalysis.GLTheoremA.Y10F
