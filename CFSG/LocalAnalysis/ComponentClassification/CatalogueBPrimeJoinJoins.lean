module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinSubnormal

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem exists_le_of_le_sSup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L)
    (subgroups : Set (Subgroup G)) (hsubnormal : ∀ N ∈ subgroups, N.IsSubnormal)
    (hle : L ≤ sSup subgroups) : ∃ N ∈ subgroups, L ≤ N := by
  classical
  by_contra hnone
  let core := pPrimeCore p G
  let q := QuotientGroup.mk' core
  let image := L.map q
  have hcoprime : p.Coprime (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  have himageComponent := (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL
    |>.2.1
  have hcentralizes : sSup subgroups ≤ (Subgroup.centralizer (image : Set _)).comap q := by
    apply sSup_le
    intro N hN
    have hnotLe : ¬ L ≤ N := fun hcontained => hnone ⟨N, hN, hcontained⟩
    have hnotImageLe : ¬ image ≤ N.map q := by
      intro himages
      exact hnotLe (le_of_coprime_kernel_map_le p q (QuotientGroup.mk'_surjective core)
        hcoprime L N hL (hsubnormal N hN) himages)
    have himageSubnormal := Components.chain_of_mathlib_subnormal
      ((hsubnormal N hN).map (QuotientGroup.mk'_surjective core))
    have hcommutes := (LocalComponents.subnormal_contains_or_commutes image (N.map q)
      himageComponent himageSubnormal).resolve_left hnotImageLe
    rw [Subgroup.commutator_comm] at hcommutes
    exact Subgroup.map_le_iff_le_comap.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes)
  have himageCentralizes : image ≤ Subgroup.centralizer (image : Set _) :=
    Subgroup.map_le_iff_le_comap.mpr (hle.trans hcentralizes)
  have himageCommutator : ⁅image, image⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr himageCentralizes
  let : Group.IsPerfect image := ⟨himageComponent.2.2.1⟩
  have himageBot : image = ⊥ := by
    rwa [Subgroup.commutator_eq_self] at himageCommutator
  let : Nontrivial image := Quasisimple.nontrivial himageComponent.2.2
  exact (image.nontrivial_iff_ne_bot.mp inferInstance) himageBot

theorem exists_le_of_le_iSup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) (hL : CFSG.IsPComponent p L)
    {ι : Type*} (N : ι → Subgroup G) (hN : ∀ i, (N i).IsSubnormal)
    (hle : L ≤ iSup N) : ∃ i, L ≤ N i := by
  have hsubnormal : ∀ H ∈ Set.range N, H.IsSubnormal := by
    rintro H ⟨i, rfl⟩
    exact hN i
  obtain ⟨H, ⟨i, rfl⟩, hcontained⟩ := exists_le_of_le_sSup p L hL (Set.range N)
    hsubnormal (by simpa only [sSup_range] using hle)
  exact ⟨i, hcontained⟩

theorem p_component_subnormal_join_irreducibility {G : Type*} [Group G] [Finite G]
    (p : ℕ) (hp : p.Prime) (r : ℕ) (N : Fin r → Subgroup G)
    (hN : ∀ i, (N i).IsSubnormal) (L : Subgroup G) (hL : CFSG.IsPComponent p L)
    (hle : L ≤ iSup N) : ∃ i : Fin r, L ≤ N i := by
  let : Fact p.Prime := ⟨hp⟩
  exact exists_le_of_le_iSup p L hL N hN hle

theorem component_sets_eq_of_sSup_eq {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (C D : Set (Subgroup G))
    (hC : ∀ L ∈ C, CFSG.IsPComponent p L) (hD : ∀ L ∈ D, CFSG.IsPComponent p L)
    (hjoins : sSup C = sSup D) : C = D := by
  apply Set.Subset.antisymm
  · intro L hL
    have hle : L ≤ sSup D := by
      rw [← hjoins]
      exact le_sSup hL
    obtain ⟨K, hK, hcontained⟩ := exists_le_of_le_sSup p L (hC L hL) D
      (fun H hH => (hD H hH).choose_spec.2.1) hle
    have heq := eq_of_le p L K (hC L hL) (hD K hK) hcontained
    exact heq ▸ hK
  · intro L hL
    have hle : L ≤ sSup C := by
      rw [hjoins]
      exact le_sSup hL
    obtain ⟨K, hK, hcontained⟩ := exists_le_of_le_sSup p L (hD L hL) C
      (fun H hH => (hC H hH).choose_spec.2.1) hle
    have heq := eq_of_le p L K (hD L hL) (hC K hK) hcontained
    exact heq ▸ hK

theorem p_component_quasisimplicity_subnormal_join {X : Type*} [Group X] [Finite X]
    (p : ℕ) (hp : p.Prime) (r : ℕ) (N : Fin r → Subgroup X)
    (hN : ∀ i, (N i).IsSubnormal) (hjoin : iSup N = ⊤)
    (hquasisimple : ∀ i, ∀ L : Subgroup (N i),
      CFSG.IsPComponent p L → CFSG.IsQuasisimple L) :
    ∀ L : Subgroup X, CFSG.IsPComponent p L → CFSG.IsQuasisimple L := by
  let : Fact p.Prime := ⟨hp⟩
  intro L hL
  obtain ⟨i, hcontained⟩ := p_component_subnormal_join_irreducibility p hp r N hN L hL
    (by rw [hjoin]; exact le_top)
  have hrestricted := pComponent_restrict_overgroup p hL hcontained
  exact CatalogueBAlternating.quasisimple_iff_native.mpr
    (Components.quasisimple_of_equiv (Subgroup.subgroupOfEquivOfLe hcontained).symm
      (CatalogueBAlternating.quasisimple_iff_native.mp
        (hquasisimple i (L.subgroupOf (N i)) hrestricted)))

end CFSG.ComponentClassification.CatalogueBPrimeJoin
