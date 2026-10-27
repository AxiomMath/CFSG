module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceNestedTransport

public section

namespace CFSG.ComponentClassification.CatalogueBAlternating

theorem primeCore_two_eq_oddCore (G : Type*) [Group G] :
    pPrimeCore 2 G = Open.componentClassificationOddCore G := by
  unfold pPrimeCore Open.componentClassificationOddCore
  congr 1
  ext N
  exact and_congr_right (fun _ => Nat.coprime_two_left)

theorem pComponent_iff_minimal_image {G : Type*} [Group G] (p : ℕ) (L : Subgroup G) :
    CFSG.IsPComponent p L ↔
      Open.IsSubnormal L ⊤ ∧
      Open.IsComponentOf (L.map (QuotientGroup.mk' (pPrimeCore p G))) ⊤ ∧
      ∀ J : Subgroup G, J ≤ L → Open.IsSubnormal J ⊤ →
        J.map (QuotientGroup.mk' (pPrimeCore p G)) =
          L.map (QuotientGroup.mk' (pPrimeCore p G)) → J = L := by
  constructor
  · rintro ⟨K, hK, hchain, hmap, hminimal⟩
    refine ⟨Components.chain_of_mathlib_subnormal hchain, ?_, ?_⟩
    · rw [hmap]
      exact (CFSG.isComponent_iff_open K).mp hK
    · intro J hJL hJ hJmap
      by_contra hne
      exact hminimal J (lt_of_le_of_ne hJL hne)
        (Components.mathlib_subnormal_of_chain hJ .top) (hJmap.trans hmap)
  · rintro ⟨hchain, hK, hminimal⟩
    refine ⟨L.map (QuotientGroup.mk' (pPrimeCore p G)),
      (CFSG.isComponent_iff_open _).mpr hK,
      Components.mathlib_subnormal_of_chain hchain .top, rfl, ?_⟩
    intro J hJL hJ hmap
    exact hJL.ne (hminimal J hJL.le (Components.chain_of_mathlib_subnormal hJ) hmap)

theorem pComponent_two_iff {G : Type*} [Group G] (L : Subgroup G) :
    CFSG.IsPComponent 2 L ↔ TwoComponents.IsTwoComponent L := by
  rw [pComponent_iff_minimal_image]
  have transport : ∀ (R T : Subgroup G) [R.Normal] [T.Normal], R = T →
      ((Open.IsSubnormal L ⊤ ∧
        Open.IsComponentOf (L.map (QuotientGroup.mk' R)) ⊤ ∧
        ∀ J : Subgroup G, J ≤ L → Open.IsSubnormal J ⊤ →
          J.map (QuotientGroup.mk' R) = L.map (QuotientGroup.mk' R) → J = L) ↔
      (Open.IsSubnormal L ⊤ ∧
        Open.IsComponentOf (L.map (QuotientGroup.mk' T)) ⊤ ∧
        ∀ J : Subgroup G, J ≤ L → Open.IsSubnormal J ⊤ →
          J.map (QuotientGroup.mk' T) = L.map (QuotientGroup.mk' T) → J = L)) := by
    intro R T _ _ heq
    cases heq
    rfl
  exact transport _ _ (primeCore_two_eq_oddCore G)

theorem pComponent_iff_lBalance_top {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    CFSG.IsPComponent p L ↔ Open.lBalanceIsPComponent p ⊤ L := by
  rw [pComponent_iff_minimal_image, LBalance.pComponent_top_iff_minimal_image]

theorem pComponent_subgroupOf_iff_lBalance {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (N L : Subgroup G) (hLN : L ≤ N) :
    CFSG.IsPComponent p (L.subgroupOf N) ↔ Open.lBalanceIsPComponent p N L := by
  rw [pComponent_iff_lBalance_top]
  have h := LBalance.pComponent_nested_iff p N N L le_rfl hLN
  rwa [Subgroup.subgroupOf_self] at h

theorem pComponent_of_normal_subgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (N : Subgroup G) [N.Normal] (L : Subgroup N)
    (hL : CFSG.IsPComponent p L) : CFSG.IsPComponent p (L.map N.subtype) := by
  have hlocal : CFSG.IsPComponent p ((L.map N.subtype).subgroupOf N) := by
    change CFSG.IsPComponent p ((L.map N.subtype).comap N.subtype)
    rwa [Subgroup.comap_map_eq_self_of_injective N.subtype_injective]
  have hrelative := (pComponent_subgroupOf_iff_lBalance p N (L.map N.subtype)
    (Subgroup.map_subtype_le L)).mp hlocal
  exact (pComponent_iff_lBalance_top p _).mpr
    (LBalance.pComponent_normal_extension p N _ hrelative)

theorem pComponent_commutes_normal_p {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L P : Subgroup G)
    (hL : CFSG.IsPComponent p L) [P.Normal] (hP : IsPGroup p P) : ⁅L, P⁆ = ⊥ := by
  let q := QuotientGroup.mk' (pPrimeCore p G)
  let I := P.map q
  let : I.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : Group.IsNilpotent I := (hP.map q).isNilpotent
  have hcomponent := (pComponent_iff_minimal_image p L).mp hL |>.2.1
  have hquotient : ⁅L.map q, I⁆ = ⊥ :=
    LocalComponents.commutes_with_solvable_subnormal _ _ hcomponent
      (Components.chain_of_mathlib_subnormal (inferInstance : I.Normal).isSubnormal)
  have hmap : ⁅L, P⁆.map q = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hquotient
  have hcore : ⁅L, P⁆ ≤ pPrimeCore p G := by
    simpa only [q, QuotientGroup.ker_mk'] using
      (Subgroup.map_eq_bot_iff _).mp hmap
  obtain ⟨k, hcard⟩ := hP.exists_card_eq
  have hcop : (Nat.card P).Coprime (Nat.card (pPrimeCore p G)) := by
    rw [hcard]
    exact (pPrimeCore_coprime_card (p := p) (G := G)).pow_left k
  have hinf := disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)
  apply le_bot_iff.mp
  exact (le_inf (Subgroup.commutator_le_right L P) hcore).trans hinf.le

theorem pComponent_le_centralizer_normal_p {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L P : Subgroup G)
    (hL : CFSG.IsPComponent p L) [P.Normal] (hP : IsPGroup p P) :
    L ≤ Subgroup.centralizer (P : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (pComponent_commutes_normal_p p L P hL hP)

end CFSG.ComponentClassification.CatalogueBAlternating
