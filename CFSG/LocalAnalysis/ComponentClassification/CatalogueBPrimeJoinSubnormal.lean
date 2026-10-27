module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

theorem coprime_card_restriction_kernel {G H : Type*} [Group G] [Group H]
    (p : ℕ) (f : G →* H) (hker : p.Coprime (Nat.card f.ker))
    (V : Subgroup G) : p.Coprime (Nat.card (f.domRestrict V).ker) := by
  let inclusion : (f.domRestrict V).ker →* f.ker :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hinjective : Function.Injective inclusion := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => z.val) hxy))
  exact hker.of_dvd_right (Subgroup.card_dvd_of_injective inclusion hinjective)

theorem ambient_residual_preimage {G H : Type*} [Group G] [Finite G] [Group H]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : p.Coprime (Nat.card f.ker)) (L : Subgroup G)
    (hL : CFSG.IsPComponent p L) :
    (primeResidual p ((L.map f).comap f)).map ((L.map f).comap f).subtype = L := by
  let I := L.map f
  let V := I.comap f
  let restriction : V →* I := (f.domRestrict V).codRestrict I fun x => x.property
  have hrestriction : Function.Surjective restriction := by
    intro x
    obtain ⟨y, hy⟩ := hf x.val
    have hyV : y ∈ V := by
      change f y ∈ I
      rw [hy]
      exact x.property
    exact ⟨⟨y, hyV⟩, Subtype.ext hy⟩
  have hkernel : restriction.ker = (f.domRestrict V).ker := by
    ext x
    change restriction x = 1 ↔ f x.val = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcoprime : p.Coprime (Nat.card restriction.ker) := by
    rw [hkernel]
    exact coprime_card_restriction_kernel p f hker V
  have hLV : L ≤ V := Subgroup.le_comap_map f L
  have hcover : Function.Surjective (restriction.domRestrict (L.subgroupOf V)) := by
    intro x
    obtain ⟨y, hy, hvalue⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨⟨y, hLV hy⟩, hy⟩, Subtype.ext hvalue⟩
  have hlocal : L.subgroupOf V = primeResidual p V :=
    primeResidual_eq_of_subnormal_covering p restriction hrestriction hcoprime
      (L.subgroupOf V) hL.choose_spec.2.1.subgroupOf
      (primeResidual_eq_top_of_equiv p (Subgroup.subgroupOfEquivOfLe hLV).symm
        (primeResidual_eq_top_of_pComponent p L hL)) hcover
  rw [← hlocal]
  exact Subgroup.map_subgroupOf_eq_of_le hLV

theorem le_of_coprime_kernel_map_le {G H : Type*} [Group G] [Finite G] [Group H]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : p.Coprime (Nat.card f.ker)) (L N : Subgroup G)
    (hL : CFSG.IsPComponent p L) (hN : N.IsSubnormal)
    (himages : L.map f ≤ N.map f) : L ≤ N := by
  let I := N.map f
  let V := I.comap f
  let restriction : V →* I := (f.domRestrict V).codRestrict I fun x => x.property
  have hrestriction : Function.Surjective restriction := by
    intro x
    obtain ⟨y, hy⟩ := hf x.val
    have hyV : y ∈ V := by
      change f y ∈ I
      rw [hy]
      exact x.property
    exact ⟨⟨y, hyV⟩, Subtype.ext hy⟩
  have hkernel : restriction.ker = (f.domRestrict V).ker := by
    ext x
    change restriction x = 1 ↔ f x.val = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hcoprime : p.Coprime (Nat.card restriction.ker) := by
    rw [hkernel]
    exact coprime_card_restriction_kernel p f hker V
  have hNV : N ≤ V := Subgroup.le_comap_map f N
  have hcover : Function.Surjective (restriction.domRestrict (N.subgroupOf V)) := by
    intro x
    obtain ⟨y, hy, hvalue⟩ := Subgroup.mem_map.mp x.property
    exact ⟨⟨⟨y, hNV hy⟩, hy⟩, Subtype.ext hvalue⟩
  have hindex := coprime_index_of_surjective_restriction p restriction hrestriction
    hcoprime (N.subgroupOf V) hcover
  have hresidual := primeResidual_le_subnormal_of_coprime_index p (N.subgroupOf V)
    hN.subgroupOf hindex
  have hLV : L ≤ V := Subgroup.map_le_iff_le_comap.mp himages
  have hgenerated := primeResidual_eq_top_of_equiv p
    (Subgroup.subgroupOfEquivOfLe hLV).symm (primeResidual_eq_top_of_pComponent p L hL)
  have hmap := primeResidual_map_le p (L.subgroupOf V).subtype
  rw [hgenerated] at hmap
  intro x hx
  exact hresidual (hmap ⟨⟨⟨x, hLV hx⟩, hx⟩, Subgroup.mem_top _, rfl⟩)

theorem contains_or_normalizes_core {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (L N : Subgroup G)
    (hL : CFSG.IsPComponent p L) (hN : N.IsSubnormal) :
    L ≤ N ∨ (N ≤ Subgroup.normalizer (L : Set G) ∧
      ⁅L, N⁆ ≤ (pPrimeCore p L).map L.subtype) := by
  let core := pPrimeCore p G
  let q := QuotientGroup.mk' core
  have hkernel : q.ker = core := QuotientGroup.ker_mk' core
  have hcoprime : p.Coprime (Nat.card q.ker) := by
    rw [hkernel]
    exact pPrimeCore_coprime_card
  have himageN := Components.chain_of_mathlib_subnormal
    (hN.map (QuotientGroup.mk'_surjective core))
  have himageL := (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL |>.2.1
  rcases LocalComponents.subnormal_contains_or_commutes (L.map q) (N.map q)
      himageL himageN with hcontained | hcommutes
  · exact Or.inl (le_of_coprime_kernel_map_le p q (QuotientGroup.mk'_surjective core)
      hcoprime L N hL hN hcontained)
  · right
    let V := (L.map q).comap q
    have hnormalizesImage : N.map q ≤ Subgroup.normalizer (L.map q : Set (G ⧸ core)) := by
      rw [Subgroup.commutator_comm] at hcommutes
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutes).trans
        (Subgroup.centralizer_le_normalizer _)
    have hnormalizesV : N ≤ Subgroup.normalizer (V : Set G) :=
      (Subgroup.map_le_iff_le_comap.mp hnormalizesImage).trans
        (Subgroup.le_normalizer_comap q)
    have hcanonical := ambient_residual_preimage p q (QuotientGroup.mk'_surjective core)
      hcoprime L hL
    have hnormalizesL : N ≤ Subgroup.normalizer (L : Set G) := by
      rw [← hcanonical]
      exact hnormalizesV.trans (primeResidual_normalizer_le p V)
    refine ⟨hnormalizesL, ?_⟩
    have hcommutatorCore : ⁅L, N⁆ ≤ core := by
      have hmap : (⁅L, N⁆).map q = ⊥ := by
        rw [Subgroup.map_commutator]
        exact hcommutes
      have hle := (Subgroup.map_eq_bot_iff _).mp hmap
      rwa [hkernel] at hle
    have hcommutatorL : ⁅L, N⁆ ≤ L :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hnormalizesL
    rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection p L hL.choose_spec.2.1,
      Subgroup.subgroupOf_map_subtype]
    exact le_inf hcommutatorCore hcommutatorL

theorem eq_of_le {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (K L : Subgroup G)
    (hK : CFSG.IsPComponent p K) (hL : CFSG.IsPComponent p L) (hle : K ≤ L) : K = L := by
  let q := QuotientGroup.mk' (pPrimeCore p G)
  have hKdata := (CatalogueBAlternating.pComponent_iff_minimal_image p K).mp hK
  have hLdata := (CatalogueBAlternating.pComponent_iff_minimal_image p L).mp hL
  have himages : K.map q = L.map q :=
    LocalComponents.eq_of_le _ _ hKdata.2.1 hLdata.2.1 (Subgroup.map_mono hle)
  exact hLdata.2.2 K hle hKdata.1 himages

end CFSG.ComponentClassification.CatalogueBPrimeJoin
