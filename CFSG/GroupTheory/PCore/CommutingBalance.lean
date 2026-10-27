module

public import CFSG.GroupTheory.PCore.CharacteristicQuotient

public section

namespace CFSG

theorem centralizer_subgroupOf_eq {G : Type*} [Group G]
    (P H : Subgroup G) (hPH : P ≤ H) :
    Subgroup.centralizer (P.subgroupOf H : Set H) =
      (Subgroup.centralizer (P : Set G)).subgroupOf H := by
  ext x
  constructor
  · intro hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp hx (⟨y, hPH hy⟩ : H) hy)
  · intro hx
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx y.val hy)

theorem pPrimeCore_map_subgroupOf {G : Type*} [Group G] (p : ℕ)
    (K H : Subgroup G) (hKH : K ≤ H) :
    ((pPrimeCore p (K.subgroupOf H)).map (K.subgroupOf H).subtype).map H.subtype =
      (pPrimeCore p K).map K.subtype := by
  let e := Subgroup.subgroupOfEquivOfLe hKH
  have hhom : K.subtype.comp e.toMonoidHom = H.subtype.comp (K.subgroupOf H).subtype := by
    ext x
    rfl
  rw [Subgroup.map_map, ← hhom, ← Subgroup.map_map, pPrimeCore_map_iso p e]

theorem pPrimeCore_common_centralizer_eq
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (H P : Subgroup G) (hPH : P ≤ H) (hP : IsPGroup p P)
    (hchar : IsCharacteristicP p (H ⧸ pPrimeCore p H)) :
    (pPrimeCore p (H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)).map
        (H ⊓ Subgroup.centralizer (P : Set G) : Subgroup G).subtype =
      (pPrimeCore p H).map H.subtype ⊓ Subgroup.centralizer (P : Set G) := by
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let I : Subgroup G := H ⊓ C
  let : (pPrimeCore p H).Normal := pPrimeCore_normal
  have hPInternal : IsPGroup p (P.subgroupOf H) :=
    hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hcore := pPrimeCore_centralizer_eq_of_isCharacteristicP_quotient
    H p (pPrimeCore p H) pPrimeCore_coprime_card hchar (P.subgroupOf H) hPInternal
  rw [centralizer_subgroupOf_eq P H hPH] at hcore
  have heq : C.subgroupOf H = I.subgroupOf H := by
    ext x
    change (x.val ∈ C) ↔ x.val ∈ H ⊓ C
    simp only [Subgroup.mem_inf, x.property, true_and]
  rw [heq] at hcore
  have hmapped := congrArg (Subgroup.map H.subtype) hcore
  rw [pPrimeCore_map_subgroupOf p I H inf_le_left,
    Subgroup.map_inf _ _ _ H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le (inf_le_left : I ≤ H)] at hmapped
  calc
    (pPrimeCore p I).map I.subtype = (pPrimeCore p H).map H.subtype ⊓ I := hmapped
    _ = (pPrimeCore p H).map H.subtype ⊓ C := by
      rw [← inf_assoc, inf_eq_left.mpr (Subgroup.map_subtype_le _)]

theorem pPrimeCore_commuting_centralizers_balance
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (P Q : Subgroup G) (hP : IsPGroup p P) (hQ : IsPGroup p Q)
    (hcomm : ⁅P, Q⁆ = ⊥)
    (hPchar : IsCharacteristicP p
      (Subgroup.centralizer (P : Set G) ⧸ pPrimeCore p (Subgroup.centralizer (P : Set G))))
    (hQchar : IsCharacteristicP p
      (Subgroup.centralizer (Q : Set G) ⧸ pPrimeCore p (Subgroup.centralizer (Q : Set G)))) :
    let H := Subgroup.centralizer (P : Set G)
    let K := Subgroup.centralizer (Q : Set G)
    let C : Subgroup G := H ⊓ K
    (pPrimeCore p H).map H.subtype ⊓ K = (pPrimeCore p C).map C.subtype ∧
      (pPrimeCore p C).map C.subtype = (pPrimeCore p K).map K.subtype ⊓ H := by
  dsimp only
  have hQH : Q ≤ Subgroup.centralizer (P : Set G) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rwa [Subgroup.commutator_comm]
  have hPK : P ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  constructor
  · exact (pPrimeCore_common_centralizer_eq G p
      (Subgroup.centralizer (P : Set G)) Q hQH hQ hPchar).symm
  · rw [inf_comm (Subgroup.centralizer (P : Set G)) (Subgroup.centralizer (Q : Set G))]
    exact pPrimeCore_common_centralizer_eq G p
      (Subgroup.centralizer (Q : Set G)) P hPK hP hQchar

end CFSG
