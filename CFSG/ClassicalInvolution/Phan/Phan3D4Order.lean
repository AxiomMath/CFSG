module

public import CFSG.ClassicalInvolution.Phan.Phan3D4Defs
public import CFSG.ClassicalInvolution.Phan.Phan3PermModel
public import CFSG.ClassicalInvolution.Phan.Phan3AModel

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.CosetTable

structure D4Checks : Prop where
  card : Finite PhanD4Group ∧ Nat.card PhanD4Group ≤ 4 * 4952179814400
  ker : ∃ N : Subgroup PhanD4Group, N.Normal ∧ Nat.card N ≤ 4 ∧
    (∀ w ∈ d4CtRels, wordVal ctEltP w ∈ N) ∧
    ∀ i : Fin 8,
      (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ N
  sl3 : Finite (PG 4 sl3Rels) ∧ Nat.card (PG 4 sl3Rels) ≤ 5616

variable (hc : D4Checks)

include hc in
theorem card_phanD4Group_le :
    Finite PhanD4Group ∧ Nat.card PhanD4Group ≤ 1516320 * (2160 * 6048) :=
  ⟨hc.card.1, hc.card.2.trans (by norm_num)⟩

@[expose] noncomputable def d4N : Subgroup PhanD4Group := hc.ker.choose

instance d4N_normal : (d4N hc).Normal := hc.ker.choose_spec.1

include hc in
theorem card_d4N_le : Nat.card (d4N hc) ≤ 4 := hc.ker.choose_spec.2.1

include hc in
theorem wordVal_ctEltP_mem {w : List (Fin 8 × Bool)} (hw : w ∈ d4CtRels) :
    wordVal ctEltP w ∈ d4N hc :=
  hc.ker.choose_spec.2.2.1 w hw

include hc in
theorem gen_mem_d4N (i : Fin 8) :
    (wordVal ctEltP (decodeWord 8 phanInCtCodes[i.val]!))⁻¹ * PresentedGroup.of i ∈ d4N hc :=
  hc.ker.choose_spec.2.2.2 i

include hc in
theorem d4N_le_ker {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) (π : PhanD4Group →* G) (hπ : Function.Surjective π) :
    d4N hc ≤ π.ker := by
  have := hc.card.1
  exact ker_le_ker_of_card_le_four hnab π hπ (d4N hc) (card_d4N_le hc)

end CFSG.ClassicalInvolution.Phan.Q3G
