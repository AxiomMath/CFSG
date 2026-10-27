module

public import CFSG.GH74.GLS.Balance.Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutQTrans
import CFSG.GH74.GLS.Balance.Bender.Final

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Balance
open scoped MatrixGroups

theorem aor_isSolvTwoCompSL23_of_hom {C : Type} [Group C] [Finite C] (Vt : Subgroup C)
    (hsub : Vt.IsSubnormal)
    (hχ : ∃ χ : ↥Vt →* SL(2, ZMod 3), Function.Surjective χ ∧ Odd (Nat.card χ.ker)) :
    IsSolvTwoCompSL23 C (Vt ⊔ pPrimeCore 2 C) := by
  obtain ⟨χ, hχs, hodd⟩ := hχ
  refine isSolvTwoCompSL23_of_subnormal Vt hsub χ hχs ?_
  intro n hn
  have hker_le : χ.ker ≤ pPrimeCore 2 ↥Vt :=
    le_sSup ⟨inferInstance, Nat.coprime_two_left.mpr hodd⟩
  have hmap : ((n : C)) ∈ (pPrimeCore 2 ↥Vt).map Vt.subtype :=
    ⟨n, hker_le (MonoidHom.mem_ker.mpr hn), rfl⟩
  exact CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hsub hmap

theorem aor_isSolvTwoCompSL23In_map {Y : Type} [Group Y] {A : Subgroup Y} {W : Subgroup ↥A}
    (h : IsSolvTwoCompSL23 ↥A W) : IsSolvTwoCompSL23In A (W.map A.subtype) := by
  refine ⟨Subgroup.map_subtype_le W, ?_⟩
  have h2 : (W.map A.subtype).subgroupOf A = W :=
    Subgroup.comap_map_eq_self_of_injective A.subtype_injective W
  rw [h2]
  exact h

theorem aor_mem_oPrimeResidualOf_of_two_element {Y : Type} [Group Y] {V : Subgroup Y} {q : Y}
    (hq : q ∈ V) (h2 : ∃ k : ℕ, q ^ (2 ^ k) = 1) : q ∈ oPrimeResidualOf 2 V := by
  obtain ⟨k, hk⟩ := h2
  refine Subgroup.mem_map.mpr ⟨⟨q, hq⟩, ?_, rfl⟩
  exact Subgroup.mem_closure_of_mem ⟨k, Subtype.ext (by simpa using hk)⟩

theorem aor_balance_two_elements {Y : Type} [Group Y] [Finite Y] (x : Y) (hx : orderOf x = 2)
    (K : Subgroup Y) (hKc : K ≤ centralizer ({x} : Set Y))
    (hKs : (K.subgroupOf (centralizer ({x} : Set Y))).IsSubnormal)
    (hχ : ∃ χ : ↥K →* SL(2, ZMod 3), Function.Surjective χ ∧ Odd (Nat.card χ.ker)) :
    (∀ q ∈ K, (∃ k : ℕ, q ^ (2 ^ k) = 1) → q ∈ pPrimePCore 2 Y) ∨
      ∃ J : Subgroup Y, IsPComponent 2 J ∧ x ∈ normalizer (J : Set Y) ∧
        ∀ q ∈ K, (∃ k : ℕ, q ^ (2 ^ k) = 1) → q ∈ J := by
  classical
  let A : Subgroup Y := centralizer ({x} : Set Y)
  have hχ' : ∃ χ : ↥(K.subgroupOf A) →* SL(2, ZMod 3),
      Function.Surjective χ ∧ Odd (Nat.card χ.ker) :=
    aor_exists_hom_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKc) hχ
  have hW : IsSolvTwoCompSL23 ↥A (K.subgroupOf A ⊔ pPrimeCore 2 ↥A) :=
    aor_isSolvTwoCompSL23_of_hom (K.subgroupOf A) hKs hχ'
  let V : Subgroup Y := (K.subgroupOf A ⊔ pPrimeCore 2 ↥A).map A.subtype
  have hV : IsSolvTwoCompSL23In A V := aor_isSolvTwoCompSL23In_map hW
  have hKV : K ≤ V := by
    intro q hq
    exact ⟨⟨q, hKc hq⟩, Subgroup.mem_sup_left (by rw [Subgroup.mem_subgroupOf]; exact hq), rfl⟩
  rcases solvableL2PrimeBalance_proved Y x hx V hV with h1 | ⟨J, hJ, hxJ, hVJ⟩
  · left
    intro q hq h2
    exact h1 (aor_mem_oPrimeResidualOf_of_two_element (hKV hq) h2)
  · right
    exact ⟨J, hJ, hxJ, fun q hq h2 =>
      hVJ (aor_mem_oPrimeResidualOf_of_two_element (hKV hq) h2)⟩

end CFSG.OddStandard.SmallF3.Omega
