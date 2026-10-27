module

public import CFSG.GH74.QTGen4.Recog.Ku.A3V2

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

omit [Finite G] in
theorem two_eq_zero_natK (h : KuHyp G T M H P z) : (2 : h.mNat.data.K) = 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fintype h.mNat.data.K := Fintype.ofFinite _
  have : CharP h.mNat.data.K 2 := by
    apply charP_of_card_eq_prime_pow (f := 2)
    rw [← Nat.card_eq_fintype_card]
    exact h.mNat.data.card
  exact CharTwo.two_eq_zero

theorem exists_fixed_vec (h : KuHyp G T M H P z) :
    ∃ w : Fin 2 → h.mNat.data.K, w ≠ 0 ∧
      ∀ g : Subgroup.normalizer (pCoreOf 2 M : Set G), (g : G) ∈ kuR T M →
        h.mNat.data.conj g w = w := by
  refine ⟨Multiplicative.toAdd (h.mNat.data.E ⟨z, h.z_mem_pCoreOf⟩), ?_, ?_⟩
  · exact h.z_ne_zero_vec
  · intro g hg
    exact mem_kuFix.mp ((h.mem_kuV2_iff_fix ⟨z, h.z_mem_pCoreOf⟩).mp h.z_mem_kuV2) g hg

omit [Finite G] in
theorem fixed_vec_ne (h : KuHyp G T M H P z) (w : Fin 2 → h.mNat.data.K) (hw : w ≠ 0) :
    w 0 ≠ 0 ∨ w 1 ≠ 0 := by
  by_contra hc
  simp only [not_or, not_not] at hc
  apply hw
  funext i
  fin_cases i
  · exact hc.1
  · exact hc.2

end KuHyp

end CFSG.GH74.QTGen4.Ku
