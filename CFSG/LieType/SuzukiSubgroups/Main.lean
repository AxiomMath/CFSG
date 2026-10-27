module

public import CFSG.LieType.SuzukiSubgroups.Bender
public import CFSG.LieType.SuzukiSubgroups.Subfield

public section

namespace CFSG.LieType.SuzukiSubgroups

open CFSG.Open Subgroup

variable {n : ℕ} {H : Type} [Group H] [Finite H]

theorem le_normalizer_or_isSz
    (hH : CFSG.Quasithin.IsSz n H) {U E : Subgroup H} (hU : U ≠ ⊤) (hEU : E ≤ U)
    (hE : IsElemAbelian 2 E) (hE4 : Nat.card E = 4) :
    (∃ Q : Sylow 2 H, U ≤ normalizer ((Q : Subgroup H) : Set H)) ∨
      ∃ k : ℕ, k ∣ n ∧ k < n ∧ CFSG.Quasithin.IsSz k ↥U := by
  by_cases h : ∃ Q : Sylow 2 H, U ≤ normalizer ((Q : Subgroup H) : Set H)
  · exact Or.inl h
  · push Not at h
    obtain ⟨N, hN, hNodd, a, ha, ⟨e⟩⟩ := exists_normal_sz_of_forall_not_le hH hEU hE hE4 h
    obtain ⟨h1, h2, h3⟩ := isSz_of_normal_sz hH hU hN hNodd ha e
    exact Or.inr ⟨2 * a + 1, h1, h2, h3⟩

end CFSG.LieType.SuzukiSubgroups
