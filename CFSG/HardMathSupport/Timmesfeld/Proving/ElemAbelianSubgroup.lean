module

public import CFSG.HardMathSupport.Timmesfeld.Proving.PRankCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Timmesfeld.Proving

open CFSG.Open

variable {G : Type*} [Group G]

theorem isElemAbelian_of_le {p : ℕ} {E Q : Subgroup G} (hE : IsElemAbelian p E)
    (hQE : Q ≤ E) : IsElemAbelian p Q := CFSG.Open.IsElemAbelian.mono hE hQE

theorem exists_elemAbelian_subgroup_card_pow {p k m : ℕ} (hp : p.Prime) [Finite G]
    {E : Subgroup G} (hE : IsElemAbelian p E) (hm : m ≤ k) (hcard : Nat.card E = p ^ k) :
    ∃ Q ≤ E, IsElemAbelian p Q ∧ Nat.card Q = p ^ m := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ^ m ∣ Nat.card E := hcard ▸ pow_dvd_pow p hm
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p hdvd
  have hle : K.map E.subtype ≤ E := fun x hx => by
    obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2
  refine ⟨K.map E.subtype, hle, isElemAbelian_of_le hE hle, ?_⟩
  rw [Subgroup.card_map_of_injective Subtype.val_injective, hK]

theorem le_pRank_of_elemAbelian_card_pow {p k m : ℕ} (hp : p.Prime) [Finite G] {H E : Subgroup G}
    (hEH : E ≤ H) (hE : IsElemAbelian p E) (hcard : Nat.card E = p ^ k) (hm : m ≤ k) :
    m ≤ pRank p H := by
  obtain ⟨Q, hQE, hQ, hQcard⟩ := exists_elemAbelian_subgroup_card_pow hp hE hm hcard
  exact le_pRank_of_elemAbelian_card hp.two_le (hQE.trans hEH) hQ hQcard

end CFSG.HardMathSupport.Timmesfeld.Proving
