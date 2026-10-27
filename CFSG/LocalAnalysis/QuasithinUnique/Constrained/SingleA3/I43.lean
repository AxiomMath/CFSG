module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.Suzuki
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Dihedral
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SingleA3.I43Semidihedral

public section

namespace CFSG.QuasithinUnique

theorem i43_of_selfCentralizing_four
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (heven : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T U : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hUT : U ≤ T) (hU4 : Nat.card U = 4) (hUexp : ∀ u ∈ U, u ^ 2 = 1)
    (hC : T ⊓ Subgroup.centralizer (U : Set G) ≤ U) (h16 : 16 ≤ Nat.card T) :
    UniqueSmallModel G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : ¬ 2 ∣ T.index := by simpa only [index_subgroupOf_top] using hT.2.2
  let P : Sylow 2 G := hT.2.1.toSylow hT2
  have hPT : (P : Subgroup G) = T := rfl
  have hne : U ≠ T := by
    rintro rfl
    omega
  rcases suzuki_selfCentralizing_four hT.2.1 hUT hU4 hUexp hC hne with
    ⟨k, hk, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
  · have hcard : Nat.card T = 2 * 2 ^ k := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hk3 : 3 ≤ k := by
      by_contra h
      have hk2 : k = 2 := by omega
      subst hk2
      omega
    obtain ⟨p, hp, hp7, hpf, ⟨f⟩⟩ := i43_dihedral hnonab heven P hk3 ⟨e⟩
    exact Or.inl ⟨p, hp, hp7, hpf, ⟨f⟩⟩
  · rcases i43_semidihedral hnonab heven P hn ⟨e⟩ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end CFSG.QuasithinUnique
