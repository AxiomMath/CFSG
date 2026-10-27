module

public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.QuasithinUnique.K1

section Ranks

variable {G : Type} [Group G]

theorem isTwoLocal_normalizer_zpowers {U : Subgroup G} (hU : CFSG.Open.IsElemAbelian 2 U) {u : G}
    (hu : u ∈ U) (hu1 : u ≠ 1) :
    CFSG.Open.IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers u : Set G)) := by
  refine ⟨Subgroup.zpowers u, ?_, ?_, rfl⟩
  · intro hb
    apply hu1
    have h := Subgroup.mem_zpowers u
    rw [hb] at h
    exact Subgroup.mem_bot.mp h
  · have hUp : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hU.2 x x.2)⟩
    exact hUp.to_le (Subgroup.zpowers_le.mpr hu)

theorem isPGroup_zpowers_of_mem_elem {U : Subgroup G} (hU : CFSG.Open.IsElemAbelian 2 U) {u : G}
    (hu : u ∈ U) : IsPGroup 2 (Subgroup.zpowers u) := by
  have hUp : IsPGroup 2 U := fun x => ⟨1, Subtype.ext (by simpa using hU.2 x x.2)⟩
  exact hUp.to_le (Subgroup.zpowers_le.mpr hu)

theorem centralizer_singleton_le_normalizer_zpowers (u : G) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure]
  exact Subgroup.centralizer_le_normalizer _

variable [Finite G]

theorem pRank_top_quotient_le (L : Subgroup G) (N : Subgroup L) [N.Normal] {p : ℕ}
    (hp : p.Prime) (hN : ¬ p ∣ Nat.card N) :
    CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ N)) ≤ CFSG.Open.pRank p L := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.SectionRank.pRank_quotient_eq N hN]
  have h := CFSG.SectionRank.pRank_le_map hp.one_lt L.subtype L.subtype_injective ⊤
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

theorem not_dvd_card_of_isPGroup_two {X : Type*} [Group X] [Finite X] (hX : IsPGroup 2 X)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : ¬ p ∣ Nat.card X := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX
  rw [hn] at hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))

theorem stronglyQuasithin_quotient {X L : Subgroup G} (hLX : L ≤ X)
    (hX : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p X ≤ 2) (N : Subgroup L) [N.Normal]
    (hN : IsPGroup 2 N) : CFSG.Open.SQTKTauCeti.StronglyQuasithin (L ⧸ N) := by
  intro p hp hp2
  have hnd : ¬ p ∣ Nat.card N := not_dvd_card_of_isPGroup_two hN hp hp2
  calc CFSG.Open.pRank p (⊤ : Subgroup (L ⧸ N)) ≤ CFSG.Open.pRank p L :=
        pRank_top_quotient_le L N hp hnd
    _ ≤ CFSG.Open.pRank p X := CFSG.SectionRank.pRank_mono hp.one_lt hLX
    _ ≤ 2 := hX p hp hp2

end Ranks

end CFSG.QuasithinUnique.K1
