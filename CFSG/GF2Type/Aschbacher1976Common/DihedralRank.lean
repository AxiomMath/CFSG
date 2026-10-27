module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherKnownGroupFacts
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank

public section

namespace CFSG.GF2Type.Aschbacher1976Common

open CFSG.ComponentClassification.AschbacherKnownGroup

private theorem card_le_of_sylow_equiv {G D : Type} [Group G] [Finite G] [Group D]
    (S : Sylow 2 G) (f : (S : Subgroup G) ≃* D) {N : ℕ}
    (hD : ∀ W : Subgroup D, (∀ w ∈ W, w ^ 2 = 1) → Nat.card W ≤ N) {E : Subgroup G}
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by simpa using hE _ x.property)⟩
  obtain ⟨T, hET⟩ := h2.exists_le_sylow
  let f' : (T : Subgroup G) ≃* D := (Sylow.equiv T S).trans f
  have h := hD ((E.subgroupOf T).map f'.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hE _ hx)
    rw [hx2, map_one])
  rwa [Subgroup.card_map_of_injective f'.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hET).toEquiv] at h

theorem card_le_four_of_dihedral_or_semidihedral {G : Type} [Group G] [Finite G]
    (h : HasDihedralSylowTwo G ∨ HasSemidihedralSylowTwo G) {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  rcases h with ⟨S, n, hn, ⟨f⟩⟩ | ⟨S, n, hn, ⟨f⟩⟩
  · exact card_le_of_sylow_equiv S f
      (fun W hW => CFSG.QuasithinUnique.dihedral_card_le_four (m := n - 1) (by omega) W hW) hE.2
  · exact card_le_of_sylow_equiv S f
      (fun W hW => CFSG.ABGDGroups.semidihedral_card_le_four hn W hW) hE.2

end CFSG.GF2Type.Aschbacher1976Common
