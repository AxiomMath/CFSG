module

public import CFSG.GH74.GLS.Stage2.Local.Concl
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29E
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local

theorem isSolvable_of_quot_pPrimePCore {X : Type} [Group X] [Finite X] (M : Subgroup X)
    [M.Normal] (hM : M = pPrimePCore 2 X) {Y : Type} [Group Y] [Group.IsSolvable Y]
    (e : (X ⧸ M) ≃* Y) : Group.IsSolvable X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hM
  let N : Subgroup X := pPrimeCore 2 X
  have hNsol : Group.IsSolvable ↥N :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
  have hNM : N ≤ pPrimePCore 2 X := L29E.pPrimeCore_le_pPrimePCore 2
  let g : X ⧸ N →* Y := QuotientGroup.lift N
    (e.toMonoidHom.comp (QuotientGroup.mk' (pPrimePCore 2 X))) (fun x hx => by
      show e (QuotientGroup.mk' (pPrimePCore 2 X) x) = 1
      have hx1 : QuotientGroup.mk' (pPrimePCore 2 X) x = 1 :=
        (QuotientGroup.eq_one_iff x).mpr (hNM hx)
      rw [hx1, map_one])
  have hQsol : Group.IsSolvable ↥(pCore 2 (X ⧸ N)) := by
    have : Group.IsNilpotent ↥(pCore 2 (X ⧸ N)) := pCore_isPGroup.isNilpotent
    infer_instance
  have hker : g.ker ≤ (pCore 2 (X ⧸ N)).subtype.range := by
    rw [Subgroup.range_subtype]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have h1 : e (QuotientGroup.mk' (pPrimePCore 2 X) x) = 1 := hy
    have h2 : QuotientGroup.mk' (pPrimePCore 2 X) x = 1 := e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hXN : Group.IsSolvable (X ⧸ N) :=
    Group.isSolvable_of_ker_le_range (pCore 2 (X ⧸ N)).subtype g hker
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_lemma29b {G : Type} [Group G] [Finite G] {U : Subgroup G}
    (h : Lemma29b U) : Group.IsSolvable ↥(centralizer (U : Set G)) := by
  obtain ⟨Q, Xg, v, -, -, -, -, -, -, -, -, hq⟩ := h
  have hsub : (O22Of (centralizer (U : Set G))).subgroupOf (centralizer (U : Set G)) =
      pPrimePCore 2 ↥(centralizer (U : Set G)) :=
    Subgroup.comap_map_eq_self_of_injective (centralizer (U : Set G)).subtype_injective _
  rcases hq with ⟨hn, ⟨e⟩⟩ | ⟨hn, ⟨e⟩⟩
  · exact isSolvable_of_quot_pPrimePCore _ hsub e
  · have : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Equiv.Perm.isSolvable (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact isSolvable_of_quot_pPrimePCore _ hsub e

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
