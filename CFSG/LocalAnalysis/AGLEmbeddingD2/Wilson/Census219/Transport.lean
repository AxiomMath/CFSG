module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.TripleCoverKit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Census219

open CFSG.RankThree.PartTwo.Sec21 Subgroup

theorem isCentral218_data {X : Type} [Group X] [Finite X] {x : X}
    (h : IsCentral218 (⊤ : Subgroup X) x) :
    ∃ S : Subgroup X, Nat.card S = 3 ^ (Nat.card X).factorization 3 ∧
      S ≤ centralizer ({x} : Set X) ∧ ∃ k : ℕ, x ^ 3 ^ k = 1 := by
  obtain ⟨S, ⟨Q, hQ⟩, hxS⟩ := h
  refine ⟨S, ?_, ?_, ?_⟩
  · rw [← hQ, Subgroup.card_map_of_injective (⊤ : Subgroup X).subtype_injective,
      Sylow.card_eq_multiplicity Q, Nat.card_congr (Subgroup.topEquiv).toEquiv]
  · obtain ⟨s, hs, rfl⟩ := hxS
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (Subgroup.mem_center_iff.1 hs) ⟨t, ht⟩
    exact congrArg Subtype.val this
  · obtain ⟨s, -, rfl⟩ := hxS
    have hs : (s : X) ∈ Subgroup.map (⊤ : Subgroup X).subtype
        (Q : Subgroup ↥(⊤ : Subgroup X)) := by
      rw [hQ]; exact s.2
    obtain ⟨q, hq, hqs⟩ := hs
    obtain ⟨k, hk⟩ := (Q.isPGroup' ⟨q, hq⟩)
    refine ⟨k, ?_⟩
    have h1 : (q : ↥(⊤ : Subgroup X)) ^ 3 ^ k = 1 := by
      simpa using congrArg (fun z : ↥(Q : Subgroup ↥(⊤ : Subgroup X)) =>
        (z : ↥(⊤ : Subgroup X))) hk
    have h2 : ((q : ↥(⊤ : Subgroup X)) : X) ^ 3 ^ k = 1 := by
      simpa using congrArg (fun z : ↥(⊤ : Subgroup X) => (z : X)) h1
    show (s : X) ^ 3 ^ k = 1
    rw [← hqs]
    exact h2

theorem ks219_transport {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y) (x : X) {m : ℕ}
    {K : Subgroup Y}
    (hK : CFSG.inSubgroup CFSG.layer (centralizer ({φ x} : Set Y)) = K) (hxK : φ x ∈ K)
    {Q : Type*} [Group Q] (e : ↥K ≃* Q)
    (hQ : CFSG.RankThree.PartTwo.Sec4.IsTripleCover Q (alternatingGroup (Fin m))) :
    x ∈ CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) ∧
      CFSG.RankThree.PartTwo.Sec4.IsTripleCover
        ↥(CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X))) (alternatingGroup (Fin m)) := by
  have hmap := Proving.map_inSubgroup_layer_centralizer φ x
  rw [hK] at hmap
  set Lx := CFSG.inSubgroup CFSG.layer (centralizer ({x} : Set X)) with hLx
  have hLxe : Lx = K.comap φ.toMonoidHom := by
    rw [← hmap]
    exact (Subgroup.comap_map_eq_self_of_injective φ.injective Lx).symm
  refine ⟨?_, ?_⟩
  · rw [hLxe]
    exact hxK
  · let e1 : ↥Lx ≃* ↥(Lx.map φ.toMonoidHom) :=
      Subgroup.equivMapOfInjective Lx φ.toMonoidHom φ.injective
    let e2 : ↥(Lx.map φ.toMonoidHom) ≃* ↥K := MulEquiv.subgroupCongr hmap
    exact isTripleCover_of_mulEquiv (e1.trans (e2.trans e)).symm hQ

end CFSG.AGLEmbeddingD2.Wilson.Census219
