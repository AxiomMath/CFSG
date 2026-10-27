module

public import CFSG.GH74.GLS.Stage2.Local.P34Bar

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

theorem exists_perfect_lift {M N : Type*} [Group M] [Finite M] [Group N] (f : M →* N)
    (hf : Function.Surjective f) {Q : Subgroup N} (hQ : ⁅Q, Q⁆ = Q) :
    ∃ P : Subgroup M, ⁅P, P⁆ = P ∧ P.map f = Q := by
  classical
  have hex : ∃ n : ℕ, ∃ P : Subgroup M, P.map f = Q ∧ Nat.card ↥P = n :=
    ⟨_, Q.comap f, Subgroup.map_comap_eq_self_of_surjective hf Q, rfl⟩
  obtain ⟨P, hPQ, hPn⟩ := Nat.find_spec hex
  refine ⟨P, ?_, hPQ⟩
  have hle : ⁅P, P⁆ ≤ P := Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) (P.inv_mem hb)
  have himg : (⁅P, P⁆).map f = Q := by rw [Subgroup.map_commutator, hPQ, hQ]
  have hmin := Nat.find_min' hex (m := Nat.card ↥⁅P, P⁆) ⟨⁅P, P⁆, himg, rfl⟩
  rw [← hPn] at hmin
  exact Subgroup.eq_of_le_of_card_ge hle hmin

variable {G : Type} [Group G] [Finite G]

theorem exists_lift_hbar (H : Subgroup G) {z : G} (hCH : Cen z ≤ H) {Q : Subgroup (CentralizerBar z)}
    (hQ : ⁅Q, Q⁆ = Q) :
    ∃ (P : Subgroup (HBar H)) (f : ↥P →* ↥Q), P ≤ barIn H (Cen z) ∧ ⁅P, P⁆ = P ∧
      Function.Surjective f ∧ ∀ p : ↥P, f p = 1 → Odd (orderOf p) := by
  classical
  obtain ⟨P₀, hP₀, hmap⟩ := exists_perfect_lift (cenToBar H hCH) (cenToBar_surjective H hCH) hQ
  let ι : ↥(barIn H (Cen z)) →* HBar H := (barIn H (Cen z)).subtype
  have hι : Function.Injective ι := (barIn H (Cen z)).subtype_injective
  let e : ↥(P₀.map ι) ≃* ↥P₀ := (P₀.equivMapOfInjective ι hι).symm
  let g : ↥P₀ →* ↥Q := ((cenToBar H hCH).comp P₀.subtype).codRestrict Q (fun p => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ p.2)
  refine ⟨P₀.map ι, g.comp e.toMonoidHom, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hP₀]
  · intro q
    have hq : (q : CentralizerBar z) ∈ P₀.map (cenToBar H hCH) := by
      rw [hmap]
      exact q.2
    obtain ⟨p, hp, hpq⟩ := Subgroup.mem_map.1 hq
    refine ⟨e.symm ⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    simpa [g] using hpq
  · intro p hp
    have h1 : cenToBar H hCH (e p : ↥(barIn H (Cen z))) = 1 := by
      have := congrArg Subtype.val hp
      simpa [g] using this
    have h2 := odd_orderOf_of_cenToBar_eq_one H hCH (e p : ↥(barIn H (Cen z))) h1
    rwa [Subgroup.orderOf_coe, MulEquiv.orderOf_eq] at h2

end CFSG.GH74.GLS.Stage2.Local.P34
