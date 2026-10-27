module

public import CFSG.LieType.Steinberg.CentralExt.AdjointCentrallyClosed

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.ExceptionalCover CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.CentralExt.AdjointClosed

namespace CFSG.LieType.Steinberg.CentralExt.MinusculeClosed

section Torus

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) (k : Type) [Field k]

@[expose] noncomputable def minTorus : (Fin τ.rank → kˣ) →* hV.minGroup k :=
  MonoidHom.noncommPiCoprod (fun a => hV.hHom k a) (by
    intro a b _ s t
    exact hV.torus_commute k a b (hV.hm_mem_torus k a s) (hV.hm_mem_torus k b t))

theorem minTorus_mulSingle (a : Fin τ.rank) (t : kˣ) :
    minTorus hV k (Pi.mulSingle a t) = hV.hm k a t := by
  rw [minTorus, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem minTorus_conj_xm (u : Fin τ.rank → kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : k) :
    minTorus hV k u * hV.xm k γ c * (minTorus hV k u)⁻¹ =
      hV.xm k γ ((rootChar k γ u : k) * c) := by
  induction u using torusVec_induction generalizing c with
  | h1 => simp
  | hmul t t' ht ht' =>
    have e : minTorus hV k (t * t') * hV.xm k γ c * (minTorus hV k (t * t'))⁻¹ =
        minTorus hV k t * (minTorus hV k t' * hV.xm k γ c * (minTorus hV k t')⁻¹) *
          (minTorus hV k t)⁻¹ := by
      rw [map_mul]
      group
    rw [e, ht', ht, map_mul, Units.val_mul, mul_assoc]
  | hsingle a s =>
    rw [minTorus_mulSingle, hV.hm_conj_xm k hγ, rootChar_mulSingle]
    rfl

end Torus

variable {k : Type} [Field k] [Finite k]

theorem e6_exists_section_of_central (hk : 5 ≤ Nat.card k) {E : Type*} [Group E]
    {π : E →* e6Data_valid.minGroup k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e6Data_valid.minGroup k →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ := e6_conclusionB k
  obtain ⟨C, -, hC⟩ := e6Datum_commutatorFormula k _ (roots_eq isFiniteType_cartan_E6) O
  exact exists_section_of_torus isFiniteType_cartan_E6 (RG := e6Data_valid.rootGroup k) hk
    (e6Data_valid.minDatum_roots isFiniteType_cartan_E6 k) (e6_chevalleyExtras k O C hC) hP
    (minTorus e6Data_valid k) (fun t _ hγ c => minTorus_conj_xm e6Data_valid k t hγ c)
    (fun _ hγ => exists_unitVec_of_neighbour neighbour_E6 hγ) hπ hcen

theorem e7_exists_section_of_central (hk : 5 ≤ Nat.card k) {E : Type*} [Group E]
    {π : E →* e7Data_valid.minGroup k} (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) :
    ∃ σ : e7Data_valid.minGroup k →* E, ∀ g, π (σ g) = g := by
  obtain ⟨-, ⟨O⟩, hP, -⟩ := e7_conclusionB k
  obtain ⟨C, -, hC⟩ := e7Datum_commutatorFormula k _ (roots_eq isFiniteType_cartan_E7) O
  exact exists_section_of_torus isFiniteType_cartan_E7 (RG := e7Data_valid.rootGroup k) hk
    (e7Data_valid.minDatum_roots isFiniteType_cartan_E7 k) (e7_chevalleyExtras k O C hC) hP
    (minTorus e7Data_valid k) (fun t _ hγ c => minTorus_conj_xm e7Data_valid k t hγ c)
    (fun _ hγ => exists_unitVec_of_neighbour neighbour_E7 hγ) hπ hcen

end CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
