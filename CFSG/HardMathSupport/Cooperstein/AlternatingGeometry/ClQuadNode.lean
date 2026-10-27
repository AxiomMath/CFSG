module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClQuadFalse
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClTheta
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ThetaSRange
public import CFSG.HardMathSupport.RichardWeiss.Proving.QuadThreeCycle
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm MulAction CFSG.AGLEmbedding CFSG.Quasithin CFSG.Open CFSG.RankThree.PartTwo
  CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem false_of_matched_quad {X S L : Subgroup G} (hA : Asc81bHyp X S) (hL : IsWeakSBlock X S L)
    (hSL : S ≤ Subgroup.normalizer (L : Set G)) {N : ℕ} (hN : 9 ≤ N)
    {θ : ↥(L ⊔ S) →* Perm (Fin N)} (hNS : NaturalSectionTheta S L N θ)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hsh : ∀ A : Subgroup G, IsMaxElemAbelian S A →
      Offender.OffenderShapeConcl ((A.subgroupOf (L ⊔ S)).map θ))
    (hall : ∀ z : Fin N, ∃ y, z ≠ y ∧
      swap z y ∈ (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))))
    {z : Fin N}
    (hz : Nat.card (orbit (((thompsonJ S).subgroupOf (L ⊔ S)).map θ : Subgroup (Perm (Fin N))) z) = 4) :
    False := by
  classical
  have hA' : Asc81bHyp (L ⊔ S) S := Coordinator.asc81bHyp_sup hA hL.toIsTwoPrimeComponent hSL
  have hS2 : IsPGroup 2 S := hA'.twoRadical.isPGroup
  have hP := pre_of_theta hS2 (le_sup_right : S ≤ L ⊔ S) θ hsh
  set W : Subgroup (Perm (Fin N)) := ((thompsonJ S).subgroupOf (L ⊔ S)).map θ with hW
  have hmatch : ∀ z : Fin N, Classif.partner hP.twoGroup z ≠ z := fun z =>
    (Classif.partner_ne_iff hP.twoGroup).2 (hall z)
  let St : Classif.Setup W _ := ⟨hP, hmatch⟩
  obtain ⟨a, c, P, hc1, hc2, hPprop, hPtrans⟩ := St.exists_quad_group hz
  have hNS' := hNS
  obtain ⟨-, -, -, hAθ, -, -⟩ := hNS'
  have hJS : thompsonJ S ≤ S := iSup_le fun A => iSup_le fun hA => hA.1
  refine Classif.false_of_threeCycle_mem_normalizer hP.twoGroup hmatch
    (Sstar := (S.subgroupOf (L ⊔ S)).map θ) ?_ ?_ hc1 hc2 ?_
  · exact Subgroup.map_mono (Subgroup.comap_mono hJS)
  · exact theta_S_le_normalizer hA' le_sup_right θ W rfl
  · have hΓ : ∃ k : Fin N, k ∉ ({a, St.ω a, c, St.ω c} : Finset (Fin N)) := by
      by_contra h
      push Not at h
      have h1 : ({a, St.ω a, c, St.ω c} : Finset (Fin N)) = Finset.univ :=
        Finset.eq_univ_of_forall h
      have h2 := Finset.card_le_four (a := a) (b := St.ω a) (c := c) (d := St.ω c)
      rw [h1, Finset.card_univ, Fintype.card_fin] at h2
      omega
    have hPS : ∀ p ∈ P, ∃ l : ↥L, (l : G) ∈ S ∧
        θ (Subgroup.inclusion le_sup_left l) = p := by
      intro p hp
      obtain ⟨hpW, hpA, -⟩ := hPprop p hp
      obtain ⟨l, hl⟩ := hAθ p (mem_alternatingGroup.1 hpA |> mem_alternatingGroup.2)
      refine ⟨l, ?_, hl⟩
      obtain ⟨j, hj, hjp⟩ := hpW
      have hjS : (j : G) ∈ S := hJS (Subgroup.mem_subgroupOf.1 hj)
      have h1 : θ (j⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩) = 1 := by
        rw [map_mul, map_inv, hjp, hl, inv_mul_cancel]
      have h2 := hθS _ h1
      have h4 : (l : G) = (j : G) * ((j⁻¹ * ⟨(l : G), (le_sup_left : L ≤ L ⊔ S) l.2⟩ :
          ↥(L ⊔ S)) : G) := by simp
      rw [h4]
      exact S.mul_mem hjS h2
    have hσ3 : (swap a (St.ω a) * swap a c).IsThreeCycle :=
      isThreeCycle_swap_mul_swap_same (Ne.symm (St.hmatch a)) (Ne.symm hc1) (Ne.symm hc2)
    have hσfix : ∀ i : Fin N, i ∉ ({a, St.ω a, c, St.ω c} : Finset (Fin N)) →
        (swap a (St.ω a) * swap a c) i = i := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi.1 hi.2.2.1,
        swap_apply_of_ne_of_ne hi.1 hi.2.1]
    exact RichardWeiss.Proving.threeCycle_mem_normalizer_of_transitive_support hA hL hSL
      (by omega) hNS _ hΓ P hPS (fun p hp => (hPprop p hp).2.2) hPtrans hσ3 hσfix

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
