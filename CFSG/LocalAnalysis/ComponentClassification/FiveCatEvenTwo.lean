module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenBasic

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Even

open CFSG Subgroup

theorem center_eq_bot_of_equiv_alt_five {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 5)) : center G = ⊥ := by
  have hAc : center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  refine eq_bot_iff.mpr fun x hx => ?_
  have h1 : e x ∈ center (alternatingGroup (Fin 5)) := by
    rw [mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hx a]
  rw [hAc, mem_bot] at h1
  exact (mem_bot.mpr (e.injective (h1.trans (map_one e).symm)))

theorem dvd_card_of_two_layers {X : Type} [Group X] [Finite X] {Y A B : Subgroup X}
    (hA : A ≤ Y) (hAp : IsPComponent 2 (A.subgroupOf Y)) (hB : B ≤ Y)
    (hBp : IsPComponent 2 (B.subgroupOf Y)) (hAB : A ≠ B)
    (eA : Nonempty (↥A ⧸ pPrimeCore 2 ↥A ≃* alternatingGroup (Fin 5)))
    (eB : Nonempty (↥B ⧸ pPrimeCore 2 ↥B ≃* alternatingGroup (Fin 5))) :
    3600 ∣ Nat.card ↥Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥Y) with hπ
  have himg : ∀ P : Subgroup X, P ≤ Y → IsPComponent 2 (P.subgroupOf Y) →
      Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5)) →
      Nonempty (↥((P.subgroupOf Y).map π) ≃* alternatingGroup (Fin 5)) := by
    intro P hP hPp ⟨e5⟩
    have hs := ((CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 _).mp
      hPp).1
    obtain ⟨e, -⟩ := UnbalancedCorr.exists_restriction_quotient_equiv_of_subnormal hP hs
    exact ⟨e.symm.trans e5⟩
  have hne : A.subgroupOf Y ≠ B.subgroupOf Y := fun h => by
    rw [subgroupOf_inj, inf_of_le_left hA, inf_of_le_left hB] at h
    exact hAB h
  obtain ⟨-, -, hc, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hAp hBp).2 hne
  have hcomm : (A.subgroupOf Y).map π ≤ centralizer ((B.subgroupOf Y).map π : Set _) := by
    rw [← commutator_eq_bot_iff_le_centralizer, ← map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
    obtain ⟨-, -, hs, -, -⟩ := id hAp
    refine hc.trans (inf_le_left.trans ?_)
    rw [UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hs]
    exact inf_le_right
  set Ab := (A.subgroupOf Y).map π with hAbdef
  set Bb := (B.subgroupOf Y).map π with hBbdef
  have hc' : ∀ (a : ↥Ab) (b : ↥Bb), Commute (Ab.subtype a) (Bb.subtype b) := fun a b =>
    (mem_centralizer_iff.mp (hcomm a.2) b b.2).symm
  obtain ⟨eAb⟩ := himg A hA hAp eA
  obtain ⟨eBb⟩ := himg B hB hBp eB
  have hdisj : Disjoint Ab Bb := by
    rw [disjoint_iff]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨hxA, hxB⟩ := mem_inf.mp hx
    have hz : (⟨x, hxA⟩ : ↥Ab) ∈ center ↥Ab := by
      rw [mem_center_iff]
      intro a
      exact Subtype.ext (mem_centralizer_iff.mp (hcomm a.2) x hxB).symm
    rw [center_eq_bot_of_equiv_alt_five eAb, mem_bot] at hz
    exact (mem_bot.mpr (congrArg Subtype.val hz))
  let ϕ := MonoidHom.noncommCoprod Ab.subtype Bb.subtype hc'
  have hinj : Function.Injective ϕ := by
    rw [MonoidHom.noncommCoprod_injective]
    refine ⟨Ab.subtype_injective, Bb.subtype_injective, ?_⟩
    rw [range_subtype, range_subtype]
    exact hdisj
  have hrange : ϕ.range = Ab ⊔ Bb := by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hcard : Nat.card ↥(Ab ⊔ Bb) = 3600 := by
    rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod,
      card_alt_five eAb, card_alt_five eBb]
  have h1 : Nat.card ↥(Ab ⊔ Bb) ∣ Nat.card (↥Y ⧸ pPrimeCore 2 ↥Y) :=
    Subgroup.card_subgroup_dvd_card _
  have h2 : Nat.card (↥Y ⧸ pPrimeCore 2 ↥Y) ∣ Nat.card ↥Y := Subgroup.card_quotient_dvd_card _
  rw [hcard] at h1
  exact h1.trans h2

end CFSG.ComponentClassification.SolMax.FiveCat.Even
