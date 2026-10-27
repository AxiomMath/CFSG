module

public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open scoped commutatorElement

namespace R1515F

theorem exists_commutator_mul_center {D : Type*} [Group D]
    (h : Group.IsPerfect (D ⧸ Subgroup.center D)) (g : D) :
    ∃ c ∈ commutator D, ∃ w ∈ Subgroup.center D, g = c * w := by
  have hπ : Function.Surjective (QuotientGroup.mk' (Subgroup.center D)) :=
    QuotientGroup.mk'_surjective _
  have hmap : Subgroup.map (QuotientGroup.mk' (Subgroup.center D)) (commutator D) = ⊤ := by
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hπ]
    exact h.commutator_eq_top
  have hg : QuotientGroup.mk' (Subgroup.center D) g ∈
      Subgroup.map (QuotientGroup.mk' (Subgroup.center D)) (commutator D) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.1 hg
  refine ⟨c, hc, c⁻¹ * g, ?_, by simp⟩
  have : (QuotientGroup.mk c : D ⧸ Subgroup.center D) = QuotientGroup.mk g := hcg
  exact QuotientGroup.eq.1 this

theorem center_quotient_center_eq_bot_of_isPerfect_quotient {D : Type*} [Group D]
    (h : Group.IsPerfect (D ⧸ Subgroup.center D)) :
    Subgroup.center (D ⧸ Subgroup.center D) = ⊥ := by
  set Z₂ : Subgroup D :=
    (Subgroup.center (D ⧸ Subgroup.center D)).comap (QuotientGroup.mk' (Subgroup.center D))
    with hZ₂
  have h1 : ⁅Z₂, (⊤ : Subgroup D)⁆ ≤ Subgroup.center D := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ _
    have hc : QuotientGroup.mk' (Subgroup.center D) g₁ ∈
        Subgroup.center (D ⧸ Subgroup.center D) := hg₁
    have h2 := Subgroup.mem_center_iff.1 hc (QuotientGroup.mk' (Subgroup.center D) g₂)
    rw [← QuotientGroup.ker_mk' (Subgroup.center D), MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact h2.symm
  have h2 : ⁅⁅(⊤ : Subgroup D), (⊤ : Subgroup D)⁆, Z₂⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm (⊤ : Subgroup D) Z₂]
      exact Subgroup.commutator_top_right_eq_bot_iff_le_center.2 h1
    · exact Subgroup.commutator_top_right_eq_bot_iff_le_center.2 h1
  have h3 : ⁅commutator D, Z₂⁆ = ⊥ := by
    rw [commutator_def]
    exact h2
  refine eq_bot_iff.2 fun p hp => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
  have hx : x ∈ Z₂ := hp
  have hxc : x ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, hc, w, hw, rfl⟩ := exists_commutator_mul_center h g
    have hcx : ⁅c, x⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hc hx
      rw [h3] at this
      exact Subgroup.mem_bot.1 this
    rw [commutatorElement_eq_one_iff_mul_comm] at hcx
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 hw x, ← mul_assoc, hcx, mul_assoc]
  exact (QuotientGroup.eq_one_iff x).2 hxc

theorem center_eq_bot_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : Subgroup.center T = ⊥) : Subgroup.center S = ⊥ := by
  refine eq_bot_iff.2 fun z hz => ?_
  have hc : e z ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro t
    obtain ⟨s, rfl⟩ := e.surjective t
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz s]
  rw [h, Subgroup.mem_bot] at hc
  exact Subgroup.mem_bot.2 (e.injective (by rw [hc, map_one]))

theorem center_eq_bot_of_equiv_derivedCentralQuotient {S G : Type*} [Group S] [Group G]
    (hS : commutator S = ⊤) (e : S ≃* TauCeti.DerivedCentralQuotient G) :
    Subgroup.center S = ⊥ := by
  haveI : Group.IsPerfect S := ⟨hS⟩
  haveI : Group.IsPerfect (TauCeti.DerivedCentralQuotient G) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact center_eq_bot_of_mulEquiv e
    (center_quotient_center_eq_bot_of_isPerfect_quotient (D := ↥(commutator G)) inferInstance)

end R1515F

theorem centre_eq_bot_of_equiv_lie {S : Type} [Group S] [Finite S] (hS : CFSG.Open.IsQuasisimple S)
    {d : TauCeti.ValidLieTypeIndex} {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    (hd : d.1 = .G2 Q ∨ d.1 = .B 2 Q ∨ d.1 = .A 3 Q) (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) :
    Subgroup.center S = ⊥ := by
  clear hQ hd
  exact R1515F.center_eq_bot_of_equiv_derivedCentralQuotient hS.1 e

end CFSG.LocalAnalysis.RankThreeUC.S15
