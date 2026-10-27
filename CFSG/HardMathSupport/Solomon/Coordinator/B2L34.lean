module

public import CFSG.HardMathSupport.Solomon.Coordinator.B2OddCore
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt

open Subgroup CFSG.Open CFSG.ComponentClassification.PSL3Four
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem glaPPrimeCore_eq_bot_of_simple {H : Type*} [Group H] [Finite H] [IsSimpleGroup H]
    (heven : Even (Nat.card H)) : GLAPPrimeCore 2 H = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (GLAPPrimeCore 2 H) with h | h
  · exact h
  · exfalso
    have hc := CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.coprime_card_GLAPPrimeCore
      Nat.prime_two H
    rw [h, Subgroup.card_top] at hc
    exact absurd (Nat.Coprime.coprime_dvd_right (even_iff_two_dvd.1 heven) hc) (by decide)

theorem commutator_eq_bot_psl34Model [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) (β : MulAut S) (hβ : β ^ 2 = 1) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  by_cases h1 : β = 1
  · exact commutator_eq_bot_of_oddCore hnc β fun h => absurd h1 h
  obtain ⟨e, he, -⟩ := full_automorphism_action
  set r : R := e.symm β with hr
  have hβr : β = e r := by rw [hr, MulEquiv.apply_symm_apply]
  have hr1 : r ≠ 1 := fun h => h1 (by rw [hβr, h, map_one])
  have hr2 : r * r = 1 := by
    apply e.injective
    rw [map_mul, ← hβr, map_one, ← sq, hβ]
  have hmap : (fixSubgroup β).map S.subtype =
      Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      have hfix : β s = s := hs
      refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, s.2⟩
      have h := congrArg Subtype.val hfix
      rw [hβr, he, InvMemClass.coe_inv] at h
      calc (s : Equiv.Perm (Fin 42)) * r
          = (r : Equiv.Perm (Fin 42)) * s * (r : Equiv.Perm (Fin 42))⁻¹ * r := by rw [h]
        _ = r * s := by group
    · rintro ⟨hy, hyS⟩
      refine ⟨⟨y, hyS⟩, ?_, rfl⟩
      show β ⟨y, hyS⟩ = ⟨y, hyS⟩
      have hc := Subgroup.mem_centralizer_singleton_iff.1 hy
      apply Subtype.ext
      rw [hβr, he, InvMemClass.coe_inv]
      show (r : Equiv.Perm (Fin 42)) * y * (r : Equiv.Perm (Fin 42))⁻¹ = y
      calc (r : Equiv.Perm (Fin 42)) * y * (r : Equiv.Perm (Fin 42))⁻¹
          = y * r * (r : Equiv.Perm (Fin 42))⁻¹ := by rw [hc]
        _ = y := by group
  let φ : ↥(fixSubgroup β) ≃* ↥(Subgroup.centralizer {(r : Equiv.Perm (Fin 42))} ⊓ S) :=
    ((fixSubgroup β).equivMapOfInjective S.subtype S.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  rcases (fixed_of_involution hr1 hr2).of_equiv φ with hsol | ⟨hsimp, heven⟩
  · exact commutator_eq_bot_of_isSolvable β hsol
  · have hO : GLAPPrimeCore 2 ↥(fixSubgroup β) = ⊥ := glaPPrimeCore_eq_bot_of_simple heven
    have hO' : GLAPPrimeCoreOf 2 (fixSubgroup β) = ⊥ := by
      rw [GLAPPrimeCoreOf, hO, Subgroup.map_bot]
    rw [hO', Subgroup.commutator_bot_right]

theorem commutator_eq_bot_of_psl34 {S' : Type} [Group S']
    [Finite S'] [IsSimpleGroup S'] (hnc : ∃ a b : S', a * b ≠ b * a)
    (h : StatedClassicalModel S' .PSL 3 2 2) (β : MulAut S') (hβ : β ^ 2 = 1) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  obtain ⟨θ⟩ := exact_model.2.2.2.1 S' h
  have : IsSimpleGroup S := θ.symm.isSimpleGroup
  have hncS : ∃ a b : S, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨θ a, θ b, fun h => hab (θ.injective ?_)⟩
    rw [map_mul, map_mul, h]
  refine commutator_eq_bot_of_mulEquiv θ β (commutator_eq_bot_psl34Model hncS _ ?_)
  show (MulAut.congr θ : MulAut S' →* MulAut S) β ^ 2 = 1
  rw [← map_pow, hβ, map_one]

end CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
