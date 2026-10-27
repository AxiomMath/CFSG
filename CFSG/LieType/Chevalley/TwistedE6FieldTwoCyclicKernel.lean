module

public import CFSG.LieType.Chevalley.CLSTwistedE6FieldTwoCover
public import CFSG.LieType.Chevalley.OddDiagramFrobeniusFixedDerived
public import CFSG.LieType.Chevalley.TwistedE6NormalForm

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std
open Subgroup

theorem nonempty_mulEquiv_stdGroup_of_card_eq_four
    {L : Type} [Field L] [Finite L]
    (hL : Nat.card L = 4) (σ : L →+* L) (hσ : ∀ c, σ c = c ^ 2) :
    Nonempty (graphFixedRootGroup TwistTag.E6 L σ ≃* stdGroup) := by
  have : Fintype L := Fintype.ofFinite L
  set φ : K ≃+* L :=
    FiniteField.ringEquivOfCardEq (by rw [card_K, ← Nat.card_eq_fintype_card, hL]) with hφ
  have hcomm : ∀ c, σ (φ.toRingHom c) = φ.toRingHom (barHom c) := fun c => by
    rw [hσ, barHom_apply, bar]
    exact (map_pow _ c 2).symm
  have hbar : Function.Surjective barHom := fun a => ⟨bar a, (barHom_apply _).trans (bar_bar a)⟩
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hpar : ∀ a, ∀ c ∈ orbitField TwistTag.E6 L σ a,
      ∃ c₀ ∈ orbitField TwistTag.E6 K barHom a, φ.toRingHom c₀ = c := by
    intro a c hc
    refine ⟨φ.symm c, ?_, φ.apply_symm_apply c⟩
    rw [mem_orbitField] at hc ⊢
    apply φ.injective
    change φ.toRingHom ((barHom ^ (TwistTag.E6.orbit a).card) (φ.symm c)) =
      φ.toRingHom (φ.symm c)
    rw [← ringHom_pow_apply_comm hcomm]
    change (σ ^ (TwistTag.E6.orbit a).card) (φ (φ.symm c)) = φ (φ.symm c)
    rw [φ.apply_symm_apply]
    exact hc
  have hmap : (graphFixedRootGroup TwistTag.E6 K barHom).map (baseChangeGL φ.toRingHom) =
      graphFixedRootGroup TwistTag.E6 L σ :=
    le_antisymm (map_baseChangeGL_graphFixedRootGroup_le hbar hcomm)
      (graphFixedRootGroup_le_map_baseChangeGL hσsurj hcomm hpar)
  exact ⟨((Subgroup.equivMapOfInjective (graphFixedRootGroup TwistTag.E6 K barHom)
    (baseChangeGL φ.toRingHom) (baseChangeGL_injective φ.toRingHom)).trans
      (MulEquiv.subgroupCongr hmap)).symm⟩

theorem twisted_E6_field_two_cyclic_central_two_kernel_bound
    {E : Type*} {J : Type} [Group E]
    [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker)
    (hcyc : IsCyclic η.ker) (hJ : LieModel J .twistedE6 0 2 1) :
    Nat.card η.ker ≤ 2 ∧ (η.ker ≠ ⊥ → Nat.card η.ker = 2) := by
  rcases hJ with ⟨hc, -⟩ | ⟨-, -, hX⟩ | ⟨-, hr, -⟩ | ⟨-, hs, -⟩
  · exact absurd hc (by decide)
  · obtain ⟨L, _, _, σ, hL, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_E6 hX
    obtain ⟨e'⟩ := nonempty_mulEquiv_stdGroup_of_card_eq_four (by rw [hL]; norm_num)
      σ.toRingHom fun c => by simpa using hσ c
    set η' : E →* stdGroup := (e.trans e').toMonoidHom.comp η with hη'
    have hker : η'.ker = η.ker := by
      ext z
      exact (e.trans e').map_eq_one_iff
    obtain ⟨hsq, -⟩ := TwistedE6FieldTwoCover.twisted_E6_field_two_central_two_kernel_elementary
      η' ((e.trans e').surjective.comp hη) (hker ▸ hC) (hker ▸ h2)
    rw [hker] at hsq
    have hdvd : Nat.card η.ker ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hsq x x.2)
    refine ⟨Nat.le_of_dvd (by norm_num) hdvd, fun hne => ?_⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (Subgroup.card_eq_one.mp h1) hne
    · exact h1
  · exact absurd hr (by decide)
  · exact absurd hs (by decide)

end CFSG.LieType.Chevalley
