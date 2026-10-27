module

public import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesDef
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesForms
import CFSG.HardMathSupport.Solomon.Coordinator.McLaughlinTypesSym
import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLaughlin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Module CFSG.ComponentClassification.OutcomeLocal

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Small

variable [FiniteDimensional (ZMod 2) V]

theorem mclt_two_le_finrank {t : LinearMap.GeneralLinearGroup (ZMod 2) V}
    (ht : IsF2Transvection t) : 2 ≤ finrank (ZMod 2) V := by
  by_contra h
  apply ht.1
  rcases Nat.lt_or_ge (finrank (ZMod 2) V) 1 with h0 | h1
  · have : Subsingleton V := (Module.finrank_zero_iff (R := ZMod 2)).mp (by omega)
    exact tv_ext fun v => Subsingleton.elim _ _
  · exact eq_one_of_finrank_eq_one (by omega) t

theorem mclt_card_gl_of_finrank_two (h2 : finrank (ZMod 2) V = 2) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) V) = 6 := by
  rw [Nat.card_congr (mclt_glMatrixEquiv (Module.finBasisOfFinrankEq (ZMod 2) V h2)).toEquiv,
    Matrix.card_GL_field, ZMod.card]
  decide

theorem mclt_eq_top_of_finrank_two (h2 : finrank (ZMod 2) V = 2)
    {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)}
    {t : LinearMap.GeneralLinearGroup (ZMod 2) V} (htG : t ∈ G) (ht : IsF2Transvection t)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g ∈ G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤) : G = ⊤ := by
  have hcard := mclt_card_gl_of_finrank_two h2
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
    Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨φ, a, hφa, hφ, ha, rfl⟩ := (isF2Transvection_iff t).mp ht
  have ht1 : (⟨tv φ a hφa, htG⟩ : G) ≠ 1 := fun h =>
    tv_ne_one hφa hφ ha (congrArg Subtype.val h)
  have hdvd : Nat.card G ∣ 6 := hcard ▸ Subgroup.card_subgroup_dvd_card G
  have h2dvd : 2 ∣ Nat.card G := by
    have hord : orderOf (⟨tv φ a hφa, htG⟩ : G) = 2 := by
      refine orderOf_eq_prime ?_ ht1
      exact Subtype.ext (by rw [pow_two]; exact tv_mul_self φ a hφa)
    have h := orderOf_dvd_natCard (⟨tv φ a hφa, htG⟩ : G)
    rwa [hord] at h
  have h26 : Nat.card G = 2 ∨ Nat.card G = 6 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases Nat.card G <;> omega
  rcases h26 with h26 | h26
  · exfalso
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : G)).mp h26
    have hG : ∀ g ∈ G, g = 1 ∨ g = tv φ a hφa := by
      intro g hg
      by_cases hg1 : g = 1
      · exact Or.inl hg1
      · refine Or.inr (congrArg Subtype.val ((hy ⟨g, hg⟩ fun h => hg1 ?_).trans (hy _ ht1).symm))
        exact congrArg Subtype.val h
    rcases hirr (LinearMap.ker φ) (fun g hg w hw => by
        rcases hG g hg with rfl | rfl
        · exact hw
        · rw [tv_apply, LinearMap.mem_ker.mp hw, zero_smul, add_zero]
          exact hw) with hbot | htop
    · exact ha ((Submodule.eq_bot_iff _).mp hbot a hφa)
    · exact hφ (LinearMap.ker_eq_top.mp htop)
  · exact Subgroup.eq_top_of_card_eq G (by rw [h26, hcard])

end Small

theorem mclt_nonempty_equiv_statedSL_of_eq_top [FiniteDimensional (ZMod 2) V]
    {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)} (hG : G = ⊤) :
    Nonempty (G ≃* CFSG.Open.StatedSL (finrank (ZMod 2) V) (ZMod 2)) :=
  ⟨((MulEquiv.subgroupCongr hG).trans Subgroup.topEquiv).trans mclt_glEquivStatedSL⟩

theorem mclt_nonempty_equiv_perm {H : Type*} [AddCommGroup H] [Module (ZMod 2) H] {m : ℕ}
    {G : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V)} (β : V ≃ₗ[ZMod 2] H)
    {ρ : Equiv.Perm (Fin m) →* LinearMap.GeneralLinearGroup (ZMod 2) H}
    (hρ : Function.Injective ρ)
    (hG : G.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom = ρ.range) :
    Nonempty (G ≃* Equiv.Perm (Fin m)) :=
  ⟨((G.equivMapOfInjective _ (LinearMap.GeneralLinearGroup.congrLinearEquiv β).injective).trans
    (MulEquiv.subgroupCongr hG)).trans (MonoidHom.ofInjective hρ).symm⟩

theorem mcLaughlinTypes_holds : McLaughlinTypes := by
  intro V _ _ _ G ⟨S, ⟨t, htS⟩, hS, hGS⟩ hirr
  have ht := hS t htS
  have htG : t ∈ G := hGS ▸ Subgroup.subset_closure htS
  have h2 := mclt_two_le_finrank ht
  by_cases hd2 : finrank (ZMod 2) V = 2
  · exact Or.inl ⟨_, h2, mclt_nonempty_equiv_statedSL_of_eq_top
      (mclt_eq_top_of_finrank_two hd2 htG ht hirr)⟩
  rcases mclaughlin_transvection_groups_F2 (by omega) G ⟨S, hS, hGS⟩ hirr with
    hG | ⟨-, f, hnd, halt, hG⟩ | ⟨⟨k, hk⟩, Q, hQ, hG⟩ | ⟨⟨k, hk⟩, ⟨β, hβ⟩ | ⟨β, hβ⟩⟩
  · exact Or.inl ⟨_, h2, mclt_nonempty_equiv_statedSL_of_eq_top hG⟩
  · obtain ⟨m, hm, ⟨e⟩⟩ := mclt_exists_bilinIsometryGroup_equiv_statedSp hnd halt
    exact Or.inr (Or.inl ⟨m, by omega, ⟨(MulEquiv.subgroupCongr hG).trans e⟩⟩)
  · rcases mclt_exists_basis_quadratic Q hQ (n := k) (by omega) (by omega) with
      ⟨b, hb⟩ | ⟨b, hb⟩
    · exact Or.inr (Or.inr (Or.inl ⟨k, by omega, mclt_nonempty_equiv_orthGroup b hb hG⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨k - 1, by omega, mclt_nonempty_equiv_orthGroup b hb hG⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, by omega,
      mclt_nonempty_equiv_perm β (mclt_sumZeroRep_injective (by omega)) hβ⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, by omega,
      mclt_nonempty_equiv_perm β (mclt_heartRep_injective (by omega)) hβ⟩)))

end CFSG.HardMathSupport.Solomon.Coordinator
