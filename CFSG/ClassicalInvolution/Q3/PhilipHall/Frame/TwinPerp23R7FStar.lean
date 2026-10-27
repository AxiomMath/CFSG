module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Defs

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp CFSG.ClassicalInvolution.Disconnected


variable {n : ℕ}

theorem p23_t_mem_fstar {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) :
    t ∈ genFittingFStar Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  set F : Subgroup Y := genFittingFStar Y with hF
  have hFn : F.Normal := genFittingFStar_normal Y
  set S₀ : Subgroup Y := (S : Subgroup R).map R.subtype with hS₀
  have hsyl : IsSylow2In S₀ (tightCore R) := hC.datum.sylow_core
  by_contra htF
  have hSF : S₀ ⊓ F = ⊥ := by
    by_contra hne
    have hP2 : IsPGroup 2 ↥(S₀ ⊓ F) := hsyl.2.1.to_le inf_le_left
    have hnt : Nontrivial ↥(S₀ ⊓ F) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
    obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' (G := ↥(S₀ ⊓ F)) 2
      (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hv' : orderOf (v : Y) = 2 := by rwa [Subgroup.orderOf_coe]
    have hvK : (v : Y) ∈ tightCore R := hsyl.1 (Subgroup.mem_inf.mp v.2).1
    have hvv : (v : Y) * v = 1 := by rw [← pow_two, ← hv', pow_orderOf_eq_one]
    rcases hz.unique _ hvK hvv with h1 | h1
    · rw [h1, orderOf_one] at hv'; exact absurd hv' (by norm_num)
    · exact htF (h1 ▸ (Subgroup.mem_inf.mp v.2).2)
  have h1 := comm613Gen_normal hΩ (mem_RSet_of_isSylow2In hK hsyl) hFn hSF
  have h2 : oddCoreOf F = ⊥ := by
    rw [AscThmA.oddCoreOf_eq_inf, hc.std.perp.core.oddFree, inf_bot_eq]
  rw [h2, le_bot_iff] at h1
  have hSc : S₀ ≤ Subgroup.centralizer (F : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  exact htF ((hSc.trans (CFSG.Adapters.generalized_fitting_self_centralizing Y)) hC.datum.mem)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
