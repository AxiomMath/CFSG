module

public import CFSG.HardMathSupport.Seitz.ExceptionsTransport.G2SplitTorusPlane
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2Family

public section

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.TauCetiBridge TauCeti CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator
  CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport

namespace CFSG.HardMathSupport.Seitz.ExceptionsTransport


theorem g2NativePlaneGenSplit_proved : G2NativePlaneGenSplit := by
  intro K _ _ hK p hp hp5 hpq E₁ hE hcard
  have : Fact p.Prime := ⟨hp⟩
  have := Fintype.ofFinite K
  obtain ⟨n, hr, hcardK⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hr⟩
  have hrp : ringChar K ≠ p := by
    intro h
    have h1 : p ∣ Nat.card K := by
      rw [Nat.card_eq_fintype_card, hcardK, ← h]
      exact dvd_pow_self _ n.ne_zero
    have h2 : p ∣ 1 := by
      have h3 := Nat.dvd_sub h1 hpq
      have h4 : Nat.card K - (Nat.card K - 1) = 1 := by
        have := Nat.card_pos (α := K); omega
      rwa [h4] at h3
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  have : IsSimpleGroup ↥(adjointGroup .G2 K) := isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card K hK)
  have : CFSG.IsElementaryAbelian p E₁ :=
    { toIsMulCommutative := hE.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g =>
        Subtype.ext (by simpa using hE.2 g g.2) }
  have hpg : IsPGroup p E₁ := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨g, hg⟩ := exists_conj_le_torus (K := K) hp hp5 hpq E₁ hpg
  set U := rootSubgroup .G2 K gA with hU
  have hUA : U ≤ adjointGroup .G2 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ _
  have hUr : IsPGroup (ringChar K) U := by
    intro x
    obtain ⟨t, ht⟩ := mem_rootSubgroup.1 x.2
    refine ⟨1, Subtype.ext ?_⟩
    show (x : ModGL .G2 K) ^ (ringChar K ^ 1) = 1
    rw [← ht, pow_one, pinnedX_pow_nat, CharP.cast_eq_zero K (ringChar K), zero_mul,
      pinnedX_zero .G2 K gA]
  have hU1 : U ≠ ⊥ := by
    intro h
    have hmem : pinnedX .G2 K gA 1 ∈ U := Subgroup.subset_closure ⟨1, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact one_ne_zero (pinnedX_injective .G2 K gA (hmem.trans (pinnedX_zero .G2 K gA).symm))
  refine CFSG.GH74.GLS.Stage2.Bender.Thm1.closure_centralizers_G2_of_normalizes K (ringChar K) p
    hrp E₁ hcard g⁻¹ U hUA hUr hU1 ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨t, ht, hxt⟩ := hg x hx
  have hnorm := torusGroup_le_normalizer_rootSubgroup (R := K) (τ := .G2) isRoot_gA ht
  have : (MulAut.conj ((g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K)).toMonoidHom
      ((adjointGroup .G2 K).subtype x) = t := by
    show ((g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K) * (x : ModGL .G2 K) *
      ((g⁻¹ : adjointGroup .G2 K) : ModGL .G2 K)⁻¹ = t
    rw [hxt]
    simp [mul_assoc]
  rw [this]
  exact hnorm

end CFSG.HardMathSupport.Seitz.ExceptionsTransport
