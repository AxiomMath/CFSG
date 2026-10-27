module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TriOddDict
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2Family

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.HardMathSupport.Seitz.TrialityOdd.Inner CFSG.RankThree.PartOne.SEITZ3
  CFSG.RankThree.PartOne.K1214 CFSG.RankThree.PartOne.SEITZ11.G2Seven
  CFSG.RankThree.PartTwo.KFacts CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.ClassicalInvolution.G2D4Models CFSG.LieType.HighestRoot CFSG.RankThree.PartTwo.Sec19
open scoped MatrixGroups

section Abstract

theorem triOdd_plane_gen_of_mulEquiv {G L : Type*} [Group G] [Group L] (H : Subgroup G)
    (Ψ : ↥H ≃* L)
    (hgen : ∀ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E → Nat.card E = 3 ^ 2 →
      Subgroup.closure {k : L | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤)
    (F : Subgroup G) (hFH : F ≤ H) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF3 : ∀ a ∈ F, a ^ 3 = 1) (hcard : Nat.card F = 3 ^ 2) :
    H ≤ Subgroup.closure {j : G | j ∈ H ∧ ∃ f ∈ F, f ≠ 1 ∧ j * f = f * j} := by
  have hmemE : ∀ x ∈ (F.subgroupOf H).map Ψ.toMonoidHom, ((Ψ.symm x : H) : G) ∈ F := by
    rintro _ ⟨y, hy, rfl⟩
    have h : Ψ.symm (Ψ.toMonoidHom y) = y := Ψ.symm_apply_apply y
    rw [h]
    exact hy
  have hEab : CFSG.Open.IsElemAbelian 3 ((F.subgroupOf H).map Ψ.toMonoidHom) := by
    refine ⟨isMulCommutative_iff.2 fun a b => ?_, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Ψ.symm.injective
      apply Subtype.ext
      simp only [Subgroup.coe_mul, map_mul]
      exact hFab _ (hmemE a a.2) _ (hmemE b b.2)
    · apply Ψ.symm.injective
      apply Subtype.ext
      rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hF3 _ (hmemE x hx)
  have hEcard : Nat.card ((F.subgroupOf H).map Ψ.toMonoidHom) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective Ψ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv]
    exact hcard
  have htop := hgen _ hEab hEcard
  intro h hh
  have h1 : Ψ ⟨h, hh⟩ ∈ Subgroup.closure
      {k : L | ∃ x ∈ (F.subgroupOf H).map Ψ.toMonoidHom, x ≠ 1 ∧ k * x = x * k} := by
    rw [htop]
    exact Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem (H.subtype.comp Ψ.symm.toMonoidHom) h1
  rw [MonoidHom.map_closure] at h2
  have h3 : (H.subtype.comp Ψ.symm.toMonoidHom) (Ψ ⟨h, hh⟩) = h := by
    show ((Ψ.symm (Ψ ⟨h, hh⟩) : H) : G) = h
    rw [Ψ.symm_apply_apply]
  rw [h3] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨k, ⟨x, hx, hx1, hkx⟩, rfl⟩
  refine ⟨(Ψ.symm k).2, ((Ψ.symm x : H) : G), hmemE x hx, ?_, ?_⟩
  · intro h0
    apply hx1
    have h4 : Ψ.symm x = 1 := Subtype.ext h0
    rw [← Ψ.apply_symm_apply x, h4, map_one]
  · show ((Ψ.symm k : H) : G) * ((Ψ.symm x : H) : G) =
      ((Ψ.symm x : H) : G) * ((Ψ.symm k : H) : G)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hkx]

end Abstract

section Main

variable
  {X : Type} [Field X] [Finite X] (σ : X ≃+* X)

theorem triOdd_gsub_eq_fixedSubgroup :
    Gsub σ = CFSG.RankThree.PartOne.CTP.fixedSubgroup (tauAut σ) := by
  ext x
  exact Iff.rfl

theorem triOdd_gsub_plane_gen {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hX : Nat.card X = (ℓ ^ f) ^ 3) (hσ : ∀ c : X, σ c = c ^ (ℓ ^ f))
    (F : Subgroup (C0 σ)) (hFG : F ≤ Gsub σ) (hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hF3 : ∀ a ∈ F, a ^ 3 = 1) (hcard : Nat.card F = 3 ^ 2) :
    Gsub σ ≤ Subgroup.closure {j : C0 σ | j ∈ Gsub σ ∧ ∃ f ∈ F, f ≠ 1 ∧ j * f = f * j} := by
  classical
  have hq2 : 2 ≤ ℓ ^ f := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
  have hℓ5 : 5 ≤ ℓ := by
    have h2 := hℓ.two_le
    rcases (by omega : ℓ = 2 ∨ ℓ = 3 ∨ ℓ = 4 ∨ 5 ≤ ℓ) with h | h | h | h
    · exact absurd h hℓ2
    · exact absurd h hℓ3
    · subst h; exact absurd hℓ (by norm_num)
    · exact h
  have hq5 : 5 ≤ ℓ ^ f := le_trans hℓ5 (by
    calc ℓ = ℓ ^ 1 := (pow_one ℓ).symm
      _ ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf)
  have hX' : Nat.card X = ℓ ^ (3 * f) := by rw [hX, ← pow_mul]; ring_nf
  haveI : CharP X ℓ := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hℓ (k := 3 * f) (by omega) hX'
  have hK2 : ringChar X ≠ 2 := by rw [ringChar.eq X ℓ]; exact hℓ2
  have hσ3 : ∀ c, σ (σ (σ c)) = c := CFSG.LieType.Steinberg.TwistedD4.sigma_three_of_card
    (σ := σ.toRingHom) hX hσ
  have hF : Nat.card (fixSubfield σ) = ℓ ^ f :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hq2 hX hσ
  have hk3 : (3 : ℕ∞) ≤ ENat.card (fixSubfield σ) := by
    rw [ENat.card_eq_coe_natCard]
    exact_mod_cast (by omega : 3 ≤ Nat.card (fixSubfield σ))
  have hG : Gsub σ = (FixedSub σ).map (triOddEqRoot σ hK2 hq2 hX hσ).toMonoidHom := by
    rw [← triOdd_fixedSubgroup_tau_eq_map σ hσ3 hK2 hq2 hX hσ]
    exact triOdd_gsub_eq_fixedSubgroup σ
  have h3q : ¬ 3 ∣ Nat.card (fixSubfield σ) := by
    rw [hF]
    intro h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  have hK3 : 3 ≤ Nat.card (fixSubfield σ) := by omega
  have hgen : CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.G2NativePlaneGen
      (fixSubfield σ) 3 := by
    rcases (by omega : 3 ∣ Nat.card (fixSubfield σ) + 1 ∨ 3 ∣ Nat.card (fixSubfield σ) - 1)
      with h | h
    · exact CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.g2NativePlaneGen_three_of_dvd_add_one
        _ hK3 h
    · exact CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.g2NativePlaneGen_three_of_dvd_sub_one
        _ hK3 h
  exact triOdd_plane_gen_of_mulEquiv (Gsub σ)
    (((MulEquiv.subgroupCongr hG).trans
      (Subgroup.equivMapOfInjective (FixedSub σ) (triOddEqRoot σ hK2 hq2 hX hσ).toMonoidHom
        (triOddEqRoot σ hK2 hq2 hX hσ).injective).symm).trans
      (triOddJDict σ hK2 hq2 hX hσ hσ3 hk3)) hgen F hFG hFab hF3 hcard

end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree
