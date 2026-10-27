module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisYb3
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisInputs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools CFSG.GH74.GLS.Bg.TwoGroups
  CFSG.GH74.GLS.Bg.TwoGroups.L23

theorem SCert.SE.ut_comm_inv : ∀ u v : UT3 F4c, u * u = 1 → v * v = 1 → u * v = v * u →
    (u.b = 0 ∧ v.b = 0) ∨ (u.a = 0 ∧ v.a = 0) ∨ (u.a = 0 ∧ u.b = 0) ∨ (v.a = 0 ∧ v.b = 0) := by
  decide +kernel

theorem SCert.SE.ut_inv_cases : ∀ u : UT3 F4c, u * u = 1 → u.a = 0 ∨ u.b = 0 := by
  decide +kernel

theorem SCert.SE.card_ut_b : (Finset.univ.filter fun u : UT3 F4c => u.b = 0).card = 16 := by
  decide +kernel

theorem SCert.SE.card_ut_a : (Finset.univ.filter fun u : UT3 F4c => u.a = 0).card = 16 := by
  decide +kernel

variable {Y : Type} [Group Y] [Finite Y]

namespace GHSylow

variable (D : GHSylow Y)

@[expose] def tUT
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) ≃* UT3 F4c :=
  (MulEquiv.subgroupCongr ((D.coe_sylowXt hO hz).trans
      (by rw [MonoidHom.range_comp, range_subtype]))).trans
    ((QuotientGroup.quotientKerEquivRange D.sigmaX).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq D.ker_sigmaX_eq).trans
        (QuotientGroup.quotientKerEquivOfSurjective D.rhoUT D.rhoUT_surjective)))

theorem mem_sylowXt (hO : pPrimeCore 2 Y = ⊥)
    (hz : ∀ y : Y, y * D.z = D.z * y) (s : D.S1Y) :
    D.piX s ∈ ((D.sylowXt hO hz : Sylow 2 D.Xt) : Subgroup D.Xt) := by
  rw [D.coe_sylowXt hO hz]
  exact mem_map_of_mem _ s.2

theorem tUT_apply
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) (s : D.S1Y) :
    D.tUT hO hz ⟨D.piX s, D.mem_sylowXt hO hz s⟩ = SE.toUT (D.preS1 s) := by
  have h1 : (QuotientGroup.quotientKerEquivRange D.sigmaX).symm
      ⟨D.sigmaX s, ⟨s, rfl⟩⟩ = (s : D.S1Y ⧸ D.sigmaX.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.quotientKerEquivOfSurjective D.rhoUT D.rhoUT_surjective
    (QuotientGroup.quotientMulEquivOfEq D.ker_sigmaX_eq
      ((QuotientGroup.quotientKerEquivRange D.sigmaX).symm ⟨D.sigmaX s, _⟩)) = _
  rw [h1]
  rfl

theorem two_classes_Xt :
    ∃ u v : D.Xt, orderOf u = 2 ∧ orderOf v = 2 ∧ ¬ IsConj u v := by
  have hx : D.toG (SE.gen 6) ∈ D.S1 := D.toG_mem_S1 (by decide)
  have ht : D.toG (SE.invRep 1) ∈ D.S1 := D.toG_mem_S1 (by decide)
  set xY : D.Y1 := ⟨D.x, D.S1_le_Y1 hx⟩ with hxY
  set tY : D.Y1 := ⟨D.t, D.S1_le_Y1 ht⟩ with htY
  have hinv : ∀ (u₀ : SE), u₀ * u₀ = 1 → (u₀ ≠ 1 ∧ u₀ ≠ SE.gen 1 ∧ u₀ ≠ SE.gen 0 ∧
      u₀ ≠ SE.gen 1 * SE.gen 0) → (hu : D.toG u₀ ∈ D.Y1) →
      orderOf (D.piX ⟨D.toG u₀, hu⟩) = 2 := by
    intro u₀ h2 hne hu
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← map_mul, show (⟨D.toG u₀, hu⟩ : D.Y1) * ⟨D.toG u₀, hu⟩ = 1 from
        Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, h2, map_one]; rfl), map_one]
    · intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, D.mem_zpowers_l_iff] at h1
      rcases h1 with h | h | h | h
      · exact hne.1 (D.toG_injective (h.trans (map_one _).symm))
      · exact hne.2.1 (D.toG_injective h)
      · exact hne.2.2.1 (D.toG_injective h)
      · exact hne.2.2.2 (D.toG_injective (h.trans (map_mul _ _ _).symm))
  refine ⟨D.piX xY, D.piX tY, hinv _ (by decide) (by decide) _, hinv _ (by decide) (by decide) _,
    fun hc => ?_⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hc
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (zpowers D.lY) c
  have hc' : D.piX (g⁻¹⁻¹ * xY * g⁻¹) = D.piX tY := by
    rw [inv_inv, map_mul, map_mul, map_inv]
    exact hc
  obtain ⟨h, hh⟩ := D.exists_conj_Y1_of_conj_Xt ht (Subtype.ext (by
      rw [Subgroup.coe_mul, ← map_mul, show SE.gen 6 * SE.gen 6 = 1 by decide, map_one]; rfl))
    (Subtype.ext (by rw [Subgroup.coe_mul, ← map_mul, SE.invRep1_mul_self, map_one]; rfl))
    (fun h1 => SE.invRep1_ne_one (D.toG_injective ((congrArg Subtype.val h1).trans
      (map_one _).symm)))
    (fun h1 => SE.gen0_ne_invRep1 (D.toG_injective h1).symm) hc'
  exact D.not_conj_x_t ⟨h, by simpa using congrArg Subtype.val hh⟩

theorem thmC_Xt
    (hC : GorensteinHaradaThmCInput)
    (hO : pPrimeCore 2 Y = ⊥) (hz : ∀ y : Y, y * D.z = D.z * y) :
    letI : (pCore 2 D.Xt).Normal := pCore_normal
    centralizer (pCore 2 D.Xt : Set D.Xt) ≤ pCore 2 D.Xt ∧
      ((pCore 2 D.Xt = (D.sylowXt hO hz : Subgroup D.Xt) ∧
          ((D.sylowXt hO hz : Subgroup D.Xt)).index ∣ 9 ∧
          ∀ B : Subgroup D.Xt, B ≤ (D.sylowXt hO hz : Subgroup D.Xt) → (∀ b ∈ B, b * b = 1) →
            (∀ b ∈ B, ∀ c ∈ B, b * c = c * b) → Nat.card B = 16 → B.Normal) ∨
        ((pCore 2 D.Xt : Subgroup D.Xt) ≤ (D.sylowXt hO hz : Subgroup D.Xt) ∧
          Nat.card (pCore 2 D.Xt) = 16 ∧
          (∀ b ∈ pCore 2 D.Xt, b * b = 1) ∧
          (∀ b ∈ pCore 2 D.Xt, ∀ c ∈ pCore 2 D.Xt, b * c = c * b) ∧
          (Nonempty (D.Xt ⧸ pCore 2 D.Xt ≃* alternatingGroup (Fin 5)) ∨
            Nonempty (D.Xt ⧸ pCore 2 D.Xt ≃* Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) ∧
          ∀ u ∈ pCore 2 D.Xt, ∀ v ∈ pCore 2 D.Xt, u ≠ 1 → v ≠ 1 → ∃ g : D.Xt, g⁻¹ * u * g = v)) :=
  hC D.Xt (D.pPrimeCore_Xt hO hz) (D.sylowXt hO hz)
    ⟨(D.tUT hO hz).trans sylLCongr.symm⟩ D.two_classes_Xt

end GHSylow

end CFSG.ComponentClassification.GHarris
