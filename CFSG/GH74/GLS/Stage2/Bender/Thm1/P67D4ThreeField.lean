module

public import CFSG.RankThree.Chevalley.SteinbergCFTrialityNoninnerDescent
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixCoreTools
public import CFSG.RankThree.PartOne.KGD.D4Frame

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.LocalRank CFSG.RankThree.PartOne.KGD
open CFSG.RankThree.Chevalley

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem outer_order_three_normal_form {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) (hφ3 : φ ^ 3 = 1)
    (hφout : φ ∉ (MulAut.conj : graphFixedRootGroup TwistTag.D4 K σ.toRingHom →*
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).range) :
    ∃ (y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (m : ℕ), (m = 1 ∨ m = 2) ∧
      φ = MulAut.conj y * fieldActor σ (σ ^ (3 - m)) := by
  classical
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hex, ⟨Θ, hΘ, -, -⟩, -, -⟩ := triality_normal_form_full hℓ hf K hK σ hσ
  obtain ⟨⟨y, δ⟩, hyδ⟩ := hex φ
  have hΘφ : Θ φ = δ := hΘ φ y δ hyδ
  have hδ1 : δ ≠ 1 := by
    intro h
    apply hφout
    rw [hyδ, h, fieldActor_one, mul_one]
    exact ⟨y, rfl⟩
  have hδ3 : δ ^ 3 = 1 := by
    rw [← hΘφ, ← map_pow, hφ3, map_one]
  obtain ⟨fr, hfr, hord, htop, -⟩ :=
    finite_field_automorphism_fixed_field_cardinality hℓ (show 1 ≤ 3 * f by omega) hK3
  obtain ⟨j, hj⟩ : ∃ j : ℕ, fr ^ j = δ := by
    have hmem : δ ∈ Subgroup.zpowers fr := htop ▸ Subgroup.mem_top δ
    obtain ⟨k, hk⟩ := hmem
    refine ⟨(k % (orderOf fr : ℤ)).toNat, ?_⟩
    rw [← hk, ← zpow_natCast]
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by
      have : 0 < orderOf fr := by rw [hord]; omega
      omega))]
    exact zpow_mod_orderOf fr k
  have h1 : fr ^ (3 * j) = 1 := by
    rw [mul_comm, pow_mul, hj, hδ3]
  have h2 : 3 * f ∣ 3 * j := by
    rw [← hord]
    exact orderOf_dvd_iff_pow_eq_one.2 h1
  obtain ⟨t, rfl⟩ : f ∣ j := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  have hσfr : fr ^ f = σ := RingEquiv.ext fun c => by
    rw [ringAut_pow_apply_of_frobenius hfr f c, hσ c]
  have hδ : δ = σ ^ t := by
    rw [← hj, pow_mul, hσfr]
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσfr, ← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one fr
  have hδ' : δ = σ ^ (t % 3) := by
    rw [hδ]
    conv_lhs => rw [← Nat.div_add_mod t 3, pow_add, pow_mul, hσ3, one_pow, one_mul]
  have hmod : t % 3 = 1 ∨ t % 3 = 2 := by
    rcases (by omega : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2) with h | h | h
    · exfalso
      apply hδ1
      rw [hδ', h, pow_zero]
    · exact Or.inl h
    · exact Or.inr h
  rcases hmod with h | h
  · refine ⟨y, 2, Or.inr rfl, ?_⟩
    rw [hyδ, hδ', h]
  · refine ⟨y, 1, Or.inl rfl, ?_⟩
    rw [hyδ, hδ', h]

theorem commute_of_fixes_element {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {m : ℕ}
    (hm : m = 1 ∨ m = 2) (L : Type) [Field L] [Algebra K L]
    (y e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (h : (MulAut.conj y * fieldActor σ (σ ^ (3 - m)) :
      MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) e = e) :
    triEmb K σ L y * diagramMap TwistTag.D4 L ^ m * triEmb K σ L e =
      triEmb K σ L e * (triEmb K σ L y * diagramMap TwistTag.D4 L ^ m) := by
  have h2 := congrArg (fun x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom =>
    (x : ModGL TwistTag.D4.tag K)) h
  simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_fieldActor] at h2
  rw [← diagramMap_pow_conj_eq_entrywise σ hm e] at h2
  have h3 : (y : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K ^ m *
      (e : ModGL TwistTag.D4.tag K) = (e : ModGL TwistTag.D4.tag K) *
        ((y : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K ^ m) := by
    calc (y : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K ^ m *
          (e : ModGL TwistTag.D4.tag K) =
        ((y : ModGL TwistTag.D4.tag K) * (diagramMap TwistTag.D4 K ^ m *
          (e : ModGL TwistTag.D4.tag K) * (diagramMap TwistTag.D4 K ^ m)⁻¹) *
          (y : ModGL TwistTag.D4.tag K)⁻¹) *
          ((y : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K ^ m) := by group
      _ = (e : ModGL TwistTag.D4.tag K) *
          ((y : ModGL TwistTag.D4.tag K) * diagramMap TwistTag.D4 K ^ m) := by
        rw [h2]
  have h4 := congrArg (baseChangeGL (algebraMap K L)) h3
  rw [map_mul, map_mul, map_mul, map_mul, map_pow, baseChangeGL_diagramMap] at h4
  exact h4

end CFSG.GH74.GLS.Stage2.Bender.Thm1
