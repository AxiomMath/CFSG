module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape.ClassX
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4MnFrame
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4PlaneMinus
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.LieType.SeitzGeneration.ExcWideThree CFSG.Fischer CFSG.RankThree.PartTwo.Sec19
  CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.PartOne.KE CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.TrialityFold

section Torus


variable {K : Type} [Field K] [Finite K]

theorem exp_of_twistedTorus {ℓ f : ℕ} [Fact ℓ.Prime] {L : Type} [Field L] [IsAlgClosed L]
    [Algebra K L] [CharP L ℓ]
    (σ : K ≃+* K) (h3q : 3 ∣ ℓ ^ f + 1) {ζ : Lˣ} (hζ : orderOf ζ = 3)
    {g₀ : ModGL TwistTag.D4.tag L} (e : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (he3 : e ^ 3 = 1) (heT : g₀⁻¹ * triEmb K σ L e * g₀ ∈ twistedTorusOf (trialityOpposition L)
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))) :
    ∃ γ : Exp3, rhoExp γ = γ ∧
      g₀⁻¹ * triEmb K σ L e * g₀ = rootDiagUnit TwistTag.D4.tag (tup ζ γ) := by
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  rw [d4Q_twistedTorus] at heT
  obtain ⟨a, ha, hea⟩ := heT
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  have hea' : rootDiagUnitHom TwistTag.D4.tag L a = d4MinusPsi σ L g₀ e := by
    rw [d4MinusPsi_apply]
    exact hea
  have ha3 : ∀ i, a i ^ 3 = 1 := fun i => by
    have h2 : a ^ 3 = 1 := by
      apply hinj0
      rw [map_pow, map_one, hea', ← map_pow, he3, map_one]
    exact congrFun h2 i
  obtain ⟨h1, h3⟩ := d4Q_eq_of_pow_eq_one hFr h3q ha ha3
  obtain ⟨γ, rfl⟩ := exists_tup_of_pow_three hζ ha3
  refine ⟨γ, ?_, hea.symm⟩
  have h1' : γ i1 = γ i0 := pow_val_inj hζ h1
  have h3' : γ i3 = γ i0 := pow_val_inj hζ h3
  funext i
  simp only [rhoExp]
  fin_cases i
  · show γ (TwistTag.D4.perm.symm i0) = γ i0
    rw [TrialityFold.perm_symm_i0, h3']
  · show γ (TwistTag.D4.perm.symm i1) = γ i1
    rw [TrialityFold.perm_symm_i1, h1']
  · show γ (TwistTag.D4.perm.symm i2) = γ i2
    rw [TrialityFold.perm_symm_i2]
  · show γ (TwistTag.D4.perm.symm i3) = γ i3
    rw [TrialityFold.perm_symm_i3, h1', h3']

end Torus

section Main


variable {K : Type} [Field K] [Finite K]

theorem not_twistedTorus_of_two_classX {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hℓ3 : ℓ ≠ 3)
    (hf : 1 ≤ f) (hq : (ℓ ^ f) % 3 = 2) (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {x y : C0 σ} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxX : TriOddIsClassX σ x) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) (hyX : TriOddIsClassX σ y)
    (hyx : y ∉ Subgroup.zpowers x)
    (hT : D4PlaneInTorusMinus ℓ f hℓ K σ (Subgroup.closure {x, y})) : False := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨L, _, _, _, _, g₀, ⟨hg₀C, -, -⟩, β, hβ⟩ := hT
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have h3q : 3 ∣ ℓ ^ f + 1 := by omega
  have hK3 : Nat.card K = ℓ ^ (f * 3) := by rw [hK, ← pow_mul]
  have : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ (by omega) hK3
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L ℓ] at h'
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h')
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  have key : ∀ e ∈ Subgroup.closure ({x, y} : Set (C0 σ)), e ^ 3 = 1 → e ≠ 1 →
      TriOddIsClassX σ e → ∃ γ : Exp3, (γ = gA2 ∨ γ = fun i => 2 * gA2 i) ∧
        g₀⁻¹ * triEmb K σ L (β⁻¹ e) * g₀ = rootDiagUnit TwistTag.D4.tag (tup ζ γ) := by
    intro e he he3 he1 heX
    have he3' : (β⁻¹ e) ^ 3 = 1 := by rw [← map_pow, he3, map_one]
    have he1' : β⁻¹ e ≠ 1 := fun h => he1 (by
      have := congrArg β h
      rwa [MulAut.apply_inv_self, map_one] at this)
    have heX' := isClassX_map σ hℓ hℓ2 hf hK hσ β⁻¹ heX
    obtain ⟨γ, hγρ, hγ⟩ := exp_of_twistedTorus σ h3q hζ (β⁻¹ e) he3' (hβ e he)
    obtain ⟨k, hk, hke⟩ := exists_conj_gA2_of_classX σ hK hσ hζ he3' he1' heX'
    refine ⟨γ, ?_, hγ⟩
    refine eq_of_conj_gA2 hζ hγρ (g := g₀⁻¹ * k) ?_ (rootDiagUnit_mem_torusGroup _)
      (rootDiagUnit_mem_torusGroup _) ?_
    · exact mul_mem (inv_mem hg₀C) hk
    · rw [← hγ, hke]
      group
  have hxE : x ∈ Subgroup.closure ({x, y} : Set (C0 σ)) := Subgroup.subset_closure (by simp)
  have hyE : y ∈ Subgroup.closure ({x, y} : Set (C0 σ)) := Subgroup.subset_closure (by simp)
  obtain ⟨γx, hγx, hx⟩ := key x hxE hx3 hx1 hxX
  obtain ⟨γy, hγy, hy⟩ := key y hyE hy3 hy1 hyX
  have hζ3 : ζ ^ 3 = 1 := pow_three_of_orderOf hζ
  have hψ : Function.Injective (d4MinusPsi σ L g₀) := d4MinusPsi_injective g₀
  have hψa : ∀ e, d4MinusPsi σ L g₀ (β⁻¹ e) = g₀⁻¹ * triEmb K σ L (β⁻¹ e) * g₀ := fun e =>
    d4MinusPsi_apply g₀ _
  have hcase : γy = γx ∨ γy = fun i => 2 * γx i := by
    rcases hγx with rfl | rfl <;> rcases hγy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · right
      funext i
      show gA2 i = 2 * (2 * gA2 i)
      rw [← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide, one_mul]
    · exact Or.inl rfl
  apply hyx
  rcases hcase with h | h
  · have : β⁻¹ y = β⁻¹ x := hψ (by rw [hψa, hψa, hx, hy, h])
    rw [(β⁻¹).injective this]
    exact Subgroup.mem_zpowers x
  · have : β⁻¹ y = β⁻¹ (x ^ 2) := by
      apply hψ
      have e1 : d4MinusPsi σ L g₀ (β⁻¹ (x ^ 2)) = (d4MinusPsi σ L g₀ (β⁻¹ x)) ^ 2 := by
        rw [map_pow, map_pow]
      rw [e1, hψa, hψa, hx, hy, h, tup_two_mul hζ3]
      exact map_pow (rootDiagUnitHom TwistTag.D4.tag L) (tup ζ γx) 2
    rw [(β⁻¹).injective this]
    exact Subgroup.npow_mem_zpowers x 2

end Main

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.ClosingMinus.Escape
