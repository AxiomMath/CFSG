module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeIndex
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnCard
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeAbs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24PSU3Classes

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSNotAll24

open CFSG.Open CFSG.LieType.Seitz CFSG.ComponentClassification CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Glue

theorem exists_conj_eq_of_psu3 {X : Type} [Group X] {C J : Subgroup X}
    (hnorm : ∀ c ∈ C, ∀ x ∈ J, c * x * c⁻¹ ∈ J) {r n : ℕ}
    (hG : StatedClassicalModel ↥J .PSU 3 r n) (hQ : 9 ∣ r ^ n + 1) :
    ∀ y ∈ C, y ^ 3 ∈ J → ∀ p ∈ J, p ^ 3 = 1 → ∃ j ∈ J, y * p * y⁻¹ = j * p * j⁻¹ := by
  intro y hy hy3 p hp hp3
  let ψ : MulAut J :=
    { toFun := fun x => ⟨y * x * y⁻¹, hnorm y hy x x.2⟩
      invFun := fun x => ⟨y⁻¹ * x * y, by simpa using hnorm y⁻¹ (C.inv_mem hy) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hψ : ∃ g : J, ∀ x, ψ (ψ (ψ x)) = g * x * g⁻¹ :=
    ⟨⟨y ^ 3, hy3⟩, fun x => Subtype.ext (by
      show y * (y * (y * (x : X) * y⁻¹) * y⁻¹) * y⁻¹ = y ^ 3 * (x : X) * (y ^ 3)⁻¹
      simp only [pow_succ, pow_zero, one_mul, mul_inv_rev, mul_assoc])⟩
  obtain ⟨j, hj⟩ := psu3_order_three_fixed_of_cube_inner hG hQ ψ hψ ⟨p, hp⟩ (Subtype.ext hp3)
  exact ⟨j, j.2, congrArg Subtype.val hj⟩


theorem nine_dvd_pow_three_add_one {q : ℕ} (hq : 3 ∣ q + 1) : 9 ∣ q ^ 3 + 1 := by
  have h9 : q % 9 = 2 ∨ q % 9 = 5 ∨ q % 9 = 8 := by omega
  rcases h9 with h | h | h <;>
    simp [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod, h]

end Glue

section Main


variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ} {h : twistedE6InndiagGL K σ}

namespace TwE6LineLang

variable (D : TwE6LineLang K σ q h)

include D in
theorem exists_component_a2out (hdim : twE6MatFixDim K σ h = 24) (hq3 : 3 ∣ q + 1)
    (hq2 : q ≠ 2) (hout : twistedE6InndiagConj K σ h ∉ twistedE6Inn K σ) :
    ∃ J : Subgroup (twistedE6RootGroup K σ),
      IsComponentOf J (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) ∧
      J.relIndex (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) ∣ 3 ∧
      (∀ c ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)),
        ∀ x ∈ J, c * x * c⁻¹ ∈ J) ∧
      (∀ y ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)), y ^ 3 ∈ J →
        ∀ p ∈ J, p ^ 3 = 1 → ∃ j ∈ J, y * p * y⁻¹ = j * p * j⁻¹) := by
  classical
  obtain ⟨i⟩ := D.nonempty_kernelComponent_a2out hdim
  obtain ⟨hZ, hqs, hmodel⟩ := D.rationalComponent_a2out hdim hq3 hq2 hout i
  obtain ⟨hi6, hall⟩ := D.orbit_three_of_outer hdim hq3 hq2 hout
  set R := rationalComponent D.S.ρ D.S.Γ (rootCharHom D.a) i with hR
  have hJ : IsComponentOf (R.comap D.ι)
      (fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h))) :=
    D.isComponentOf_comap i hqs
  have hnorm : ∀ c ∈ fixedPoints (Subgroup.zpowers (twistedE6InndiagConj K σ h)),
      ∀ x ∈ R.comap D.ι, c * x * c⁻¹ ∈ R.comap D.ι := by
    intro c hc x hx
    have hfc : twistedE6InndiagConj K σ h c = c :=
      hc _ (Subgroup.mem_zpowers (twistedE6InndiagConj K σ h))
    have hcomm : twistedE6InndiagConj K σ h * (MulAut.conj c : MulAut _) =
        (MulAut.conj c : MulAut _) * twistedE6InndiagConj K σ h := by
      have := mulAut_mul_conj_mul_inv (twistedE6InndiagConj K σ h) c
      rw [hfc] at this
      exact mul_inv_eq_iff_eq_mul.1 this
    have hJ' := isComponentOf_map_of_commute _ (MulAut.conj c : MulAut _) hcomm hJ
    have heq := D.eq_of_isComponentOf_a2out hdim hq3 hq2 hout hJ hJ'
    have hmem : c * x * c⁻¹ ∈ (R.comap D.ι).map (MulAut.conj c : MulAut _).toMonoidHom :=
      ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [heq] at hmem
  refine ⟨R.comap D.ι, hJ, ?_, hnorm, ?_⟩
  · rw [Subgroup.relIndex_comap, D.map_fixedPoints]
    refine relIndex_rationalComponent_centralizer_dvd_three D.S D.hT D.hap D.h1 D.hL3
      (D.ncard_kernelRoots_a2out hdim) hall D.hℓ D.hchar D.he D.hSq (D.three_dvd_sq hq3)
      (by rw [D.sq_eq]; exact hq2) (fun hΓ => hout (D.conj_mem_inner_of_mem_Gamma hΓ)) i
  · have hRle : R ≤ D.ι.range := by
      rw [D.hrange]
      exact (langSubnormal_of_mem_torus D.S D.hT i).1.trans inf_le_left
    have hJmap : (R.comap D.ι).map D.ι = R := Subgroup.map_comap_eq_self hRle
    let eJR : ↥(R.comap D.ι) ≃* ↥R :=
      (Subgroup.equivMapOfInjective _ D.ι D.hinj).trans (MulEquiv.subgroupCongr hJmap)
    let eRQ : ↥R ≃* (↥R ⧸ Subgroup.center ↥R) :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm
    have hG : StatedClassicalModel ↥(R.comap D.ι) .PSU 3 (ringChar K) (D.e * 3) :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv (eJR.trans eRQ).symm hmodel
    have hQ : 9 ∣ ringChar K ^ (D.e * 3) + 1 := by
      rw [pow_mul, ← D.hqe]
      exact nine_dvd_pow_three_add_one hq3
    exact exists_conj_eq_of_psu3 hnorm hG hQ

end TwE6LineLang

theorem twE6LineGenAt_a2out {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {q : ℕ}
    {E : Subgroup (MulAut (twistedE6RootGroup K σ))} (hE : TwE6Cube K σ q E)
    {f : MulAut (twistedE6RootGroup K σ)} (hf : f ∈ E) (hf1 : f ≠ 1)
    (hfo : f ∉ twistedE6Inn K σ) (hd : TwE6LineDim K σ f 24) : TwE6LineGenAt K σ E f := by
  classical
  obtain ⟨h, rfl, -, -, hdim, ⟨D⟩⟩ := exists_twE6LineLang_of_cube hE hf hf1 hd
  obtain ⟨J, hJ, hidx, hnorm, hLA⟩ := D.exists_component_a2out hdim hE.three_dvd hE.ne_two hfo
  have hEI : Nat.card ↥(E ⊓ OuterAutomorphisms.inner (twistedE6RootGroup K σ)) = 3 ^ 2 :=
    card_inf_twistedE6Inn hE.card_field σ hE.frob hE.card_E hE.le_inndiag hE.not_le_inn
  have hZ : ∀ s : twistedE6RootGroup K σ, (MulAut.conj s : MulAut (twistedE6RootGroup K σ)) = 1 →
      s = 1 := fun s hs =>
    mulAut_conj_injective_of_center_eq_bot (exceptional_fixed_center_trivial TwistTag.E6 K σ)
      (hs.trans (map_one _).symm)
  exact lineGen_of_cube_abstract hE.elemAbelian hE.card_E hEI hZ hf hf1 hfo hJ hidx hnorm hLA

theorem twE6LineStructureA2Out_holds : TwE6LineStructureA2Out := by
  intro K _ _ σ q E hE f hf hf1 hfo hd
  exact ⟨twE6LineComponentsAt_a2out hE hf hf1 hfo hd, twE6LineGenAt_a2out hE hf hf1 hfo hd⟩

end Main

end KSNotAll24

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
