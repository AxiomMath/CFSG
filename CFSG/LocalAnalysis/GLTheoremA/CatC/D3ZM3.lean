module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZM2
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZField
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZCase

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Dickson.Bal207.D4Graph CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open scoped Pointwise
local notation "Inn" => CFSG.ComponentClassification.OuterAutomorphisms.inner


section Card3

variable {K : Type} [Field K] [Finite K]

theorem ringEquiv_eq_one_of_card_three (hK : Nat.card K = 3) (σ : K ≃+* K) : σ = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let e : ZMod 3 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_three hcard
  have hf : (e.symm.toRingHom.comp (σ.toRingHom.comp e.toRingHom)) = RingHom.id (ZMod 3) :=
    RingHom.ext_zmod _ _
  refine RingEquiv.ext fun x => ?_
  obtain ⟨k, rfl⟩ := e.surjective x
  have h := congrArg (fun f : ZMod 3 →+* ZMod 3 => e (f k)) hf
  simpa using h

theorem d3_involution_inner_card3 (hK : Nat.card K = 3) {t : MulAut (D4Model K)} (ht3 : t ^ 3 = 1)
    (htE : t ∉ D4Img K) {z : MulAut (D4Model K)} (hz2 : z ^ 2 = 1) (hzt : z * t = t * z) :
    z ∈ Inn (D4Model K) := by
  have hK' : Nat.card K = 3 ^ 1 := by simpa using hK
  haveI := charP_three_of_card hK'
  have hrc : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  let ψ : adjointGroup Tag.D4 K ≃* D4Model K := coordinatePlusWitnessEquiv K (isoAdj K).symm
  let φ : D4Model K ≃* adjointGroup Tag.D4 K := ψ.symm
  set α : MulAut (adjointGroup Tag.D4 K) := MulAut.congr φ t with hα
  set ζ : MulAut (adjointGroup Tag.D4 K) := MulAut.congr φ z with hζdef
  have hα3 : α ^ 3 = 1 := by rw [hα, ← map_pow, ht3, map_one]
  have hζ2 : ζ * ζ = 1 := by rw [hζdef, ← map_mul, ← pow_two, hz2, map_one]
  have hζα : ζ * α = α * ζ := by rw [hζdef, hα, ← map_mul, ← map_mul, hzt]
  have htα : t = MulAut.congr ψ α := (congr_congr_symm ψ t).symm
  obtain ⟨g, a, σ, ε, hε3, -, hαform⟩ :=
    CFSG.HardMathSupport.Lang.D4Three.exists_cube_normal_form_sigma α hα3
  have hε0 : ε ≠ 0 := eps_ne_zero hK' ht3 htE g a σ ε (by rw [htα, hαform])
  have hε : ε = 1 ∨ ε = 2 := by omega
  obtain ⟨c, a_z, σ_z, hσz2, hζ⟩ := z_normal_form α ζ g a σ ε hε hαform hζ2 hζα
  have hσ1 : σ_z = 1 := ringEquiv_eq_one_of_card_three hK σ_z
  subst hσ1
  obtain ⟨y, hy⟩ := diag_case_inner hrc α ζ g c a a_z σ ε hε hαform hζ hζα
  refine ⟨ψ y, ?_⟩
  have h1 : z = MulAut.congr ψ ζ := (congr_congr_symm ψ z).symm
  rw [h1, hy, d3f_congr_conj]

theorem d3CaseTwoOneFour_holds : D3CaseTwoOneFour := by
  intro K _ _ hK b x y hb3 hbE hx2 hy2 hxy hx1 hy1 hxne hbx hby A hA hA9 hAb hAx hAy
  classical
  have hK' : Nat.card K = 3 ^ 1 := by simpa using hK
  haveI := charP_three_of_card hK'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcen : Subgroup.center (D4Model K) = ⊥ :=
    (d4Facts2 Nat.prime_three (by norm_num) le_rfl hK').2.2
  have hinj := CFSG.HardMathSupport.Timmesfeld.ComponentBalance.conj_injective_of_center_eq_bot hcen
  obtain ⟨x₀, rfl⟩ := d3_involution_inner_card3 hK hb3 hbE hx2 hbx.symm
  obtain ⟨y₀, rfl⟩ := d3_involution_inner_card3 hK hb3 hbE hy2 hby.symm
  have hsq : ∀ u : D4Model K, (MulAut.conj u) ^ 2 = 1 → u * u = 1 := by
    intro u hu
    apply hinj
    rw [map_mul, map_one, ← pow_two]
    exact hu
  have hfix : ∀ u : D4Model K, b * MulAut.conj u = MulAut.conj u * b → b u = u := by
    intro u hu
    apply hinj
    have e : MulAut.conj (b u) = b * MulAut.conj u * b⁻¹ := by
      ext w
      simp [MulAut.conj_apply, MulAut.mul_apply]
    rw [e, hu]
    group
  have hx₀2 := hsq x₀ hx2
  have hy₀2 := hsq y₀ hy2
  have hcomm : x₀ * y₀ = y₀ * x₀ := by
    apply hinj
    rw [map_mul, map_mul]
    exact hxy
  have hx₀1 : x₀ ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hy₀1 : y₀ ≠ 1 := fun h => hy1 (by rw [h, map_one])
  have hne : x₀ ≠ y₀ := fun h => hxne (by rw [h])
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hA9
    omega
  exact d3_fourgroup_false hK' hb3 hbE hx₀2 hy₀2 hcomm hx₀1 hy₀1 hne (hfix x₀ hbx) (hfix y₀ hby)
    hA hA1 hAb (fun a ha => by simpa [MulAut.conj_apply] using hAx a ha)
    (fun a ha => by simpa [MulAut.conj_apply] using hAy a ha)

end Card3

end CFSG.LocalAnalysis.GLTheoremA
