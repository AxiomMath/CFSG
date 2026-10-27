module

public import CFSG.CGT.T75A.FixRoot
public import CFSG.LocalAnalysis.SteinbergBNUnitaryThreeOuterInvolutionRigidity
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsModel

public section

namespace CFSG.CGT.T75A

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.CGT.Timmesfeld75
open CFSG.ComponentClassification.AschbacherToolkit.Bender
open CFSG.ComponentClassification.AschbacherToolkit.Bender.UnitaryAut
open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryHulls

theorem exists_fixed_root_pair {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) :
    ∃ S₀ S₁ : Sylow 2 D, sylowCenter (S₀ : Subgroup D) ≠ sylowCenter (S₁ : Subgroup D) ∧
      (∀ x ∈ sylowCenter (S₀ : Subgroup D), α x = x) ∧
      (∀ x ∈ sylowCenter (S₁ : Subgroup D), α x = x) ∧
      ∀ P : Subgroup (MulAut D), IsPGroup 2 P →
        (∀ β ∈ P, (∀ x ∈ sylowCenter (S₀ : Subgroup D), β x = x) ∧
          ∀ x ∈ sylowCenter (S₁ : Subgroup D), β x = x) → Nat.card P ≤ 2 := by
  classical
  obtain ⟨K, instF, instFin, F, hF, hcard, -, -, hk, j, hjinj, hjfix, -, -, -, hjtwo, η, -, hjm⟩ :=
    CFSG.LocalAnalysis.even_unitary_three_outer_involution_perfect_fixed_rigidity hf hD α hα hαout
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have hK2 : CharP K 2 := charP_of_card_eq_prime_pow (f := 2 * f)
    (by rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, mul_comm])
  have hfixed : Nat.card {x : K // F.conj x = x} = 2 ^ f := by
    let c : unitaryCoverFixedField F ≃ {x : K // F.conj x = x} :=
      { toFun := fun x => ⟨x, x.property⟩
        invFun := fun x => ⟨x, x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr c.symm).trans hk
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup F) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  let ρ : F.specialSubgroup ⧸ scalarCenter F ≃* ProjectiveSpecialUnitaryMatrixGroup F :=
    (QuotientGroup.quotientMulEquivOfEq (scalarCenter_eq_ker F hF)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (psuMk F) psuMk_surjective)
  have hρ : ∀ x, ρ x = coverToPSU F (scalarCenter F) hF le_rfl x := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    rfl
  let eP : D ≃* ProjectiveSpecialUnitaryMatrixGroup F := η.symm.trans ρ
  have hU : ∀ z, eP (η (heisL F (scalarCenter F) hF z)) = hermitianUnipotentPSU F hF z := by
    intro z
    change ρ (η.symm (η _)) = _
    rw [MulEquiv.symm_apply_apply, hρ]
    exact Subtype.ext rfl
  let R : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup F) :=
    unitaryCoverSylow F f hf hcard hfixed hF
  let S₀ : Sylow 2 D := R.mapSurjective (f := eP.symm.toMonoidHom) eP.symm.surjective
  have hS₀ : sylowCenter (S₀ : Subgroup D) =
      (upperRootL F (scalarCenter F) hF).map η.toMonoidHom := by
    ext x
    have h1 : x ∈ sylowCenter (S₀ : Subgroup D) ↔ eP x ∈ sylowCenter (unitaryCoverRoot F hF) := by
      have := AutTransport.mem_sylowCenter_map eP.symm (S := (R : Subgroup _)) (g := eP x)
      rw [MulEquiv.symm_apply_apply] at this
      exact this
    rw [h1]
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := (mem_sylowCenter.1 hx).1
      have hz0 : z.1.1 = 0 :=
        (mem_sylowCenter_root F (2 ^ f) hcard hfixed hq hF z).1 (hz ▸ hx)
      refine ⟨heisL F (scalarCenter F) hF z, (mem_upperRootL_iff hF _).2 ⟨z, hz0, rfl⟩, ?_⟩
      apply eP.injective
      change eP (η (heisL F (scalarCenter F) hF z)) = eP x
      rw [hU, hz]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz0, rfl⟩ := (mem_upperRootL_iff hF y).1 hy
      change eP (η (heisL F (scalarCenter F) hF z)) ∈ _
      rw [hU]
      exact mem_sylowCenter_root_of_fst F hF hz0
  have hjsub : ∀ m, j m = η (QuotientGroup.mk (sublineHom F hF m)) := by
    intro m
    obtain ⟨g, hg, hjg⟩ := hjm m
    have : g = sublineHom F hF m :=
      Subtype.ext (Units.ext (hg.trans (coe_sublineHom hF m).symm))
    rw [hjg, this]
  have hT₀fix : ∀ x ∈ sylowCenter (S₀ : Subgroup D), α x = x := by
    intro x hx
    rw [hS₀] at hx
    obtain ⟨y, ⟨b, rfl⟩, rfl⟩ := hx
    have hm := hjfix (j (upperSL _ b)) ⟨_, rfl⟩
    rw [hjsub] at hm
    exact hm
  have h2k : (2 : unitaryCoverFixedField F) = 0 := CharTwo.two_eq_zero
  let w : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField F) :=
    ⟨!![0, 1; 1, 0], by
      rw [Matrix.det_fin_two_of]
      linear_combination (-1 : unitaryCoverFixedField F) * h2k⟩
  have hwu : ∀ b : Multiplicative (unitaryCoverFixedField F),
      w * upperSL _ b = lowerSL _ b * w := by
    intro b
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_upperSL,
      coe_lowerSL]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply, Fin.sum_univ_two]
  obtain ⟨S₁, hS₁⟩ := exists_sylow_center_conj S₀ (j w)
  have hup : ∀ b, j (upperSL _ b) ∈ sylowCenter (S₀ : Subgroup D) := fun b => by
    rw [hS₀]
    exact ⟨_, ⟨b, rfl⟩, (hjsub _).symm⟩
  have hlow : ∀ b, j (lowerSL _ b) ∈ sylowCenter (S₁ : Subgroup D) := fun b => by
    rw [hS₁]
    refine ⟨j (upperSL _ b), hup b, ?_⟩
    change j w * j (upperSL _ b) * (j w)⁻¹ = _
    rw [← map_mul, hwu, map_mul, mul_inv_cancel_right]
  have hjrange : ∀ m, j m ∈ sylowCenter (S₀ : Subgroup D) ⊔ sylowCenter (S₁ : Subgroup D) := by
    intro m
    have hm : (QuotientGroup.mk (sublineHom F hF m) : F.specialSubgroup ⧸ scalarCenter F) ∈
        sublineL F (scalarCenter F) hF := ⟨m, rfl⟩
    rw [sublineL_eq_sup hF] at hm
    have h1 : η (QuotientGroup.mk (sublineHom F hF m)) ∈
        (upperRootL F (scalarCenter F) hF ⊔ lowerRootL F (scalarCenter F) hF).map
          η.toMonoidHom := ⟨_, hm, rfl⟩
    rw [Subgroup.map_sup] at h1
    rw [hjsub]
    refine (sup_le_sup (le_of_eq hS₀.symm) ?_) h1
    rintro _ ⟨y, ⟨b, rfl⟩, rfl⟩
    have := hlow b
    rw [hjsub] at this
    exact this
  refine ⟨S₀, S₁, ?_, hT₀fix, ?_, ?_⟩
  · intro heq
    have hl1 := hlow (Multiplicative.ofAdd 1)
    rw [← heq, hS₀] at hl1
    obtain ⟨y, ⟨b, rfl⟩, hy⟩ := hl1
    have hb : j (upperSL _ b) = j (lowerSL _ (Multiplicative.ofAdd 1)) := by
      rw [hjsub (upperSL _ b)]
      exact hy
    have h3 := hjinj hb
    have h4 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin 2) (unitaryCoverFixedField F) =>
      (m : Matrix (Fin 2) (Fin 2) (unitaryCoverFixedField F)) 1 0) h3
    simp [coe_upperSL, coe_lowerSL] at h4
  · intro x hx
    rw [hS₁] at hx
    obtain ⟨t, ht, rfl⟩ := hx
    have hg : α (j w) = j w := hjfix (j w) ⟨w, rfl⟩
    have ht' := hT₀fix t ht
    change α (j w * t * (j w)⁻¹) = j w * t * (j w)⁻¹
    rw [map_mul, map_mul, map_inv, hg, ht']
  · intro P hP hPfix
    refine hjtwo P hP fun β hβ x hx => ?_
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨h0, h1⟩ := hPfix β hβ
    have hfix : ∀ y ∈ sylowCenter (S₀ : Subgroup D) ⊔ sylowCenter (S₁ : Subgroup D), β y = y := by
      intro y hy
      have hsub : sylowCenter (S₀ : Subgroup D) ⊔ sylowCenter (S₁ : Subgroup D) ≤
          MonoidHom.eqLocus (β : D →* D) (MonoidHom.id D) :=
        sup_le (fun x hx => h0 x hx) (fun x hx => h1 x hx)
      exact hsub hy
    exact hfix _ (hjrange m)

theorem outer_involution_root_pair {D : Type} [Group D] [Finite D] {f : ℕ} (hf : 2 ≤ f)
    (hD : StatedClassicalModel D .PSU 3 2 f) (α : MulAut D) (hα : orderOf α = 2)
    (hαout : α ∉ (MulAut.conj : D →* MulAut D).range) {S : Sylow 2 D}
    (hαT : ∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype,
      α x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype) :
    (∀ x ∈ (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype, α x = x) ∧
      ∃ S' : Sylow 2 D, (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype ≠
          (Subgroup.center (S : Subgroup D)).map (S : Subgroup D).subtype ∧
        ∀ x ∈ (Subgroup.center (S' : Subgroup D)).map (S' : Subgroup D).subtype, α x = x := by
  have hαα : α * α = 1 := by
    have h := pow_orderOf_eq_one α
    rw [hα, pow_two] at h
    exact h
  refine ⟨fix_root_group hf hD α hαα hαT, ?_⟩
  obtain ⟨S₀, S₁, hne, h₀, h₁, -⟩ := exists_fixed_root_pair hf hD α hα hαout
  simp only [map_center_eq_sylowCenter]
  by_cases h : sylowCenter (S₀ : Subgroup D) = sylowCenter (S : Subgroup D)
  · exact ⟨S₁, fun h' => hne (h.trans h'.symm), h₁⟩
  · exact ⟨S₀, h, h₀⟩

end CFSG.CGT.T75A
