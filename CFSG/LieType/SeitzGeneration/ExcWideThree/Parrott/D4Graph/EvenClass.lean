module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Transfer
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldNF
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridgeClass
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Families

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {K : Type} [Field K] [Finite K]

theorem exactNormalAut_eq_conj_of_charTwo (h2 : ringChar K = 2) (a : Fin Tag.D4.rank → Kˣ) :
    ∃ d : ↥(adjointGroup Tag.D4 K), exactNormalAut Tag.D4 K a 1 0 = MulAut.conj d := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [h2] at hn
  have hsq : ∀ u : Kˣ, (u ^ (2 ^ ((n : ℕ) - 1))) ^ 2 = u := by
    intro u
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel n.pos, ← hn]
    exact Units.ext (by simp [FiniteField.pow_card])
  set b : Fin Tag.D4.rank → Kˣ := fun j => a j ^ (2 ^ ((n : ℕ) - 1))
  have hab : (fun j : Fin 4 => b j ^ 2) = a := funext fun j => hsq (a j)
  have hmem : rootDiagUnit Tag.D4 a ∈ adjointGroup Tag.D4 K := by
    have := rootDiagUnit_sq_mem_adjointGroup_D4 (K := K) b
    rwa [hab] at this
  refine ⟨⟨rootDiagUnit Tag.D4 a, hmem⟩, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [coe_exactNormalAut, CFSG.HardMathSupport.Lang.E6Descent.exactQ_D4]
  have hid : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) = h :=
    Units.ext (entrywise_id _)
  rw [hid]
  simp [MulAut.conj_apply]

theorem gammaP_inv (B : SL2 K) :
    (gammaP K B)⁻¹ = MulAut.conj (sl2At K ⟨2, by decide⟩ B⁻¹) * d4Graph K 2 := by
  have h12 : (d4Graph K 1)⁻¹ = d4Graph K 2 := by
    rw [inv_eq_iff_mul_eq_one, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
      CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three]
  have hρ : (d4Rho ^ 2) (⟨2, by decide⟩ : Fin Tag.D4.rank) = ⟨2, by decide⟩ := by decide
  rw [gammaP, mul_inv_rev, h12, ← map_inv, ← map_inv, mul_conj_eq, d4Graph_sl2At, hρ]

theorem d4Graph_two_two (y : ↥(adjointGroup Tag.D4 K)) :
    d4Graph K 2 (d4Graph K 2 y) = d4Graph K 1 y := by
  rw [← MulAut.mul_apply, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_mod_three]

theorem d4Graph_two_one (y : ↥(adjointGroup Tag.D4 K)) :
    d4Graph K 2 (d4Graph K 1 y) = y := by
  rw [← MulAut.mul_apply, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
    CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three, MulAut.one_apply]

theorem conj_d4Graph_two_pow_three (x : ↥(adjointGroup Tag.D4 K)) :
    (MulAut.conj x * d4Graph K 2) ^ 3 =
      MulAut.conj (x * d4Graph K 2 x * d4Graph K 1 x) := by
  refine MulEquiv.ext fun h => ?_
  have e : (MulAut.conj x * d4Graph K 2) ^ 3 =
      (MulAut.conj x * d4Graph K 2) * ((MulAut.conj x * d4Graph K 2) *
        (MulAut.conj x * d4Graph K 2)) := by
    rw [pow_succ, pow_two, mul_assoc]
  rw [e]
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, d4Graph_two_two,
    d4Graph_two_one]

theorem conj_injective_D4 :
    Function.Injective (MulAut.conj : ↥(adjointGroup Tag.D4 K) →*
      MulAut ↥(adjointGroup Tag.D4 K)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hZ : Subgroup.center ↥(adjointGroup Tag.D4 K) = ⊥ := center_adjointGroup_eq_bot
  have hgc : g ∈ Subgroup.center ↥(adjointGroup Tag.D4 K) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut ↥(adjointGroup Tag.D4 K) => φ y) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * g = g * (g⁻¹ * y * g) := by group
      _ = g * y := by
        have h3 : g⁻¹ * y * g = y := by
          calc g⁻¹ * y * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [this]
            _ = y := by group
        rw [h3]
  rw [hZ] at hgc
  exact hgc

theorem sl2At_two_eq_d4TrialityY0 :
    (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1) : ModGL Tag.D4 K) =
      CFSG.RankThree.PartTwo.Sec8.d4TrialityY0 K := by
  rw [map_mul, Subgroup.coe_mul, coe_sl2At, coe_sl2At, simpleRootSL2_uSL, simpleRootSL2_vSL]
  rfl

theorem uSL_mul_vSL_pow_three [CharP K 2] : (uSL (1 : K) * vSL 1) ^ 3 = 1 := by
  have h2 : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  have e : (((uSL (1 : K) * vSL 1) ^ 3 : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      (!![1, 1; 0, 1] * !![1, 0; 1, 1]) * (!![1, 1; 0, 1] * !![1, 0; 1, 1]) *
        (!![1, 1; 0, 1] * !![1, 0; 1, 1]) := by
    simp only [pow_succ, pow_zero, one_mul, Matrix.SpecialLinearGroup.coe_mul]
    rfl
  ext i j
  rw [e]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, h2]

theorem uSL_mul_vSL_ne_one : uSL (1 : K) * vSL 1 ≠ 1 := by
  intro h
  have := congrArg (fun A : SL2 K => (A : Matrix (Fin 2) (Fin 2) K) 0 1) h
  have e : ((uSL (1 : K) * vSL 1 : SL2 K) : Matrix (Fin 2) (Fin 2) K) =
      !![1, 1; 0, 1] * !![1, 0; 1, 1] := rfl
  simp only [e] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this

theorem cube_mul_inv_of_pow_three {M : Type*} [Group M] {P x : M} (hP : P ^ 3 = 1) :
    (x * P⁻¹) ^ 3 = x * (P ^ 2 * x * (P ^ 2)⁻¹) * (P ^ 1 * x * (P ^ 1)⁻¹) := by
  have hPinv : P⁻¹ = P ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hP
  have hP2inv : (P ^ 2)⁻¹ = P := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ]
    exact hP
  rw [hP2inv, pow_one, hPinv]
  simp only [pow_succ, pow_zero, one_mul, mul_assoc]

theorem classify_conj_d4Graph_two (h2 : ringChar K = 2) (x : ↥(adjointGroup Tag.D4 K))
    (h3 : (MulAut.conj x * d4Graph K 2) ^ 3 = 1) :
    ∃ ψ : MulAut ↥(adjointGroup Tag.D4 K),
      ψ * (MulAut.conj x * d4Graph K 2) * ψ⁻¹ = d4Graph K 2 ∨
        ∃ B : SL2 K, B ^ 3 = 1 ∧ B ≠ 1 ∧
          ψ * (MulAut.conj x * d4Graph K 2) * ψ⁻¹ = (gammaP K B)⁻¹ := by
  have : CharP K 2 := ringChar.of_eq h2
  have hcube : x * d4Graph K 2 x * d4Graph K 1 x = 1 :=
    conj_injective_D4 (by rw [← conj_d4Graph_two_pow_three, h3, map_one])
  have hP3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hP2 : d4P K ^ 2 = (d4P K)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ]
    exact hP3
  have hs3 : ((show ModGL TwistTag.D4.tag K from x.1) * (diagramMap TwistTag.D4 K)⁻¹) ^ 3 = 1 := by
    have e := congrArg (fun z : ↥(adjointGroup Tag.D4 K) => (z : ModGL Tag.D4 K)) hcube
    simp only [Subgroup.coe_mul, coe_d4Graph, Subgroup.coe_one] at e
    exact (cube_mul_inv_of_pow_three (x := (x : ModGL Tag.D4 K)) hP3).trans e
  obtain ⟨y, hy, hys⟩ := CFSG.StandardType.TriBridge.exists_conj_classes_D4 x.2 hs3
  set yG : ↥(adjointGroup Tag.D4 K) := ⟨y, hy⟩
  refine ⟨MulAut.conj yG, ?_⟩
  have hconj : ∀ h : ↥(adjointGroup Tag.D4 K),
      (((MulAut.conj yG * (MulAut.conj x * d4Graph K 2) * (MulAut.conj yG)⁻¹) h :
        ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        ((yG : ModGL Tag.D4 K) * ((x : ModGL Tag.D4 K) * (d4P K)⁻¹) * (yG : ModGL Tag.D4 K)⁻¹) *
          (h : ModGL Tag.D4 K) *
          ((yG : ModGL Tag.D4 K) * ((x : ModGL Tag.D4 K) * (d4P K)⁻¹) *
            (yG : ModGL Tag.D4 K)⁻¹)⁻¹ := by
    intro h
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply,
      Subgroup.coe_mul, Subgroup.coe_inv, coe_d4Graph]
    rw [hP2]
    group
  have hys' : ((yG : ModGL Tag.D4 K) * ((x : ModGL Tag.D4 K) * (d4P K)⁻¹) *
      (yG : ModGL Tag.D4 K)⁻¹) = (d4P K)⁻¹ ∨
      ((yG : ModGL Tag.D4 K) * ((x : ModGL Tag.D4 K) * (d4P K)⁻¹) *
        (yG : ModGL Tag.D4 K)⁻¹) =
          (sl2At K ⟨2, by decide⟩ (uSL 1 * vSL 1) : ModGL Tag.D4 K) * (d4P K)⁻¹ := by
    rw [sl2At_two_eq_d4TrialityY0]
    exact hys
  rcases hys' with hys' | hys'
  · left
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hconj, hys', coe_d4Graph, hP2]
  · right
    refine ⟨(uSL 1 * vSL 1)⁻¹, by rw [inv_pow, uSL_mul_vSL_pow_three, inv_one],
      inv_ne_one.2 uSL_mul_vSL_ne_one, ?_⟩
    rw [gammaP_inv, inv_inv]
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hconj, hys']
    simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_d4Graph]
    rw [hP2]
    group

theorem isG2Type_or_isA2Type_of_charTwo :
    ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 →
      ∀ α : MulAut ↥(adjointGroup Tag.D4 K), α ^ 3 = 1 →
        (CFSG.LieType.SeitzGeneration.ExcWideThree.D4ElemType α fun ε σ => ε ≠ 0 ∧ σ = 1) →
          IsG2Type α ∨ IsA2Type α := by
  intro K _ _ h2 α hα3 hαT
  obtain ⟨g, a, σ, ε, hε, -, ⟨hε0, hσ1⟩, hαeq⟩ := hαT
  subst hσ1
  obtain ⟨d, hd⟩ := exactNormalAut_eq_conj_of_charTwo h2 a
  rw [hd, ← mul_assoc, ← map_mul] at hαeq
  set x := g * d
  have hε12 : ε = 1 ∨ ε = 2 := by omega
  rcases hε12 with rfl | rfl
  · have hinv : α⁻¹ = MulAut.conj (d4Graph K 2 x⁻¹) * d4Graph K 2 := by
      have h12 : (d4Graph K 1)⁻¹ = d4Graph K 2 := by
        rw [inv_eq_iff_mul_eq_one, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
          CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three]
      rw [hαeq, mul_inv_rev, h12, ← map_inv, mul_conj_eq]
    have h3' : (MulAut.conj (d4Graph K 2 x⁻¹) * d4Graph K 2) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα3, inv_one]
    obtain ⟨ψ, h | ⟨B, hB3, hB1, h⟩⟩ := classify_conj_d4Graph_two h2 _ h3'
    · left
      refine ⟨ψ, Or.inl ?_⟩
      have e : ψ * α * ψ⁻¹ = (ψ * α⁻¹ * ψ⁻¹)⁻¹ := by group
      rw [e, hinv, h, inv_eq_iff_mul_eq_one, ← CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_add,
        CFSG.LieType.SeitzGeneration.ExcWideThree.d4Graph_three]
    · right
      refine ⟨ψ, B, hB3, hB1, Or.inl ?_⟩
      have e : ψ * α * ψ⁻¹ = (ψ * α⁻¹ * ψ⁻¹)⁻¹ := by group
      rw [e, hinv, h, inv_inv]
  · obtain ⟨ψ, h | ⟨B, hB3, hB1, h⟩⟩ := classify_conj_d4Graph_two h2 x (hαeq ▸ hα3)
    · exact Or.inl ⟨ψ, Or.inr (hαeq ▸ h)⟩
    · exact Or.inr ⟨ψ, B, hB3, hB1, Or.inr (hαeq ▸ h)⟩

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
