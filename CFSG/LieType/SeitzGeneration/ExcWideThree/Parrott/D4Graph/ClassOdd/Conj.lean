module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow
public import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Transfer

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

section Abstract

variable {M : Type*} [Group M] {H : Subgroup M}

@[expose] def IsConjBy (ψ : MulAut H) (v : M) : Prop :=
  ∀ h : H, ((ψ h : H) : M) = v * h * v⁻¹

theorem IsConjBy.mul {ψ ψ' : MulAut H} {v v' : M} (h : IsConjBy ψ v) (h' : IsConjBy ψ' v') :
    IsConjBy (ψ * ψ') (v * v') := by
  intro x
  rw [MulAut.mul_apply, h, h']
  group

theorem IsConjBy.inv {ψ : MulAut H} {v : M} (h : IsConjBy ψ v) : IsConjBy ψ⁻¹ v⁻¹ := by
  intro x
  have e := h (ψ⁻¹ x)
  rw [MulAut.apply_inv_self] at e
  rw [inv_inv]
  calc (((ψ⁻¹ x : H)) : M) = v⁻¹ * (v * ((ψ⁻¹ x : H) : M) * v⁻¹) * v := by group
    _ = v⁻¹ * x * v := by rw [← e]

theorem IsConjBy.ext {ψ ψ' : MulAut H} {v : M} (h : IsConjBy ψ v) (h' : IsConjBy ψ' v) :
    ψ = ψ' :=
  MulEquiv.ext fun x => Subtype.ext (by rw [h, h'])

theorem IsConjBy.congr {ψ : MulAut H} {v v' : M} (h : IsConjBy ψ v) (e : v = v') :
    IsConjBy ψ v' :=
  e ▸ h

theorem isConjBy_conj (j : H) : IsConjBy (MulAut.conj j) (j : M) := fun x => by
  simp [MulAut.conj_apply]

theorem IsConjBy.conj {ψ α : MulAut H} {v X : M} (hψ : IsConjBy ψ v) (hα : IsConjBy α X) :
    IsConjBy (ψ * α * ψ⁻¹) (v * X * v⁻¹) :=
  (hψ.mul hα).mul hψ.inv

end Abstract

section D4


variable {K : Type} [Field K]

theorem d4P_pow_three : d4P K ^ 3 = 1 :=
  diagramMap_pow_order TwistTag.D4 K

theorem d4P_sq : d4P K ^ 2 = (d4P K)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← pow_succ]
  exact d4P_pow_three

theorem isConjBy_d4Graph (ε : ℕ) : IsConjBy (d4Graph K ε) (d4P K ^ ε) :=
  fun h => coe_d4Graph ε h

theorem isConjBy_exactNormalAut (b : Fin Tag.D4.rank → Kˣ) :
    IsConjBy (exactNormalAut Tag.D4 K b 1 0) (rootDiagUnit Tag.D4 b) := by
  intro h
  have h1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) = h := by
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [coe_exactNormalAut, exactQ_zero, h1]
  group

theorem isConjBy_normalForm (g : ↥(adjointGroup Tag.D4 K)) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ) :
    IsConjBy (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε))
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) := by
  have h := (isConjBy_conj g).mul ((isConjBy_exactNormalAut a).mul (isConjBy_d4Graph (K := K) ε))
  exact h.congr (by rw [mul_assoc])

theorem isConjBy_gammaP (B : SL2 K) :
    IsConjBy (gammaP K B) ((sl2At K ⟨2, by decide⟩ B : ModGL Tag.D4 K) * d4P K) := by
  have h := (isConjBy_conj (sl2At K ⟨2, by decide⟩ B)).mul (isConjBy_d4Graph (K := K) 1)
  exact h.congr (by rw [pow_one])

theorem isConjBy_inndiagConj (w : inndiagGroup Tag.D4 K) :
    IsConjBy (inndiagConj Tag.D4 K w) (w : ModGL Tag.D4 K) :=
  fun h => coe_inndiagConj w h

theorem d4Graph_two_inv : (d4Graph K 2)⁻¹ = d4Graph K 1 := by
  refine ((isConjBy_d4Graph (K := K) 2).inv.congr ?_).ext (isConjBy_d4Graph 1)
  rw [d4P_sq, inv_inv, pow_one]

theorem d4P_inv_mul_rootDiagUnit_mul (b : Fin Tag.D4.rank → Kˣ) :
    (d4P K)⁻¹ * rootDiagUnit Tag.D4 b * d4P K = rootDiagUnit Tag.D4 fun i => b (d4Rho i) := by
  have h := diagramMap_mul_rootDiagUnit (K := K) (t := TwistTag.D4) (fun i => b (d4Rho i))
  have e : (fun i => (fun i => b (d4Rho i)) (TwistTag.D4.perm.symm i)) = b :=
    funext fun i => congrArg b (Equiv.apply_symm_apply d4Rho i)
  rw [e] at h
  calc (d4P K)⁻¹ * rootDiagUnit Tag.D4 b * d4P K =
      (d4P K)⁻¹ * (rootDiagUnit Tag.D4 b * d4P K) := by rw [mul_assoc]
    _ = (d4P K)⁻¹ * (d4P K * rootDiagUnit Tag.D4 fun i => b (d4Rho i)) := by
        rw [show rootDiagUnit Tag.D4 b * d4P K =
          d4P K * rootDiagUnit Tag.D4 (fun i => b (d4Rho i)) from h.symm]
    _ = rootDiagUnit Tag.D4 fun i => b (d4Rho i) := by group

theorem d4P_inv_conj_mem {j : ModGL Tag.D4 K} (hj : j ∈ adjointGroup Tag.D4 K) :
    (d4P K)⁻¹ * j * d4P K ∈ adjointGroup Tag.D4 K := by
  have h := (d4Graph K 2 ⟨j, hj⟩).2
  rw [coe_d4Graph, d4P_sq, inv_inv] at h
  exact h

theorem d4P_conj_mem {j : ModGL Tag.D4 K} (hj : j ∈ adjointGroup Tag.D4 K) :
    d4P K * j * (d4P K)⁻¹ ∈ adjointGroup Tag.D4 K := by
  have h := (d4Graph K 1 ⟨j, hj⟩).2
  rw [coe_d4Graph, pow_one] at h
  exact h

theorem inv_conj_d4P_mem_inndiag {w : ModGL Tag.D4 K} (hw : w ∈ inndiagGroup Tag.D4 K) :
    (d4P K)⁻¹ * w * d4P K ∈ inndiagGroup Tag.D4 K := by
  obtain ⟨b, j, hj, rfl⟩ := hw
  refine ⟨fun i => b (d4Rho i), _, d4P_inv_conj_mem hj, ?_⟩
  rw [← d4P_inv_mul_rootDiagUnit_mul]
  group

theorem mem_adjointGroup_of_mem_inndiag_of_pow_three {w : ModGL Tag.D4 K}
    (hw : w ∈ inndiagGroup Tag.D4 K) (h3 : w ^ 3 = 1) : w ∈ adjointGroup Tag.D4 K := by
  obtain ⟨b, j, hj, rfl⟩ := hw
  have hsq : rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K := by
    rw [← rootDiagUnit_mul]
    convert rootDiagUnit_sq_mem_adjointGroup_D4 (K := K) b using 2
    congr 1
    funext j
    rw [Pi.mul_apply, pow_two]
  have hconj : (rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b ∈ adjointGroup Tag.D4 K := by
    have h := conj_rootDiagUnit_mem_adjointGroup (τ := Tag.D4) b⁻¹ hj
    rwa [← rootDiagUnit_inv, inv_inv] at h
  have h2 : (rootDiagUnit Tag.D4 b * j) ^ 2 ∈ adjointGroup Tag.D4 K := by
    have e : (rootDiagUnit Tag.D4 b * j) ^ 2 = (rootDiagUnit Tag.D4 b * rootDiagUnit Tag.D4 b) *
        ((rootDiagUnit Tag.D4 b)⁻¹ * j * rootDiagUnit Tag.D4 b) * j := by rw [pow_two]; group
    rw [e]
    exact mul_mem (mul_mem hsq hconj) hj
  have e : rootDiagUnit Tag.D4 b * j = ((rootDiagUnit Tag.D4 b * j) ^ 2)⁻¹ *
      (rootDiagUnit Tag.D4 b * j) ^ 3 := by group
  rw [e, h3, mul_one]
  exact inv_mem h2

theorem coe_fieldActor_eq_conj [Finite K] (σ : K ≃+* K)
    (s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    ((fieldActor (t := TwistTag.D4) σ σ s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) =
        (diagramMap TwistTag.D4 K)⁻¹ * s * diagramMap TwistTag.D4 K := by
  have hx := ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
    (graphFixedRootGroup_le _ _ _ s.2)).2
  rw [twistHom_apply] at hx
  rw [coe_fieldActor]
  calc Units.map (entrywiseHom σ.toRingHom) (s : ModGL TwistTag.D4.tag K) =
      (diagramMap TwistTag.D4 K)⁻¹ * (diagramMap TwistTag.D4 K *
        Units.map (entrywiseHom σ.toRingHom) (s : ModGL TwistTag.D4.tag K) *
          (diagramMap TwistTag.D4 K)⁻¹) * diagramMap TwistTag.D4 K := by group
    _ = (diagramMap TwistTag.D4 K)⁻¹ * s * diagramMap TwistTag.D4 K := by rw [hx]

end D4

section Short


variable {K : Type} [Field K]

theorem sl2Short_eq_mul_d4Graph_two (A : SL2 K) (hA : A ^ 3 = 1) :
    sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨3, by decide⟩ A *
        d4Graph K 2 (sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨3, by decide⟩ A)⁻¹ =
      sl2Short K A := by
  have e3 : (d4Rho ^ 2) (⟨3, by decide⟩ : Fin Tag.D4.rank) = ⟨1, by decide⟩ := by decide
  have e1 : (d4Rho ^ 2) (⟨1, by decide⟩ : Fin Tag.D4.rank) = ⟨0, by decide⟩ := by decide
  have hAinv2 : A⁻¹ * A⁻¹ = A := by
    have : A⁻¹ * A⁻¹ = A ^ 3 * A⁻¹ * A⁻¹ := by rw [hA, one_mul]
    rw [this]
    group
  rw [mul_inv_rev, map_mul, ← map_inv, ← map_inv, inv_inv, d4Graph_sl2At, d4Graph_sl2At, e3, e1,
    sl2Short_apply]
  have h13 := sl2At_commute (K := K) (i := ⟨3, by decide⟩) (j := ⟨1, by decide⟩) (by decide)
    (by decide) (by decide) A A⁻¹
  have h03 := sl2At_commute (K := K) (i := ⟨3, by decide⟩) (j := ⟨0, by decide⟩) (by decide)
    (by decide) (by decide) A A
  have h01 := sl2At_commute (K := K) (i := ⟨1, by decide⟩) (j := ⟨0, by decide⟩) (by decide)
    (by decide) (by decide) A A
  have h11 : sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨1, by decide⟩ A⁻¹ =
      sl2At K ⟨1, by decide⟩ A := by rw [← map_mul, hAinv2]
  calc sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨3, by decide⟩ A *
        (sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨0, by decide⟩ A) =
      sl2At K ⟨1, by decide⟩ A⁻¹ * (sl2At K ⟨3, by decide⟩ A * sl2At K ⟨1, by decide⟩ A⁻¹) *
        sl2At K ⟨0, by decide⟩ A := by group
    _ = sl2At K ⟨1, by decide⟩ A⁻¹ * (sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨3, by decide⟩ A) *
        sl2At K ⟨0, by decide⟩ A := by rw [h13.eq]
    _ = (sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨1, by decide⟩ A⁻¹) *
        (sl2At K ⟨3, by decide⟩ A * sl2At K ⟨0, by decide⟩ A) := by group
    _ = sl2At K ⟨1, by decide⟩ A * (sl2At K ⟨0, by decide⟩ A * sl2At K ⟨3, by decide⟩ A) := by
        rw [h11, h03.eq]
    _ = (sl2At K ⟨1, by decide⟩ A * sl2At K ⟨0, by decide⟩ A) * sl2At K ⟨3, by decide⟩ A := by
        group
    _ = sl2At K ⟨0, by decide⟩ A * sl2At K ⟨1, by decide⟩ A * sl2At K ⟨3, by decide⟩ A := by
        rw [h01.eq]

theorem sl2Short_mul_inv_d4P (A : SL2 K) (hA : A ^ 3 = 1) :
    ((sl2Short K A : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) * (d4P K)⁻¹ =
      ((sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨3, by decide⟩ A : ↥(adjointGroup Tag.D4 K)) :
        ModGL Tag.D4 K) * (d4P K)⁻¹ *
        ((sl2At K ⟨1, by decide⟩ A⁻¹ * sl2At K ⟨3, by decide⟩ A : ↥(adjointGroup Tag.D4 K)) :
          ModGL Tag.D4 K)⁻¹ := by
  have h := congrArg (fun z : ↥(adjointGroup Tag.D4 K) => (z : ModGL Tag.D4 K))
    (sl2Short_eq_mul_d4Graph_two A hA)
  simp only [Subgroup.coe_mul, coe_d4Graph, Subgroup.coe_inv, d4P_sq, inv_inv] at h
  rw [← h, Subgroup.coe_mul]
  group

end Short

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
