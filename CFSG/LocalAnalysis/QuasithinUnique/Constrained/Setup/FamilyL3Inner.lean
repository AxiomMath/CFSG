module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyWeights
public import CFSG.RankThree.SubgroupLists.SL3Involutions

public section

namespace CFSG.QuasithinUnique.Setup.Family

open Matrix Module


section Matrices

variable {K : Type*} [Field K]

@[expose] def uMat (x y : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, x; 0, 1, y; 0, 0, 1]

theorem det_uMat (x y : K) : (uMat x y).det = 1 := by
  simp [uMat, Matrix.det_fin_three]

@[expose] def uSL (v : K × K) : SpecialLinearGroup (Fin 3) K := ⟨uMat v.1 v.2, det_uMat _ _⟩

theorem uSL_apply (v : K × K) : (uSL v : Matrix (Fin 3) (Fin 3) K) = uMat v.1 v.2 := rfl

theorem uSL_add (v w : K × K) : uSL (v + w) = uSL v * uSL w := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL_apply, uMat, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uSL_zero : uSL (0 : K × K) = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [uSL_apply, uMat]

@[expose] def negD : SpecialLinearGroup (Fin 3) K :=
  ⟨!![-1, 0, 0; 0, -1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem negD_apply : (negD : SpecialLinearGroup (Fin 3) K) =
    (!![-1, 0, 0; 0, -1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) := rfl

theorem negD_mul_self : (negD : SpecialLinearGroup (Fin 3) K) * negD = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [negD_apply, Matrix.mul_apply, Fin.sum_univ_three]

theorem negD_mul_uSL (v : K × K) : (negD : SpecialLinearGroup (Fin 3) K) * uSL v =
    uSL (-v) * negD := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [negD_apply, uSL_apply, uMat, Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def blockSL (a b c d : K) (h : a * d - b * c = 1) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![a, b, 0; c, d, 0; 0, 0, 1], by simp [Matrix.det_fin_three, h]⟩

theorem blockSL_apply (a b c d : K) (h : a * d - b * c = 1) :
    (blockSL a b c d h : Matrix (Fin 3) (Fin 3) K) = !![a, b, 0; c, d, 0; 0, 0, 1] := rfl

theorem blockSL_mul_uSL (a b c d : K) (h : a * d - b * c = 1) (v : K × K) :
    blockSL a b c d h * uSL v = uSL (a * v.1 + b * v.2, c * v.1 + d * v.2) * blockSL a b c d h := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [blockSL_apply, uSL_apply, uMat, Matrix.mul_apply, Fin.sum_univ_three]

end Matrices


section Conj

variable {K : Type} [Field K]

open CFSG.RankThree.SubgroupLists

theorem exists_conj_negD (h2 : (2 : K) ≠ 0) {t : SpecialLinearGroup (Fin 3) K}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : ∃ P : SpecialLinearGroup (Fin 3) K, P * negD = t * P := by
  classical
  have ht2' : SpecialLinearGroup.toGL t * SpecialLinearGroup.toGL t = 1 := by
    rw [← map_mul, ht2, map_one]
  have ht1' : SpecialLinearGroup.toGL t ≠ 1 := fun h =>
    ht1 (SpecialLinearGroup.toGL_injective (by rw [h, map_one]))
  have hdet : ((SpecialLinearGroup.toGL t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
    t.2
  obtain ⟨Q, hQ⟩ := exists_conj_negDiag3 h2 ht2' ht1' hdet
  have hQ' : SpecialLinearGroup.toGL t * Q = Q * negDiag3 K := by
    calc SpecialLinearGroup.toGL t * Q = Q * (Q⁻¹ * SpecialLinearGroup.toGL t * Q) := by group
      _ = Q * negDiag3 K := by rw [hQ]
  have hmat : (t : Matrix (Fin 3) (Fin 3) K) * (Q : Matrix (Fin 3) (Fin 3) K) =
      (Q : Matrix (Fin 3) (Fin 3) K) * diagonal ![-1, -1, 1] := by
    have := congrArg (fun X : GL (Fin 3) K => (X : Matrix (Fin 3) (Fin 3) K)) hQ'
    simpa [Units.val_mul, coe_negDiag3] using this
  set Qm : Matrix (Fin 3) (Fin 3) K := (Q : Matrix (Fin 3) (Fin 3) K) with hQm
  have hd : Qm.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det Qm).1 (Units.isUnit Q)).ne_zero
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![(Qm.det)⁻¹, 1, 1] with hD
  have hdetM : (Qm * D).det = 1 := by
    rw [Matrix.det_mul, hD, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [hd]
  have hDN : D * diagonal ![-1, -1, 1] = diagonal ![-1, -1, 1] * D := by
    rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]
  let P : SpecialLinearGroup (Fin 3) K := ⟨Qm * D, hdetM⟩
  have hPm : (P : Matrix (Fin 3) (Fin 3) K) = Qm * D := rfl
  refine ⟨P, ?_⟩
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have key : Qm * D * diagonal ![-1, -1, 1] = (t : Matrix (Fin 3) (Fin 3) K) * (Qm * D) := by
    calc Qm * D * diagonal ![-1, -1, 1] = Qm * (D * diagonal ![-1, -1, 1]) := by
          rw [Matrix.mul_assoc]
      _ = Qm * (diagonal ![-1, -1, 1] * D) := by rw [hDN]
      _ = (Qm * diagonal ![-1, -1, 1]) * D := by rw [Matrix.mul_assoc]
      _ = ((t : Matrix (Fin 3) (Fin 3) K) * Qm) * D := by rw [hmat]
      _ = (t : Matrix (Fin 3) (Fin 3) K) * (Qm * D) := by rw [Matrix.mul_assoc]
  have hneg : (diagonal ![-1, -1, 1] : Matrix (Fin 3) (Fin 3) K) =
      !![-1, 0, 0; 0, -1, 0; 0, 0, 1] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [diagonal]
  have key' : ((P * negD : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((t * P : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, negD_apply, hPm,
      ← hneg]
    exact key
  exact congrFun (congrFun key' i) j

end Conj


section Rank

variable {K : Type} [Field K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  (ρ₀ : SpecialLinearGroup (Fin 3) K →* (E ≃ₗ[ZMod 2] E))

@[expose] def vRep : K × K → (E ≃ₗ[ZMod 2] E) := fun v => ρ₀ (uSL v)

theorem isVAct_vRep : IsVAct (vRep ρ₀) :=
  ⟨by simp [vRep, uSL_zero], fun x y => by simp [vRep, uSL_add]⟩

theorem vRep_faithful (hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    ∀ x, vRep ρ₀ x = 1 → x = 0 := by
  intro x hx
  have hc := hρ _ hx
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hc
  have e1 := congrFun (congrFun hr 0) 2
  have e2 := congrFun (congrFun hr 1) 2
  simp [Matrix.scalar_apply, uSL_apply, uMat] at e1 e2
  exact Prod.ext e1.symm e2.symm

theorem vRep_trans : ∀ u : K × K, u ≠ 0 → ∃ (γ : K × K → K × K) (g : E ≃ₗ[ZMod 2] E),
    Function.Bijective γ ∧ (∀ (k : K) (x : K × K), γ (k • x) = k • γ x) ∧ γ (1, 0) = u ∧
      ∀ x, g * vRep ρ₀ x * g⁻¹ = vRep ρ₀ (γ x) := by
  intro u hu
  obtain ⟨b, d, hbd⟩ : ∃ b d : K, u.1 * d - b * u.2 = 1 := by
    by_cases h1 : u.1 = 0
    · have h2' : u.2 ≠ 0 := fun h => hu (Prod.ext h1 h)
      exact ⟨-(u.2)⁻¹, 0, by simp [h1, h2']⟩
    · exact ⟨0, u.1⁻¹, by simp [h1]⟩
  set γ : K × K → K × K := fun x => (u.1 * x.1 + b * x.2, u.2 * x.1 + d * x.2) with hγ
  refine ⟨γ, ρ₀ (blockSL u.1 b u.2 d hbd), ⟨fun x y hxy => ?_, fun z => ⟨(d * z.1 - b * z.2,
    -u.2 * z.1 + u.1 * z.2), ?_⟩⟩, fun k x => ?_, ?_, fun x => ?_⟩
  · have e1 := congrArg Prod.fst hxy
    have e2 := congrArg Prod.snd hxy
    simp only [hγ] at e1 e2
    refine Prod.ext ?_ ?_
    · linear_combination d * e1 - b * e2 - (x.1 - y.1) * hbd
    · linear_combination u.1 * e2 - u.2 * e1 - (x.2 - y.2) * hbd
  · refine Prod.ext ?_ ?_
    · simp only [hγ]; linear_combination z.1 * hbd
    · simp only [hγ]; linear_combination z.2 * hbd
  · simp only [hγ, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_eq_mul]
    refine Prod.ext ?_ ?_ <;> simp only <;> ring
  · simp [hγ]
  · have := blockSL_mul_uSL u.1 b u.2 d hbd x
    have h2 := congrArg ρ₀ this
    rw [map_mul, map_mul] at h2
    simp only [vRep, hγ]
    rw [mul_inv_eq_iff_eq_mul]
    exact h2

end Rank


section Main

variable {K : Type} [Field K] [Fintype K] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [Module.Finite (ZMod 2) E] (ρ₀ : SpecialLinearGroup (Fin 3) K →* (E ≃ₗ[ZMod 2] E))

omit [Module.Finite (ZMod 2) E] in
theorem range_sub1_conj (g s : E ≃ₗ[ZMod 2] E) :
    LinearMap.range (sub1 (g * s * g⁻¹)) =
      (LinearMap.range (sub1 s)).map (g : E →ₗ[ZMod 2] E) := by
  have hg : ∀ v : E, g (g⁻¹ v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]; rfl
  have hg' : ∀ v : E, g⁻¹ (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
  ext x
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨sub1 s (g⁻¹ v), ⟨_, rfl⟩, ?_⟩
    simp only [sub1_apply, LinearEquiv.coe_coe, map_sub, hg, LinearEquiv.mul_apply]
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨g w, ?_⟩
    simp only [sub1_apply, LinearEquiv.coe_coe, map_sub, hg', LinearEquiv.mul_apply]

omit [Module.Finite (ZMod 2) E] in
theorem finrank_range_sub1_conj (g s : E ≃ₗ[ZMod 2] E) :
    finrank (ZMod 2) (LinearMap.range (sub1 (g * s * g⁻¹))) =
      finrank (ZMod 2) (LinearMap.range (sub1 s)) := by
  rw [range_sub1_conj]
  exact LinearEquiv.finrank_map_eq g _

theorem negD_rank (h2 : (2 : K) ≠ 0) (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k)
    (hodd : Odd (Fintype.card K))
    (hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K)) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ₀ negD))) := by
  classical
  have hV := isVAct_vRep ρ₀
  have hall := lineProj_ne_zero_of_trans hV hodd (vRep_faithful ρ₀ hρ) (vRep_trans ρ₀)
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  have hm1 : (-1 : K) ≠ 0 := neg_ne_zero.2 h1
  have h11 : (1 : K) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have hA : (-1 : K) - 1 ≠ 0 := by
    intro h
    apply h2
    linear_combination -h
  have hB : (1 : K) + 1 ≠ 0 := by
    rw [one_add_one_eq_two]; exact h2
  set U : Finset (K × K) := {(1, 0), (0, 1), (1, 1), (1, -1)} with hU
  have hmem : ∀ u ∈ U, u = (1, 0) ∨ u = (0, 1) ∨ u = (1, 1) ∨ u = (1, -1) := by
    intro u hu
    simpa [hU] using hu
  have hU0 : ∀ u ∈ U, u ≠ 0 := by
    intro u hu
    rcases hmem u hu with rfl | rfl | rfl | rfl <;> simp [Prod.ext_iff]
  have hUind : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → det2 u v ≠ 0 := by
    intro u hu v hv huv
    rcases hmem u hu with rfl | rfl | rfl | rfl <;> rcases hmem v hv with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl huv
      | simp [det2, hm1, hA, hB]
  have hcard : U.card = 4 := by
    rw [hU, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp [Prod.ext_iff, h11]
    · simp [Prod.ext_iff]
    · simp [Prod.ext_iff]
  have hs : ρ₀ negD * ρ₀ negD = 1 := by rw [← map_mul, negD_mul_self, map_one]
  have hsρ : ∀ x, ρ₀ negD * vRep ρ₀ x * ρ₀ negD = vRep ρ₀ (-x) := by
    intro x
    have := congrArg ρ₀ (negD_mul_uSL x)
    rw [map_mul, map_mul] at this
    calc ρ₀ negD * vRep ρ₀ x * ρ₀ negD = ρ₀ (uSL (-x)) * ρ₀ negD * ρ₀ negD := by
          simp only [vRep]; rw [this]
      _ = vRep ρ₀ (-x) := by rw [mul_assoc, hs, mul_one]; rfl
  have := card_le_finrank_range_sub1 hV hodd hK hs hsρ U hU0 hUind
    (fun u hu => hall u (hU0 u hu))
  rwa [hcard] at this

theorem inner_rank_ge_four (h2 : (2 : K) ≠ 0) (hK : ∀ k : K, ∃ n : ℕ, (n : K) = k)
    (hodd : Odd (Fintype.card K))
    (hρ : ∀ g, ρ₀ g = 1 → g ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K))
    {t : SpecialLinearGroup (Fin 3) K} (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range (sub1 (ρ₀ t))) := by
  obtain ⟨P, hP⟩ := exists_conj_negD h2 ht2 ht1
  have : ρ₀ t = ρ₀ P * ρ₀ negD * (ρ₀ P)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← map_mul, ← map_mul, hP]
  rw [this, finrank_range_sub1_conj]
  exact negD_rank ρ₀ h2 hK hodd hρ

end Main

end CFSG.QuasithinUnique.Setup.Family
