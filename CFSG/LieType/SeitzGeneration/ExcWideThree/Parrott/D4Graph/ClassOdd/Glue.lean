module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Conj
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Duality
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd.Defs

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Small


variable {K : Type} [Field K] [Finite K]

theorem normalForm_cube_eq_one (g : ↥(adjointGroup Tag.D4 K)) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ)
    (hα3 : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε)) ^ 3 = 1) :
    ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) ^ 3 = 1 := by
  set L := AlgebraicClosure K
  set ι := algebraMap K L
  have hx : baseChangeGL ι ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) ∈
      adjointGroup Tag.D4 L :=
    baseChangeGL_mem_adjointGroup_of_mem_inndiag ι
      (mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a))
  have h := D4Dual.graphType_cube_eq_one ι _ hα3 g a ε hx
    (fun u => D4Dual.graphType_baseChange_normalForm_one ι g a ε u)
  apply baseChangeGL_injective ι
  rw [map_pow, map_one, map_mul, map_pow, D4Dual.graphType_baseChangeGL_d4P]
  exact h

theorem d4P_mul_eq_of_fixed {w : ↥(adjointGroup Tag.D4 K)} (hw : d4Graph K 1 w = w) :
    d4P K * (w : ModGL Tag.D4 K) = w * d4P K := by
  have e := congrArg Subtype.val hw
  rw [coe_d4Graph, pow_one] at e
  calc d4P K * (w : ModGL Tag.D4 K) = (d4P K * w * (d4P K)⁻¹) * d4P K := by group
    _ = w * d4P K := by rw [e]

theorem conj_mul_d4P_inv {w : ↥(adjointGroup Tag.D4 K)} (hw : d4Graph K 1 w = w)
    (t : ModGL Tag.D4 K) :
    (w : ModGL Tag.D4 K) * (t * (d4P K)⁻¹) * (w : ModGL Tag.D4 K)⁻¹ =
      (w * t * (w : ModGL Tag.D4 K)⁻¹) * (d4P K)⁻¹ := by
  have hwP := d4P_mul_eq_of_fixed hw
  calc (w : ModGL Tag.D4 K) * (t * (d4P K)⁻¹) * (w : ModGL Tag.D4 K)⁻¹ =
      w * t * (w * d4P K)⁻¹ := by group
    _ = w * t * (d4P K * w)⁻¹ := by rw [hwP]
    _ = (w * t * (w : ModGL Tag.D4 K)⁻¹) * (d4P K)⁻¹ := by group

end Small

section Large


variable {K : Type} [Field K] [Finite K]

theorem exists_conj_of_isConjBy (hN : GraphShintaniNF) (hG : G2ThreeClass)
    (h5 : 5 ≤ ringChar K) {α : MulAut ↥(adjointGroup Tag.D4 K)} {x : ModGL Tag.D4 K}
    (hx : x ∈ inndiagGroup Tag.D4 K) (hx3 : (x * (d4P K)⁻¹) ^ 3 = 1)
    (hα : IsConjBy α (x * (d4P K)⁻¹)) :
    ∃ ψ : MulAut ↥(adjointGroup Tag.D4 K), ψ * α * ψ⁻¹ = d4Graph K 2 ∨
      ∃ B : SL2 K, B ^ 3 = 1 ∧ B ≠ 1 ∧ ψ * α * ψ⁻¹ = (gammaP K B)⁻¹ := by
  obtain ⟨v, hv, t, htγ, ht3, hvt⟩ := hN K h5 x hx hx3
  set ψ₀ := inndiagConj Tag.D4 K ⟨v, hv⟩
  have hc : IsConjBy (ψ₀ * α * ψ₀⁻¹) ((t : ModGL Tag.D4 K) * (d4P K)⁻¹) :=
    ((isConjBy_inndiagConj (K := K) ⟨v, hv⟩).conj hα).congr hvt
  have hγ2 : IsConjBy (d4Graph K 2) (d4P K)⁻¹ := (isConjBy_d4Graph 2).congr d4P_sq
  by_cases ht1 : t = 1
  · refine ⟨ψ₀, Or.inl ((hc.congr ?_).ext hγ2)⟩
    rw [ht1, Subgroup.coe_one, one_mul]
  obtain ⟨w, A, hwγ, hA3, hA1, hwt | hwt⟩ := hG K h5 t htγ ht3 ht1
  ·
    have hc' : IsConjBy ((MulAut.conj w * ψ₀) * α * (MulAut.conj w * ψ₀)⁻¹)
        ((sl2At K ⟨2, by decide⟩ A : ModGL Tag.D4 K) * (d4P K)⁻¹) := by
      have h := (isConjBy_conj w).conj hc
      rw [conj_mul_d4P_inv hwγ] at h
      have e : MulAut.conj w * (ψ₀ * α * ψ₀⁻¹) * (MulAut.conj w)⁻¹ =
          (MulAut.conj w * ψ₀) * α * (MulAut.conj w * ψ₀)⁻¹ := by group
      rw [e] at h
      refine h.congr ?_
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hwt]
    have hP2 := d4P_mul_eq_of_fixed (d4Graph_one_sl2Two (K := K) A)
    have hB : IsConjBy (gammaP K A⁻¹)⁻¹
        ((sl2At K ⟨2, by decide⟩ A : ModGL Tag.D4 K) * (d4P K)⁻¹) := by
      refine (isConjBy_gammaP A⁻¹).inv.congr ?_
      rw [map_inv, Subgroup.coe_inv]
      calc ((((sl2At K ⟨2, by decide⟩ A : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K))⁻¹ *
          d4P K)⁻¹ = (d4P K)⁻¹ * (sl2At K ⟨2, by decide⟩ A : ModGL Tag.D4 K) := by group
        _ = (d4P K)⁻¹ * ((sl2At K ⟨2, by decide⟩ A : ModGL Tag.D4 K) * d4P K) *
            (d4P K)⁻¹ := by group
        _ = (d4P K)⁻¹ * (d4P K * (sl2At K ⟨2, by decide⟩ A : ModGL Tag.D4 K)) *
            (d4P K)⁻¹ := by rw [hP2]
        _ = (sl2At K ⟨2, by decide⟩ A : ModGL Tag.D4 K) * (d4P K)⁻¹ := by group
    exact ⟨MulAut.conj w * ψ₀, Or.inr ⟨A⁻¹, by rw [inv_pow, hA3, inv_one], inv_ne_one.2 hA1,
      hc'.ext hB⟩⟩
  ·
    obtain ⟨u, hu⟩ : ∃ u : ↥(adjointGroup Tag.D4 K),
        ((sl2Short K A : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) * (d4P K)⁻¹ =
          (u : ModGL Tag.D4 K) * (d4P K)⁻¹ * (u : ModGL Tag.D4 K)⁻¹ :=
      ⟨_, sl2Short_mul_inv_d4P A hA3⟩
    have hc' : IsConjBy ((MulAut.conj u⁻¹ * MulAut.conj w * ψ₀) * α *
        (MulAut.conj u⁻¹ * MulAut.conj w * ψ₀)⁻¹) (d4P K)⁻¹ := by
      have h := (isConjBy_conj u⁻¹).conj ((isConjBy_conj w).conj hc)
      rw [conj_mul_d4P_inv hwγ] at h
      have e : MulAut.conj u⁻¹ * (MulAut.conj w * (ψ₀ * α * ψ₀⁻¹) * (MulAut.conj w)⁻¹) *
          (MulAut.conj u⁻¹)⁻¹ = (MulAut.conj u⁻¹ * MulAut.conj w * ψ₀) * α *
            (MulAut.conj u⁻¹ * MulAut.conj w * ψ₀)⁻¹ := by group
      rw [e] at h
      refine h.congr ?_
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hwt, hu, Subgroup.coe_inv]
      group
    exact ⟨_, Or.inl (hc'.ext hγ2)⟩

theorem d4GraphClassOdd_of (hN : GraphShintaniNF) (hG : G2ThreeClass) : D4GraphClassOdd := by
  intro K _ _ h5 α hα3 hαT
  obtain ⟨g, a, σ, ε, hε, -, ⟨hε0, hσ1⟩, hαeq⟩ := hαT
  subst hσ1
  have hX : IsConjBy α ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ ε) := by
    rw [hαeq]
    exact isConjBy_normalForm g a ε
  have hX3 := normalForm_cube_eq_one g a ε (hαeq ▸ hα3)
  have hgd : (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a ∈ inndiagGroup Tag.D4 K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  have hε12 : ε = 1 ∨ ε = 2 := by omega
  rcases hε12 with rfl | rfl
  · have hx := inv_conj_d4P_mem_inndiag (inv_mem hgd)
    have hxX : (d4P K)⁻¹ * ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ * d4P K *
        (d4P K)⁻¹ = ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 1)⁻¹ := by
      rw [pow_one]
      group
    have hx3 : ((d4P K)⁻¹ * ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ * d4P K *
        (d4P K)⁻¹) ^ 3 = 1 := by rw [hxX, inv_pow, hX3, inv_one]
    obtain ⟨ψ, h | ⟨B, hB3, hB1, h⟩⟩ :=
      exists_conj_of_isConjBy hN hG h5 hx hx3 (hX.inv.congr hxX.symm)
    · refine Or.inl ⟨ψ, Or.inl ?_⟩
      have e : ψ * α * ψ⁻¹ = (ψ * α⁻¹ * ψ⁻¹)⁻¹ := by group
      rw [e, h, d4Graph_two_inv]
    · refine Or.inr ⟨ψ, B, hB3, hB1, Or.inl ?_⟩
      have e : ψ * α * ψ⁻¹ = (ψ * α⁻¹ * ψ⁻¹)⁻¹ := by group
      rw [e, h, inv_inv]
  · have hxX : (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * d4P K ^ 2 =
        (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a * (d4P K)⁻¹ := by rw [d4P_sq]
    obtain ⟨ψ, h | ⟨B, hB3, hB1, h⟩⟩ :=
      exists_conj_of_isConjBy hN hG h5 hgd (hxX ▸ hX3) (hX.congr hxX)
    · exact Or.inl ⟨ψ, Or.inr h⟩
    · exact Or.inr ⟨ψ, B, hB3, hB1, Or.inr h⟩

end Large

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.ClassOdd
