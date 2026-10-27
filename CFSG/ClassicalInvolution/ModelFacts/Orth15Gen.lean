module

public import CFSG.ClassicalInvolution.Asc77.AscE189OrthV
public import CFSG.ClassicalInvolution.Balance.StrongPowOrthElem

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
  CFSG.ClassicalInvolution.Balance.StrongBalance.Orth QuadraticMap

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem elemOn_mono {S S' : Submodule K V} (h : S ≤ S') : elemOn Q S ≤ elemOn Q S' := by
  rw [elemOn, Subgroup.closure_le]
  rintro _ ⟨u, w, hu, hw, -, -, rfl⟩
  exact eichler_mem_elemOn (h hu) (h hw)

section Subgroup

variable (P : HypPair Q) (H : Subgroup (V ≃ₗ[K] V))

theorem exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero'
    (hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H)
    (hW : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • P.f) {z : V}
    (hz : Q z = 0) (hez : polar Q P.e z ≠ 0) : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • z := by
  obtain ⟨g₀, hg₀, c₀, hc₀, hg₀f⟩ := hW
  set b := polar Q P.e z with hb
  set z' := b⁻¹ • z with hz'
  have hz'1 : polar Q P.e z' = 1 := by rw [hz', polar_smul_right_eq, inv_mul_cancel₀ hez]
  have hQz' : Q z' = Q P.f := by
    rw [hz', map_smul_eq_sq, hz, P.Q_f, mul_zero]
  have hw : polar Q P.e ((1 : K)⁻¹ • (z' - P.f)) = 0 := by
    rw [polar_smul_right_eq, polar_sub_right, hz'1, P.polar_ef, sub_self, mul_zero]
  have h1 := eichler_apply_eq_of_polar_eq P.Q_e hQz'.symm P.polar_ef hz'1 one_ne_zero
  refine ⟨eichler Q P.e ((1 : K)⁻¹ • (z' - P.f)) * g₀, mul_mem (hU _ hw) hg₀, c₀ * b⁻¹,
    mul_ne_zero hc₀ (inv_ne_zero hez), ?_⟩
  rw [LinearEquiv.mul_apply, hg₀f, map_smul, h1, hz', smul_smul]

variable {P}

theorem exists_mem_subgroup_apply_eq_smul' (hQ : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H)
    (hW : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • P.f) {z : V}
    (hz : Q z = 0) (hz0 : z ≠ 0) : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • z := by
  by_cases hez : polar Q P.e z = 0
  swap
  · exact exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero' P H hU hW hz hez
  by_cases hze : ∀ c : K, z ≠ c • P.e
  swap
  · push Not at hze
    obtain ⟨c, rfl⟩ := hze
    have hc : c ≠ 0 := by
      rintro rfl
      exact hz0 (zero_smul K P.e)
    refine ⟨1, one_mem _, c⁻¹, inv_ne_zero hc, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    rfl
  obtain ⟨y, hy, hey, hyz⟩ := exists_singular_polar_ne_zero_both hQ P.Q_e P.e_ne_zero hez hze
  obtain ⟨g₁, hg₁, c₁, hc₁, h₁⟩ :=
    exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero' P H hU hW hy hey
  have hg₁O := hH hg₁
  have hg₁'O := hH (inv_mem hg₁)
  have hQ₁ : Q (g₁⁻¹ z) = 0 := by rw [map_of_mem hg₁'O, hz]
  have hE₁ : polar Q P.e (g₁⁻¹ z) ≠ 0 := by
    rw [← polar_map_of_mem hg₁O P.e (g₁⁻¹ z), LinearEquiv.apply_inv_apply', h₁,
      polar_smul_left_eq]
    exact mul_ne_zero hc₁ hyz
  obtain ⟨g₂, hg₂, c₂, hc₂, h₂⟩ :=
    exists_mem_subgroup_apply_eq_smul_of_polar_ne_zero' P H hU hW hQ₁ hE₁
  refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, c₂, hc₂, ?_⟩
  rw [LinearEquiv.mul_apply, h₂, map_smul, LinearEquiv.apply_inv_apply']

theorem elementaryGroup_le_of_subgroup' (hQ : (polarBilin Q).Nondegenerate)
    (hH : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H)
    (hW : ∃ g ∈ H, ∃ c : K, c ≠ 0 ∧ g P.e = c • P.f) : elementaryGroup Q ≤ H := by
  apply elementaryGroup_le_of_eichler_mem
  intro u w hu hw
  by_cases hu0 : u = 0
  · subst hu0
    rw [eichler_zero_left]
    exact one_mem _
  obtain ⟨g, hg, c, hc, hgu⟩ := exists_mem_subgroup_apply_eq_smul' H hQ hH hU hW hu hu0
  have hgO := hH hg
  have hv : polar Q P.e (c⁻¹ • g⁻¹ w) = 0 := by
    rw [polar_smul_right_eq, ← polar_map_of_mem hgO P.e (g⁻¹ w), hgu,
      LinearEquiv.apply_inv_apply', polar_smul_left_eq, hw, mul_zero, mul_zero]
  have h1 : eichler Q u w = g * eichler Q P.e (c⁻¹ • g⁻¹ w) * g⁻¹ := by
    rw [eichler_conj hgO, hgu, map_smul, LinearEquiv.apply_inv_apply', eichler_smul_left,
      smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [h1]
  exact mul_mem (mul_mem hg (hU _ hv)) (inv_mem hg)

end Subgroup

section Decomp

variable [Finite K] [FiniteDimensional K V]

theorem elementaryGroup_le_join_of_decomp (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) {U₁ U₂ W : Submodule K V} (hW : PolarNondegOn Q W)
    (h3 : 3 ≤ Module.finrank K W) (hU₁W : ∀ x ∈ U₁, ∀ y ∈ W, polar Q x y = 0)
    (hU₂W : ∀ x ∈ U₂, ∀ y ∈ W, polar Q x y = 0) (htop : U₁ ⊔ U₂ ⊔ W = ⊤) :
    elementaryGroup Q ≤ elemOn Q (U₂ ⊔ W) ⊔ elemOn Q (U₁ ⊔ W) := by
  obtain ⟨P, he, hf⟩ := CFSG.ClassicalInvolution.Asc77.exists_hypPair_le hodd hW h3
  set H : Subgroup (V ≃ₗ[K] V) := elemOn Q (U₂ ⊔ W) ⊔ elemOn Q (U₁ ⊔ W) with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    sup_le (elemOn_le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q))
      (elemOn_le_elementaryGroup.trans (elementaryGroup_le_orthogonalGroup Q))
  have hWU₂ : W ≤ U₂ ⊔ W := le_sup_right
  have hWU₁ : W ≤ U₁ ⊔ W := le_sup_right
  have hU₁le : U₁ ≤ U₁ ⊔ W := le_sup_left
  have hU₂le : U₂ ≤ U₂ ⊔ W := le_sup_left
  have hU : ∀ w, polar Q P.e w = 0 → eichler Q P.e w ∈ H := by
    intro w hw
    have hwtop : w ∈ U₁ ⊔ U₂ ⊔ W := by rw [htop]; trivial
    obtain ⟨x, hx, w₃, hw₃, rfl⟩ := Submodule.mem_sup.mp hwtop
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hx
    have h1 : polar Q P.e w₁ = 0 := by rw [polar_comm]; exact hU₁W w₁ hw₁ _ he
    have h2 : polar Q P.e w₂ = 0 := by rw [polar_comm]; exact hU₂W w₂ hw₂ _ he
    have h3' : polar Q P.e w₃ = 0 := by
      rw [polar_add_right, polar_add_right, h1, h2, zero_add, zero_add] at hw
      exact hw
    rw [← eichler_mul (by rw [polar_add_right, h1, h2, add_zero]) h3',
      ← eichler_mul h1 h2]
    exact mul_mem (mul_mem
      (Subgroup.mem_sup_right (eichler_mem_elemOn (hWU₁ he) (hU₁le hw₁)))
      (Subgroup.mem_sup_left (eichler_mem_elemOn (hWU₂ he) (hU₂le hw₂))))
      (Subgroup.mem_sup_left (eichler_mem_elemOn (hWU₂ he) (hWU₂ hw₃)))
  have hX : PolarNondegOn Q (W ⊓ P.perp) := PolarNondegOn.inf_perp hW P he hf
  have hdim := CFSG.ClassicalInvolution.Asc77.finrank_inf_perp_hypPair hQ P he hf
  have hpos : 0 < Module.finrank K ↥(W ⊓ P.perp) := by omega
  obtain ⟨a, haX, hca⟩ : ∃ a ∈ W ⊓ P.perp, Q a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : ∀ x ∈ W ⊓ P.perp, x = 0 := by
      intro x hx
      refine hX x hx fun y hy => ?_
      have h1 := hcon (x + y) (Submodule.add_mem _ hx hy)
      rw [QuadraticMap.map_add Q, hcon x hx, hcon y hy] at h1
      simpa using h1
    obtain ⟨x, hx⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact hx (Subtype.ext (h0 x x.2))
  have haW : a ∈ W := haX.1
  have haP : a ∈ P.perp := haX.2
  set s : K := (Q a)⁻¹ with hs_def
  have hs : Q a * s * 1 = 1 := by rw [hs_def, mul_inv_cancel₀ hca, mul_one]
  have hweyl : (eichler Q P.e (s • a) * eichler Q P.f ((1 : K) • a) * eichler Q P.e (s • a)) P.e =
      (-((1 : K) ^ 2 * Q a)) • P.f := by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, eichler_e_apply_e, eichler_f_apply_e P haP,
      map_sub, map_add, map_smul, map_smul, eichler_e_apply_e, eichler_e_apply_a P haP,
      eichler_e_apply_f P haP]
    match_scalars
    · linear_combination (Q a * s * 1 - 1) * hs
    · linear_combination (-1) * hs
    · ring
  have hwmem : eichler Q P.e (s • a) * eichler Q P.f ((1 : K) • a) * eichler Q P.e (s • a) ∈ H := by
    refine Subgroup.mem_sup_left (mul_mem (mul_mem ?_ ?_) ?_)
    · exact eichler_mem_elemOn (hWU₂ he) (hWU₂ (Submodule.smul_mem _ _ haW))
    · exact eichler_mem_elemOn (hWU₂ hf) (hWU₂ (Submodule.smul_mem _ _ haW))
    · exact eichler_mem_elemOn (hWU₂ he) (hWU₂ (Submodule.smul_mem _ _ haW))
  refine elementaryGroup_le_of_subgroup' H hQ hHO hU ⟨_, hwmem, -((1 : K) ^ 2 * Q a), ?_, hweyl⟩
  rw [neg_ne_zero]
  exact mul_ne_zero (by norm_num) hca

end Decomp

end CFSG.ClassicalInvolution.ModelFacts.Orth15
