module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldNF

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent

section GraphNF


variable {K : Type} [Field K]

theorem d4Graph_add (m n : ℕ) : d4Graph K (m + n) = d4Graph K m * d4Graph K n := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [MulAut.mul_apply, coe_d4Graph, coe_d4Graph, coe_d4Graph, pow_add]
  group

theorem d4Graph_mod_three (n : ℕ) : d4Graph K (n % 3) = d4Graph K n := by
  have h3 : d4P K ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 K
  have hn : d4P K ^ (n % 3) = d4P K ^ n := by
    conv_rhs => rw [← Nat.mod_add_div n 3]
    rw [pow_add, pow_mul, h3, one_pow, mul_one]
  exact MulEquiv.ext fun h => Subtype.ext (by rw [coe_d4Graph, coe_d4Graph, hn])

theorem d4Graph_three : d4Graph K 3 = 1 := by
  rw [← d4Graph_mod_three 3, show 3 % 3 = 0 from rfl, d4Graph_zero]

theorem d4Graph_mul_exactNormalAut (ε : ℕ) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    d4Graph K ε * exactNormalAut Tag.D4 K a σ 0 =
      exactNormalAut Tag.D4 K (fun j => a ((d4Rho ^ ε).symm j)) σ 0 * d4Graph K ε := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [MulAut.mul_apply, MulAut.mul_apply, exactNormalAut_adjX, exactPerm_D4, d4Graph_adjX,
      d4Graph_adjX, exactNormalAut_adjX, exactPerm_D4]
    simp only [Equiv.Perm.one_apply, Equiv.symm_apply_apply]
  · rw [MulAut.mul_apply, MulAut.mul_apply, exactNormalAut_adjY, exactPerm_D4, d4Graph_adjY,
      d4Graph_adjY, exactNormalAut_adjY, exactPerm_D4]
    simp only [Equiv.Perm.one_apply, Equiv.symm_apply_apply]

@[expose] def HasNF (α : MulAut (adjointGroup Tag.D4 K)) (ε : ℕ) (σ : K ≃+* K) : Prop :=
  ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ),
    α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)

theorem HasNF.mul {α₁ α₂ : MulAut (adjointGroup Tag.D4 K)} {ε₁ ε₂ : ℕ} {σ₁ σ₂ : K ≃+* K}
    (h₁ : HasNF α₁ ε₁ σ₁) (h₂ : HasNF α₂ ε₂ σ₂) : HasNF (α₁ * α₂) (ε₁ + ε₂) (σ₁ * σ₂) := by
  obtain ⟨g₁, a₁, rfl⟩ := h₁
  obtain ⟨g₂, a₂, rfl⟩ := h₂
  set N₁ := exactNormalAut Tag.D4 K a₁ σ₁ 0 with hN₁
  set N₂ := exactNormalAut Tag.D4 K a₂ σ₂ 0 with hN₂
  obtain ⟨a₃, ha₃⟩ : ∃ a₃ : Fin Tag.D4.rank → Kˣ,
      N₁ * exactNormalAut Tag.D4 K (fun j => a₂ ((d4Rho ^ ε₁).symm j)) σ₂ 0 =
        exactNormalAut Tag.D4 K a₃ (σ₁ * σ₂) 0 :=
    ⟨_, exactNormalAut_mul a₁ (fun j => a₂ ((d4Rho ^ ε₁).symm j)) σ₁ σ₂ 0 0⟩
  refine ⟨g₁ * (N₁ * d4Graph K ε₁) g₂, a₃, ?_⟩
  have h1 : MulAut.conj g₁ * (N₁ * d4Graph K ε₁) * (MulAut.conj g₂ * (N₂ * d4Graph K ε₂)) =
      MulAut.conj (g₁ * (N₁ * d4Graph K ε₁) g₂) *
        (N₁ * d4Graph K ε₁ * (N₂ * d4Graph K ε₂)) := by
    rw [mul_assoc, ← mul_assoc (N₁ * d4Graph K ε₁), mul_conj_eq, map_mul]
    simp only [mul_assoc]
  rw [h1]
  congr 1
  calc N₁ * d4Graph K ε₁ * (N₂ * d4Graph K ε₂)
      = N₁ * (d4Graph K ε₁ * N₂) * d4Graph K ε₂ := by simp only [mul_assoc]
    _ = N₁ * (exactNormalAut Tag.D4 K (fun j => a₂ ((d4Rho ^ ε₁).symm j)) σ₂ 0 *
          d4Graph K ε₁) * d4Graph K ε₂ := by rw [hN₂, d4Graph_mul_exactNormalAut]
    _ = (N₁ * exactNormalAut Tag.D4 K (fun j => a₂ ((d4Rho ^ ε₁).symm j)) σ₂ 0) *
          (d4Graph K ε₁ * d4Graph K ε₂) := by simp only [mul_assoc]
    _ = exactNormalAut Tag.D4 K a₃ (σ₁ * σ₂) 0 * d4Graph K (ε₁ + ε₂) := by
        rw [ha₃, d4Graph_add]

theorem HasNF.mod_three {α : MulAut (adjointGroup Tag.D4 K)} {ε : ℕ} {σ : K ≃+* K}
    (h : HasNF α ε σ) : HasNF α (ε % 3) σ := by
  obtain ⟨g, a, rfl⟩ := h
  exact ⟨g, a, by rw [d4Graph_mod_three]⟩

theorem hasNF_conj (g : adjointGroup Tag.D4 K) : HasNF (MulAut.conj g) 0 1 := by
  have h1 : exactNormalAut Tag.D4 K 1 1 0 = 1 := by
    rw [← rootDiagAut_eq_normalAut]
    exact map_one (rootDiagAutHom Tag.D4 K)
  exact ⟨g, 1, by rw [h1, d4Graph_zero, mul_one, mul_one]⟩

end GraphNF

end CFSG.LieType.SeitzGeneration.ExcWideThree
