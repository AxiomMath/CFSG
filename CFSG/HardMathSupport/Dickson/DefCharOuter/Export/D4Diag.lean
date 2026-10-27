module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Solomon.LocalBalance.Balance
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs

public noncomputable section

set_option linter.unusedSectionVars false

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Solomon.LocalBalance

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4Diag

theorem exactQ_D4_eq_one {K : Type} [Field K] (ε : ℕ) : exactQ Tag.D4 K ε = 1 := rfl

theorem exactPerm_D4_eq_one (ε : ℕ) : exactPerm Tag.D4 ε = 1 := rfl

theorem cartanD4_apply (i j : Fin 4) :
    Tag.D4.cartan i j =
      (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) i j := by
  fin_cases i <;> fin_cases j <;> rfl

theorem d4Rho_symm_zero : d4Rho.symm (0 : Fin 4) = (3 : Fin 4) := by rfl

theorem d4Rho_symm_one : d4Rho.symm (1 : Fin 4) = (0 : Fin 4) := by rfl

theorem d4Rho_symm_two : d4Rho.symm (2 : Fin 4) = (2 : Fin 4) := by rfl

theorem d4Rho_symm_three : d4Rho.symm (3 : Fin 4) = (1 : Fin 4) := by rfl

section Reduction

variable {K : Type} [Field K]

theorem graph_mul_normal (ε : ℕ) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) :
    d4Graph K ε * exactNormalAut Tag.D4 K a σ 0 =
      exactNormalAut Tag.D4 K (fun j => a ((d4Rho ^ ε).symm j)) σ 0 * d4Graph K ε := by
  refine mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_
  · rw [MulAut.mul_apply, MulAut.mul_apply, exactNormalAut_adjX, exactPerm_D4_eq_one,
      d4Graph_adjX, d4Graph_adjX, exactNormalAut_adjX, exactPerm_D4_eq_one]
    simp only [Equiv.Perm.one_apply, Equiv.symm_apply_apply]
  · rw [MulAut.mul_apply, MulAut.mul_apply, exactNormalAut_adjY, exactPerm_D4_eq_one,
      d4Graph_adjY, d4Graph_adjY, exactNormalAut_adjY, exactPerm_D4_eq_one]
    simp only [Equiv.Perm.one_apply, Equiv.symm_apply_apply]

theorem normal_one_one_zero :
    exactNormalAut Tag.D4 K (1 : Fin Tag.D4.rank → Kˣ) (1 : K ≃+* K) 0 = 1 := by
  refine MulEquiv.ext fun h => Subtype.ext ?_
  rw [coe_exactNormalAut, rootDiagUnit_one, exactQ_D4_eq_one]
  simp only [one_mul, inv_one, mul_one, MulAut.one_apply]
  exact Units.ext (entrywise_id _)

variable (K) in
@[expose] def diagAut : (Fin 4 → Kˣ) →* MulAut (adjointGroup Tag.D4 K) where
  toFun b := exactNormalAut Tag.D4 K b 1 0
  map_one' := normal_one_one_zero
  map_mul' b a := (exactNormalAut_diag_mul (τ := Tag.D4) b a 1 0).symm

variable (K) in
@[expose] def InnerDiag : Subgroup (Fin 4 → Kˣ) :=
  (innerAut (adjointGroup Tag.D4 K)).comap (diagAut K)

variable (K) in
@[expose] def twistDiag : (Fin 4 → Kˣ) →* (Fin 4 → Kˣ) where
  toFun b j := b (d4Rho.symm j)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem twistDiag_apply (b : Fin 4 → Kˣ) (j : Fin 4) :
    twistDiag K b j = b (d4Rho.symm j) := rfl

theorem graph_mul_diag (b : Fin 4 → Kˣ) :
    d4Graph K 1 * diagAut K b = diagAut K (twistDiag K b) * d4Graph K 1 := by
  have h := graph_mul_normal (K := K) 1 b 1
  rw [pow_one] at h
  exact h

theorem twist_mem_innerDiag {b : Fin 4 → Kˣ} (hb : b ∈ InnerDiag K) :
    twistDiag K b ∈ InnerDiag K := by
  obtain ⟨h, hh⟩ := hb
  refine ⟨d4Graph K 1 h, ?_⟩
  have e1 : d4Graph K 1 * MulAut.conj h = MulAut.conj (d4Graph K 1 h) * d4Graph K 1 :=
    mul_conj_eq _ _
  rw [hh] at e1
  exact mul_right_cancel (e1.symm.trans (graph_mul_diag b))

theorem conj_eq_normal_of_eq_rootDiagUnit {c : adjointGroup Tag.D4 K}
    {b : Fin Tag.D4.rank → Kˣ} (hb : (c : ModGL Tag.D4 K) = rootDiagUnit Tag.D4 b) :
    MulAut.conj c = exactNormalAut Tag.D4 K b 1 0 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [coe_exactNormalAut, exactQ_D4_eq_one, inv_one, mul_one, mul_one, ← hb]
  change (c : ModGL Tag.D4 K) * g * (c : ModGL Tag.D4 K)⁻¹ = _
  congr 2
  exact (Units.ext (entrywise_id _)).symm

theorem gen_mem_innerDiag (i : Fin 4) (t : Kˣ) :
    (fun j : Fin 4 => t ^ Tag.D4.cartan i j) ∈ InnerDiag K :=
  ⟨⟨torusElt Tag.D4 K i t, torusElt_mem_adjointGroup (τ := Tag.D4) i t⟩,
    conj_eq_normal_of_eq_rootDiagUnit (torusElt_eq_rootDiagUnit (τ := Tag.D4) i t)⟩

theorem sq_mem_innerDiag (b : Fin 4 → Kˣ) : b ^ 2 ∈ InnerDiag K := by
  have h : b ^ 2 =
      (fun j : Fin 4 => (b 0 ^ 2 * b 1 * b 3 * b 2 ^ 2) ^ Tag.D4.cartan (0 : Fin 4) j) *
      (fun j : Fin 4 => (b 0 * b 1 ^ 2 * b 3 * b 2 ^ 2) ^ Tag.D4.cartan (1 : Fin 4) j) *
      (fun j : Fin 4 => (b 0 ^ 2 * b 1 ^ 2 * b 3 ^ 2 * b 2 ^ 4) ^ Tag.D4.cartan (2 : Fin 4) j) *
      (fun j : Fin 4 => (b 0 * b 1 * b 3 ^ 2 * b 2 ^ 2) ^ Tag.D4.cartan (3 : Fin 4) j) := by
    funext j
    fin_cases j <;> simp [cartanD4_apply] <;>
      (apply Additive.ofMul.injective
       simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
       abel)
  rw [h]
  exact mul_mem (mul_mem (mul_mem (gen_mem_innerDiag 0 _) (gen_mem_innerDiag 1 _))
    (gen_mem_innerDiag 2 _)) (gen_mem_innerDiag 3 _)

theorem const_mem_innerDiag (x y : Kˣ) :
    (fun j : Fin 4 => if j = 2 then y else x) ∈ InnerDiag K := by
  have h : (fun j : Fin 4 => if j = 2 then y else x) =
      (fun j : Fin 4 => (y * x ^ 2) ^ Tag.D4.cartan (0 : Fin 4) j) *
      (fun j : Fin 4 => (y * x ^ 2) ^ Tag.D4.cartan (1 : Fin 4) j) *
      (fun j : Fin 4 => (y ^ 2 * x ^ 3) ^ Tag.D4.cartan (2 : Fin 4) j) *
      (fun j : Fin 4 => (y * x ^ 2) ^ Tag.D4.cartan (3 : Fin 4) j) := by
    funext j
    fin_cases j <;> simp [cartanD4_apply] <;>
      (apply Additive.ofMul.injective
       simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
       abel)
  rw [h]
  exact mul_mem (mul_mem (mul_mem (gen_mem_innerDiag 0 _) (gen_mem_innerDiag 1 _))
    (gen_mem_innerDiag 2 _)) (gen_mem_innerDiag 3 _)

theorem norm_twist (b : Fin 4 → Kˣ) :
    b * twistDiag K b * twistDiag K (twistDiag K b) =
      fun j : Fin 4 => if j = 2 then b 2 ^ 3 else b 0 * b 1 * b 3 := by
  funext j
  fin_cases j <;>
    simp [twistDiag_apply, d4Rho_symm_zero, d4Rho_symm_one, d4Rho_symm_two, d4Rho_symm_three] <;>
      (apply Additive.ofMul.injective
       simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
       abel)

theorem mem_innerDiag_of_mul_twist_inv {b : Fin 4 → Kˣ}
    (hb : b * (twistDiag K b)⁻¹ ∈ InnerDiag K) : b ∈ InnerDiag K := by
  have h2 : twistDiag K (b * (twistDiag K b)⁻¹) ∈ InnerDiag K := twist_mem_innerDiag hb
  rw [map_mul, map_inv] at h2
  have h3 : b * (twistDiag K (twistDiag K b))⁻¹ ∈ InnerDiag K := by
    have h := mul_mem hb h2
    simpa [mul_assoc] using h
  have hn : b * twistDiag K b * twistDiag K (twistDiag K b) ∈ InnerDiag K := by
    rw [norm_twist]
    exact const_mem_innerDiag _ _
  have hb3 : b ^ 3 ∈ InnerDiag K := by
    have e : b ^ 3 = (b * twistDiag K b * twistDiag K (twistDiag K b)) *
        (b * (twistDiag K b)⁻¹) * (b * (twistDiag K (twistDiag K b))⁻¹) := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel
    rw [e]
    exact mul_mem (mul_mem hn hb) h3
  have key : b ^ 3 * (b ^ 2)⁻¹ ∈ InnerDiag K := mul_mem hb3 (inv_mem (sq_mem_innerDiag b))
  rwa [show b ^ 3 * (b ^ 2)⁻¹ = b by group] at key

theorem mul_twist_inv_mem_of_comm (g c : adjointGroup Tag.D4 K) (a b : Fin 4 → Kˣ)
    (hcomm : (MulAut.conj c * diagAut K b) *
        (MulAut.conj g * (diagAut K a * d4Graph K 1)) =
      (MulAut.conj g * (diagAut K a * d4Graph K 1)) * (MulAut.conj c * diagAut K b)) :
    b * (twistDiag K b)⁻¹ ∈ InnerDiag K := by
  set γ := d4Graph K 1 with hγ
  set N := diagAut K with hN
  have e1 : (MulAut.conj c * N b) * (MulAut.conj g * (N a * γ)) =
      MulAut.conj (c * (N b) g) * (N (b * a) * γ) := by
    have h1 : N b * MulAut.conj g = MulAut.conj ((N b) g) * N b := mul_conj_eq _ _
    calc (MulAut.conj c * N b) * (MulAut.conj g * (N a * γ))
        = MulAut.conj c * ((N b * MulAut.conj g) * (N a * γ)) := by simp only [mul_assoc]
      _ = MulAut.conj c * ((MulAut.conj ((N b) g) * N b) * (N a * γ)) := by rw [h1]
      _ = MulAut.conj (c * (N b) g) * (N (b * a) * γ) := by
        simp only [map_mul, mul_assoc]
  have e2 : (MulAut.conj g * (N a * γ)) * (MulAut.conj c * N b) =
      MulAut.conj (g * (N a) (γ c)) * (N (a * twistDiag K b) * γ) := by
    have h2 : γ * MulAut.conj c = MulAut.conj (γ c) * γ := mul_conj_eq _ _
    have h3 : N a * MulAut.conj (γ c) = MulAut.conj ((N a) (γ c)) * N a := mul_conj_eq _ _
    have h4 : γ * N b = N (twistDiag K b) * γ := graph_mul_diag b
    calc (MulAut.conj g * (N a * γ)) * (MulAut.conj c * N b)
        = MulAut.conj g * (N a * (γ * MulAut.conj c) * N b) := by simp only [mul_assoc]
      _ = MulAut.conj g * (N a * (MulAut.conj (γ c) * γ) * N b) := by rw [h2]
      _ = MulAut.conj g * ((N a * MulAut.conj (γ c)) * (γ * N b)) := by simp only [mul_assoc]
      _ = MulAut.conj g * ((MulAut.conj ((N a) (γ c)) * N a) * (N (twistDiag K b) * γ)) := by
        rw [h3, h4]
      _ = MulAut.conj (g * (N a) (γ c)) * (N (a * twistDiag K b) * γ) := by
        simp only [map_mul, mul_assoc]
  have E : MulAut.conj (c * (N b) g) * N (b * a) =
      MulAut.conj (g * (N a) (γ c)) * N (a * twistDiag K b) := by
    rw [e1, e2] at hcomm
    refine mul_right_cancel (b := γ) ?_
    simpa only [mul_assoc] using hcomm
  refine ⟨(c * (N b) g)⁻¹ * (g * (N a) (γ c)), ?_⟩
  have e : b * (twistDiag K b)⁻¹ = (b * a) * (a * twistDiag K b)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  show MulAut.conj _ = N _
  have hN1 : N (b * a) = (MulAut.conj (c * (N b) g))⁻¹ *
      (MulAut.conj (g * (N a) (γ c)) * N (a * twistDiag K b)) := eq_inv_mul_of_mul_eq E
  calc MulAut.conj ((c * (N b) g)⁻¹ * (g * (N a) (γ c)))
      = (MulAut.conj (c * (N b) g))⁻¹ * MulAut.conj (g * (N a) (γ c)) := by
        rw [map_mul, map_inv]
    _ = N (b * a) * (N (a * twistDiag K b))⁻¹ := by rw [hN1]; group
    _ = N (b * a * (a * twistDiag K b)⁻¹) := by simp only [map_mul, map_inv]
    _ = N (b * (twistDiag K b)⁻¹) := by rw [← e]

end Reduction

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4Diag

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export

theorem d4_commute_diag_inner {K : Type} [Field K] [Finite K]
    (g c : adjointGroup Tag.D4 K) (a b : Fin Tag.D4.rank → Kˣ)
    (hcomm : (MulAut.conj c * exactNormalAut Tag.D4 K b 1 0) *
        (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) =
      (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 1)) *
        (MulAut.conj c * exactNormalAut Tag.D4 K b 1 0)) :
    MulAut.conj c * exactNormalAut Tag.D4 K b 1 0 ∈ innerAut (adjointGroup Tag.D4 K) := by
  obtain ⟨h, hh⟩ := D4Diag.mem_innerDiag_of_mul_twist_inv
    (D4Diag.mul_twist_inv_mem_of_comm g c a b hcomm)
  exact (show ∃ y : adjointGroup Tag.D4 K,
      MulAut.conj y = MulAut.conj c * exactNormalAut Tag.D4 K b 1 0 from
    ⟨c * h, by rw [map_mul, hh]; rfl⟩)

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export
