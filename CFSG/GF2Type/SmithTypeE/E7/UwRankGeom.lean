module

public import CFSG.GF2Type.SmithTypeE.E7.IdUA
public import CFSG.GF2Type.SmithTypeE.E7.UwRankAbs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open CFSG.SmithD6 CFSG.GF2Type.SmithTypeE.DMod
open scoped Matrix

section Blocks

@[expose] noncomputable def LA (σ : V12 ≃ₗ[ZMod 2] V12) : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.snd (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2) ∘ₗ σ.toLinearMap ∘ₗ
    LinearMap.inr (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)

@[expose] noncomputable def LD (σ : V12 ≃ₗ[ZMod 2] V12) : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.fst (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2) ∘ₗ σ.toLinearMap ∘ₗ
    LinearMap.inl (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)

@[expose] noncomputable def LS (σ : V12 ≃ₗ[ZMod 2] V12) : (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.snd (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2) ∘ₗ σ.toLinearMap ∘ₗ
    LinearMap.inl (ZMod 2) (Fin 6 → ZMod 2) (Fin 6 → ZMod 2)

@[expose] noncomputable def Ablk (σ : V12 ≃ₗ[ZMod 2] V12) : M6 := LinearMap.toMatrix' (LA σ)

@[expose] noncomputable def Dblk (σ : V12 ≃ₗ[ZMod 2] V12) : M6 := LinearMap.toMatrix' (LD σ)

@[expose] noncomputable def Sblk (σ : V12 ≃ₗ[ZMod 2] V12) : M6 := LinearMap.toMatrix' (LS σ)

theorem Ablk_mulVec (σ : V12 ≃ₗ[ZMod 2] V12) (y : Fin 6 → ZMod 2) :
    Ablk σ *ᵥ y = (σ (0, y)).2 := by
  rw [Ablk, LinearMap.toMatrix'_mulVec]
  rfl

theorem Dblk_mulVec (σ : V12 ≃ₗ[ZMod 2] V12) (x : Fin 6 → ZMod 2) :
    Dblk σ *ᵥ x = (σ (x, 0)).1 := by
  rw [Dblk, LinearMap.toMatrix'_mulVec]
  rfl

theorem Sblk_mulVec (σ : V12 ≃ₗ[ZMod 2] V12) (x : Fin 6 → ZMod 2) :
    Sblk σ *ᵥ x = (σ (x, 0)).2 := by
  rw [Sblk, LinearMap.toMatrix'_mulVec]
  rfl

theorem Ablk_apply (σ : V12 ≃ₗ[ZMod 2] V12) (i j : Fin 6) :
    Ablk σ i j = (σ (0, Pi.single j 1)).2 i := rfl

theorem apply_blocks (σ : V12 ≃ₗ[ZMod 2] V12) (hF : ∀ y, (σ (0, y)).1 = 0)
    (x y : Fin 6 → ZMod 2) : σ (x, y) = (Dblk σ *ᵥ x, Sblk σ *ᵥ x + Ablk σ *ᵥ y) := by
  have h : ((x, y) : V12) = (x, 0) + (0, y) := by
    refine Prod.ext ?_ ?_ <;> simp
  rw [h, map_add, Dblk_mulVec, Sblk_mulVec, Ablk_mulVec]
  refine Prod.ext ?_ ?_
  · simp [hF y]
  · simp

theorem apply_F (σ : V12 ≃ₗ[ZMod 2] V12) (hF : ∀ y, (σ (0, y)).1 = 0) (y : Fin 6 → ZMod 2) :
    σ (0, y) = (0, Ablk σ *ᵥ y) := by
  rw [apply_blocks σ hF, Matrix.mulVec_zero, Matrix.mulVec_zero, zero_add]

theorem Ablk_mul (σ τ : V12 ≃ₗ[ZMod 2] V12) (hFτ : ∀ y, (τ (0, y)).1 = 0) :
    Ablk (σ * τ) = Ablk σ * Ablk τ := by
  have h : LA (σ * τ) = LA σ ∘ₗ LA τ := by
    refine LinearMap.ext fun y => ?_
    have h1 : τ (0, y) = (0, (τ (0, y)).2) := Prod.ext (hFτ y) rfl
    show (σ (τ (0, y))).2 = (σ (0, (τ (0, y)).2)).2
    rw [← h1]
  rw [Ablk, h, LinearMap.toMatrix'_comp]
  rfl

theorem Ablk_one : Ablk (1 : V12 ≃ₗ[ZMod 2] V12) = 1 := by
  have h : LA (1 : V12 ≃ₗ[ZMod 2] V12) = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    rfl
  rw [Ablk, h, LinearMap.toMatrix'_id]

theorem Dblk_transpose_mul_Ablk (σ : V12 ≃ₗ[ZMod 2] V12) (hσ : ∀ x, q12 (σ x) = q12 x)
    (hF : ∀ y, (σ (0, y)).1 = 0) : (Dblk σ)ᵀ * Ablk σ = 1 := by
  ext j k
  have h := B12_of_isometry hσ (Pi.single j 1, 0) (0, Pi.single k 1)
  have e1 : σ (Pi.single j 1, 0) = (fun i => Dblk σ i j, fun i => Sblk σ i j) := rfl
  have e2 : σ (0, Pi.single k 1) = (0, fun i => Ablk σ i k) := by
    refine Prod.ext (hF _) rfl
  rw [e1, e2, B12_pair, B12_pair] at h
  simp only [Pi.zero_apply, mul_zero, add_zero, zero_mul, Pi.single_apply, ite_mul, one_mul,
    mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.one_apply]
  rw [h]
  simp [Pi.single_apply, eq_comm]

end Blocks

section Generic

variable {σ τ : V12 ≃ₗ[ZMod 2] V12}

theorem Mlin_mul (hσ : ∀ x, q12 (σ x) = q12 x) (hF : FixesF σ) (hτ : ∀ x, q12 (τ x) = q12 x)
    (hF' : FixesF τ) : Mlin (σ * τ) = Mlin σ + Mlin τ := by
  refine LinearMap.ext fun x => ?_
  have h1 : τ (x, 0) = (x, (τ (x, 0)).2) := by
    have := fix_apply hτ hF' x 0
    rw [zero_add] at this
    exact this
  have h2 : σ (x, (τ (x, 0)).2) = (x, (τ (x, 0)).2 + (σ (x, 0)).2) := fix_apply hσ hF x _
  show (σ (τ (x, 0))).2 = (σ (x, 0)).2 + (τ (x, 0)).2
  rw [h1, h2, add_comm]

theorem comm_AN (hσ : ∀ x, q12 (σ x) = q12 x) (hFσ : ∀ y, (σ (0, y)).1 = 0)
    (hτ : ∀ x, q12 (τ x) = q12 x) (hF' : FixesF τ) (hst : σ * τ = τ * σ) :
    Ablk σ * LinearMap.toMatrix' (Mlin τ) * (Ablk σ)ᵀ = LinearMap.toMatrix' (Mlin τ) := by
  have hAN : Ablk σ * LinearMap.toMatrix' (Mlin τ) = LinearMap.toMatrix' (Mlin τ) * Dblk σ := by
    refine Matrix.toLin'.injective (LinearMap.ext fun x => ?_)
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : τ (x, 0) = (x, LinearMap.toMatrix' (Mlin τ) *ᵥ x) := by
      have := fix_apply hτ hF' x 0
      rw [zero_add] at this
      rw [this, LinearMap.toMatrix'_mulVec]
      rfl
    have h2 : τ (Dblk σ *ᵥ x, Sblk σ *ᵥ x) =
        (Dblk σ *ᵥ x, Sblk σ *ᵥ x + LinearMap.toMatrix' (Mlin τ) *ᵥ (Dblk σ *ᵥ x)) := by
      have := fix_apply hτ hF' (Dblk σ *ᵥ x) (Sblk σ *ᵥ x)
      rw [this, LinearMap.toMatrix'_mulVec]
      rfl
    have h3 := congrArg (fun f : V12 ≃ₗ[ZMod 2] V12 => (f (x, 0)).2) hst
    simp only [LinearEquiv.mul_apply] at h3
    rw [h1, apply_blocks σ hFσ, apply_blocks σ hFσ x 0, Matrix.mulVec_zero, add_zero, h2] at h3
    exact add_left_cancel h3
  have hDA : Dblk σ * (Ablk σ)ᵀ = 1 := by
    have h := Dblk_transpose_mul_Ablk σ hσ hFσ
    have h' : (Ablk σ)ᵀ * Dblk σ = 1 := by
      have := congrArg Matrix.transpose h
      rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
    exact mul_eq_one_comm.mp h'
  rw [hAN, Matrix.mul_assoc, hDA, Matrix.mul_one]

end Generic

section Data

@[expose] noncomputable def sig (g : TD6) : V12 ≃ₗ[ZMod 2] V12 := (omegaTD6.symm g).1

theorem sig_mul (g h : TD6) : sig (g * h) = sig g * sig h := by
  refine LinearEquiv.ext fun x => ?_
  show (omegaTD6.symm (g * h)).1 x = (omegaTD6.symm g).1 ((omegaTD6.symm h).1 x)
  rw [map_mul]
  rfl

theorem sig_one : sig (1 : TD6) = 1 := by
  refine LinearEquiv.ext fun x => ?_
  show (omegaTD6.symm (1 : TD6)).1 x = x
  rw [map_one]
  rfl

theorem sig_injective {g h : TD6} (hgh : sig g = sig h) : g = h :=
  omegaTD6.symm.injective (Subtype.ext hgh)

theorem iso_sig (g : TD6) : ∀ x, q12 (sig g x) = q12 x := iso_symm g

theorem stab_F {g : TD6} (hg : g ∈ Stab0) (y : Fin 6 → ZMod 2) : (sig g (0, y)).1 = 0 := by
  have hm := mem_Stab0.mp hg
  have h1 : ((0 : Fin 6 → ZMod 2), y) ∈ planeSub 0 := mem_F_iff.mpr rfl
  have h2 : sig g (0, y) ∈ planeSub 0 := by
    rw [← hm]
    exact ⟨(0, y), h1, rfl⟩
  exact mem_F_iff.mp h2

attribute [local irreducible] sig

variable (E : Subgroup TD6) (hE : E ≤ Stab0)

@[expose] noncomputable def aM : E →* M6 where
  toFun e := Ablk (sig e.1)
  map_one' := by
    show Ablk (sig 1) = 1
    rw [sig_one]
    exact Ablk_one
  map_mul' e e' := by
    show Ablk (sig (e.1 * e'.1)) = Ablk (sig e.1) * Ablk (sig e'.1)
    rw [sig_mul]
    exact Ablk_mul _ _ (stab_F (hE e'.2))

theorem aM_apply (e : E) : aM E hE e = Ablk (sig e.1) := rfl

@[expose] noncomputable def nE (e : E) : M6 := LinearMap.toMatrix' (Mlin (sig e.1))

theorem nE_apply (e : E) (i j : Fin 6) : nE E e i j = ent (sig e.1) i j := rfl

theorem fixesF_of_aM_eq_one {e : E} (h : aM E hE e = 1) : FixesF (sig e.1) := by
  intro b
  have h1 := apply_F (sig e.1) (stab_F (hE e.2)) b
  rw [aM_apply] at h
  rw [h1, h, Matrix.one_mulVec]

theorem nE_add {e e' : E} (he : aM E hE e = 1) (he' : aM E hE e' = 1) :
    nE E (e * e') = nE E e + nE E e' := by
  have h := Mlin_mul (iso_sig e.1) (fixesF_of_aM_eq_one E hE he) (iso_sig e'.1)
    (fixesF_of_aM_eq_one E hE he')
  rw [nE, nE, nE, ← map_add, ← h]
  show LinearMap.toMatrix' (Mlin (sig (e.1 * e'.1))) = LinearMap.toMatrix' (Mlin (sig e.1 * sig e'.1))
  rw [sig_mul]

theorem nE_inj {e e' : E} (he : aM E hE e = 1) (he' : aM E hE e' = 1)
    (h : nE E e = nE E e') : e = e' := by
  have hs : sig e.1 = sig e'.1 := fix_ext (iso_sig e.1) (fixesF_of_aM_eq_one E hE he)
    (iso_sig e'.1) (fixesF_of_aM_eq_one E hE he') (fun i j _ => by
      rw [← nE_apply E, ← nE_apply E, h])
  exact Subtype.ext (sig_injective hs)

theorem nE_alt {e : E} (he : aM E hE e = 1) : IsAlt (nE E e) := by
  have hF := fixesF_of_aM_eq_one E hE he
  have hσ := iso_sig e.1
  refine ⟨?_, fun i => ?_⟩
  · ext i j
    rw [Matrix.transpose_apply, nE_apply, nE_apply]
    exact ent_comm hσ hF j i
  · rw [nE_apply]
    exact ent_diag hσ hF i

theorem aM_comm [CFSG.IsElementaryAbelian 2 E] {e e' : E} (he' : aM E hE e' = 1) :
    Ablk (sig e.1) * nE E e' * (Ablk (sig e.1))ᵀ = nE E e' := by
  have hcomE : e * e' = e' * e := (IsMulCommutative.is_comm (M := E)).comm e e'
  have hst : sig e.1 * sig e'.1 = sig e'.1 * sig e.1 := by
    rw [← sig_mul, ← sig_mul]
    exact congrArg (fun z : E => sig z.1) hcomE
  exact comm_AN (iso_sig e.1) (stab_F (hE e.2)) (iso_sig e'.1) (fixesF_of_aM_eq_one E hE he') hst

theorem toHomUnits_eq_one_iff {e : E} : MonoidHom.toHomUnits (aM E hE) e = 1 ↔ aM E hE e = 1 := by
  rw [Units.ext_iff]
  rfl

include hE in
theorem rank_data [CFSG.IsElementaryAbelian 2 E] :
    ∃ (a : E →* GL6) (n : E → M6),
      (∀ e e', a e = 1 → a e' = 1 → n (e * e') = n e + n e') ∧
      (∀ e e', a e = 1 → a e' = 1 → n e = n e' → e = e') ∧
      (∀ e, a e = 1 → IsAlt (n e)) ∧
      (∀ e e', a e' = 1 → ((a e : GL6) : M6) * n e' * ((a e : GL6) : M6)ᵀ = n e') := by
  refine ⟨MonoidHom.toHomUnits (aM E hE), nE E, ?_, ?_, ?_, ?_⟩
  · intro e e' he he'
    exact nE_add E hE ((toHomUnits_eq_one_iff E hE).mp he) ((toHomUnits_eq_one_iff E hE).mp he')
  · intro e e' he he' h
    exact nE_inj E hE ((toHomUnits_eq_one_iff E hE).mp he) ((toHomUnits_eq_one_iff E hE).mp he') h
  · intro e he
    exact nE_alt E hE ((toHomUnits_eq_one_iff E hE).mp he)
  · intro e e' he'
    exact aM_comm E hE ((toHomUnits_eq_one_iff E hE).mp he')

end Data

section Rank

theorem card_le_of_isElementaryAbelian_stab0 (E : Subgroup TD6) (hE : E ≤ Stab0)
    [CFSG.IsElementaryAbelian 2 E] : Nat.card E ≤ 2 ^ 15 := by
  obtain ⟨a, n, h1, h2, h3, h4⟩ := rank_data E hE
  exact rank_abstract a n h1 h2 h3 h4

theorem card_le_of_isElementaryAbelian_TD6 (E : Subgroup TD6) (hE : CFSG.IsElementaryAbelian 2 E) :
    Nat.card E ≤ 2 ^ 15 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := hE
  have hP : IsPGroup 2 E := CFSG.IsElementaryAbelian.isPGroup 2 E
  obtain ⟨i, hi⟩ := exists_fixed_plane E hP
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i 0
  have hinv : g₀⁻¹ • (0 : Fin 75735) = i := by
    rw [inv_smul_eq_iff]
    exact hg₀.symm
  have hE' : E.map (MulAut.conj g₀).toMonoidHom ≤ Stab0 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    show (g₀ * y * g₀⁻¹) • (0 : Fin 75735) = 0
    rw [mul_smul, mul_smul, hinv, hi y hy, hg₀]
  haveI : CFSG.IsElementaryAbelian 2 (E.map (MulAut.conj g₀).toMonoidHom) :=
    CFSG.IsElementaryAbelian.map _
  have h := card_le_of_isElementaryAbelian_stab0 _ hE'
  rwa [Subgroup.card_map_of_injective (MulAut.conj g₀).injective] at h

end Rank

end CFSG.GF2Type.SmithTypeE.E7
