module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Units
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Assemble
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2Beta
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaN2IdCheck

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaN2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def fb (A B C D : Mat9) : Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)

theorem fb_mul (A B C D A' B' C' D' : Mat9) :
    fb A B C D * fb A' B' C' D' =
      fb (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  simp only [fb, Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, fromBlocks_multiply]

theorem fb_one : fb 1 0 0 1 = 1 := by
  rw [fb, Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

theorem bdN_eq_fb (A B : Mat9) : bdN (n := 9) A B = fb A 0 0 B := rfl

theorem rhoN_eq_fb (A : Mat9) : rhoN (n := 9) A = fb A 0 0 A := rfl

theorem fb_cc (A B C D : Mat9) (i j : Fin 9) :
    fb A B C D (Fin.castAdd 9 i) (Fin.castAdd 9 j) = A i j := by
  simp only [fb, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    fromBlocks_apply₁₁]

theorem fb_cn (A B C D : Mat9) (i j : Fin 9) :
    fb A B C D (Fin.castAdd 9 i) (Fin.natAdd 9 j) = B i j := by
  simp only [fb, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂]

theorem fb_nc (A B C D : Mat9) (i j : Fin 9) :
    fb A B C D (Fin.natAdd 9 i) (Fin.castAdd 9 j) = C i j := by
  simp only [fb, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₁]

theorem fb_nn (A B C D : Mat9) (i j : Fin 9) :
    fb A B C D (Fin.natAdd 9 i) (Fin.natAdd 9 j) = D i j := by
  simp only [fb, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd,
    fromBlocks_apply₂₂]

@[expose] def pmM : Mat18 := toMat 18 18 pmBits

@[expose] def pmiM : Mat18 := toMat 18 18 pmiBits

theorem pmM_eq : pmM = fb 0 1 1 1 := by
  ext r c
  refine Fin.addCases (m := 9) (n := 9) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 9) (n := 9) (fun j => ?_) (fun j => ?_) c
  · rw [fb_cc, pmM, toMat_apply, Matrix.zero_apply]; revert i j; decide
  · rw [fb_cn, pmM, toMat_apply, one_apply_eq_bz]; congr 1; revert i j; decide
  · rw [fb_nc, pmM, toMat_apply, one_apply_eq_bz]; congr 1; revert i j; decide
  · rw [fb_nn, pmM, toMat_apply, one_apply_eq_bz]; congr 1; revert i j; decide

theorem pmiM_eq : pmiM = fb 1 1 1 0 := by
  ext r c
  refine Fin.addCases (m := 9) (n := 9) (fun i => ?_) (fun i => ?_) r <;>
    refine Fin.addCases (m := 9) (n := 9) (fun j => ?_) (fun j => ?_) c
  · rw [fb_cc, pmiM, toMat_apply, one_apply_eq_bz]; congr 1; revert i j; decide
  · rw [fb_cn, pmiM, toMat_apply, one_apply_eq_bz]; congr 1; revert i j; decide
  · rw [fb_nc, pmiM, toMat_apply, one_apply_eq_bz]; congr 1; revert i j; decide
  · rw [fb_nn, pmiM, toMat_apply, Matrix.zero_apply]; revert i j; decide

theorem tauM_eq_fb : tauM = fb 1 1 0 1 := by
  rw [← tMN_eq_tauM, tMN, blkN]; rfl

theorem pm_mul_pmi : pmM * pmiM = 1 := by
  rw [pmM_eq, pmiM_eq, fb_mul, ← fb_one]
  congr 1 <;> simp [matN_add_self]

theorem pmi_mul_pm : pmiM * pmM = 1 := by
  rw [pmM_eq, pmiM_eq, fb_mul, ← fb_one]
  congr 1 <;> simp [matN_add_self]

theorem pm_bd_pmi (A B : Mat9) : pmM * bdN (n := 9) A B * pmiM = fb B 0 (A + B) A := by
  rw [pmM_eq, pmiM_eq, bdN_eq_fb, fb_mul, fb_mul]
  congr 1 <;> simp

theorem rhoN_eq_pm (A : Mat9) : rhoN (n := 9) A = pmM * bdN (n := 9) A A * pmiM := by
  rw [pm_bd_pmi, rhoN_eq_fb, matN_add_self]

theorem mat9_c1 (A B : Mat9) : B + (A + B) = A := by
  ext i j; simp only [Matrix.add_apply]
  generalize A i j = a; generalize B i j = b; revert a b; decide

theorem mat9_c3 (A B : Mat9) : A + (A + B) = B := by
  ext i j; simp only [Matrix.add_apply]
  generalize A i j = a; generalize B i j = b; revert a b; decide

theorem tau_conj_pm (A B : Mat9) :
    tauM * (pmM * bdN (n := 9) A B * pmiM) * tauM = pmM * bdN (n := 9) B A * pmiM := by
  rw [pm_bd_pmi, pm_bd_pmi, tauM_eq_fb, fb_mul, fb_mul]
  congr 1 <;> simp [mat9_c1, mat9_c3, matN_add_self, add_comm]

theorem gen3_zero : gen3 0 = st3 0 1 1 := rfl

theorem gen3_one : gen3 1 = st3 0 1 CFSG.Fischer.F4.ω := rfl

theorem gen3_two : gen3 2 = st3 0 2 1 := rfl

theorem gen3_three : gen3 3 = st3 0 2 CFSG.Fischer.F4.ω := rfl

section U

@[expose] noncomputable def rhoU : SL3 →* Mat18 where
  toFun g := pmM * bdN (n := 9) (rhoA g) 1 * pmiM
  map_one' := by rw [map_one, bdN_one, Matrix.mul_one, pm_mul_pmi]
  map_mul' a b := by
    rw [map_mul, show bdN (n := 9) (rhoA a * rhoA b) 1 = bdN (rhoA a) 1 * bdN (rhoA b) 1 by
      rw [bdN_mul, Matrix.one_mul]]
    calc pmM * (bdN (n := 9) (rhoA a) 1 * bdN (rhoA b) 1) * pmiM
        = pmM * bdN (n := 9) (rhoA a) 1 * (pmiM * pmM) * bdN (rhoA b) 1 * pmiM := by
          rw [pmi_mul_pm, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = pmM * bdN (n := 9) (rhoA a) 1 * pmiM * (pmM * bdN (rhoA b) 1 * pmiM) := by
          simp only [Matrix.mul_assoc]

theorem rhoU_apply (g : SL3) : rhoU g = pmM * bdN (n := 9) (rhoA g) 1 * pmiM := rfl

theorem rhoN_rhoA_eq (g : SL3) : rhoN (rhoA g) = rhoU g * (tauM * rhoU g * tauM) := by
  rw [rhoU_apply, tau_conj_pm, rhoN_eq_pm]
  calc pmM * bdN (n := 9) (rhoA g) (rhoA g) * pmiM
      = pmM * (bdN (n := 9) (rhoA g) 1 * bdN 1 (rhoA g)) * pmiM := by
        rw [bdN_mul, Matrix.mul_one, Matrix.one_mul]
    _ = pmM * bdN (n := 9) (rhoA g) 1 * (pmiM * pmM) * bdN 1 (rhoA g) * pmiM := by
        rw [pmi_mul_pm, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem rhoU_comm (a b : SL3) :
    rhoU a * (tauM * rhoU b * tauM) = tauM * rhoU b * tauM * rhoU a := by
  rw [rhoU_apply, rhoU_apply, tau_conj_pm]
  have e : ∀ A B : Mat9, pmM * bdN (n := 9) A 1 * pmiM * (pmM * bdN 1 B * pmiM) =
      pmM * bdN (n := 9) A B * pmiM := fun A B => by
    calc pmM * bdN (n := 9) A 1 * pmiM * (pmM * bdN 1 B * pmiM)
        = pmM * bdN (n := 9) A 1 * (pmiM * pmM) * bdN 1 B * pmiM := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [pmi_mul_pm, Matrix.mul_one, Matrix.mul_assoc pmM, bdN_mul, Matrix.mul_one,
          Matrix.one_mul]
  have e' : ∀ A B : Mat9, pmM * bdN (n := 9) 1 B * pmiM * (pmM * bdN A 1 * pmiM) =
      pmM * bdN (n := 9) A B * pmiM := fun A B => by
    calc pmM * bdN (n := 9) 1 B * pmiM * (pmM * bdN A 1 * pmiM)
        = pmM * bdN (n := 9) 1 B * (pmiM * pmM) * bdN A 1 * pmiM := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [pmi_mul_pm, Matrix.mul_one, Matrix.mul_assoc pmM, bdN_mul, Matrix.mul_one,
          Matrix.one_mul]
  rw [e, e']

theorem conj_pm_cancel (X : Mat18) : pmiM * (pmM * X * pmiM) * pmM = X := by
  calc pmiM * (pmM * X * pmiM) * pmM = (pmiM * pmM) * X * (pmiM * pmM) := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [pmi_mul_pm, Matrix.one_mul, Matrix.mul_one]

theorem rhoU_sc {a b : SL3} (h : rhoU a = tauM * rhoU b * tauM) : a ∈ Subgroup.zpowers omegaI := by
  rw [rhoU_apply, rhoU_apply, tau_conj_pm] at h
  have h2 : bdN (n := 9) (rhoA a) 1 = bdN 1 (rhoA b) := by
    have := congrArg (fun X => pmiM * X * pmM) h
    rwa [conj_pm_cancel, conj_pm_cancel] at this
  exact mem_zpowers_of_rhoA_eq_one (bdN_injective_left h2)

end U

section LiftU

variable {Γ : Type*} [Group Γ] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable {π : Γ →* (W →ₗ[ZMod 2] W)} {θ : SL3 →* Γ} {τW : W →ₗ[ZMod 2] W}
  {ι : (Fin 9 → ZMod 2) →ₗ[ZMod 2] W} {D : Subgroup Γ} {W₀ V : Submodule (ZMod 2) W}
  {τ : Γ →* Γ} {e : W ≃ₗ[ZMod 2] (Fin (9 + 9) → ZMod 2)}

theorem uIdCheck_spec : pmM * pmiM = 1 ∧ ∀ m < 4,
    toMat 18 18 (candXBits 0 m) = pmM * bdN (n := 9) (genA (Fin.ofNat 12 m)) 1 * pmiM := by
  have h := uIdCheck_eq_true
  simp only [uIdCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨pm_mul_pmi, fun m hm => ?_⟩
  rw [h.2 m hm, toMat_bmul, toMat_bmul, toMat_bd9Bits, toMat_id9]
  rfl

theorem rhoU_conj (y g : SL3) :
    rhoU (y * g * y⁻¹) = rhoN (rhoA y) * rhoU g * rhoN (rhoA y⁻¹) := by
  rw [rhoU_apply, rhoU_apply, rhoN_eq_pm, rhoN_eq_pm]
  calc pmM * bdN (n := 9) (rhoA (y * g * y⁻¹)) 1 * pmiM
      = pmM * (bdN (n := 9) (rhoA y) (rhoA y) * bdN (rhoA g) 1 * bdN (rhoA y⁻¹) (rhoA y⁻¹)) *
          pmiM := by
        rw [bdN_mul, bdN_mul, Matrix.mul_one, ← map_mul, ← map_mul, ← map_mul, mul_inv_cancel,
          map_one]
    _ = pmM * bdN (n := 9) (rhoA y) (rhoA y) * (pmiM * pmM) * bdN (rhoA g) 1 * (pmiM * pmM) *
          bdN (rhoA y⁻¹) (rhoA y⁻¹) * pmiM := by
        rw [pmi_mul_pm, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_liftU (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ}
    (hX : ∀ n < 4, matOfN e (π (d n)) = toMat 18 18 (candXBits 0 n))
    (hKc : π.ker ≤ Subgroup.center Γ) (hKo : Odd (Nat.card π.ker)) :
    ∃ ψ : SL3 →* Γ, ∀ g, matOfN e (π (ψ g)) = rhoU g := by
  set f := fU e π with hfdef
  have hfk := fU_ker e π
  set ρ := rhoU.toHomUnits with hρdef
  have hρ : ∀ g, ((ρ g : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = rhoU g := fun g => rfl
  set N := f.range.comap ρ with hNdef
  have hNn : N.Normal := by
    constructor
    intro g hg y
    obtain ⟨γ, hγ⟩ := hg
    refine ⟨θ y * γ * θ y⁻¹, Units.ext ?_⟩
    have hγ' : matOfN e (π γ) = rhoU g := by
      have := congrArg Units.val hγ
      rwa [coe_fU, hρ] at this
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, coe_fU, coe_fU, coe_fU, hK, hK, hγ', hρ,
      rhoU_conj]
  have hE : ∀ m < 4, gen3 (Fin.ofNat 12 m) ∈ N := fun m hm => by
    refine ⟨d m, Units.ext ?_⟩
    rw [coe_fU, hX m hm, hρ, rhoU_apply, rhoA_gen3, (uIdCheck_spec.2 m hm)]
  have h01 : ∀ c, st3 0 1 c ∈ N :=
    st3_mem_of_gen (by decide) (gen3_zero ▸ hE 0 (by norm_num)) (gen3_one ▸ hE 1 (by norm_num))
  have h02 : ∀ c, st3 0 2 c ∈ N :=
    st3_mem_of_gen (by decide) (gen3_two ▸ hE 2 (by norm_num)) (gen3_three ▸ hE 3 (by norm_num))
  have htop := eq_top_of_E h01 h02
  have hall : ∀ g, ρ g ∈ f.range := fun g => by
    have : g ∈ N := by rw [htop]; exact Subgroup.mem_top g
    exact this
  obtain ⟨ψ, hψ⟩ := exists_hom_comp_eq_of_odd_center (F := CFSG.Fischer.F4) (m := 2)
    (by norm_num) f (by rw [hfk]; exact hKc) (by rw [hfk]; exact hKo) ρ
    (fun i j _ c => hall _)
  refine ⟨ψ, fun g => ?_⟩
  have h1 := congrArg Units.val (DFunLike.congr_fun hψ g)
  rw [MonoidHom.comp_apply, coe_fU, hρ] at h1
  exact h1

theorem R3bHyp.concl_U [Finite Γ] (h : R3bHyp π θ τW ι D W₀ V τ) (he : matOfN e τW = tMN 9)
    (hK : ∀ g, matOfN e (π (θ g)) = rhoN (rhoA g)) {d : ℕ → Γ}
    (hX : ∀ n < 4, matOfN e (π (d n)) = toMat 18 18 (candXBits 0 n))
    (hspan : ∀ x ∈ D, ∃ μ < 16, ∃ ν < 16, x = dProd d ν * eProdG θ μ)
    (hKc : π.ker ≤ Subgroup.center Γ) (hKo : Odd (Nat.card π.ker)) :
    (∀ γ, τ γ = γ → γ ∈ θ.range) ∧ ∃ X : Subgroup Γ, X ⊔ X.map τ = ⊤ ∧ ⁅X, X.map τ⁆ = ⊥ ∧
      Nat.card (X ⊓ X.map τ : Subgroup Γ) ∣ 3 ∧ ∃ ψ' : SL3 →* X, Function.Surjective ψ' ∧
        ψ'.ker ≤ Subgroup.center SL3 ∧ ∀ g, θ g = (ψ' g : Γ) * τ (ψ' g) := by
  obtain ⟨ψ, hψ⟩ := exists_liftU hK hX hKc hKo
  have hfk := fU_ker e π
  have hfψ : ∀ g, ((fU e π (ψ g) : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = rhoU g := fun g => by rw [coe_fU, hψ]
  have hconj : ∀ g, ((TU * fU e π (ψ g) * TU⁻¹ : (Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2))ˣ) :
      Matrix (Fin (9 + 9)) (Fin (9 + 9)) (ZMod 2)) = tauM * rhoU g * tauM := fun g => by
    rw [Units.val_mul, Units.val_mul, hfψ, coe_TU, coe_TU_inv]
  have hcomm : ∀ a b, fU e π (ψ a) * (TU * fU e π (ψ b) * TU⁻¹) =
      (TU * fU e π (ψ b) * TU⁻¹) * fU e π (ψ a) := fun a b => by
    ext1; simp only [Units.val_mul, hfψ, coe_TU, coe_TU_inv]; exact rhoU_comm a b
  have hsc : ∀ a b, fU e π (ψ a) = TU * fU e π (ψ b) * TU⁻¹ → a ∈ Subgroup.zpowers omegaI :=
    fun a b hab => rhoU_sc (b := b) (by have := congrArg Units.val hab; rwa [hfψ, hconj] at this)
  have hθ : ∀ g, fU e π (θ g) = fU e π (ψ g) * (TU * fU e π (ψ g) * TU⁻¹) := fun g => by
    ext1; simp only [Units.val_mul, hfψ, coe_TU, coe_TU_inv]; rw [coe_fU, hK, rhoN_rhoA_eq]
  have hd' : ∀ n < 4, fU e π (d n) = fU e π (ψ (gen3 (Fin.ofNat 12 n))) *
      (TU * fU e π (ψ 1) * TU⁻¹) := fun n hn => by
    rw [map_one, map_one, mul_one, mul_inv_cancel, mul_one]
    ext1
    rw [hfψ, coe_fU, hX n hn, rhoU_apply, rhoA_gen3, (uIdCheck_spec.2 n hn)]
  refine concl_of_assemble τ (fU e π) TU ψ θ h.ττ (by rw [hfk]; exact hKc) (by rw [hfk]; exact hKo)
    (fun g hg hτ => h.Kr g (by rw [hfk] at hg; exact hg) hτ) (h.fU_τ he) hcomm hsc hθ h.τK
    (closure_range_union θ D h.gen) ?_
  rintro s (⟨g, rfl⟩ | hsD)
  · exact Or.inl ⟨g, rfl⟩
  · refine Or.inr ⟨h.D_sq s hsD, ?_⟩
    set S₀ : Set Γ := {x | (∃ n < 4, x = d n) ∨ x ∈ Set.range θ} with hS₀
    refine exists_Q_of_mem_closure (fU e π) TU ψ hcomm (S₀ := S₀) ?_ ?_
    · rintro x (⟨n, hn, rfl⟩ | ⟨g, rfl⟩)
      · exact ⟨_, _, hd' n hn⟩
      · exact ⟨g, g, hθ g⟩
    · obtain ⟨μ, -, ν, -, rfl⟩ := hspan s hsD
      refine mul_mem (Subgroup.list_prod_mem _ fun y hy => ?_)
        (Subgroup.list_prod_mem _ fun y hy => ?_)
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
        exact Subgroup.subset_closure (Or.inl ⟨n, bitList_lt hn, rfl⟩)
      · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hy
        exact Subgroup.subset_closure (Or.inr ⟨_, rfl⟩)

end LiftU

end CFSG.EvenSmallLie.UnitarySix.YamadaN2
