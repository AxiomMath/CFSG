module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainL
public import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainDesc

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.Models
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace ChainL

variable {F : Type} [Field F]

theorem psl3_std [Finite F] (h2 : (2 : F) ≠ 0) [Group.IsPerfect SL(3, F)] {H : Type} [Group H]
    (ψ : SL(3, F) →* H) (hker : ψ.ker ≤ Subgroup.center SL(3, F)) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), v * ψ r = ψ r * v) :
    (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, (v * ψ xN) * y = y * (v * ψ xN)) := by
  have hπk : (proj 3 F).ker = Subgroup.center SL(3, F) :=
    (ker_proj (n := 3) (K := F)).trans (scalars_eq_center 3 F)
  have hsurj := proj_surjective 3 F
  obtain ⟨φ, hφ⟩ := exists_descent ψ hker (proj 3 F) hsurj hπk hv
  have key : ∀ s t : SL(3, F), ψ s = ψ t → proj 3 F s = proj 3 F t := fun s t h => by
    have h1 : s * t⁻¹ ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
    have h3 : proj 3 F (s * t⁻¹) = 1 := by
      rw [← MonoidHom.mem_ker, hπk]
      exact hker h1
    rwa [map_mul, map_inv, mul_inv_eq_one] at h3
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hex : ∀ s : SL(3, F), ∃ s', ψ s' = v * ψ s * v⁻¹ := fun s =>
    (Subgroup.mem_normalizer_iff.mp hv (ψ s)).mp ⟨s, rfl⟩
  have hfix : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), φ (proj 3 F r) = proj 3 F r := by
    intro r hr
    apply hφ r r
    rw [hvR r hr]
    group
  have hα : φ * φ = 1 := by
    ext x
    obtain ⟨s, rfl⟩ := hsurj x
    show φ (φ (proj 3 F s)) = proj 3 F s
    obtain ⟨s', hs'⟩ := hex s
    obtain ⟨s'', hs''⟩ := hex s'
    rw [hφ s s' hs'.symm, hφ s' s'' hs''.symm]
    apply key
    rw [hs'', hs', hvinv]
    have : v * (v * ψ s * v) * v = ψ s := by
      calc v * (v * ψ s * v) * v = (v * v) * ψ s * (v * v) := by group
        _ = ψ s := by rw [hv2]; group
    exact this
  rcases psl3_aut_centralizing h2 φ hfix hα with h | h
  · left
    refine commutes_of_descent_trivial ψ (proj 3 F) hπk hv fun s s' hs => ?_
    rw [← hφ s s' hs]
    exact h s
  · right
    have hxx : (xN : SL(3, F)) * xN = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [xN, Matrix.mul_apply, Fin.sum_univ_three]
    have hxinv : (xN : SL(3, F))⁻¹ = xN := inv_eq_of_mul_eq_one_right hxx
    have hψx : ψ xN * ψ xN = 1 := by rw [← map_mul, hxx, map_one]
    have hψxi : (ψ xN)⁻¹ = ψ xN := inv_eq_of_mul_eq_one_right hψx
    have hv' : v * ψ xN ∈ Subgroup.normalizer (ψ.range : Set H) :=
      Subgroup.mul_mem _ hv (Subgroup.le_normalizer (⟨xN, rfl⟩ : ψ xN ∈ ψ.range))
    refine commutes_of_descent_trivial ψ (proj 3 F) hπk hv' fun s s' hs => ?_
    have e : (v * ψ xN)⁻¹ = ψ xN * v⁻¹ := by rw [_root_.mul_inv_rev, hψxi]
    rw [e] at hs
    have hs1 : v * ψ (xN * s * xN⁻¹) * v⁻¹ = ψ s' := by
      rw [← hs, map_mul, map_mul, map_inv, hψxi]
      group
    have h3 := hφ _ _ hs1
    rw [h] at h3
    rw [← h3]
    congr 1
    rw [hxinv]
    calc xN * (xN * s * xN) * xN = (xN * xN) * s * (xN * xN) := by group
      _ = s := by rw [hxx]; group


theorem eq_xN_of_central {r₀ : SL(3, F)}
    (hr₀ : r₀ ∈ rootSL2 F (show 2 ≤ 3 by norm_num))
    (hc : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), r₀ * r = r * r₀) (h1 : r₀ ≠ 1) :
    r₀ = xN := by
  obtain ⟨A, rfl⟩ := hr₀
  have hAc : A ∈ Subgroup.center SL(2, F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    have := hc (blockSL F 3 2 0 (by omega) B) ⟨B, rfl⟩
    rw [← map_mul, ← map_mul] at this
    exact (blockSL_injective _ this).symm
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAc
  rw [Fintype.card_fin] at hr
  have hr' : (r - 1) * (r + 1) = 0 := by linear_combination hr
  rcases mul_eq_zero.mp hr' with h | h
  · exfalso
    apply h1
    have hr1 : r = 1 := by linear_combination h
    have hA1 : A = 1 := by
      apply Subtype.ext
      rw [← hrA, hr1]
      simp
    rw [hA1, map_one]
  · have hr1 : r = -1 := by linear_combination h
    let A₁ : SL(2, F) := ⟨!![-1, 0; 0, -1], by simp⟩
    have hA1 : A = A₁ := by
      apply Subtype.ext
      rw [← hrA, hr1]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [A₁, Matrix.scalar_apply]
    rw [hA1]
    apply Subtype.ext
    rw [coe_blockSL, blockMat_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A₁, xN]

theorem psl3_involution_fund [Finite F] (h2 : (2 : F) ≠ 0) [Group.IsPerfect SL(3, F)] {H : Type}
    [Group H] (ψ : SL(3, F) →* H) (hker : ψ.ker ≤ Subgroup.center SL(3, F))
    {R : Subgroup SL(3, F)} (hR : R ∈ longRootSet (K := F) (show 2 ≤ 3 by norm_num))
    {x : SL(3, F)} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) :
    (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, (v * ψ x) * y = y * (v * ψ x)) := by
  obtain ⟨g, hg⟩ := (mem_longRootSet_iff (show 2 ≤ 3 by norm_num)).mp hR
  have hψg : ψ g ∈ ψ.range := ⟨g, rfl⟩
  set w : H := (ψ g)⁻¹ * v * ψ g with hwdef
  have hw : w ∈ Subgroup.normalizer (ψ.range : Set H) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _
      (Subgroup.le_normalizer hψg)) hv) (Subgroup.le_normalizer hψg)
  have hw2 : w * w = 1 := by
    calc w * w = (ψ g)⁻¹ * (v * v) * ψ g := by rw [hwdef]; group
      _ = 1 := by rw [hv2]; group
  have hmemR : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), g * r * g⁻¹ ∈ R := by
    intro r hr
    rw [hg]
    exact ⟨r, hr, rfl⟩
  have hwR : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), w * ψ r = ψ r * w := by
    intro r hr
    have h := hvR _ (hmemR r hr)
    rw [map_mul, map_mul, map_inv] at h
    calc w * ψ r = (ψ g)⁻¹ * (v * (ψ g * ψ r * (ψ g)⁻¹)) * ψ g := by rw [hwdef]; group
      _ = (ψ g)⁻¹ * ((ψ g * ψ r * (ψ g)⁻¹) * v) * ψ g := by rw [h]
      _ = ψ r * w := by rw [hwdef]; group
  obtain ⟨r₀, hr₀, hr₀x⟩ : ∃ r₀ ∈ rootSL2 F (show 2 ≤ 3 by norm_num), g * r₀ * g⁻¹ = x := by
    rw [hg] at hxR
    obtain ⟨r₀, hr₀, hr⟩ := hxR
    exact ⟨r₀, hr₀, hr⟩
  have hr₀c : ∀ r ∈ rootSL2 F (show 2 ≤ 3 by norm_num), r₀ * r = r * r₀ := by
    intro r hr
    have h := hxc _ (hmemR r hr)
    rw [← hr₀x] at h
    have h' : g * (r₀ * r) * g⁻¹ = g * (r * r₀) * g⁻¹ := by
      calc g * (r₀ * r) * g⁻¹ = g * r₀ * g⁻¹ * (g * r * g⁻¹) := by group
        _ = g * r * g⁻¹ * (g * r₀ * g⁻¹) := h
        _ = g * (r * r₀) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  have hr₀1 : r₀ ≠ 1 := by
    intro h
    apply hx1
    rw [← hr₀x, h]
    group
  have hr₀xN : r₀ = xN := eq_xN_of_central hr₀ hr₀c hr₀1
  have hxe : x = g * xN * g⁻¹ := by rw [← hr₀xN, hr₀x]
  have hcentral : ∀ w' : H, (∀ y ∈ ψ.range, w' * y = y * w') →
      ∀ y ∈ ψ.range, (ψ g * w' * (ψ g)⁻¹) * y = y * (ψ g * w' * (ψ g)⁻¹) := by
    intro w' hw' y hy
    have hy' : (ψ g)⁻¹ * y * ψ g ∈ ψ.range :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hψg) hy) hψg
    have := hw' _ hy'
    calc ψ g * w' * (ψ g)⁻¹ * y = ψ g * (w' * ((ψ g)⁻¹ * y * ψ g)) * (ψ g)⁻¹ := by group
      _ = ψ g * (((ψ g)⁻¹ * y * ψ g) * w') * (ψ g)⁻¹ := by rw [this]
      _ = y * (ψ g * w' * (ψ g)⁻¹) := by group
  rcases psl3_std h2 ψ hker hw hw2 hwR with h | h
  · left
    have := hcentral w h
    have e : ψ g * w * (ψ g)⁻¹ = v := by rw [hwdef]; group
    rwa [e] at this
  · right
    have := hcentral (w * ψ xN) h
    have e : ψ g * (w * ψ xN) * (ψ g)⁻¹ = v * ψ x := by
      rw [hxe, map_mul, map_mul, map_inv, hwdef]
      group
    rwa [e] at this

end ChainL

theorem psl3_model_involution_fund {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ}
    (hadm : StatedLieAdmissible .PSL 3 p e) {H : Type} [Group H]
    (ψ : (modelUniv .PSL 3 p e Fact.out).K →* H)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv .PSL 3 p e Fact.out).K)
    {R : Subgroup (modelUniv .PSL 3 p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSL (modelUniv .PSL 3 p e Fact.out).D)
    {x : (modelUniv .PSL 3 p e Fact.out).K} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    (hx1 : x ≠ 1) {v : H} (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) :
    (∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, (v * ψ x) * y = y * (v * ψ x)) := by
  have h2 : (2 : GaloisField p e) ≠ 0 := two_ne_zero_galoisField e hp2
  have : Group.IsPerfect SL(3, GaloisField p e) :=
    Group.isPerfect_def.2 (modelClauseZero .PSL 3 p e Fact.out trivial hadm).1.1
  exact ChainL.psl3_involution_fund (F := GaloisField p e) h2 ψ hker
    (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 2) (by norm_num) hR)
    hxR hxc hx1 hv hv2 hvR

end CFSG.ClassicalInvolution.ModelFacts.Orth15
