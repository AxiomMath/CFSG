module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMB01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YM01
public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMH02
public import CFSG.ClassicalInvolution.Asc77.AscC5OM20
public import CFSG.ClassicalInvolution.Asc77.AscC5OM33

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (exists_conjAut_fieldAut_sp4)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix
variable {F : Type} [Field F] {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
  {z' : Y}
namespace Frame
open CFSG.ClassicalInvolution.Asc77.C5O.M.Frame
variable (fr : Frame F Y Φ A A' z')
include fr

theorem centerless [Finite F] (h4 : Nat.card F = 3) {y : Y} (hy : ∀ x : Y, y * x = x * y) :
    y = 1 := by
  obtain ⟨h, rfl⟩ := fr.surj y
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inr (Or.inl ⟨h4, le_rfl⟩))).1
  have : Group.IsPerfect (MonoidHom.id (StatedSp 2 F)).range := Group.IsPerfect.range _
  have key := CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU.eq_of_central_ratio
    (MonoidHom.id (StatedSp 2 F)).range (MulAut.conj h).toMonoidHom (fun r _ => by
      rw [CFSG.LieType.Universal.Symplectic.center_eq]
      change h * r * h⁻¹ * r⁻¹ ∈ spScalars 2 F
      rw [← fr.ker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hy (fr.ψ r)]
      group)
  have hc : h ∈ Subgroup.center (StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro r
    have e1 : h * r * h⁻¹ = r := key r ⟨r, rfl⟩
    calc r * h = h * r * h⁻¹ * h := by rw [e1]
      _ = h * r := by group
  rw [CFSG.LieType.Universal.Symplectic.center_eq] at hc
  change h ∈ spScalars 2 F at hc
  rw [← fr.ker] at hc
  exact hc
end Frame
end Asc77.C5O.M

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem om5Centerless_proved : Om5Centerless := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD y hy
  obtain ⟨fr⟩ := M.exists_frame hD
  exact M.Frame.centerless fr Q3T7P25.natCard_gf3 hy

theorem om5InvFixFour_proved : Om5InvFixFour := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD y hy2 _
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.invFixFour (M.two_ne_zero_gf 1 (by norm_num : (3 : ℕ) ≠ 2)) hy2

theorem om5Interchange_proved : Om5Interchange := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD β t' ht' hne hcomm
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.interchange (M.two_ne_zero_gf 1 (by norm_num : (3 : ℕ) ≠ 2)) Q3T7P25.odd_natCard_gf3
      hD.twin.hzA
    hD.twin.ha₀ hD.twin.hb₀ hD.twin.ha₀sq hD.twin.hb₀sq β t' ht' hne hcomm

theorem om5ZSwap_proved : Om5ZSwap := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.zSwap (M.two_ne_zero_gf 1 (by norm_num : (3 : ℕ) ≠ 2))

theorem om5USwapNotZ_proved : Om5USwapNotZ := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD s hs hsz β
  obtain ⟨fr⟩ := M.exists_frame hD
  exact fr.uSwapNotZ (M.two_ne_zero_gf 1 (by norm_num : (3 : ℕ) ≠ 2)) hD.twin.ne hD.twin.hzA
      hD.twin.hzA' hs hsz β
end Asc77.C5O

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix
variable {F : Type} [Field F]
namespace Frame
open CFSG.ClassicalInvolution.Asc77.C5O.M.Frame
variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem exc_shape [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2) (h2 : (2 : F) ≠ 0)
    (h4 : Nat.card F = 3) (β : Y ≃* Y) (hβ2 : ∀ x, β (β x) = x)
    (hfix : ∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β x ≠ x) :
    ∃ M : gsp 2 F, (∀ x, β (fr.ψ x) = fr.ψ (conjSp 2 F M x)) ∧ ¬ IsSquare (mu M) ∧
      (gm M * gm M = mu M • 1 ∨ gm M * gm M = (-mu M) • 1) := by
  obtain ⟨M, σ, hβM⟩ := fr.exists_lift_aut h2 β
  have hsq1 : (conjAut 2 F M * fieldAut 2 F σ) * (conjAut 2 F M * fieldAut 2 F σ) = 1 := by
    ext u
    obtain ⟨x, rfl⟩ := proj_surjective (r := 2) (K := F) u
    simp only [MulAut.mul_apply, conjAut_proj, fieldAut_proj, MulAut.one_apply]
    apply fr.proj_eq_of_ψ_eq
    rw [← hβM, ← hβM, hβ2]
  rw [C25W.Sp.sq_formula] at hsq1
  obtain ⟨hσσ, a, ha, hMa⟩ := C25W.Sp.shape_of_trivial h4 _ _ hsq1
  have hσ2 : ∀ x, σ (σ x) = x := fun x => by
    have := RingEquiv.congr_fun hσσ x
    simpa using this
  have hMa' : gm M * (gm M).map σ = a • 1 := by
    have := hMa
    rw [Subgroup.coe_mul, Units.val_mul] at this
    exact this
  have hns : ¬ IsSquare (mu M) := by
    intro hsq
    obtain ⟨u, w, s, huw, hs, hs4, hsc, hfx⟩ := stable_of_isSquare h2 M σ hσ2 hMa' hsq
    apply hfix _ (fr.mem' _ ⟨u, w, huw, rfl⟩) (fr.ψ s) (Subgroup.mem_map_of_mem _ hs)
    · rw [← map_mul, ← map_mul, ← map_mul, show s * s * s * s = s * s * (s * s) by group, hs4,
        map_one]
    · intro h1
      rw [← map_mul, ← MonoidHom.mem_ker, fr.ker] at h1
      exact hsc (C25W.Sp.scalar_of_mem_spScalars h1)
    · rw [hβM, hfx]
  have hmu : mu M * σ (mu M) = a * a := by
    rw [← mu_mul_gspFieldMap]
    exact mu_eq_of_gm_eq _ hMa
  have hσ1 : ∀ x, σ x = x := by
    by_contra h
    push Not at h
    exact hns (isSquare_of_mul_ringEquiv hp σ hσ2 h (Units.ne_zero _) (map_scalar_eq hσ2 ha hMa')
      hmu)
  have hmap : (gm M).map σ = gm M := by
    ext i j
    simp [Matrix.map_apply, hσ1]
  rw [hmap] at hMa'
  rw [hσ1] at hmu
  refine ⟨M, fun x => by rw [hβM, fieldSp_of_forall_eq hσ1], hns, ?_⟩
  have h3 : (a - mu M) * (a + mu M) = 0 := by linear_combination -hmu
  rcases mul_eq_zero.mp h3 with h | h
  · left
    rw [hMa', show a = mu M by linear_combination h]
  · right
    rw [hMa', show a = -mu M by linear_combination h]
end Frame
end Asc77.C5O.M

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups
variable {F : Type} [Field F]
variable (μ : F)
variable [Fact (¬ IsSquare μ)]
variable [Finite F]

theorem isSimpleGroup_range_phiSL (h4 : Nat.card F = 3) {Y : Type} [Group Y]
    (φ : StatedSp 2 F →* Y) (hφ : φ.ker = spScalars 2 F) :
    IsSimpleGroup (φ.comp (phiSL μ)).range := by
  have : Finite (QuadraticAlgebra F μ 0) := finite_quadAlg μ
  have h4E : 4 ≤ Nat.card (QuadraticAlgebra F μ 0) := by
    rw [card_quadAlg, h4]
    norm_num
  have : IsSimpleGroup PSL(2, QuadraticAlgebra F μ 0) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4E
  let e : (φ.comp (phiSL μ)).range ≃* PSL(2, QuadraticAlgebra F μ 0) :=
    (QuotientGroup.quotientKerEquivRange (φ.comp (phiSL μ))).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (ker_phiSL_comp μ φ hφ))
  exact e.isSimpleGroup
end Asc77.C5O.M

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (exists_conjAut_fieldAut_sp4)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups
variable {F : Type} [Field F]
  {Y₁ : Type} [Group Y₁] {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ : Y₁}
  {Y₂ : Type} [Group Y₂] {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ : Y₂}
namespace Frame
open CFSG.ClassicalInvolution.Asc77.C5O.M.Frame

theorem lift_longInv [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    (fr₁ : Frame F Y₁ Φ₁ A₁ A₁' z₁) (fr₂ : Frame F Y₂ Φ₂ A₂ A₂' z₂) (γ : Y₁ ≃* Y₂)
    (M : gsp 2 F) (σ : F ≃+* F)
    (hγ : ∀ x, γ (fr₁.ψ x) = fr₂.ψ (conjSp 2 F M (fieldSp 2 F σ x)))
    (hA : A₁.map γ.toMonoidHom ≤ A₂) :
    conjSp 2 F M (fieldSp 2 F σ (longInv F 2 0)) = longInv F 2 0 := by
  set α : MulAut (StatedSp 2 F) := conjSp 2 F M * fieldSp 2 F σ with hαdef
  have hα : ∀ x, α x = conjSp 2 F M (fieldSp 2 F σ x) := fun x => rfl
  obtain ⟨eL⟩ := (isClassicalSL2_longRootSp2 (n := 2) h2 0).nonempty_mulEquiv
  have hHle : (longRootSp2 F 2 0).map α.toMonoidHom ≤ longRootSp2 F 2 0 ⊔ spScalars 2 F := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : fr₂.ψ (α r) ∈ A₂ := by
      rw [hα, ← hγ]
      exact hA ⟨fr₁.ψ r, fr₁.mem_A hr, rfl⟩
    have h1' : fr₂.ψ (α r) ∈ (longRootSp2 F 2 0).map fr₂.ψ := fr₂.hA ▸ h1
    obtain ⟨l, hl, hle⟩ := h1'
    rcases fr₂.lift_eq_iff.mp hle.symm with h | h
    · rw [MulEquiv.coe_toMonoidHom, h]
      exact Subgroup.mem_sup_left hl
    · rw [MulEquiv.coe_toMonoidHom, h]
      exact Subgroup.mul_mem_sup hl negOne_mem_spScalars
  have hle := Q3T7P25.le_of_le_sup_center3_card h4
    (((longRootSp2 F 2 0).equivMapOfInjective α.toMonoidHom α.injective).symm.trans eL)
    CFSG.ClassicalInvolution.Asc77.C5O.M.spScalars_le_center
    (fun z hz => Q3T7P25.mul_self_of_mem_spScalars hz) hHle
  have hi : α (longInv F 2 0) ∈ longRootSp2 F 2 0 :=
    hle ⟨_, longInv_mem_longRootSp2 0, rfl⟩
  have hsq : α (longInv F 2 0) * α (longInv F 2 0) = 1 := by
    rw [← map_mul, longInv_mul_self, map_one]
  rcases sq_eq_one_of_mem_L h2 0 hi hsq with h | h
  · exfalso
    apply longInv_ne_one h2 0
    exact α.injective (by rw [h, map_one])
  · exact h
end Frame
end Asc77.C5O.M

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups
variable {F : Type} [Field F]
namespace Frame
open CFSG.ClassicalInvolution.Asc77.C5O.M.Frame
variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem hasBigFix_of_plus [Finite F] (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    (hodd : Odd (Nat.card F)) (β : Y ≃* Y) (M : gsp 2 F)
    (hβ : ∀ x, β (fr.ψ x) = fr.ψ (conjSp 2 F M x)) (hns : ¬ IsSquare (mu M))
    (hN : gm M * gm M = mu M • 1) :
    ∃ L : Subgroup Y, (∀ x ∈ L, β x = x) ∧ IsSimpleGroup L ∧ (∃ x y : L, x * y ≠ y * x) ∧
      Nat.card SL(2, F) ^ 2 < 4 * Nat.card L := by
  obtain ⟨g, hg⟩ := exists_conj_nPlus h2 hN hns
  have : Fact (¬ IsSquare (mu M)) := ⟨hns⟩
  set φ := fr.ψ.comp (MulAut.conj g).toMonoidHom with hφdef
  have hφ : φ.ker = spScalars 2 F := ker_comp_conj fr.ψ fr.ker g
  refine ⟨(φ.comp (phiSL (mu M))).range, ?_, isSimpleGroup_range_phiSL _ h4 φ hφ,
    exists_not_comm_range_phiSL _ h2 φ hφ, ?_⟩
  · rintro _ ⟨s, rfl⟩
    change β (fr.ψ (g * phiSL (mu M) s * g⁻¹)) = fr.ψ (g * phiSL (mu M) s * g⁻¹)
    rw [hβ, conjSp_eq_self_of_comm]
    have hGi : mat 2 F g * mat 2 F g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have hiG : ∀ X, mat 2 F g⁻¹ * (mat 2 F g * X) = X := fun X => by
      rw [← Matrix.mul_assoc, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]
    have hM : gm M = mat 2 F g * nPlus (mu M) * mat 2 F g⁻¹ := by
      rw [hg, Matrix.mul_assoc, hGi, Matrix.mul_one]
    rw [map_mul, map_mul, mat_phiSL, hM]
    simp only [Matrix.mul_assoc, hiG]
    rw [← Matrix.mul_assoc (nPlus (mu M)), ← phiM_mul_nPlus, Matrix.mul_assoc]
  · have : Finite (QuadraticAlgebra F (mu M) 0) := finite_quadAlg _
    have hc := card_range_phiSL (mu M) hodd φ hφ
    rw [natCard_sl2, card_quadAlg] at hc
    rw [natCard_sl2]
    have hq : 2 ≤ Nat.card F := by omega
    have := card_ineq (Nat.card F) hq
    omega
end Frame
end Asc77.C5O.M

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU (eq_of_central_ratio)
open scoped Matrix MatrixGroups
variable {F : Type} [Field F]
section OddNormal
variable [Finite F]

theorem eq_bot_of_odd_normal_L (h2 : (2 : F) ≠ 0) (k : Fin 2)
    {K : Subgroup (StatedSp 2 F)} (hK : K ≤ longRootSp2 F 2 k)
    (hnorm : ∀ x ∈ K, ∀ r ∈ longRootSp2 F 2 k, r * x * r⁻¹ ∈ K) (hodd : Odd (Nat.card K)) :
    K = ⊥ := by
  set e := longBlock F 2 k with he
  have hinj : Function.Injective e := longBlock_injective k
  set K' := K.comap e with hK'
  have hmap : K'.map e = K := by
    rw [hK', Subgroup.map_comap_eq, ← longRootSp2, inf_eq_right.mpr hK]
  have hnormal : K'.Normal := ⟨fun x hx g => by
    change e (g * x * g⁻¹) ∈ K
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ hx _ ⟨g, rfl⟩⟩
  have hodd' : Odd (Nat.card K') := by
    rw [← hmap, Subgroup.card_map_of_injective hinj] at hodd
    exact hodd
  have hle : K' ≤ classicalInvolutionOddCore SL(2, F) := le_sSup ⟨hnormal, hodd'⟩
  rw [CFSG.ClassicalInvolution.Asc77.CX.CX4.L4.oddCore_sl2_eq_bot_odd h2, le_bot_iff] at hle
  rw [← hmap, hle, Subgroup.map_bot]
variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
namespace Frame
open CFSG.ClassicalInvolution.Asc77.C5O.M.Frame
variable (fr : Frame F Y Φ A A' z')
include fr

theorem comm_of_odd_normal (h2 : (2 : F) ≠ 0)
    {N : Subgroup Y} (hN : N ≤ A ⊔ A') (hnorm : ∀ n ∈ N, ∀ r ∈ A ⊔ A', r * n * r⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) (k : Fin 2) {n : Y} (hn : n ∈ N) {r : StatedSp 2 F}
    (hr : r ∈ longRootSp2 F 2 k) : n * fr.ψ r = fr.ψ r * n := by
  have hLk : ∀ x ∈ longRootSp2 F 2 k, fr.ψ x ∈ A ⊔ A' := fun x hx => by
    rw [← fr.map_sup_L]
    refine ⟨x, ?_, rfl⟩
    fin_cases k
    · exact Subgroup.mem_sup_left hx
    · exact Subgroup.mem_sup_right hx
  set K := longRootSp2 F 2 k ⊓ N.comap fr.ψ with hK
  have hKnorm : ∀ x ∈ K, ∀ s ∈ longRootSp2 F 2 k, s * x * s⁻¹ ∈ K := fun x hx s hs => by
    rw [Subgroup.mem_inf] at hx ⊢
    refine ⟨mul_mem (mul_mem hs hx.1) (inv_mem hs), ?_⟩
    change fr.ψ (s * x * s⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hnorm _ hx.2 _ (hLk s hs)
  let f : K →* N := (fr.ψ.comp K.subtype).codRestrict N (fun x => (Subgroup.mem_inf.mp x.2).2)
  have hf : Function.Injective f := fun x y hxy => by
    have e : fr.ψ x = fr.ψ y := congrArg Subtype.val hxy
    exact Subtype.ext (fr.injOn_L h2 k (Subgroup.mem_inf.mp x.2).1 (Subgroup.mem_inf.mp y.2).1 e)
  have hKodd : Odd (Nat.card K) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_injective f hf)
  have hK0 : K = ⊥ := eq_bot_of_odd_normal_L h2 k inf_le_left hKnorm hKodd
  have hnA : n ∈ (longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1).map fr.ψ := by
    rw [fr.map_sup_L]
    exact hN hn
  obtain ⟨x, hx, rfl⟩ := hnA
  have hc : x * r * x⁻¹ * r⁻¹ ∈ K := by
    rw [Subgroup.mem_inf]
    refine ⟨mul_mem (conj_mem_L_of_mem_sup h2 k hx hr) (inv_mem hr), ?_⟩
    change fr.ψ (x * r * x⁻¹ * r⁻¹) ∈ N
    have e : fr.ψ (x * r * x⁻¹ * r⁻¹) =
        fr.ψ x * (fr.ψ r * (fr.ψ x)⁻¹ * (fr.ψ r)⁻¹) := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      group
    rw [e]
    exact mul_mem hn (hnorm _ (inv_mem hn) _ (hLk r hr))
  rw [hK0, Subgroup.mem_bot] at hc
  have hxr : x * r = r * x := by
    calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
      _ = r * x := by rw [hc, one_mul]
  rw [← map_mul, ← map_mul, hxr]

theorem eq_one_of_odd_normal (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3)
    {N : Subgroup Y} (hN : N ≤ A ⊔ A') (hnorm : ∀ n ∈ N, ∀ r ∈ A ⊔ A', r * n * r⁻¹ ∈ N)
    (hodd : Odd (Nat.card N)) {n : Y} (hn : n ∈ N) : n = 1 := by
  have hnA : n ∈ (longRootSp2 F 2 0 ⊔ longRootSp2 F 2 1).map fr.ψ := by
    rw [fr.map_sup_L]
    exact hN hn
  obtain ⟨x, hx, rfl⟩ := hnA
  have hxc : ∀ (k : Fin 2), ∀ r ∈ longRootSp2 F 2 k, x * r = r * x := by
    intro k r hr
    obtain ⟨eB⟩ := (isClassicalSL2_longRootSp2 h2 k).nonempty_mulEquiv
    have key := Q3T7P25.eq_of_central_ratio3_card (longRootSp2 F 2 k) h4 eB
      (fun z hz => Q3T7P25.mul_self_of_mem_center_sp hz) (MulAut.conj x).toMonoidHom
      (fun s hs => by
        have e := Frame.comm_of_odd_normal fr h2 hN hnorm hodd k hn hs
        have e' : fr.ψ (x * s * x⁻¹) = fr.ψ s := by
          rw [map_mul, map_mul, map_inv, e]
          group
        rcases fr.lift_eq_iff.mp e' with h | h
        · change x * s * x⁻¹ * s⁻¹ ∈ _
          rw [h, mul_inv_cancel]
          exact one_mem _
        · change x * s * x⁻¹ * s⁻¹ ∈ _
          have e2 : s * negOne F * s⁻¹ = negOne F := by
            rw [Subgroup.mem_center_iff.mp negOne_mem_center s]
            group
          rw [h, e2]
          exact negOne_mem_center) r hr
    change x * r * x⁻¹ = r at key
    calc x * r = x * r * x⁻¹ * x := by group
      _ = r * x := by rw [key]
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_L h2 hx
  have hac : ∀ r ∈ longRootSp2 F 2 0, a * r = r * a := fun r hr => by
    have e1 := hxc 0 r hr
    have e2 : b * r = r * b := (commute_L 0 hr hb).symm
    calc a * r = a * b * r * b⁻¹ := by rw [mul_assoc a b r, e2]; group
      _ = r * (a * b) * b⁻¹ := by rw [e1]
      _ = r * a := by group
  have hbc : ∀ r ∈ longRootSp2 F 2 1, b * r = r * b := fun r hr => by
    have e1 := hxc 1 r hr
    have e2 : a * r = r * a := commute_L 0 ha hr
    calc b * r = a⁻¹ * (a * b * r) := by group
      _ = a⁻¹ * (r * (a * b)) := by rw [e1]
      _ = a⁻¹ * (a * r) * b := by rw [e2]; group
      _ = r * b := by group
  have hz1 : fr.ψ (longInv F 2 0) ≠ 1 := by
    intro h
    rw [← MonoidHom.mem_ker, fr.ker, mem_spScalars_iff] at h
    rcases h with h | h
    · exact longInv_ne_one h2 0 h
    · exact negOne_not_mem_L h2 0 (h ▸ longInv_mem 0)
  have hz2 : fr.ψ (longInv F 2 0) * fr.ψ (longInv F 2 0) = 1 := by
    rw [← map_mul, longInv_mul_self, map_one]
  have hzN : fr.ψ (a * b) = fr.ψ (longInv F 2 0) → False := fun h => by
    have hmem : fr.ψ (longInv F 2 0) ∈ N := h ▸ hn
    have hord : orderOf (fr.ψ (longInv F 2 0)) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hz2) hz1
    have hdvd : orderOf (fr.ψ (longInv F 2 0)) ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨_, hmem⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  rcases eq_of_mem_center_L 0 ha hac with rfl | rfl <;>
    rcases eq_of_mem_center_L 1 hb hbc with rfl | rfl
  · rw [mul_one, map_one]
  · exfalso
    apply hzN
    rw [one_mul, fr.ψ_longInv_one, ← fr.hz]
  · exfalso
    exact hzN (by rw [mul_one])
  · rw [show longInv F 2 0 * longInv F 2 1 = negOne F from (negOne_eq_longInv_mul 0).symm,
      fr.ψ_negOne]

theorem ker_le_ker (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3) {M Y' : Type} [Group M]
    [Group Y'] (π₁ : M →* Y') (π₂ : M →* Y) (hrange : π₂.range = A ⊔ A')
    (hodd : Odd (Nat.card π₁.ker)) : π₁.ker ≤ π₂.ker := by
  set N := π₁.ker.map π₂ with hNdef
  have hN : N ≤ A ⊔ A' := by
    rw [← hrange, hNdef]
    exact Subgroup.map_le_range _ _
  have hnorm : ∀ n ∈ N, ∀ r ∈ A ⊔ A', r * n * r⁻¹ ∈ N := by
    rintro _ ⟨k, hk, rfl⟩ r hr
    rw [← hrange] at hr
    obtain ⟨m, rfl⟩ := hr
    refine ⟨m * k * m⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact (inferInstance : π₁.ker.Normal).conj_mem k hk m
  have hoddN : Odd (Nat.card N) := Odd.of_dvd_nat hodd (Subgroup.card_map_dvd π₁.ker π₂)
  intro k hk
  rw [MonoidHom.mem_ker]
  exact Frame.eq_one_of_odd_normal fr h2 h4 hN hnorm hoddN ⟨k, hk, rfl⟩
end Frame
end OddNormal
end Asc77.C5O.M

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups
variable {F : Type} [Field F]
namespace Frame
open CFSG.ClassicalInvolution.Asc77.C5O.M.Frame
variable {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
  (fr : Frame F Y Φ A A' z')
include fr

theorem excClass [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp : p ≠ 2)
    (h2 : (2 : F) ≠ 0) (h4 : Nat.card F = 3) (hodd : Odd (Nat.card F)) (β₁ β₂ : Y ≃* Y)
    (hβ₁2 : ∀ x, β₁ (β₁ x) = x) (hβ₂2 : ∀ x, β₂ (β₂ x) = x)
    (hfix₁ : ∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₁ x ≠ x)
    (hfix₂ : ∀ J ∈ Φ, ∀ x ∈ J, x * x * x * x = 1 → x * x ≠ 1 → β₂ x ≠ x)
    (hbig₁ : ¬ ∃ L : Subgroup Y, (∀ x ∈ L, β₁ x = x) ∧ IsSimpleGroup L ∧
      (∃ x y : L, x * y ≠ y * x) ∧ Nat.card SL(2, F) ^ 2 < 4 * Nat.card L)
    (hbig₂ : ¬ ∃ L : Subgroup Y, (∀ x ∈ L, β₂ x = x) ∧ IsSimpleGroup L ∧
      (∃ x y : L, x * y ≠ y * x) ∧ Nat.card SL(2, F) ^ 2 < 4 * Nat.card L) :
    ∃ g : Y, ∀ x : Y, β₂ x = g * β₁ (g⁻¹ * x * g) * g⁻¹ := by
  obtain ⟨M₁, hM₁, hns₁, h₁⟩ := Frame.exc_shape fr hp h2 h4 β₁ hβ₁2 hfix₁
  obtain ⟨M₂, hM₂, hns₂, h₂⟩ := Frame.exc_shape fr hp h2 h4 β₂ hβ₂2 hfix₂
  rcases h₁ with h₁ | h₁
  · exact absurd (Frame.hasBigFix_of_plus fr h2 h4 hodd β₁ M₁ hM₁ hns₁ h₁) hbig₁
  rcases h₂ with h₂ | h₂
  · exact absurd (Frame.hasBigFix_of_plus fr h2 h4 hodd β₂ M₂ hM₂ hns₂ h₂) hbig₂
  exact fr.exc_conj h2 β₁ β₂ M₁ M₂ hM₁ hM₂ hns₁ hns₂ h₁ h₂
end Frame
end Asc77.C5O.M

end

section

namespace Asc77.C5O.M
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Asc77.C5O.M
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix MatrixGroups
variable {F : Type} [Field F]
  {Y₁ : Type} [Group Y₁] {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ : Y₁}
  {Y₂ : Type} [Group Y₂] {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ : Y₂}
section Setup

theorem exists_setup {Y₁ Y₂ : Type} [Group Y₁] [Finite Y₁] [Group Y₂] [Finite Y₂]
    {Φ₁ : Set (Subgroup Y₁)} {A₁ A₁' : Subgroup Y₁} {z₁ a₁ b₁ : Y₁}
    {Φ₂ : Set (Subgroup Y₂)} {A₂ A₂' : Subgroup Y₂} {z₂ a₂ b₂ : Y₂}
    {M : Type} [Group M] [Finite M] {π₁ : M →* Y₁} {π₂ : M →* Y₂} {L L' : Subgroup M}
    (hT : TwinShare Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ π₁ π₂ L L') :
    ∃ (fr₁ : Frame (GaloisField 3 1) Y₁ Φ₁ A₁ A₁' z₁) (Φ₂' : Set (Subgroup Y₂))
      (fr₂ : Frame (GaloisField 3 1) Y₂ Φ₂' A₂ A₂' z₂)
      (θ : Fin 2 → MulAut SL(2, GaloisField 3 1)) (d : Fin 2 → GL (Fin 2) (GaloisField 3 1)),
      π₁.ker = π₂.ker ∧
      (∀ k b, Matrix.SpecialLinearGroup.toGL (θ k b) =
        d k * Matrix.SpecialLinearGroup.toGL b * (d k)⁻¹) ∧
      (∀ (k : Fin 2) (m : M) (b : SL(2, GaloisField 3 1)),
        π₁ m = fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) →
          π₂ m = fr₂.ψ (longBlock (GaloisField 3 1) 2 k (θ k b))) := by
  obtain ⟨fr₁⟩ := exists_frame hT.data₁
  obtain ⟨fr₂⟩ := exists_frame hT.data₂
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 := two_ne_zero_gf 1 hp
  have h4 : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  have hker : π₁.ker = π₂.ker := le_antisymm
    (Frame.ker_le_ker fr₂ h2 h4 π₁ π₂ hT.range₂ hT.odd₁)
    (Frame.ker_le_ker fr₁ h2 h4 π₂ π₁ hT.range₁ hT.odd₂)
  have hr : ∀ {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y} {z' : Y}
      (fr : Frame (GaloisField 3 1) Y Φ A A' z') (π : M →* Y)
      (hm : L.map π = A ∧ L'.map π = A'),
      L.map π = (fr.ψ.comp (longBlock (GaloisField 3 1) 2 0)).range ∧
        L'.map π = (fr.ψ.comp (longBlock (GaloisField 3 1) 2 1)).range := by
    intro Y _ Φ A A' z' fr π hm
    rw [range_ψ_longBlock, range_ψ_longBlock, hm.1, hm.2]
    exact ⟨fr.hA, fr.hA'⟩
  obtain ⟨θ₀, hθ₀⟩ := exists_twin_iso π₁ π₂ hker L _ _ (injective_ψ_longBlock fr₁ h2 0)
    (injective_ψ_longBlock fr₂ h2 0) (hr fr₁ π₁ hT.map₁).1 (hr fr₂ π₂ hT.map₂).1
  obtain ⟨θ₁, hθ₁⟩ := exists_twin_iso π₁ π₂ hker L' _ _ (injective_ψ_longBlock fr₁ h2 1)
    (injective_ψ_longBlock fr₂ h2 1) (hr fr₁ π₁ hT.map₁).2 (hr fr₂ π₂ hT.map₂).2
  obtain ⟨d₀, ρ₀, hd₀⟩ := Q3T7P25.exists_semilinear3 h4 θ₀
  obtain ⟨d₁, ρ₁, hd₁⟩ := Q3T7P25.exists_semilinear3 h4 θ₁
  have hρ : ρ₀ = ρ₁ := Q3T7P25.ringEquiv_eq3 h4 ρ₀ ρ₁
  subst hρ
  refine ⟨fr₁, _, fr₂.twist ρ₀, fun k => if k = 0 then (slMap ρ₀)⁻¹ * θ₀ else (slMap ρ₀)⁻¹ * θ₁,
    fun k => glm ρ₀.symm (if k = 0 then d₀ else d₁), hker, ?_, ?_⟩
  · intro k b
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · simp only [↓reduceIte]
      change Matrix.SpecialLinearGroup.toGL ((slMap ρ₀).symm (θ₀ b)) = _
      rw [slg_slMap_symm, hd₀, map_mul, map_mul, map_inv, glm_symm_glm]
    · simp only [one_ne_zero, ↓reduceIte]
      change Matrix.SpecialLinearGroup.toGL ((slMap ρ₀).symm (θ₁ b)) = _
      rw [slg_slMap_symm, hd₁, map_mul, map_mul, map_inv, glm_symm_glm]
  · intro k m b hm
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · simp only [↓reduceIte]
      rw [hθ₀ m b hm, MonoidHom.comp_apply, fr₂.twist_ψ_longBlock ρ₀]
      rfl
    · simp only [one_ne_zero, ↓reduceIte]
      rw [hθ₁ m b hm, MonoidHom.comp_apply, fr₂.twist_ψ_longBlock ρ₀]
      rfl
end Setup
end Asc77.C5O.M

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.ClassicalInvolution.Generic

theorem om5ExcClass_proved : Om5ExcClass := by
  intro Y _ _ Φ A A' z' a₀ b₀ hD β₁ β₂ hβ₁2 hβ₂2 hfix₁ hfix₂ hbig₁ hbig₂
  obtain ⟨fr⟩ := M.exists_frame hD
  exact M.Frame.excClass fr (by norm_num : (3 : ℕ) ≠ 2) (M.two_ne_zero_gf 1 (by norm_num : (3 : ℕ)
      ≠ 2)) Q3T7P25.natCard_gf3
    Q3T7P25.odd_natCard_gf3
    β₁ β₂ hβ₁2 hβ₂2 hfix₁ hfix₂ hbig₁ hbig₂

theorem modelFacts_proved : ModelFacts where
  invFixFour := om5InvFixFour_proved
  interchange := om5Interchange_proved
  zSwap := om5ZSwap_proved
  uSwapNotZ := om5USwapNotZ_proved
  excClass := om5ExcClass_proved
  centerless := om5Centerless_proved
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Asc77.C5O.M
open scoped Matrix MatrixGroups
section Main

theorem om5TwinComm_proved : Om5TwinComm := by
  intro Y₁ Y₂ _ _ _ _ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ Mg _ _ π₁ π₂ L L' hT γ₁ δ₁ γ₂ δ₂
    hγ₁A _ hγ₂A _ hδ₁A _ hδ₂A _ hγ hδ
  obtain ⟨fr₁, Φ₂', fr₂, θ, d, -, hθ, hrel⟩ := M.exists_setup hT
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 := M.two_ne_zero_gf 1 hp
  have h4 : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  have hF : ringChar (GaloisField 3 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 1) 3]
    exact hp
  have hsurj : ∀ (k : Fin 2) (b : SL(2, GaloisField 3 1)),
      ∃ m : Mg, π₁ m = fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) := by
    intro k b
    have hb : fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) ∈
        (longRootSp2 (GaloisField 3 1) 2 k).map fr₁.ψ := ⟨_, ⟨b, rfl⟩, rfl⟩
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · have e : (longRootSp2 (GaloisField 3 1) 2 0).map fr₁.ψ = L.map π₁ :=
        fr₁.hA.symm.trans hT.map₁.1.symm
      rw [e] at hb
      obtain ⟨m, -, hm⟩ := hb
      exact ⟨m, hm⟩
    · have e : (longRootSp2 (GaloisField 3 1) 2 1).map fr₁.ψ = L'.map π₁ :=
        fr₁.hA'.symm.trans hT.map₁.2.symm
      rw [e] at hb
      obtain ⟨m, -, hm⟩ := hb
      exact ⟨m, hm⟩
  obtain ⟨G₁, σ₁, hG₁⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₁ γ₁
  obtain ⟨N₁, τ₁, hN₁⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₁ δ₁
  obtain ⟨G₂, σ₂, hG₂⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₂ γ₂
  obtain ⟨N₂, τ₂, hN₂⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₂ δ₂
  obtain ⟨g₁, hg₁, hdg₁⟩ := M.exists_gl_blocks G₁ (M.isBD_gm_of_conjSp_longInv h2 G₁ σ₁
    (M.Frame.lift_longInv h2 h4 fr₁ fr₁ γ₁ G₁ σ₁ hG₁ hγ₁A.le))
  obtain ⟨n₁, hn₁, hdn₁⟩ := M.exists_gl_blocks N₁ (M.isBD_gm_of_conjSp_longInv h2 N₁ τ₁
    (M.Frame.lift_longInv h2 h4 fr₁ fr₁ δ₁ N₁ τ₁ hN₁ hδ₁A.le))
  obtain ⟨g₂, hg₂, hdg₂⟩ := M.exists_gl_blocks G₂ (M.isBD_gm_of_conjSp_longInv h2 G₂ σ₂
    (M.Frame.lift_longInv h2 h4 fr₂ fr₂ γ₂ G₂ σ₂ hG₂ hγ₂A.le))
  obtain ⟨n₂, hn₂, hdn₂⟩ := M.exists_gl_blocks N₂ (M.isBD_gm_of_conjSp_longInv h2 N₂ τ₂
    (M.Frame.lift_longInv h2 h4 fr₂ fr₂ δ₂ N₂ τ₂ hN₂ hδ₂A.le))
  have rγ := fun k => M.fix_block_rel h2 fr₁ fr₂ π₁ π₂ (θ k) (d k) k (hθ k) (hrel k) (hsurj k)
    γ₁ γ₂ G₁ G₂ σ₁ σ₂ hG₁ hG₂ hg₁ hg₂ hγ
  have rδ := fun k => M.fix_block_rel h2 fr₁ fr₂ π₁ π₂ (θ k) (d k) k (hθ k) (hrel k) (hsurj k)
    δ₁ δ₂ N₁ N₂ τ₁ τ₂ hN₁ hN₂ hn₁ hn₂ hδ
  obtain ⟨hσ, -⟩ := rγ 0
  obtain ⟨hτ, -⟩ := rδ 0
  subst hσ hτ
  choose ℓ hℓ using fun k => (rγ k).2
  choose κ hκ using fun k => (rδ k).2
  set C₁ : gsp 2 (GaloisField 3 1) := G₁ * gspFieldMap σ₁ N₁ * gspFieldMap τ₁ G₁⁻¹ * N₁⁻¹
    with hC₁def
  set c₁ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => g₁ k * glm σ₁ (n₁ k) * (glm τ₁ (g₁ k))⁻¹ * (n₁ k)⁻¹ with hc₁def
  have hC₁ : gm C₁ = bd (fun k => (c₁ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₁def, gm_comm_bd G₁ N₁ N₁ σ₁ τ₁ hg₁ hn₁ hn₁]
    simp only [map_inv, hc₁def]
  have hc1 : ∀ x, γ₁ (δ₁ (γ₁.symm (δ₁.symm (fr₁.ψ x)))) = fr₁.ψ (conjSp 2 _ C₁ x) := fun x => by
    rw [comm_apply_of_lift fr₁.ψ γ₁ δ₁ (conjSp 2 _ G₁ * fieldSp 2 _ σ₁)
      (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) hG₁ hN₁ x, comm_conjSp_fieldSp]
  set C₂ : gsp 2 (GaloisField 3 1) := G₂ * gspFieldMap σ₁ N₂ * gspFieldMap τ₁ G₂⁻¹ * N₂⁻¹
    with hC₂def
  set c₂ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => g₂ k * glm σ₁ (n₂ k) * (glm τ₁ (g₂ k))⁻¹ * (n₂ k)⁻¹ with hc₂def
  have hC₂ : gm C₂ = bd (fun k => (c₂ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₂def, gm_comm_bd G₂ N₂ N₂ σ₁ τ₁ hg₂ hn₂ hn₂]
    simp only [map_inv, hc₂def]
  have hc2 : ∀ x, γ₂ (δ₂ (γ₂.symm (δ₂.symm (fr₂.ψ x)))) = fr₂.ψ (conjSp 2 _ C₂ x) := fun x => by
    rw [comm_apply_of_lift fr₂.ψ γ₂ δ₂ (conjSp 2 _ G₂ * fieldSp 2 _ σ₁)
      (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) hG₂ hN₂ x, comm_conjSp_fieldSp]
  have hμG₁ : mu G₁ ≠ 0 := Units.ne_zero _
  have hμN₁ : mu N₁ ≠ 0 := Units.ne_zero _
  obtain ⟨s, hs⟩ := isSquare_comm_det hF σ₁ τ₁ hμG₁ hμN₁
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hs
    have h1 : τ₁ (mu G₁) ≠ 0 := (map_ne_zero τ₁).mpr hμG₁
    have h2 : σ₁ (mu N₁) ≠ 0 := (map_ne_zero σ₁).mpr hμN₁
    simp_all
  have hdc : ∀ k, ((c₁ k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det =
      mu G₁ * σ₁ (mu N₁) * (τ₁ (mu G₁))⁻¹ * (mu N₁)⁻¹ := fun k => by
    simp only [hc₁def, det_gl_mul, det_gl_inv, det_glm, hdg₁, hdn₁]
  obtain ⟨w₀, hw₀⟩ := exists_sl_smul hs0 ((hdc 0).trans hs)
  obtain ⟨w₁, hw₁⟩ := exists_sl_smul hs0 ((hdc 1).trans hs)
  have hg₂' : ∀ k, g₂ k = scl (ℓ k) * (d k * g₁ k * (glm σ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hℓ k)]
    group
  have hn₂' : ∀ k, n₂ k = scl (κ k) * (d k * n₁ k * (glm τ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hκ k)]
    group
  have htr : ∀ k, c₂ k = scl (ℓ k * Units.map (σ₁ : _ →* _) (κ k) *
      (Units.map (τ₁ : _ →* _) (ℓ k))⁻¹ * (κ k)⁻¹) * (d k * c₁ k * (d k)⁻¹) := fun k => by
    simp only [hc₁def, hc₂def]
    rw [hg₂' k, hn₂' k]
    exact fix_transport (d k) (g₁ k) (n₁ k) σ₁ τ₁ (ℓ k) (κ k)
  have hν : ∀ k, ((d k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det ≠ 0 := fun k =>
    (Matrix.isUnits_det_units (d k)).ne_zero
  have hr := fix_ratio hp σ₁ τ₁ (hν 0) (hν 1) hμG₁ hμN₁ (ℓ 0) (ℓ 1) (κ 0) (κ 1)
    (det_rel (hdg₁ 0) (hdg₂ 0) (hℓ 0)) (det_rel (hdg₁ 1) (hdg₂ 1) (hℓ 1))
    (det_rel (hdn₁ 0) (hdn₂ 0) (hκ 0)) (det_rel (hdn₁ 1) (hdn₂ 1) (hκ 1))
  set r := ℓ 0 * Units.map (σ₁ : _ →* _) (κ 0) * (Units.map (τ₁ : _ →* _) (ℓ 0))⁻¹ * (κ 0)⁻¹
    with hrdef
  have hw'₀ : ((c₂ 0 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r : GaloisField 3 1) * s) •
      ((θ 0 w₀ : SL(2, GaloisField 3 1)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 0]
    exact conj_smul_eq (hθ 0) hw₀ _
  have hw'₁ : ((c₂ 1 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r : GaloisField 3 1) * s) •
      ((θ 1 w₁ : SL(2, GaloisField 3 1)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 1, ← hr]
    exact conj_smul_eq (hθ 1) hw₁ _
  obtain ⟨m₀, hm₀⟩ := hsurj 0 w₀
  obtain ⟨m₁, hm₁⟩ := hsurj 1 w₁
  refine ⟨m₀ * m₁, fun y => ?_, fun y => ?_⟩
  · rw [fr₁.inner_of_lift (fun y => γ₁ (δ₁ (γ₁.symm (δ₁.symm y)))) C₁ hc1 hC₁ hs0 w₀ w₁ hw₀ hw₁
      y, map_mul π₁, hm₀, hm₁, ← map_mul]
  · rw [fr₂.inner_of_lift (fun y => γ₂ (δ₂ (γ₂.symm (δ₂.symm y)))) C₂ hc2 hC₂
      (mul_ne_zero r.ne_zero hs0) (θ 0 w₀) (θ 1 w₁) hw'₀ hw'₁ y, map_mul π₂, hrel 0 m₀ w₀ hm₀,
      hrel 1 m₁ w₁ hm₁, ← map_mul]
end Main
end Asc77.C5O

end

section

namespace Asc77.C5O
open CFSG.ClassicalInvolution.Asc77
open CFSG.ClassicalInvolution.Asc77.C5O
open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open CFSG.ClassicalInvolution.Asc77.C5O.M
open scoped Matrix MatrixGroups
section Main

theorem om5TwinCommSwap_proved : Om5TwinCommSwap := by
  intro Y₁ Y₂ _ _ _ _ Φ₁ A₁ A₁' z₁ a₁ b₁ Φ₂ A₂ A₂' z₂ a₂ b₂ Mg _ _ π₁ π₂ L L' hT ψ ψ' δ₁ δ₂
    hψA _ hψ'A _ hδ₁A _ hδ₂A _ hψ hδ
  obtain ⟨fr₁, Φ₂', fr₂, θ, d, hker, hθ, hrel⟩ := M.exists_setup hT
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h2 := M.two_ne_zero_gf 1 hp
  have h4 : Nat.card (GaloisField 3 1) = 3 := Q3T7P25.natCard_gf3
  have hF : ringChar (GaloisField 3 1) ≠ 2 := by
    rw [ringChar.eq (GaloisField 3 1) 3]
    exact hp
  have hsurj : ∀ (k : Fin 2) (b : SL(2, GaloisField 3 1)),
      ∃ m : Mg, π₁ m = fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) := by
    intro k b
    have hb : fr₁.ψ (longBlock (GaloisField 3 1) 2 k b) ∈
        (longRootSp2 (GaloisField 3 1) 2 k).map fr₁.ψ := ⟨_, ⟨b, rfl⟩, rfl⟩
    rcases (by decide : ∀ k : Fin 2, k = 0 ∨ k = 1) k with rfl | rfl
    · have e : (longRootSp2 (GaloisField 3 1) 2 0).map fr₁.ψ = L.map π₁ :=
        fr₁.hA.symm.trans hT.map₁.1.symm
      rw [e] at hb
      obtain ⟨m, -, hm⟩ := hb
      exact ⟨m, hm⟩
    · have e : (longRootSp2 (GaloisField 3 1) 2 1).map fr₁.ψ = L'.map π₁ :=
        fr₁.hA'.symm.trans hT.map₁.2.symm
      rw [e] at hb
      obtain ⟨m, -, hm⟩ := hb
      exact ⟨m, hm⟩
  obtain ⟨P, π, hP⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₂ ψ
  obtain ⟨P', π', hP'⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₁ ψ'
  obtain ⟨N₁, τ₁, hN₁⟩ := M.Frame.exists_lift_iso h2 fr₁ fr₁ δ₁
  obtain ⟨N₂, τ₂, hN₂⟩ := M.Frame.exists_lift_iso h2 fr₂ fr₂ δ₂
  obtain ⟨pb, hpb, hdpb⟩ := M.exists_gl_blocks P (M.isBD_gm_of_conjSp_longInv h2 P π
    (M.Frame.lift_longInv h2 h4 fr₁ fr₂ ψ P π hP hψA.le))
  obtain ⟨pb', hpb', hdpb'⟩ := M.exists_gl_blocks P' (M.isBD_gm_of_conjSp_longInv h2 P' π'
    (M.Frame.lift_longInv h2 h4 fr₂ fr₁ ψ' P' π' hP' hψ'A.le))
  obtain ⟨n₁, hn₁, hdn₁⟩ := M.exists_gl_blocks N₁ (M.isBD_gm_of_conjSp_longInv h2 N₁ τ₁
    (M.Frame.lift_longInv h2 h4 fr₁ fr₁ δ₁ N₁ τ₁ hN₁ hδ₁A.le))
  obtain ⟨n₂, hn₂, hdn₂⟩ := M.exists_gl_blocks N₂ (M.isBD_gm_of_conjSp_longInv h2 N₂ τ₂
    (M.Frame.lift_longInv h2 h4 fr₂ fr₂ δ₂ N₂ τ₂ hN₂ hδ₂A.le))
  have rψ := fun k => M.swap_block_rel h2 fr₁ fr₂ π₁ π₂ hker (θ k) (d k) k (hθ k) (hrel k)
    (hsurj k) ψ ψ' P P' π π' hP hP' hpb hpb' hψ
  have rδ := fun k => M.fix_block_rel h2 fr₁ fr₂ π₁ π₂ (θ k) (d k) k (hθ k) (hrel k) (hsurj k)
    δ₁ δ₂ N₁ N₂ τ₁ τ₂ hN₁ hN₂ hn₁ hn₂ hδ
  obtain ⟨hπ, -⟩ := rψ 0
  obtain ⟨hτ, -⟩ := rδ 0
  have hπ' := hπ.symm
  subst hπ' hτ
  choose lam hlam using fun k => (rψ k).2
  choose κ hκ using fun k => (rδ k).2
  set C₁ : gsp 2 (GaloisField 3 1) := P' * gspFieldMap π N₂ * gspFieldMap τ₁ P'⁻¹ * N₁⁻¹
    with hC₁def
  set c₁ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => pb' k * glm π (n₂ k) * (glm τ₁ (pb' k))⁻¹ * (n₁ k)⁻¹ with hc₁def
  have hC₁ : gm C₁ = bd (fun k => (c₁ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₁def, gm_comm_bd P' N₂ N₁ π τ₁ hpb' hn₂ hn₁]
    simp only [map_inv, hc₁def]
  have hc1 : ∀ x, ψ' (δ₂ (ψ'.symm (δ₁.symm (fr₁.ψ x)))) = fr₁.ψ (conjSp 2 _ C₁ x) := fun x => by
    rw [comm_apply_of_lift_swap fr₁.ψ fr₂.ψ ψ' δ₁ δ₂ (conjSp 2 _ P' * fieldSp 2 _ π)
      (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) hP' hN₁ hN₂ x,
      comm_conjSp_fieldSp_gen]
  set C₂ : gsp 2 (GaloisField 3 1) := P * gspFieldMap π N₁ * gspFieldMap τ₁ P⁻¹ * N₂⁻¹
    with hC₂def
  set c₂ : Fin 2 → GL (Fin 2) (GaloisField 3 1) :=
    fun k => pb k * glm π (n₁ k) * (glm τ₁ (pb k))⁻¹ * (n₂ k)⁻¹ with hc₂def
  have hC₂ : gm C₂ = bd (fun k => (c₂ k : Matrix (Fin 2) (Fin 2) (GaloisField 3 1))) := by
    rw [hC₂def, gm_comm_bd P N₁ N₂ π τ₁ hpb hn₁ hn₂]
    simp only [map_inv, hc₂def]
  have hc2 : ∀ x, ψ (δ₁ (ψ.symm (δ₂.symm (fr₂.ψ x)))) = fr₂.ψ (conjSp 2 _ C₂ x) := fun x => by
    rw [comm_apply_of_lift_swap fr₂.ψ fr₁.ψ ψ δ₂ δ₁ (conjSp 2 _ P * fieldSp 2 _ π)
      (conjSp 2 _ N₂ * fieldSp 2 _ τ₁) (conjSp 2 _ N₁ * fieldSp 2 _ τ₁) hP hN₂ hN₁ x,
      comm_conjSp_fieldSp_gen]
  have hμP : mu P ≠ 0 := Units.ne_zero _
  have hμN₁ : mu N₁ ≠ 0 := Units.ne_zero _
  have hμN₂ : mu N₂ ≠ 0 := Units.ne_zero _
  have hν : ∀ k, ((d k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det ≠ 0 := fun k =>
    (Matrix.isUnits_det_units (d k)).ne_zero
  have hκrel := fun k => det_rel (hdn₁ k) (hdn₂ k) (hκ k)
  obtain ⟨s, hs⟩ := isSquare_swap_det hF π τ₁ hμP hμN₁ (hν 0) (κ 0) (hκrel 0)
  have hne : mu P * π (mu N₁) * (τ₁ (mu P))⁻¹ * (mu N₂)⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hμP ((map_ne_zero π).mpr hμN₁))
      (inv_ne_zero ((map_ne_zero τ₁).mpr hμP))) (inv_ne_zero hμN₂)
  have hs0 : s ≠ 0 := fun h => hne (by rw [hs, h, mul_zero])
  have hdc : ∀ k, ((c₂ k : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)).det =
      mu P * π (mu N₁) * (τ₁ (mu P))⁻¹ * (mu N₂)⁻¹ := fun k => by
    simp only [hc₂def, det_gl_mul, det_gl_inv, det_glm, hdpb, hdn₁, hdn₂]
  obtain ⟨w₀, hw₀⟩ := exists_sl_smul hs0 ((hdc 0).trans hs)
  obtain ⟨w₁, hw₁⟩ := exists_sl_smul hs0 ((hdc 1).trans hs)
  have hp' : ∀ k, pb' k = scl (lam k) * ((d k)⁻¹ * pb k * (glm π (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hlam k)]
    group
  have hn₂' : ∀ k, n₂ k = scl (κ k) * (d k * n₁ k * (glm τ₁ (d k))⁻¹) := fun k => by
    rw [eq_mul_inv_of_mul_eq (hκ k)]
    group
  have htr : ∀ k, c₁ k = scl (lam k * Units.map (π : _ →* _) (κ k) *
      (Units.map (τ₁ : _ →* _) (lam k))⁻¹ * κ k) * ((d k)⁻¹ * c₂ k * d k) := fun k => by
    simp only [hc₁def, hc₂def]
    rw [hp' k, hn₂' k]
    exact swap_transport (d k) (pb k) (n₁ k) π τ₁ (lam k) (κ k)
  have hr := swap_ratio hp π τ₁ (hν 0) (hν 1) hμP hμN₁ (lam 0) (lam 1) (κ 0) (κ 1)
    (det_rel_swap (hdpb 0) (hdpb' 0) (hlam 0)) (det_rel_swap (hdpb 1) (hdpb' 1) (hlam 1))
    (hκrel 0) (hκrel 1)
  set r := lam 0 * Units.map (π : _ →* _) (κ 0) * (Units.map (τ₁ : _ →* _) (lam 0))⁻¹ * κ 0
    with hrdef
  have hw'₀ : ((c₁ 0 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r : GaloisField 3 1) * s) •
      (((θ 0)⁻¹ w₀ : SL(2, GaloisField 3 1)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 0]
    exact conj_smul_eq_inv (hθ 0) hw₀ _
  have hw'₁ : ((c₁ 1 : GL (Fin 2) (GaloisField 3 1)) :
      Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) = ((r : GaloisField 3 1) * s) •
      (((θ 1)⁻¹ w₁ : SL(2, GaloisField 3 1)) : Matrix (Fin 2) (Fin 2) (GaloisField 3 1)) := by
    rw [htr 1, ← hr]
    exact conj_smul_eq_inv (hθ 1) hw₁ _
  obtain ⟨m₀, hm₀⟩ := hsurj 0 ((θ 0)⁻¹ w₀)
  obtain ⟨m₁, hm₁⟩ := hsurj 1 ((θ 1)⁻¹ w₁)
  have e₀ : π₂ m₀ = fr₂.ψ (longBlock (GaloisField 3 1) 2 0 w₀) := by
    rw [hrel 0 m₀ _ hm₀, show (θ 0) ((θ 0)⁻¹ w₀) = w₀ from by simp]
  have e₁ : π₂ m₁ = fr₂.ψ (longBlock (GaloisField 3 1) 2 1 w₁) := by
    rw [hrel 1 m₁ _ hm₁, show (θ 1) ((θ 1)⁻¹ w₁) = w₁ from by simp]
  refine ⟨m₀ * m₁, fun y => ?_, fun y => ?_⟩
  · rw [fr₁.inner_of_lift (fun y => ψ' (δ₂ (ψ'.symm (δ₁.symm y)))) C₁ hc1 hC₁
      (mul_ne_zero r.ne_zero hs0) ((θ 0)⁻¹ w₀) ((θ 1)⁻¹ w₁) hw'₀ hw'₁ y, map_mul π₁, hm₀, hm₁,
      ← map_mul]
  · rw [fr₂.inner_of_lift (fun y => ψ (δ₁ (ψ.symm (δ₂.symm y)))) C₂ hc2 hC₂ hs0 w₀ w₁ hw₀ hw₁ y,
      map_mul π₂, e₀, e₁, ← map_mul]

theorem m8gFacts_proved : M8GFacts where
  comm := om5TwinComm_proved
  commSwap := om5TwinCommSwap_proved
end Main
end Asc77.C5O

end

end CFSG.ClassicalInvolution.Q3.Q3T8
