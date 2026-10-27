module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismUnitaryDecomp
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineCentralizer

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.RootCenter

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism CFSG.ShultStronglyClosedTI.UnitaryModel

variable {K : Type} [Field K] (J : HermitianForm 3 K)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

abbrev diagBar : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  (diagHom J hJ).range ⊔ Subgroup.zpowers (barAut J hJ)

theorem mul_conj_mul_inv {G : Type*} [Group G] (γ : MulAut G) (r : G) :
    γ * MulAut.conj r * γ⁻¹ = MulAut.conj (γ r) := by
  ext x
  simp [MulAut.mul_apply, map_mul, map_inv]

theorem barAut_mul_diagAut (c : normOne J) :
    barAut J hJ * diagAut J hJ c = diagAut J hJ c⁻¹ * barAut J hJ := by
  rw [← barAut_conj_diagAut J hJ c, inv_mul_cancel_right]

theorem diagAut_mul (c d : normOne J) :
    diagAut J hJ (c * d) = diagAut J hJ c * diagAut J hJ d :=
  (diagHom J hJ).map_mul c d

theorem diagAut_one : diagAut J hJ 1 = 1 :=
  (diagHom J hJ).map_one

theorem diagAut_inv (c : normOne J) : diagAut J hJ c⁻¹ = (diagAut J hJ c)⁻¹ :=
  (diagHom J hJ).map_inv c

theorem mem_diagBar_iff {g : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)} :
    g ∈ diagBar J hJ ↔
      ∃ c : normOne J, ∃ ε : Fin 2, g = diagAut J hJ c * barAut J hJ ^ (ε : ℕ) := by
  have hτ2 := barAut_mul_self J hJ
  have hτinv : (barAut J hJ)⁻¹ = barAut J hJ := inv_eq_of_mul_eq_one_right hτ2
  have hswap := barAut_mul_diagAut J hJ
  let D' : Subgroup (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    { carrier := {g | ∃ c : normOne J, ∃ ε : Fin 2, g = diagAut J hJ c * barAut J hJ ^ (ε : ℕ)}
      mul_mem' := by
        rintro _ _ ⟨c, ε, rfl⟩ ⟨c', ε', rfl⟩
        fin_cases ε <;> fin_cases ε'
        · exact ⟨c * c', 0, by simp [diagAut_mul]⟩
        · exact ⟨c * c', 1, by simp [diagAut_mul, mul_assoc]⟩
        · refine ⟨c * c'⁻¹, 1, ?_⟩
          simp only [Fin.isValue, Fin.val_one, pow_zero, pow_one, mul_one]
          rw [mul_assoc, hswap, ← mul_assoc, diagAut_mul]
        · refine ⟨c * c'⁻¹, 0, ?_⟩
          simp only [Fin.isValue, Fin.val_zero, pow_zero, pow_one, mul_one]
          rw [mul_assoc, ← mul_assoc (barAut J hJ), hswap, mul_assoc, hτ2, mul_one, diagAut_mul]
      one_mem' := ⟨1, 0, by simp [diagAut_one]⟩
      inv_mem' := by
        rintro _ ⟨c, ε, rfl⟩
        fin_cases ε
        · exact ⟨c⁻¹, 0, by simp [diagAut_inv]⟩
        · refine ⟨c, 1, ?_⟩
          simp only [Fin.isValue, Fin.val_one, pow_one]
          rw [_root_.mul_inv_rev, hτinv, ← diagAut_inv, hswap, inv_inv] }
  have hD : diagBar J hJ = D' := by
    refine le_antisymm (sup_le ?_ (Subgroup.zpowers_le.2
      (show ∃ c : normOne J, ∃ ε : Fin 2, barAut J hJ = diagAut J hJ c * barAut J hJ ^ (ε : ℕ)
        from ⟨1, 1, by rw [diagAut_one, one_mul, Fin.val_one, pow_one]⟩))) ?_
    · rintro _ ⟨c, rfl⟩
      exact show ∃ c' : normOne J, ∃ ε : Fin 2,
          diagHom J hJ c = diagAut J hJ c' * barAut J hJ ^ (ε : ℕ)
        from ⟨c, 0, by rw [Fin.val_zero, pow_zero, mul_one]; rfl⟩
    · rintro _ ⟨c, ε, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨c, rfl⟩)
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _))
  rw [hD]
  rfl

variable [Finite K] (f : ℕ) (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
  (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
include hf hcard hfixed

theorem conj_root_inf_diagBar :
    (unitaryCoverRoot J hJ).map MulAut.conj ⊓ diagBar J hJ = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨r, hr, rfl⟩, hD⟩
  obtain ⟨c, ε, hcε⟩ := (mem_diagBar_iff J hJ).1 hD
  have h : MulAut.conj r * diagAut J hJ 1 * barAut J hJ ^ ((0 : Fin 2) : ℕ) =
      MulAut.conj 1 * diagAut J hJ c * barAut J hJ ^ (ε : ℕ) := by
    simp only [diagAut_one, Fin.isValue, Fin.val_zero, pow_zero, mul_one, map_one, one_mul]
    exact hcε
  obtain ⟨rfl, -, -⟩ := eq_of_conj_diag_bar_eq J hJ f hf hcard hfixed hr (one_mem _) h
  rw [map_one]
  exact Subgroup.one_mem _

theorem conj_root_sup_diagBar :
    (unitaryCoverRoot J hJ).map MulAut.conj ⊔ diagBar J hJ =
      rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
  have : CharP K 2 := charP_two_of_card f hcard
  refine le_antisymm (sup_le ?_ (sup_le ?_ ?_)) fun γ hγ => ?_
  · rintro _ ⟨r, hr, rfl⟩
    exact conj_mem_rootCenterAut J hJ hr
  · rintro _ ⟨c, rfl⟩
    exact diagAut_mem_rootCenterAut J hJ c
  · exact Subgroup.zpowers_le.2 (barAut_mem_rootCenterAut J hJ)
  · obtain ⟨r, hr, c, ε, rfl⟩ := exists_eq_conj_diag_bar J hJ f hf hcard hfixed hγ
    rw [mul_assoc]
    exact Subgroup.mul_mem_sup ⟨r, hr, rfl⟩ ((mem_diagBar_iff J hJ).2 ⟨c, ε, rfl⟩)

omit hf hcard hfixed [Finite K] in
theorem conj_root_normal :
    (((unitaryCoverRoot J hJ).map MulAut.conj).subgroupOf
      (rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ))).Normal := by
  have hle : (unitaryCoverRoot J hJ).map MulAut.conj ≤
      rootCenterAut (unitaryCoverRoot J hJ) (unitaryRootCenter J hJ) := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨map_conj_of_mem hr, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, rfl⟩ := hr
    rw [conj_hermitianUnipotentPSU, ← mul_comm_of_fst_eq_zero J hz y, mul_inv_cancel_right]
  rw [Subgroup.normal_subgroupOf_iff hle]
  rintro _ γ ⟨r, hr, rfl⟩ hγ
  rw [mul_conj_mul_inv]
  refine ⟨γ r, ?_, rfl⟩
  rw [← hγ.1]
  exact Subgroup.mem_map_of_mem _ hr

theorem diagHom_injective : Function.Injective (diagHom J hJ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro c hc
  have h : MulAut.conj 1 * diagAut J hJ c * barAut J hJ ^ ((0 : Fin 2) : ℕ) =
      MulAut.conj 1 * diagAut J hJ 1 * barAut J hJ ^ ((0 : Fin 2) : ℕ) := by
    rw [diagAut_one, ← diagHom_apply, hc]
  exact (eq_of_conj_diag_bar_eq J hJ f hf hcard hfixed (one_mem _) (one_mem _) h).2.1

theorem diagBar_dihedral :
    Nat.card (diagBar J hJ) = 2 * (2 ^ f + 1) ∧
      Nonempty (diagBar J hJ ≃* DihedralGroup (2 ^ f + 1)) := by
  have : CharP K 2 := charP_two_of_card f hcard
  have hq : 2 < 2 ^ f := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_injective _ Subtype.coe_injective
  have : Finite (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    Finite.of_injective _ DFunLike.coe_injective
  have hM : Nat.card (normOne J) = 2 ^ f + 1 := card_normOne Nat.prime_two hq hcard hfixed
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := normOne J)
  let ρ : diagBar J hJ := ⟨diagAut J hJ g, Subgroup.mem_sup_left ⟨g, rfl⟩⟩
  let σ : diagBar J hJ := ⟨barAut J hJ, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
  have hgen : (⊤ : Subgroup (diagBar J hJ)) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective (diagBar J hJ).subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    show (diagHom J hJ).range ⊔ Subgroup.zpowers (barAut J hJ) =
      Subgroup.zpowers (diagAut J hJ g) ⊔ Subgroup.zpowers (barAut J hJ)
    have htop : Subgroup.zpowers g = ⊤ := eq_top_iff.2 fun x _ => hg x
    rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_zpowers, diagHom_apply]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, pow_two]
    exact barAut_mul_self J hJ)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv]
    exact (barAut_conj_diagAut J hJ g).trans (diagAut_inv J hJ g))
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    rintro ⟨k, hk⟩
    have hk' : diagAut J hJ (g ^ k) = barAut J hJ := by
      rw [← diagHom_apply, map_zpow]
      exact congrArg Subtype.val hk
    have h : MulAut.conj 1 * diagAut J hJ (g ^ k) * barAut J hJ ^ ((0 : Fin 2) : ℕ) =
        MulAut.conj 1 * diagAut J hJ 1 * barAut J hJ ^ ((1 : Fin 2) : ℕ) := by
      simp [hk', diagAut_one]
    exact absurd (eq_of_conj_diag_bar_eq J hJ f hf hcard hfixed (one_mem _) (one_mem _) h).2.2
      (by decide)
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = 2 ^ f + 1 := by
    rw [← orderOf_injective (diagBar J hJ).subtype (diagBar J hJ).subtype_injective ρ]
    show orderOf (diagAut J hJ g) = _
    rw [← diagHom_apply, orderOf_injective _ (diagHom_injective J hJ f hf hcard hfixed) g,
      orderOf_eq_card_of_forall_mem_zpowers hg, hM]
  rw [hord] at e
  exact ⟨(Nat.card_congr e.toEquiv).trans DihedralGroup.nat_card, ⟨e⟩⟩

end CFSG.ProperTwoGeneratedCore.RootCenter
