module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Lang.D4Three.DiagSquare
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityArith
public import CFSG.HardMathSupport.Lang.Triality.G2ClassOrder

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E6Descent

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Order

theorem twentySeven_dvd_card_adjointGroup_D4 (F : Type) [Field F] [Finite F] :
    27 ∣ Nat.card (adjointGroup Tag.D4 F) := by
  have hle : graphFixedRootGroup TwistTag.D4 F (RingHom.id F) ≤ adjointGroup Tag.D4 F :=
    (graphFixedRootGroup_le TwistTag.D4 F (RingHom.id F)).trans inf_le_left
  have h := CFSG.HardMathSupport.Lang.Triality.card_graphFixedRootGroup_D4_id (K := F)
  have h27 := CFSG.HardMathSupport.Lang.E27Lie.twentySeven_dvd_ordG2 (Nat.card F)
  rw [← h] at h27
  exact h27.trans (Subgroup.card_dvd_of_le hle)

end Order

section Cube

variable {K : Type} [Field K]

theorem d4Graph_zero : d4Graph K 0 = 1 :=
  MulEquiv.ext fun h => Subtype.ext (by
    rw [coe_d4Graph, pow_zero, one_mul, inv_one, mul_one]; rfl)

theorem d4Rho_pow_three : d4Rho ^ 3 = 1 := by
  unfold d4Rho TwistTag.perm
  decide +kernel

theorem exactPerm_D4 (ε : ℕ) : exactPerm Tag.D4 ε = 1 := rfl

theorem exactQ_D4 (ε : ℕ) : exactQ Tag.D4 K ε = 1 := rfl

theorem exists_pow_adjX [Finite K] (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) (n : ℕ) :
    ∃ u : Fin Tag.D4.rank → K, ∀ (j : Fin Tag.D4.rank) (c : K),
      ((exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ^ n) (adjX Tag.D4 K j c) =
        adjX Tag.D4 K (((d4Rho ^ ε) ^ n) j) (u j * (σ ^ n) c) := by
  induction n with
  | zero => exact ⟨fun _ => 1, fun j c => by simp⟩
  | succ n ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨fun j => u ((d4Rho ^ ε) j) * (σ ^ n) (a ((d4Rho ^ ε) j)), fun j c => ?_⟩
    rw [pow_succ, MulAut.mul_apply, MulAut.mul_apply, d4Graph_adjX, exactNormalAut_adjX,
      exactPerm_D4, Equiv.Perm.one_apply, hu, pow_succ, Equiv.Perm.mul_apply, pow_succ,
      RingAut.mul_apply]
    congr 1
    simp only [map_mul]
    ring

theorem pow_three_eq_conj_of_conj_mul_pow_three {G : Type*} [Group G] {β : MulAut G} {g : G}
    (hα : (MulAut.conj g * β) ^ 3 = 1) : β ^ 3 = MulAut.conj (g * β g * β (β g))⁻¹ := by
  refine MulEquiv.ext fun x => ?_
  have h1 : ((MulAut.conj g * β) ^ 3) x =
      (g * β g * β (β g)) * (β ^ 3) x * (g * β g * β (β g))⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul,
      map_inv]
    group
  rw [hα, MulAut.one_apply] at h1
  rw [MulAut.conj_apply, inv_inv]
  calc (β ^ 3) x = (g * β g * β (β g))⁻¹ * ((g * β g * β (β g)) * (β ^ 3) x *
        (g * β g * β (β g))⁻¹) * (g * β g * β (β g)) := by group
    _ = (g * β g * β (β g))⁻¹ * x * (g * β g * β (β g)) := by rw [← h1]

theorem cube_normal_form_sigma_cube [Finite K] {g : adjointGroup Tag.D4 K}
    {a : Fin Tag.D4.rank → Kˣ} {σ : K ≃+* K} {ε : ℕ}
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) ^ 3 = 1) :
    σ ^ 3 = 1 := by
  have hA : exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε ∈ unipotentPairAut Tag.D4 K :=
    mul_mem (exactNormalAut_mem _ _ _) (d4Graph_mem _)
  have hβ3 := pow_three_eq_conj_of_conj_mul_pow_three hα
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag (hβ3 ▸ pow_mem hA 3)
  obtain ⟨u, hu⟩ := exists_pow_adjX a σ ε 3
  have hπ : (d4Rho ^ ε) ^ 3 = 1 := by rw [pow_right_comm, d4Rho_pow_three, one_pow]
  have hc : ∀ (j : Fin Tag.D4.rank) (c : K), u j * (σ ^ 3) c = (b j : K) * c := by
    intro j c
    have h1 := hu j c
    rw [hβ3, hb, exactNormalAut_adjX, hπ, exactPerm_D4] at h1
    simp only [Equiv.Perm.one_apply, RingAut.one_apply] at h1
    exact (adjX_injective j h1).symm
  refine RingEquiv.ext fun c => ?_
  have j0 : Fin Tag.D4.rank := ⟨0, by decide⟩
  have h1 := hc j0 1
  rw [map_one, mul_one, mul_one] at h1
  have h2 := hc j0 c
  rw [h1] at h2
  rw [RingAut.one_apply]
  exact mul_left_cancel₀ (b j0).ne_zero h2

theorem coe_conj_normal_form_one (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (h : adjointGroup Tag.D4 K) :
    ((MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 0)) h : ModGL Tag.D4 K) =
      ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a) * (h : ModGL Tag.D4 K) *
        ((g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a)⁻¹ := by
  have h1 : Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) (h : ModGL Tag.D4 K) = h := by
    have e1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    rw [e1]
    exact Units.ext (entrywise_id (R := K) _)
  rw [d4Graph_zero, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply,
    Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, coe_exactNormalAut, exactQ_D4, h1]
  group

theorem mem_inner_of_normal_form_one (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ)
    (hα : (MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 0)) ^ 3 = 1) :
    MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 0) ∈ inner (adjointGroup Tag.D4 K) := by
  set α := MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K 0) with hαdef
  have hγ : (g : ModGL Tag.D4 K) * rootDiagUnit Tag.D4 a ∈ inndiagGroup Tag.D4 K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  have hsq := sq_mem_adjointGroup_of_mem_inndiagGroup hγ
  have hα2 : α ^ 2 = MulAut.conj ⟨_, hsq⟩ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [pow_two, MulAut.mul_apply, hαdef, coe_conj_normal_form_one, coe_conj_normal_form_one,
      MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, pow_two]
    group
  have hinv : α = (α ^ 2)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ' α 2]
    exact hα
  rw [hinv, hα2, ← map_inv]
  exact ⟨_, rfl⟩

theorem outer_cube_normal_form_cases [Finite K] (α : MulAut (adjointGroup Tag.D4 K))
    (hα3 : α ^ 3 = 1) (hα : α ∉ inner (adjointGroup Tag.D4 K)) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ),
      ε < 3 ∧ α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ∧ σ ^ 3 = 1 ∧
      ((ε = 0 ∧ σ ≠ 1) ∨ (ε ≠ 0 ∧ σ ≠ 1) ∨ (ε ≠ 0 ∧ σ = 1)) := by
  obtain ⟨g, a, σ, ε, hε, hαeq⟩ := exists_cube_normal_form α hα3
  refine ⟨g, a, σ, ε, hε, hαeq, cube_normal_form_sigma_cube (hαeq ▸ hα3), ?_⟩
  by_cases hε0 : ε = 0
  · by_cases hσ1 : σ = 1
    · subst hε0 hσ1
      exact absurd (hαeq ▸ mem_inner_of_normal_form_one g a (hαeq ▸ hα3)) hα
    · exact Or.inl ⟨hε0, hσ1⟩
  · by_cases hσ1 : σ = 1
    · exact Or.inr (Or.inr ⟨hε0, hσ1⟩)
    · exact Or.inr (Or.inl ⟨hε0, hσ1⟩)

end Cube

end CFSG.HardMathSupport.Lang.E6Descent
