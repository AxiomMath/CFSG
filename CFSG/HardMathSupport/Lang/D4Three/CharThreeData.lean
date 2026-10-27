module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Lang.E27Lie.CocycleCount
public import CFSG.HardMathSupport.Lang.Triality.HeightCoord

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem permLattice_mul' {τ : Tag} (π₁ π₂ : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice (π₁ * π₂) v = permLattice π₁ (permLattice π₂ v) := by
  funext i
  simp [permLattice, Equiv.Perm.mul_def]

theorem permLattice_one' {τ : Tag} (v : Fin τ.rank → ℤ) :
    permLattice (1 : Equiv.Perm (Fin τ.rank)) v = v := by
  funext i
  rfl

theorem d4Rho_pow_three : d4Rho ^ 3 = 1 := by decide

theorem d4Rho_cartan (n : ℕ) (i j : Fin Tag.D4.rank) :
    Tag.D4.cartan ((d4Rho ^ n) i) ((d4Rho ^ n) j) = Tag.D4.cartan i j :=
  TwistTag.D4.cartan_perm_pow n i j


variable {K : Type} [Field K]

theorem isRoot_permLattice_d4Rho_pow {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) (n : ℕ) :
    IsRoot Tag.D4 (permLattice (d4Rho ^ n) γ) :=
  hγ.permLattice (d4Rho_cartan n)

theorem exists_d4P_pow_conj_pinnedX (n : ℕ) {γ : Fin Tag.D4.rank → ℤ} (hγ : IsRoot Tag.D4 γ) :
    ∃ μ : K, ∀ c : K, d4P K ^ n * pinnedX Tag.D4 K γ c * (d4P K ^ n)⁻¹ =
      pinnedX Tag.D4 K (permLattice (d4Rho ^ n) γ) (μ * c) := by
  induction n with
  | zero =>
    refine ⟨1, fun c => ?_⟩
    simp [permLattice_one']
  | succ n ih =>
    obtain ⟨μ, hμ⟩ := ih
    have hroot := isRoot_permLattice_d4Rho_pow hγ n
    obtain ⟨ε, -, hε⟩ := diagramMap_conj_pinnedX (K := K) TwistTag.D4 hroot
    refine ⟨ε * μ, fun c => ?_⟩
    have e1 : d4P K ^ (n + 1) = d4P K * d4P K ^ n := pow_succ' _ _
    have e2 : d4Rho ^ (n + 1) = d4Rho * d4Rho ^ n := pow_succ' _ _
    have e3 : (d4P K ^ (n + 1)) = d4P K * d4P K ^ n := e1
    calc d4P K ^ (n + 1) * pinnedX Tag.D4 K γ c * (d4P K ^ (n + 1))⁻¹
        = d4P K * (d4P K ^ n * pinnedX Tag.D4 K γ c * (d4P K ^ n)⁻¹) * (d4P K)⁻¹ := by
          rw [e1]; group
      _ = d4P K * pinnedX Tag.D4 K (permLattice (d4Rho ^ n) γ) (μ * c) * (d4P K)⁻¹ := by
          rw [hμ]
      _ = pinnedX Tag.D4 K (permLattice d4Rho (permLattice (d4Rho ^ n) γ)) (ε * (μ * c)) := hε _
      _ = pinnedX Tag.D4 K (permLattice (d4Rho ^ (n + 1)) γ) (ε * μ * c) := by
          rw [e2, permLattice_mul', mul_assoc]

variable (K) in
@[expose] def d4F (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    ModGL Tag.D4 K →* ModGL Tag.D4 K :=
  (exactNormalAutGL Tag.D4 K a σ 0).toMonoidHom.comp (MulAut.conj (d4P K ^ ε)).toMonoidHom

theorem coe_normal_mul_graph [Finite K] (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (x : ↥(adjointGroup Tag.D4 K)) :
    (((exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K)
      = d4F K a σ ε (x : ModGL Tag.D4 K) := rfl

theorem exists_d4F_pinnedX (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ) :
    ∃ e : (Fin Tag.D4.rank → ℤ) → K, ∀ γ, IsRoot Tag.D4 γ → ∀ c : K,
      d4F K a σ ε (pinnedX Tag.D4 K γ c) =
        pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) γ) (e γ * σ c) := by
  have h : ∀ γ : Fin Tag.D4.rank → ℤ, ∃ e : K, IsRoot Tag.D4 γ → ∀ c : K,
      d4F K a σ ε (pinnedX Tag.D4 K γ c) =
        pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) γ) (e * σ c) := by
    intro γ
    by_cases hγ : IsRoot Tag.D4 γ
    · obtain ⟨μ, hμ⟩ := exists_d4P_pow_conj_pinnedX (K := K) ε hγ
      have hroot := isRoot_permLattice_d4Rho_pow hγ ε
      refine ⟨((rootChar a (permLattice (d4Rho ^ ε) γ) : Kˣ) : K) * σ μ, fun _ c => ?_⟩
      change exactNormalAutGL Tag.D4 K a σ 0 (d4P K ^ ε * pinnedX Tag.D4 K γ c * (d4P K ^ ε)⁻¹) = _
      rw [hμ, exactNormalAutGL_apply]
      have hQ : exactQ Tag.D4 K 0 = 1 := rfl
      rw [hQ]
      simp only [mul_one, inv_one]
      rw [show Units.map (entrywiseHom σ.toRingHom)
          (pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) γ) (μ * c)) =
          pinnedX Tag.D4 K (permLattice (d4Rho ^ ε) γ) (σ (μ * c)) from
        Units.ext (entrywise_pinnedX σ.toRingHom _ _)]
      rw [rootDiagUnit_conj_pinnedX a hroot, map_mul, mul_assoc]
    · exact ⟨0, fun h' => absurd h' hγ⟩
  choose e he using h
  exact ⟨e, he⟩

end CFSG.HardMathSupport.Lang.D4Three
