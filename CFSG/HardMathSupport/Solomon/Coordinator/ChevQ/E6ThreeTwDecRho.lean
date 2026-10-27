module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwFrames
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwUnitary

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.RankThree.PartOne.KE (diagGL3 conjDiag3)

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)

open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

theorem exists_hom_comp_eq {G H P : Type*} [Group G] [Group H] [Group P] (ψ : G →* H)
    (hψ : Function.Injective ψ) (f : P →* H) (hf : ∀ p, f p ∈ ψ.range) :
    ∃ g : P →* G, ∀ p, ψ (g p) = f p := by
  refine ⟨(MonoidHom.ofInjective hψ).symm.toMonoidHom.comp (f.codRestrict ψ.range hf),
    fun p => ?_⟩
  have h := (MonoidHom.ofInjective hψ).apply_symm_apply ⟨f p, hf p⟩
  have h' := congrArg Subtype.val h
  simpa using h'

section Frame


variable {Ω : Type} [Field Ω] {Fr : Ω →+* Ω} {ℓ f : ℕ}

structure TwFrameFacts (ℓ f : ℕ) (Fr : Ω →+* Ω) (Φ : Fin 3 → SL(3, Ω) ≃* SL(3, Ω))
    (Hc : Fin 3 → SL(3, Ω)) : Prop where
  theta : ∀ i X, tw6Theta Ω Fr (twFrame Ω i X) = twFrame Ω i (Φ i X)
  fix : ∀ i (X : SL(3, Ω)), X ∈ fixSubgroup (Φ i) ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
    Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL (Hc i) * Y *
      (Matrix.SpecialLinearGroup.toGL (Hc i))⁻¹

variable {Φ : Fin 3 → SL(3, Ω) ≃* SL(3, Ω)} {Hc : Fin 3 → SL(3, Ω)}

theorem TwFrameFacts.theta_fixed_iff {K : Type} [Field K] [Algebra K Ω]
    (F : TwFrameFacts ℓ f Fr Φ Hc) (h : UnitaryFieldData ℓ f K) (i : Fin 3) (X : SL(3, Ω)) :
    tw6Theta Ω Fr (twFrame Ω i X) = twFrame Ω i X ↔
      ∃ x : unitarySU ℓ f K 3, twUnitaryFrame h (Hc i) x = X := by
  rw [F.theta, (twFrame_injective i).eq_iff,
    ← mem_fixSubgroup_iff_exists_twUnitaryFrame h (F.fix i), mem_fixSubgroup]

theorem TwFrameFacts.conjDiag3_mem_fix (F : TwFrameFacts ℓ f Fr Φ Hc) (i : Fin 3)
    {m : ModGL Tag.E6 Ω} (hθ : tw6Theta Ω Fr m = m) {d : Fin 3 → Ωˣ}
    (hd : ∀ X, m * twFrame Ω i X * m⁻¹ = twFrame Ω i (conjDiag3 d X)) {X : SL(3, Ω)}
    (hX : X ∈ fixSubgroup (Φ i)) : conjDiag3 d X ∈ fixSubgroup (Φ i) := by
  rw [mem_fixSubgroup] at hX ⊢
  apply twFrame_injective i
  rw [← F.theta, ← hd, map_mul, map_mul, map_inv, hθ, F.theta, hX]

theorem TwFrameFacts.exists_realizes {K : Type} [Field K] [Algebra K Ω] [IsAlgClosed Ω]
    [CharP Ω ℓ] (F : TwFrameFacts ℓ f Fr Φ Hc) (h : UnitaryFieldData ℓ f K) (hℓ3 : ℓ ≠ 3)
    (hq1 : ℓ ^ f % 3 = 2) (i : Fin 3) {m : ModGL Tag.E6 Ω} (hm : m ∈ torusGroup Tag.E6 Ω)
    (hθ : tw6Theta Ω Fr m = m) :
    ∃ (γ : primeFormUnitary h (idGram K 3)) (d : Fin 3 → Ωˣ),
      (∀ X, m * twFrame Ω i X * m⁻¹ = twFrame Ω i (conjDiag3 d X)) ∧
        TwDiagRealizes (Hc i) d (γ : GL (Fin 3) K) := by
  obtain ⟨d, hd⟩ := twFrame_torus i hm
  obtain ⟨B, hB, hreal⟩ := exists_twDiagRealizes h hℓ3 hq1 (F.fix i)
    (fun X hX => F.conjDiag3_mem_fix i hθ hd hX)
  exact ⟨⟨B, twMem_primeFormUnitary_of_mem_unitaryIsom3 h hB⟩, d, hd, hreal⟩

theorem TwFrameFacts.act {K : Type} [Field K] [Algebra K Ω]
    (h : UnitaryFieldData ℓ f K) (i : Fin 3) {m : ModGL Tag.E6 Ω}
    {γ : primeFormUnitary h (idGram K 3)} {d : Fin 3 → Ωˣ}
    (hd : ∀ X, m * twFrame Ω i X * m⁻¹ = twFrame Ω i (conjDiag3 d X))
    (hγ : TwDiagRealizes (Hc i) d (γ : GL (Fin 3) K)) (x : unitarySU ℓ f K 3) :
    m * twFrame Ω i (twUnitaryFrame h (Hc i) x) * m⁻¹ =
      twFrame Ω i (twUnitaryFrame h (Hc i) (conjSU h γ x)) := by
  rw [hd, hγ.conjDiag3_twUnitaryFrame h]

end Frame

section Rho


variable {K : Type} [Field K] {σ : K ≃+* K} {q ℓ f : ℕ}
  {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  {g₀ : ModGL Tag.E6 (AlgebraicClosure K)} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K}
  {Φ : Fin 3 → SL(3, AlgebraicClosure K) ≃* SL(3, AlgebraicClosure K)}
  {Hc : Fin 3 → SL(3, AlgebraicClosure K)}

theorem exists_twRho (h : UnitaryFieldData ℓ f K) (pic : TwE6ThreeA2Picture K σ q Fr g₀ h₀ L T n)
    (hLle : ∀ i, L i ≤ twistedE6RootGroup K σ) (F : TwFrameFacts ℓ f Fr Φ Hc) (i : Fin 3) :
    ∃ ρ : unitarySU ℓ f K 3 →* twistedE6RootGroup K σ, ∀ x,
      twLinePsi K g₀ (ρ x : ModGL TwistTag.E6.tag K) =
        twFrame (AlgebraicClosure K) i (twUnitaryFrame h (Hc i) x) := by
  have hinj : Function.Injective ((twLinePsi K g₀).comp (twistedE6RootGroup K σ).subtype) :=
    (twLinePsi_injective K g₀).comp (Subgroup.subtype_injective _)
  have hrange : ∀ x : unitarySU ℓ f K 3,
      ((twFrame (AlgebraicClosure K) i).comp (twUnitaryFrame h (Hc i))) x ∈
        ((twLinePsi K g₀).comp (twistedE6RootGroup K σ).subtype).range := by
    intro x
    have hmem : twFrame (AlgebraicClosure K) i (twUnitaryFrame h (Hc i) x) ∈
        (L i).map (twLinePsi K g₀) := by
      rw [pic.L_image i]
      exact Subgroup.mem_inf.2 ⟨twFrame_mem_rootSpan i _, (F.theta_fixed_iff h i _).2 ⟨x, rfl⟩⟩
    obtain ⟨l, hl, hle⟩ := hmem
    exact ⟨⟨l, hLle i hl⟩, hle⟩
  obtain ⟨ρ, hρ⟩ := exists_hom_comp_eq _ hinj
    ((twFrame (AlgebraicClosure K) i).comp (twUnitaryFrame h (Hc i))) hrange
  exact ⟨ρ, hρ⟩

theorem twRho_injective (h : UnitaryFieldData ℓ f K) {i : Fin 3}
    {ρ : unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
    (hρ : ∀ x, twLinePsi K g₀ (ρ x : ModGL TwistTag.E6.tag K) =
      twFrame (AlgebraicClosure K) i (twUnitaryFrame h (Hc i) x)) :
    Function.Injective ρ := by
  intro x y hxy
  have h1 : twLinePsi K g₀ (ρ x : ModGL TwistTag.E6.tag K) =
      twLinePsi K g₀ (ρ y : ModGL TwistTag.E6.tag K) := by rw [hxy]
  rw [hρ, hρ] at h1
  exact twUnitaryFrame_injective h (Hc i) (twFrame_injective i h1)

theorem twRho_range (h : UnitaryFieldData ℓ f K) (pic : TwE6ThreeA2Picture K σ q Fr g₀ h₀ L T n)
    (F : TwFrameFacts ℓ f Fr Φ Hc) {i : Fin 3} {ρ : unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
    (hρ : ∀ x, twLinePsi K g₀ (ρ x : ModGL TwistTag.E6.tag K) =
      twFrame (AlgebraicClosure K) i (twUnitaryFrame h (Hc i) x)) :
    ρ.range.map (twistedE6RootGroup K σ).subtype = L i := by
  ext y
  simp only [Subgroup.mem_map, MonoidHom.mem_range, Subgroup.coe_subtype]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    refine (pic.mem_L i _).2 ⟨(ρ x).2, ?_⟩
    rw [hρ]
    exact twFrame_mem_rootSpan i _
  · intro hy
    have hψy : twLinePsi K g₀ y ∈ (L i).map (twLinePsi K g₀) := Subgroup.mem_map_of_mem _ hy
    rw [pic.L_image i] at hψy
    obtain ⟨hmem, hfix⟩ := Subgroup.mem_inf.1 hψy
    obtain ⟨X, hX⟩ := exists_twFrame_eq i hmem
    have hfixX : tw6Theta (AlgebraicClosure K) Fr (twFrame (AlgebraicClosure K) i X) =
        twFrame (AlgebraicClosure K) i X := by
      rw [hX]
      exact hfix
    obtain ⟨x, rfl⟩ := (F.theta_fixed_iff h i X).1 hfixX
    refine ⟨ρ x, ⟨x, rfl⟩, ?_⟩
    apply twLinePsi_injective K g₀
    rw [hρ, hX]

end Rho

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
