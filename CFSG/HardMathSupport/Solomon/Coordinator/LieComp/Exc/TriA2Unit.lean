module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2SplitMu
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Tau
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2Fixed
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2RecStruct
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2UnitSU
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TriA2UnitMu

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley.RootWalk CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.GH74.GLS.SP
  CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Dual CFSG.Open
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87 renaming fixSub → fixSubO
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Compat

variable {K : Type} [Field K] [Finite K] {σ ε : K ≃+* K} {b : Kˣ} {q₄ : ℕ}

theorem tau_rho_compat (h : A2Core σ b q₄)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (ρ : SL(3, fixSubfield σ) →* ↥(fixSubO φ)) {μ : Kˣ} (hμε : (μ : K) * ε (μ : K) = -1)
    (h1 : ∀ c : fixSubfield σ, (((ρ (Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 1 by decide) c) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      ((fP1 σ.toRingHom h.cube_apply (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K))
    (h2 : ∀ c : fixSubfield σ, (((ρ (Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 2 by decide) c) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      ((fP2 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K))
    (h3 : ∀ c : fixSubfield σ, (((ρ (Matrix.SpecialLinearGroup.transvection
        (show (0 : Fin 3) ≠ 2 by decide) c) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      ((fP3 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K))
    (h4 : ∀ c : fixSubfield σ, (((ρ (Matrix.SpecialLinearGroup.transvection
        (show (1 : Fin 3) ≠ 0 by decide) c) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      ((fM1 σ.toRingHom h.cube_apply (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K))
    (h5 : ∀ c : fixSubfield σ, (((ρ (Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 1 by decide) c) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      ((fM2 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K))
    (h6 : ∀ c : fixSubfield σ, (((ρ (Matrix.SpecialLinearGroup.transvection
        (show (2 : Fin 3) ≠ 0 by decide) c) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      ((fM3 σ.toRingHom h.cube_apply μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K))
    (x : SL(3, fixSubfield σ)) :
    unTau σ ε ((ρ x : ↥(fixSubO φ)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) =
      ((ρ (stdUnitaryEquiv (ν := 3) (fixSubfieldRestrict ε σ) x) : ↥(fixSubO φ)) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
  classical
  have hσ3 := h.cube_apply
  have hcomm : ∀ c, σ.toRingHom (ε c) = ε (σ.toRingHom c) :=
    fun c => apply_apply_comm_of_finite σ ε c
  have hμne : (μ : K) ≠ 0 := μ.ne_zero
  have hεμne : ε (μ : K) ≠ 0 := fun h0 => hμne (ε.injective (by rw [h0, map_zero]))
  have hκ : ((μ⁻¹ : Kˣ) : K) * ε ((μ⁻¹ : Kˣ) : K) = -1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hμε]
    norm_num
  let σQ : fixSubfield σ ≃+* fixSubfield σ := fixSubfieldRestrict ε σ
  let θ : SL(3, fixSubfield σ) ≃* SL(3, fixSubfield σ) := stdUnitaryEquiv (ν := 3) σQ
  let ρY : SL(3, fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixSubO φ).subtype.comp ρ
  let H : Subgroup SL(3, fixSubfield σ) :=
    MonoidHom.eqLocus ((unTau σ ε).toMonoidHom.comp ρY) (ρY.comp θ.toMonoidHom)
  have hθt : ∀ {i j : Fin 3} (hij : i ≠ j) (c : fixSubfield σ),
      θ (Matrix.SpecialLinearGroup.transvection hij c) =
        Matrix.SpecialLinearGroup.transvection hij.symm (-(σQ c)) := fun hij c => by
    show stdUnitary σQ.toRingHom (Matrix.SpecialLinearGroup.transvection hij c) = _
    rw [stdUnitary_transvection]
    rfl
  have key : ∀ y, (MonoidHom.id SL(3, fixSubfield σ)) y ∈ H :=
    forall_mem_of_transvections H (MonoidHom.id _)
      (fun c => by
        show unTau σ ε (ρY _) = ρY (θ _)
        apply Subtype.ext
        have lhs : ((unTau σ ε (ρY (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 1 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fM1 σ.toRingHom hσ3 (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [coe_unTau]
          have e1 : ((ρY (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 1 by decide) c) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
              ModGL TwistTag.D4.tag K) =
              ((fP1 σ.toRingHom hσ3 (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := h1 c
          rw [e1]
          exact tau_fP1 hσ3 ε hcomm (c : K)
        have rhs : ((ρY (θ (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 1 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fM1 σ.toRingHom hσ3 (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [hθt]
          exact h4 (-(σQ c))
        exact lhs.trans rhs.symm)
      (fun c => by
        show unTau σ ε (ρY _) = ρY (θ _)
        apply Subtype.ext
        have lhs : ((unTau σ ε (ρY (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fM2 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [coe_unTau]
          have e1 : ((ρY (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 2 by decide) c) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
              ModGL TwistTag.D4.tag K) =
              ((fP2 σ.toRingHom hσ3 μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := h2 c
          rw [e1]
          have h' := tau_fP2 hσ3 ε hcomm μ (c : K)
          rw [hμε, neg_one_mul] at h'
          exact h'
        have rhs : ((ρY (θ (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 2 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fM2 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [hθt]
          exact h5 (-(σQ c))
        exact lhs.trans rhs.symm)
      (fun c => by
        show unTau σ ε (ρY _) = ρY (θ _)
        apply Subtype.ext
        have lhs : ((unTau σ ε (ρY (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fM3 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [coe_unTau]
          have e1 : ((ρY (Matrix.SpecialLinearGroup.transvection
              (show (0 : Fin 3) ≠ 2 by decide) c) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
              ModGL TwistTag.D4.tag K) =
              ((fP3 σ.toRingHom hσ3 μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := h3 c
          rw [e1]
          have h' := tau_fP3 hσ3 ε hcomm μ (c : K)
          rw [hμε, neg_one_mul] at h'
          exact h'
        have rhs : ((ρY (θ (Matrix.SpecialLinearGroup.transvection
            (show (0 : Fin 3) ≠ 2 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fM3 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [hθt]
          exact h6 (-(σQ c))
        exact lhs.trans rhs.symm)
      (fun c => by
        show unTau σ ε (ρY _) = ρY (θ _)
        apply Subtype.ext
        have lhs : ((unTau σ ε (ρY (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fP1 σ.toRingHom hσ3 (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [coe_unTau]
          have e1 : ((ρY (Matrix.SpecialLinearGroup.transvection
              (show (1 : Fin 3) ≠ 0 by decide) c) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
              ModGL TwistTag.D4.tag K) =
              ((fM1 σ.toRingHom hσ3 (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := h4 c
          rw [e1]
          exact tau_fM1 hσ3 ε hcomm (c : K)
        have rhs : ((ρY (θ (Matrix.SpecialLinearGroup.transvection
            (show (1 : Fin 3) ≠ 0 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fP1 σ.toRingHom hσ3 (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [hθt]
          exact h1 (-(σQ c))
        exact lhs.trans rhs.symm)
      (fun c => by
        show unTau σ ε (ρY _) = ρY (θ _)
        apply Subtype.ext
        have lhs : ((unTau σ ε (ρY (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fP2 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [coe_unTau]
          have e1 : ((ρY (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 1 by decide) c) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
              ModGL TwistTag.D4.tag K) =
              ((fM2 σ.toRingHom hσ3 μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := h5 c
          rw [e1]
          have h' := tau_fM2 hσ3 ε hcomm μ (c : K)
          rw [hκ, neg_one_mul] at h'
          exact h'
        have rhs : ((ρY (θ (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 1 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fP2 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [hθt]
          exact h2 (-(σQ c))
        exact lhs.trans rhs.symm)
      (fun c => by
        show unTau σ ε (ρY _) = ρY (θ _)
        apply Subtype.ext
        have lhs : ((unTau σ ε (ρY (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fP3 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [coe_unTau]
          have e1 : ((ρY (Matrix.SpecialLinearGroup.transvection
              (show (2 : Fin 3) ≠ 0 by decide) c) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
              ModGL TwistTag.D4.tag K) =
              ((fM3 σ.toRingHom hσ3 μ (c : K) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := h6 c
          rw [e1]
          have h' := tau_fM3 hσ3 ε hcomm μ (c : K)
          rw [hκ, neg_one_mul] at h'
          exact h'
        have rhs : ((ρY (θ (Matrix.SpecialLinearGroup.transvection
            (show (2 : Fin 3) ≠ 0 by decide) c)) : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
            ModGL TwistTag.D4.tag K) =
            ((fP3 σ.toRingHom hσ3 μ (-(ε (c : K))) : adjointGroup d4 K) : ModGL TwistTag.D4.tag K) := by
          rw [hθt]
          exact h3 (-(σQ c))
        exact lhs.trans rhs.symm)
  exact key x

end Compat

section Core

theorem compsWith_unitary_core {P : (X : Type) → [Group X] → Prop}
    {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hf : 1 ≤ f) (hq : (p ^ f) % 3 = 2)
    (hq5 : 5 ≤ p ^ f) {K : Type} [Field K] [Finite K] [CharP K p] {σ ε : K ≃+* K}
    (hK : Nat.card K = ((p ^ f) ^ 4) ^ 3) (hσ : ∀ c, σ c = c ^ ((p ^ f) ^ 4))
    (hε : ∀ c, ε c = c ^ ((p ^ f) ^ 9)) {b : Kˣ} (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1)
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hs : (s : ModGL TwistTag.D4.tag K) = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1])
    (hPquot : ∀ {F : Type} [Field F] [Finite F], Nat.card F = (p ^ f) ^ 2 →
      ∀ {Q : Type} [Group Q] [Finite Q] (g : ↥(StatedSU 3 (p ^ f) F) →* Q),
        Function.Surjective g → g.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) F) → P Q) :
    CompsWith P ↥(foldFix ((MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ : MulAut
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓
      foldFix ((unTau σ ε : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
          graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
            graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  set q := p ^ f with hqdef
  set q₄ := q ^ 4 with hq₄def
  have hq2 : 2 ≤ q := by omega
  have hq4two : 2 ≤ q₄ := by
    calc 2 ≤ q := hq2
      _ = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hmod : q₄ % 3 = 1 := by rw [hq₄def, Nat.pow_mod, hq]
  have hodd : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hb3' : (b : K) ^ 3 = 1 := by
    have := congrArg Units.val hb3
    simpa using this
  have hbσ : Units.map σ.toRingHom.toMonoidHom b = b := by
    apply Units.ext
    show σ (b : K) = b
    rw [hσ]
    obtain ⟨k, hk⟩ : ∃ k, q₄ = 3 * k + 1 := ⟨q₄ / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hb3', one_pow, one_mul]
  have hεb : Units.map ε.toRingHom.toMonoidHom b = b⁻¹ := by
    apply Units.ext
    show ε (b : K) = ((b⁻¹ : Kˣ) : K)
    rw [hε]
    have h9 : (q ^ 9) % 3 = 2 := by rw [Nat.pow_mod, hq]
    obtain ⟨k, hk⟩ : ∃ k, q ^ 9 = 3 * k + 2 := ⟨q ^ 9 / 3, by omega⟩
    have hb2 : (b : K) ^ 2 = ((b⁻¹ : Kˣ) : K) := by
      rw [Units.val_inv_eq_inv_val]
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ]
      exact hb3'
    rw [hk, pow_add, pow_mul, hb3', one_pow, one_mul, hb2]
  have hA : A2Std σ b q₄ := ⟨hq4two, hK, hσ, hmod, hodd, hbσ, hb3, hb1⟩
  have hε4 : ∀ c, ε (ε (ε (ε c))) = c := by
    intro c
    simp only [hε]
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    have hN : Nat.card K = q₄ ^ 3 := hK
    have hpowN : ∀ n : ℕ, c ^ (Nat.card K ^ n) = c := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, pow_mul, ih]
        haveI : Fintype K := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card, FiniteField.pow_card]
    have : q ^ 9 * (q ^ 9 * (q ^ 9 * q ^ 9)) = Nat.card K ^ 3 := by
      rw [hN, hq₄def]
      ring
    rw [this]
    exact hpowN 3
  obtain ⟨μ, hμ, hμε⟩ := exists_mu_unitary (p := p) (f := f) hf hA.toCore rfl hε hεb hε4
  set φ₄ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    MulAut.conj s * fieldActor (t := TwistTag.D4) σ σ with hφ₄
  have hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ₄ y : ModGL TwistTag.D4.tag K) = a2Conj σ b (y : ModGL TwistTag.D4.tag K) :=
    a2_hφ_of_class (σ := σ) (d := b) hs
  obtain ⟨ρ, hnt, hcard, h1, h2, h3, h4, h5, h6⟩ :=
    exists_hom_fixSub_mu hA.toCore φ₄ hφ μ hμ
  obtain ⟨hker, hN, hsolv⟩ := sl3_hom_structure ρ hnt hcard
  have hcompat := tau_rho_compat hA.toCore φ₄ ρ hμε h1 h2 h3 h4 h5 h6
  have hFcard : Nat.card (fixSubfield σ) = q₄ :=
    CFSG.GH74.GLS.Stage4.Hex.card_fixedField_of_cube σ.toRingHom hA.two_le hA.card hA.frob
  haveI hFchar : CharP (fixSubfield σ) p :=
    ((fixSubfield σ).subtype.charP_iff (fixSubfield σ).subtype_injective p).2 inferInstance
  let σQ : fixSubfield σ ≃+* fixSubfield σ := fixSubfieldRestrict ε σ
  have hσQ : ∀ c : fixSubfield σ, σQ c = c ^ (p ^ f) :=
    eps_restrict_frob (Q := p ^ f) rfl hσ hε
  obtain ⟨F₂, hF₂, ⟨e⟩⟩ := stdUnitary_equiv_fin (ℓ := p) (f := f) (ν := 3) hp
    (L := ↥(fixSubfield σ)) hf σQ hσQ le_rfl (by rw [hFcard])
  haveI hF₂char : CharP ↥F₂ p := (F₂.subtype.charP_iff F₂.subtype_injective p).2 inferInstance
  let θ : SL(3, fixSubfield σ) ≃* SL(3, fixSubfield σ) := stdUnitaryEquiv (ν := 3) σQ
  let S : Subgroup SL(3, fixSubfield σ) := fixSubgroup θ
  have hSmem : ∀ x, x ∈ S ↔ θ x = x := fun x => mem_fixSubgroup
  have hFD : LieFactorData p ↥(StatedSU 3 (p ^ f) ↥F₂) :=
    lieFactorData_statedSU_three hp hF₂ hq5
  have hSperf : Group.IsPerfect ↥S := ⟨(hFD.of_mulEquiv e).perfect⟩
  let ρY : SL(3, fixSubfield σ) →* graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (fixSubO φ₄).subtype.comp ρ
  let τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := unTau σ ε
  have hτρ : ∀ x, τ.toMonoidHom (ρY x) = ρY (θ.toMonoidHom x) := fun x => hcompat x
  have hkerY : ρY.ker ≤ Subgroup.center SL(3, fixSubfield σ) := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact Subtype.ext hx
  have hrange_le : ρY.range ≤ fixSubO φ₄ := by
    rintro _ ⟨x, rfl⟩
    exact (ρ x).2
  have hrng : ρY.range.subgroupOf (fixSubO φ₄) = ρ.range := by
    ext ⟨c, hc⟩
    simp only [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, congrArg Subtype.val hx⟩
  haveI hN' : (ρY.range.subgroupOf (fixSubO φ₄)).Normal := by
    rw [hrng]
    exact hN
  have hsolv' : Group.IsSolvable (↥(fixSubO φ₄) ⧸ ρY.range.subgroupOf (fixSubO φ₄)) := by
    have e' := QuotientGroup.quotientMulEquivOfEq hrng
    exact Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
  have hC' : ∀ g, g ∈ foldFix (φ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓ foldFix (τ : graphFixedRootGroup
          TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ↔
      g ∈ fixSubO φ₄ ∧ τ.toMonoidHom g = g := by
    intro g
    rw [Subgroup.mem_inf, mem_foldFix, mem_foldFix]
    rfl
  obtain ⟨hSle, hNorm, hSolv⟩ := normal_solvable_of_fixed ρY θ.toMonoidHom τ.toMonoidHom hτρ hkerY
    S hSmem hSperf (fixSubO φ₄) hrange_le hsolv' _ hC'
  set C' := foldFix (φ₄ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom ≃*
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊓ foldFix (τ : graphFixedRootGroup
          TwistTag.D4 K σ.toRingHom ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom) with hC'def
  haveI hJN := hNorm
  let J : Subgroup ↥C' := (S.map ρY).subgroupOf C'
  let ρS : ↥S →* ↥C' := (ρY.comp S.subtype).codRestrict C' (fun x => hSle ⟨x, x.2, rfl⟩)
  let gS : ↥S →* ↥J := ρS.codRestrict J (fun x => ⟨x, x.2, rfl⟩)
  let g : ↥(StatedSU 3 (p ^ f) ↥F₂) →* ↥J := gS.comp e.toMonoidHom
  have hg : Function.Surjective g := by
    intro j
    obtain ⟨x, hx, hxj⟩ := j.2
    refine ⟨e.symm ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show ρY ((e (e.symm ⟨x, hx⟩) : ↥S) : SL(3, fixSubfield σ)) = ((j : ↥C') : _)
    rw [MulEquiv.apply_symm_apply]
    exact hxj
  have hgk : g.ker ≤ Subgroup.center ↥(StatedSU 3 (p ^ f) ↥F₂) := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ρY ((e y : ↥S) : SL(3, fixSubfield σ)) = 1 := by
      have := congrArg (fun j : ↥J => ((j : ↥C') : graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
        hy
      exact this
    have hz : ((e y : ↥S) : SL(3, fixSubfield σ)) ∈ Subgroup.center SL(3, fixSubfield σ) :=
      hkerY h1
    rw [Subgroup.mem_center_iff]
    intro y'
    apply e.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.1 hz _
  exact compsWith_of_su_hom hp hF₂ hq5 (hPquot hF₂) J hSolv g hg hgk

end Core

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp.TriA2
