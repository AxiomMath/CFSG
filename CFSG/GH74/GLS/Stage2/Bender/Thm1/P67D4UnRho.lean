module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnM1
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnM2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnM3
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnLay2
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4UnFinal

public noncomputable section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4 CFSG.Timmesfeld.RankTwo
  CFSG.GH74.GLS.SP CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage2.OddAut
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed CFSG.GH74.GLS.Stage2.Signalizer.Odd87
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley CFSG.GH74.BNPair Multiplicative

section Aux

private theorem unRho_weyl_aux {X : Type*} [Group X] (D : RankTwoSystem X 3) {n n₁ : D.N}
    (hn : (n : D.Weyl) = D.w₂) (hn₁ : (n₁ : D.Weyl) = D.w₁) :
    ((n * n₁ * n⁻¹ : D.N) : D.Weyl) = D.w₀ := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn, hn₁,
    inv_eq_of_mul_eq_one_right D.w₂_mul_self]
  exact RankTwoSystem.w₂_mul_w₁_mul_w₂

private theorem unRho_tau_aux {G : Type*} [Group G] (τ : G ≃* G) (g y z : G)
    (hz : (g⁻¹ * τ g) * τ y * (g⁻¹ * τ g)⁻¹ = z) : τ (g * y * g⁻¹) = g * z * g⁻¹ := by
  rw [← hz]
  simp only [map_mul, map_inv]
  group

end Aux

variable {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {d : Kˣ} {q : ℕ}
variable (h : A2Core σ d q) (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
  (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
    (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))

@[expose] def A2Core.unRho (n : ↥(unD h φ hφ).N) :
    Matrix.SpecialLinearGroup (Fin 2) (UnK σ) →* ↥(foldFix (a2Phi h φ)) :=
  (MulAut.conj (n : ↥(foldFix (a2Phi h φ)))).toMonoidHom.comp (unSlFix h φ hφ)

@[expose, reducible] def unRho
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (n : ↥(unD h φ hφ).N) :
    Matrix.SpecialLinearGroup (Fin 2) (UnK σ) →* ↥(foldFix (a2Phi h φ)) :=
  A2Core.unRho h.toCore φ hφ n

theorem A2Core.unRho_apply (n : ↥(unD h φ hφ).N) (A : Matrix.SpecialLinearGroup (Fin 2) (UnK σ)) :
    unRho h φ hφ n A =
      (n : ↥(foldFix (a2Phi h φ))) * unSlFix h φ hφ A * (n : ↥(foldFix (a2Phi h φ)))⁻¹ := rfl

include hφ in
theorem A2Core.unRho_injective (n : ↥(unD h φ hφ).N) : Function.Injective (unRho h φ hφ n) := by
  intro A B hAB
  exact unSlFix_injective h φ hφ ((MulAut.conj (n : ↥(foldFix (a2Phi h φ)))).injective hAB)

theorem unRho_injective
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (n : ↥(unD h φ hφ).N) : Function.Injective (unRho h φ hφ n) :=
  A2Core.unRho_injective h.toCore φ hφ n

include hφ in
theorem A2Core.unRho_upper_mem {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) (a : UnK σ) :
    unRho h φ hφ n (sl2Upper a) ∈ (unD h φ hφ).root 2 := by
  have h1 := (unD h φ hφ).conj_mem_root₂ n hn (k := 1) le_rfl (by norm_num)
    (unSlFix_upper_mem h φ hφ a)
  rw [show (((3 : ℕ) : ℤ) - 1) = 2 by norm_num] at h1
  exact h1

theorem unRho_upper_mem
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) (a : UnK σ) :
    unRho h φ hφ n (sl2Upper a) ∈ (unD h φ hφ).root 2 :=
  A2Core.unRho_upper_mem h.toCore φ hφ hn a

include hφ in
theorem A2Core.unRho_upper_surj {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) {y : ↥(foldFix (a2Phi h φ))}
    (hy : y ∈ (unD h φ hφ).root 2) : ∃ a : UnK σ, y = unRho h φ hφ n (sl2Upper a) := by
  have h1 := (unD h φ hφ).conj_mem_root₂ (n⁻¹) ((unD h φ hφ).lift₂_inv n hn) (k := 2)
    (by norm_num) (by norm_num) hy
  rw [show (((3 : ℕ) : ℤ) - 2) = 1 by norm_num] at h1
  obtain ⟨a, ha⟩ := unSlFix_upper_surj h φ hφ h1
  refine ⟨a, ?_⟩
  rw [unRho_apply, ← ha, Subgroup.coe_inv]
  group

theorem unRho_upper_surj
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) {y : ↥(foldFix (a2Phi h φ))}
    (hy : y ∈ (unD h φ hφ).root 2) : ∃ a : UnK σ, y = unRho h φ hφ n (sl2Upper a) :=
  A2Core.unRho_upper_surj h.toCore φ hφ hn hy

include hφ in
theorem A2Core.unRho_lower_mem {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) (a : UnK σ) :
    unRho h φ hφ n (sl2Lower a) ∈ (unD h φ hφ).root (-2) :=
  RankTwoSystem.conj_mem_root₂_neg n hn (unSlFix_lower_mem h φ hφ a)

theorem unRho_lower_mem
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) (a : UnK σ) :
    unRho h φ hφ n (sl2Lower a) ∈ (unD h φ hφ).root (-2) :=
  A2Core.unRho_lower_mem h.toCore φ hφ hn a

include hφ in
theorem A2Core.unRho_N {n n₁ : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂)
    (hn₁ : (n₁ : (unD h φ hφ).Weyl) = (unD h φ hφ).w₁)
    (hn₁' : (n₁ : ↥(foldFix (a2Phi h φ))) = unSlFix h φ hφ unSL2W) :
    ∃ m₀ : ↥(unD h φ hφ).N, (m₀ : ↥(foldFix (a2Phi h φ))) = unRho h φ hφ n unSL2W ∧
      (m₀ : (unD h φ hφ).Weyl) = (unD h φ hφ).w₀ := by
  refine ⟨n * n₁ * n⁻¹, ?_, unRho_weyl_aux _ hn hn₁⟩
  rw [unRho_apply, ← hn₁']
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem unRho_N
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {n n₁ : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂)
    (hn₁ : (n₁ : (unD h φ hφ).Weyl) = (unD h φ hφ).w₁)
    (hn₁' : (n₁ : ↥(foldFix (a2Phi h φ))) = unSlFix h φ hφ unSL2W) :
    ∃ m₀ : ↥(unD h φ hφ).N, (m₀ : ↥(foldFix (a2Phi h φ))) = unRho h φ hφ n unSL2W ∧
      (m₀ : (unD h φ hφ).Weyl) = (unD h φ hφ).w₀ :=
  A2Core.unRho_N h.toCore φ hφ hn hn₁ hn₁'

include hφ in
theorem A2Core.unRho_H {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) (u : (UnK σ)ˣ) :
    unRho h φ hφ n (unSL2Diag u) ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N := by
  have _hn := hn
  have ht := unSlFix_diag h φ hφ u
  have hmem : (⟨unSlFix h φ hφ (unSL2Diag u), ht.2⟩ : (unD h φ hφ).N) ∈
      cartan (unD h φ hφ).B (unD h φ hφ).N := ht
  exact (unD h φ hφ).normal.conj_mem _ hmem n

theorem unRho_H
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂) (u : (UnK σ)ˣ) :
    unRho h φ hφ n (unSL2Diag u) ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N :=
  A2Core.unRho_H h.toCore φ hφ hn u

include hφ in
theorem A2Core.unRho_tau {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂)
    (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ κ : (UnK σ)ˣ, ∀ a : UnK σ,
      unTauX h φ ε hcomm (unRho h φ hφ n (sl2Upper a)) =
        unRho h φ hφ n (sl2Lower ((κ : UnK σ) * unEps ε hεσ a)) ∧
      unTauX h φ ε hcomm (unRho h φ hφ n (sl2Lower a)) =
        unRho h φ hφ n (sl2Upper (((κ⁻¹ : (UnK σ)ˣ) : UnK σ) * unEps ε hεσ a)) := by
  have hτ := un_isOpposition h φ hφ ε hεσ hcomm
  obtain ⟨μ, hμ⟩ := unSlFix_tau h φ hφ ε hεσ hcomm
  obtain ⟨χ, hχ⟩ := unSlFix_torus h φ hφ (hτ.lift₂_all hn)
  have e1 : ∀ a : UnK σ, (((χ⁻¹ * μ : (UnK σ)ˣ)) : UnK σ) * unEps ε hεσ a =
      ((χ⁻¹ : (UnK σ)ˣ) : UnK σ) * ((μ : UnK σ) * unEps ε hεσ a) := fun a => by
    rw [Units.val_mul, mul_assoc]
  have e2 : ∀ a : UnK σ, ((((χ⁻¹ * μ : (UnK σ)ˣ))⁻¹ : (UnK σ)ˣ) : UnK σ) * unEps ε hεσ a =
      (χ : UnK σ) * (((μ⁻¹ : (UnK σ)ˣ) : UnK σ) * unEps ε hεσ a) := fun a => by
    rw [mul_inv_rev, inv_inv, Units.val_mul]
    ring
  refine ⟨χ⁻¹ * μ, fun a => ⟨?_, ?_⟩⟩
  · rw [unRho_apply, unRho_apply]
    refine unRho_tau_aux _ _ _ _ ?_
    rw [(hμ a).1, (hχ _).2, e1]
  · rw [unRho_apply, unRho_apply]
    refine unRho_tau_aux _ _ _ _ ?_
    rw [(hμ a).2, (hχ _).1, e2]

theorem unRho_tau
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {n : ↥(unD h φ hφ).N}
    (hn : (n : (unD h φ hφ).Weyl) = (unD h φ hφ).w₂)
    (ε : K ≃+* K) (hεσ : ∀ c, ε (σ c) = σ (ε c))
    (hcomm : ∀ y, unTau σ ε (φ y) = φ (unTau σ ε y)) :
    ∃ κ : (UnK σ)ˣ, ∀ a : UnK σ,
      unTauX h φ ε hcomm (unRho h φ hφ n (sl2Upper a)) =
        unRho h φ hφ n (sl2Lower ((κ : UnK σ) * unEps ε hεσ a)) ∧
      unTauX h φ ε hcomm (unRho h φ hφ n (sl2Lower a)) =
        unRho h φ hφ n (sl2Upper (((κ⁻¹ : (UnK σ)ˣ) : UnK σ) * unEps ε hεσ a)) :=
  A2Core.unRho_tau h.toCore φ hφ hn ε hεσ hcomm

@[expose] def A2Core.unX1 : Multiplicative (UnK σ) →* ↥(foldFix (a2Phi h φ)) :=
  (unSlFix h φ hφ).comp (unSL2UpperHom (UnK σ))

@[expose, reducible] def unX1
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : Multiplicative (UnK σ) →* ↥(foldFix (a2Phi h φ)) :=
  A2Core.unX1 h.toCore φ hφ

include hφ in
theorem A2Core.unX1_injective : Function.Injective (unX1 h φ hφ) := by
  intro a b hab
  exact toAdd.injective (un_sl2Upper_injective (unSlFix_injective h φ hφ hab))

theorem unX1_injective
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : Function.Injective (unX1 h φ hφ) :=
  A2Core.unX1_injective h.toCore φ hφ

include hφ in
theorem A2Core.unX1_mem (a : Multiplicative (UnK σ)) : unX1 h φ hφ a ∈ (unD h φ hφ).root 1 :=
  unSlFix_upper_mem h φ hφ (toAdd a)

theorem unX1_mem
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (a : Multiplicative (UnK σ)) : unX1 h φ hφ a ∈ (unD h φ hφ).root 1 :=
  A2Core.unX1_mem h.toCore φ hφ a

include hφ in
theorem A2Core.unX1_surj {y : ↥(foldFix (a2Phi h φ))} (hy : y ∈ (unD h φ hφ).root 1) :
    ∃ a : Multiplicative (UnK σ), y = unX1 h φ hφ a := by
  obtain ⟨a, ha⟩ := unSlFix_upper_surj h φ hφ hy
  exact ⟨ofAdd a, ha⟩

theorem unX1_surj
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    {y : ↥(foldFix (a2Phi h φ))} (hy : y ∈ (unD h φ hφ).root 1) :
    ∃ a : Multiplicative (UnK σ), y = unX1 h φ hφ a :=
  A2Core.unX1_surj h.toCore φ hφ hy

include hφ in
theorem A2Core.unX1_torus : ∀ t ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N, ∃ χ : (UnK σ)ˣ,
    ∀ a : UnK σ, t * unX1 h φ hφ (ofAdd a) * t⁻¹ = unX1 h φ hφ (ofAdd ((χ : UnK σ) * a)) := by
  intro t ht
  obtain ⟨χ, hχ⟩ := unSlFix_torus h φ hφ ht
  exact ⟨χ, fun a => (hχ a).1⟩

theorem unX1_torus
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    : ∀ t ∈ (unD h φ hφ).B ⊓ (unD h φ hφ).N, ∃ χ : (UnK σ)ˣ,
    ∀ a : UnK σ, t * unX1 h φ hφ (ofAdd a) * t⁻¹ = unX1 h φ hφ (ofAdd ((χ : UnK σ) * a)) :=
  A2Core.unX1_torus h.toCore φ hφ

include hφ in
theorem A2Core.unX1_field (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ δ y)) (a : UnK σ) :
    unFieldX h φ δ hcomm (unX1 h φ hφ (ofAdd a)) = unX1 h φ hφ (ofAdd (unEps δ hδσ a)) :=
  unSlFix_field h φ hφ δ hδσ hcomm a

theorem unX1_field
    (h : A2Std σ d q)
    (φ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (hφ : ∀ y : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      (φ y : ModGL TwistTag.D4.tag K) = a2Conj σ d (y : ModGL TwistTag.D4.tag K))
    (δ : K ≃+* K) (hδσ : ∀ c, δ (σ c) = σ (δ c))
    (hcomm : ∀ y, fieldActor (t := TwistTag.D4) σ δ (φ y) =
      φ (fieldActor (t := TwistTag.D4) σ δ y)) (a : UnK σ) :
    unFieldX h φ δ hcomm (unX1 h φ hφ (ofAdd a)) = unX1 h φ hφ (ofAdd (unEps δ hδσ a)) :=
  A2Core.unX1_field h.toCore φ hφ δ hδσ hcomm a

end CFSG.GH74.GLS.Stage2.Bender.Thm1
