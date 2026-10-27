module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwTorusDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwLayerShiftAbs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeDiagTwisted
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwInnerLineSplit
public import CFSG.RankThree.PartOne.KD4T.Certs

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KE6 CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Lang.SeitzPlane CFSG.RankThree.PartOne.KD4T
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (rootSpan_commute_of_orth)

open scoped Matrix MatrixGroups

set_option linter.unusedSectionVars false

section Hat


variable {K : Type} [Field K] {σ : K ≃+* K} {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  {g₀ : ModGL Tag.E6 (AlgebraicClosure K)} {h₀ : ModGL TwistTag.E6.tag K}
  {L : Fin 3 → Subgroup (ModGL TwistTag.E6.tag K)} {T : Subgroup (ModGL TwistTag.E6.tag K)}
  {n : ModGL TwistTag.E6.tag K}

theorem twRootGroup_le_inndiagGL : twistedE6RootGroup K σ ≤ twistedE6InndiagGL K σ :=
  le_sup_left

@[expose] def twTorusHat (K : Type) [Field K] (σ : K ≃+* K)
    (g₀ : ModGL Tag.E6 (AlgebraicClosure K)) : Subgroup (ModGL TwistTag.E6.tag K) :=
  twistedE6InndiagGL K σ ⊓ (torusGroup Tag.E6 (AlgebraicClosure K)).comap (twLinePsi K g₀)

theorem mem_twTorusHat {τ : ModGL TwistTag.E6.tag K} :
    τ ∈ twTorusHat K σ g₀ ↔ τ ∈ twistedE6InndiagGL K σ ∧
      twLinePsi K g₀ τ ∈ torusGroup Tag.E6 (AlgebraicClosure K) :=
  Iff.rfl

theorem twTorusHat_comm : ∀ x ∈ twTorusHat K σ g₀, ∀ y ∈ twTorusHat K σ g₀, x * y = y * x := by
  intro x hx y hy
  apply twLinePsi_injective K g₀
  rw [map_mul, map_mul]
  exact twLine_torusGroup_comm _ (mem_twTorusHat.1 hx).2 _ (mem_twTorusHat.1 hy).2

theorem twLinePsi_inndiag {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n) {ĝ : ModGL TwistTag.E6.tag K}
    (hĝ : ĝ ∈ twistedE6InndiagGL K σ) :
    twLinePsi K g₀ ĝ ∈ adjointGroup Tag.E6 (AlgebraicClosure K) ∧
      tw6Theta (AlgebraicClosure K) Fr (twLinePsi K g₀ ĝ) = twLinePsi K g₀ ĝ := by
  have hmem := map_twistedE6InndiagGL_le_twistedFixedGroup hℓ hf pic.card_eq σ pic.σ_apply Fr
    pic.Fr_apply (Subgroup.mem_map_of_mem _ hĝ)
  obtain ⟨hadj, hfix⟩ :=
    (mem_twistedFixedGroup_iff_twistHom TwistTag.E6 (AlgebraicClosure K) Fr).1 hmem
  refine ⟨?_, ?_⟩
  · rw [twLinePsi_apply]
    exact mul_mem (mul_mem (inv_mem pic.g₀_mem) hadj) pic.g₀_mem
  · have hfix' : twistE6 (AlgebraicClosure K) Fr
        (baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) ĝ) =
        baseChangeGL (τ := Tag.E6) (algebraMap K (AlgebraicClosure K)) ĝ := hfix
    rw [twLinePsi_apply, tw6Theta_apply, map_mul, map_mul, map_inv, pic.g₀_lang, hfix']
    group

theorem twInndiag_commute {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {g : ↥(twistedE6InndiagGL K σ)} {s : twistedE6RootGroup K σ}
    (hcomm : twistedE6InndiagConj K σ g * MulAut.conj s =
      MulAut.conj s * twistedE6InndiagConj K σ g) :
    (g : ModGL TwistTag.E6.tag K) * (s : ModGL TwistTag.E6.tag K) =
      (s : ModGL TwistTag.E6.tag K) * (g : ModGL TwistTag.E6.tag K) := by
  set ŝ : ↥(twistedE6InndiagGL K σ) := ⟨(s : ModGL TwistTag.E6.tag K),
    twRootGroup_le_inndiagGL s.2⟩ with hŝdef
  have hŝ : twistedE6InndiagConj K σ ŝ = MulAut.conj s := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    rw [twistedE6InndiagConj_apply]
    simp [hŝdef, MulAut.conj_apply]
  have h1 : twistedE6InndiagConj K σ (g * ŝ) = twistedE6InndiagConj K σ (ŝ * g) := by
    rw [map_mul, map_mul, hŝ]
    exact hcomm
  exact congrArg Subtype.val (twistedE6InndiagConj_injective hℓ hf hK σ hσ h1)


theorem twDec_decomp {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hl : TwE6ThreeA2Line K σ h₀ L T n) (pic : TwE6ThreeA2Picture K σ (ℓ ^ f) Fr g₀ h₀ L T n)
    {ρ : Fin 3 → unitarySU ℓ f K 3 →* twistedE6RootGroup K σ}
    (hρ : ∀ i, (ρ i).range.map (twistedE6RootGroup K σ).subtype = L i)
    {ĝ : ModGL TwistTag.E6.tag K} (hĝ : ĝ ∈ twistedE6InndiagGL K σ) (hcomm : ĝ * h₀ = h₀ * ĝ)
    (hnorm : ∀ i, ∀ l ∈ L i, ĝ⁻¹ * l * ĝ ∈ L i) :
    ∃ τ ∈ twTorusHat K σ g₀, ∃ x : Fin 3 → unitarySU ℓ f K 3, ĝ = τ * twLayerProd ρ x := by
  classical
  have hq : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by omega) hℓ.one_lt
  obtain ⟨hmadj, hmθ⟩ := twLinePsi_inndiag hℓ hf pic hĝ
  obtain ⟨ω, hω3, hω1, hψh₀⟩ := pic.h₀_image
  have hmd : rootDiagUnit Tag.E6 (twLineChar ω) * twLinePsi K g₀ ĝ =
      twLinePsi K g₀ ĝ * rootDiagUnit Tag.E6 (twLineChar ω) := by
    have h1 := congrArg (twLinePsi K g₀) hcomm.symm
    rw [map_mul, map_mul, hψh₀] at h1
    exact h1
  obtain ⟨k, hk⟩ := twLine_conj_shift hω3 hω1 hmadj hmd
  obtain ⟨a, b, hab⟩ := shiftQs_exists_noncomm (hl.L_quasisimple 0)
  have hψL : ∀ l ∈ L 0, twLinePsi K g₀ l ∈
      rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS 0) := fun l hl => ((pic.mem_L 0 l).1 hl).2
  have hψab : twLinePsi K g₀ (a : ModGL TwistTag.E6.tag K) * twLinePsi K g₀ (b : ModGL _ K) ≠
      twLinePsi K g₀ (b : ModGL _ K) * twLinePsi K g₀ (a : ModGL _ K) := by
    intro h'
    apply hab
    apply Subtype.ext
    apply twLinePsi_injective K g₀
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h'
  have hk0 : k = 0 := by
    by_contra hk0
    have hbk : twLinePsi K g₀ (b : ModGL _ K) ∈
        rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS k) := by
      have h2 := hψL _ (hnorm 0 b b.2)
      rw [map_mul, map_mul, map_inv] at h2
      have h3 : twLinePsi K g₀ ĝ * ((twLinePsi K g₀ ĝ)⁻¹ * twLinePsi K g₀ (b : ModGL _ K) *
          twLinePsi K g₀ ĝ) * (twLinePsi K g₀ ĝ)⁻¹ ∈
          (rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS 0)).map
            (MulAut.conj (twLinePsi K g₀ ĝ)).toMonoidHom :=
        ⟨_, h2, by simp [MulAut.conj_apply]⟩
      rw [hk 0, zero_add] at h3
      have e : twLinePsi K g₀ ĝ * ((twLinePsi K g₀ ĝ)⁻¹ * twLinePsi K g₀ (b : ModGL _ K) *
          twLinePsi K g₀ ĝ) * (twLinePsi K g₀ ĝ)⁻¹ = twLinePsi K g₀ (b : ModGL _ K) := by
        group
      rwa [e] at h3
    exact hψab (rootSpan_commute_of_orth (Or.inr (Or.inl rfl))
      (fun α hα => twE6FrameS_root 0 hα) (fun α hα => twE6FrameS_root k hα)
      (twE6FrameS_orth (Ne.symm hk0)) _ (hψL _ a.2) _ hbk)
  have hsh : ∀ i : Fin 3, (rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS i)).map
      (MulAut.conj (twLinePsi K g₀ ĝ)).toMonoidHom =
        rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS i) := fun i => by
    rw [hk i, hk0, add_zero]
  have hnc : ∃ a ∈ rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS 0),
      ∃ b ∈ rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS 0), a * b ≠ b * a :=
    ⟨_, hψL _ a.2, _, hψL _ b.2, hψab⟩
  have hm' := twLine_shift_zero hω3 hω1 hnc hmadj hmd hsh
  obtain ⟨t, htH, -, p₀, hp₀, hp₀θ, p₁, hp₁, hp₁θ, p₂, hp₂, hp₂θ, hmeq⟩ :=
    twLine_fixed_split hq pic.Fr_apply hm' hmθ
  have hp : ∀ (j : Fin 3) (p : ModGL Tag.E6 (AlgebraicClosure K)),
      p ∈ rootSpan Tag.E6 (AlgebraicClosure K) (twE6FrameS j) →
        tw6Theta (AlgebraicClosure K) Fr p = p →
        ∃ y : unitarySU ℓ f K 3, twLinePsi K g₀ (ρ j y : ModGL TwistTag.E6.tag K) = p := by
    intro j p hpS hpθ
    have hpL : p ∈ (L j).map (twLinePsi K g₀) := by
      rw [pic.L_image j]
      exact Subgroup.mem_inf.2 ⟨hpS, hpθ⟩
    obtain ⟨l, hl, rfl⟩ := hpL
    rw [← hρ j] at hl
    obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := hl
    exact ⟨y, rfl⟩
  obtain ⟨y₀, hy₀⟩ := hp 0 p₀ hp₀ hp₀θ
  obtain ⟨y₁, hy₁⟩ := hp 1 p₁ hp₁ hp₁θ
  obtain ⟨y₂, hy₂⟩ := hp 2 p₂ hp₂ hp₂θ
  have hprod : twLinePsi K g₀ (twLayerProd ρ ![y₀, y₁, y₂]) = p₀ * p₁ * p₂ := by
    change twLinePsi K g₀ (((ρ 0 y₀ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
      ((ρ 1 y₁ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) *
        ((ρ 2 y₂ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K)) = _
    rw [map_mul, map_mul, hy₀, hy₁, hy₂]
  have hmemC : twLayerProd ρ ![y₀, y₁, y₂] ∈ twistedE6InndiagGL K σ :=
    mul_mem (mul_mem (twRootGroup_le_inndiagGL (ρ 0 y₀).2) (twRootGroup_le_inndiagGL (ρ 1 y₁).2))
      (twRootGroup_le_inndiagGL (ρ 2 y₂).2)
  refine ⟨ĝ * (twLayerProd ρ ![y₀, y₁, y₂])⁻¹, mem_twTorusHat.2 ⟨mul_mem hĝ (inv_mem hmemC), ?_⟩,
    ![y₀, y₁, y₂], by group⟩
  rw [map_mul, map_inv, hprod, hmeq]
  have e : t * p₀ * p₁ * p₂ * (p₀ * p₁ * p₂)⁻¹ = t := by group
  rw [e]
  exact htH

end Hat

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
