module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRootVec
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadow
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadowDim
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree

section Kind3A2


theorem twE6CaseI_rankOne_kind3A2 (K : Type) [Field K] (σ : K ≃+* K) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hplane : ∀ y ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
          (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
            (3 : ℤ) ∣ γ 3) →
          twE6FixDim K σ y = 24 → TwE6All24PlaneIn K σ E₀)
    {x₁ : twistedE6RootGroup K σ} (hx₁ : x₁ ∈ E₀)
    {t₁ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₁ : t₁ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₁ : WeylGroup TwistTag.E6.tag}
    (hx₁w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL TwistTag.E6.tag K) *
      g0 = t₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁)
    (hk : E6Kind3A2 w₁) :
    TwE6All24PlaneIn K σ E₀ := by
  have hN : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, v + w₁ • v + w₁ • w₁ • v = 0 := hk
  refine hplane x₁ hx₁ t₁ ht₁ w₁ hx₁w (fun γ hγ hwγ => ?_) ?_
  ·
    refine absurd ?_ hγ.ne_zero
    have h := hN γ
    rw [hwγ, hwγ] at h
    funext i
    have h' := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at h' ⊢
    omega
  · exact twE6FixDim_eq_24_of_kind3A2 hK3 (hE₀.2 x₁ hx₁) ht₁
      (pow_eq_one_of_twE6Frame_eq (hE₀.2 x₁ hx₁) ht₁ hx₁w) hx₁w hN

end Kind3A2

section Kind2A2


theorem twE6CaseI_rankOne_kind2A2 (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    (hplane : ∀ y ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
          (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
            (3 : ℤ) ∣ γ 3) →
          twE6FixDim K σ y = 24 → TwE6All24PlaneIn K σ E₀)
    {x₁ : twistedE6RootGroup K σ} (hx₁ : x₁ ∈ E₀)
    {t₁ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₁ : t₁ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₁ : WeylGroup TwistTag.E6.tag} (hw₁ : w₁ ≠ 1)
    (hx₁w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL TwistTag.E6.tag K) *
      g0 = t₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁)
    (hW : TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w₁))
    {γ₁ γ₂ : Fin Tag.E6.rank → ℤ} (hk : E6Kind2A2 w₁ γ₁ γ₂)
    (hin : ∀ γ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ γ 3) :
    TwE6All24PlaneIn K σ E₀ ∨ NormalizesRGroup (ringChar K) E₀ := by
  obtain ⟨hγ, h₁, h₂, hfix, hμ, hN⟩ := hk
  have hw₁3 : w₁ ^ 3 = 1 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₁ hx₁) ht₁ hx₁w
  by_cases h24 : ∃ y ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁ ∧
        twE6FixDim K σ y = 24
  ·
    obtain ⟨y, hy, t, ht, hyt, hfd⟩ := h24
    exact Or.inl (hplane y hy t ht w₁ hyt (fun γ hγr hwγ => hin γ (hfix γ hγr hwγ)) hfd)
  right
  set F := twE6RootVecFixer K σ g0 (a2Roots γ₁ γ₂) with hF
  have hover : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
        g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁ →
      x ∈ F := by
    intro x hx t ht hxt
    have hv₁ := not_not.1 fun hne => h24 ⟨x, hx, t, ht, hxt,
      (twE6FixDim_eq_24_iff_of_kind2A2 hK3 (hE₀.2 x hx) ht hw₁3 hxt hγ h₁ h₂ hfix hμ hN).2 hne⟩
    exact mem_twE6RootVecFixer.2 fun γ hγa =>
      rootVec_fixed_of_kind2A2 (hE₀.2 x hx) ht hxt hγ h₁ h₂ hμ (Set.mem_insert _ _) hγa hv₁
  have hEF : ∀ x ∈ E₀, x ∈ F := by
    intro x hx
    obtain ⟨t, ht, u, hxu⟩ := hmono x hx
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hw₁3 (hW x hx t ht u hxu) with
      rfl | rfl | rfl
    · obtain ⟨s, hs, hxs⟩ := exists_twE6Frame_mul_eq ht ht₁ hxu hx₁w
      rw [one_mul] at hxs
      have h := F.mul_mem (hover _ (mul_mem hx hx₁) s hs hxs)
        (F.inv_mem (hover x₁ hx₁ t₁ ht₁ hx₁w))
      rwa [mul_inv_cancel_right] at h
    · exact hover x hx t ht hxu
    · obtain ⟨s, hs, hxs⟩ := exists_twE6Frame_inv_eq ht hxu
      rw [inv_inv] at hxs
      have h := F.inv_mem (hover _ (inv_mem hx) s hs hxs)
      rwa [inv_inv] at h
  refine normalizesRGroup_of_monomial_fixed_rootVec q K σ hK hσ hK3 E₀ Fr hFr v g0 hg0C hg0
    hγ.isRoot_fst (hv γ₁) fun x hx => ?_
  obtain ⟨t, ht, u, hxu⟩ := hmono x hx
  have hu := hW x hx t ht u hxu
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hxF := mem_twE6RootVecFixer.1 (hEF x hx)
  have hγ₁ : γ₁ ∈ a2Roots γ₁ γ₂ := Set.mem_insert _ _
  refine ⟨a, u, hxu, ?_, hxF γ₁ hγ₁, hxF (-γ₁) (neg_mem_a2Roots hγ₁)⟩
  exact MulAction.mem_stabilizer_iff.1
    (Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h₁) hu)

end Kind2A2

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
