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


theorem twE6CaseIIRankTwo_of_pairs (hp : E6Order3Pairs) : TwE6CaseIIRankTwo := by
  intro K _ _ σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN hII Fr hFr v hv g0 hg0C hg0 hmono h0 hnc
  exfalso
  have hpart : ∀ w : WeylGroup TwistTag.E6.tag, ∃ x ∈ E₀,
      ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K), ∃ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u ∧
          u ∉ Subgroup.zpowers w := by
    intro w
    by_contra hcon
    refine hnc w fun x hx t ht u hxu => ?_
    by_contra hu
    exact hcon ⟨x, hx, t, ht, u, hxu, hu⟩
  obtain ⟨x₁, hx₁, t₁, ht₁, w₁, hw₁, hw₁n⟩ := hpart 1
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    exact hw₁n (Subgroup.mem_zpowers 1)
  obtain ⟨x₂, hx₂, t₂, ht₂, w₂, hw₂, hw₂n⟩ := hpart w₁
  have hw₁3 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₁ hx₁) ht₁ hw₁
  have hw₂3 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₂ hx₂) ht₂ hw₂
  have hcomm : Commute w₁ w₂ := commute_of_twE6Frame_eq (hE₀.comm hx₁ hx₂) ht₁ ht₂ hw₁ hw₂
  have hppE : ∀ a b : ℕ, x₁ ^ a * x₂ ^ b ∈ E₀ := fun a b =>
    mul_mem (pow_mem hx₁ a) (pow_mem hx₂ b)
  have hpp : ∀ a b : ℕ, ∃ s ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((x₁ ^ a * x₂ ^ b : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        s * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
          (w₁ ^ a * w₂ ^ b) := by
    intro a b
    obtain ⟨s₁, hs₁, e₁⟩ := exists_twE6Frame_pow_eq ht₁ hw₁ a
    obtain ⟨s₂, hs₂, e₂⟩ := exists_twE6Frame_pow_eq ht₂ hw₂ b
    exact exists_twE6Frame_mul_eq hs₁ hs₂ e₁ e₂
  rcases hp w₁ w₂ hw₁3 hw₁1 hw₂3 hcomm hw₂n with ⟨i, j, hk3⟩ |
    ⟨hcommon, ⟨i, j, k, l, hdet, ⟨γ₁, γ₂, hγ, h₁, h₂, hfix, hμ, hNj⟩,
      ⟨δ₁, δ₂, hδ, h₁', h₂', hfix', hμ', hNj'⟩⟩, hrank3⟩
  ·
    obtain ⟨s, hs, hy⟩ := hpp i j
    exact not_kind3A2_of_twE6FixDim_ne hK3 hE₀.2 hII (hppE i j) hs hy hk3
  obtain ⟨γ, hγr, hγ1, hγ2⟩ : ∃ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ ∧
      w₁ • γ = γ ∧ w₂ • γ = γ := hcommon
  have hparts : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
          ∃ a b : ℕ, u = w₁ ^ a * w₂ ^ b := by
    intro x hx t ht u hxu
    by_contra hne
    obtain ⟨a, b, c, hk3⟩ := hrank3 u (pow_eq_one_of_twE6Frame_eq (hE₀.2 x hx) ht hxu)
      (commute_of_twE6Frame_eq (hE₀.comm hx₁ hx) ht₁ ht hw₁ hxu)
      (commute_of_twE6Frame_eq (hE₀.comm hx₂ hx) ht₂ ht hw₂ hxu) fun a b h => hne ⟨a, b, h⟩
    obtain ⟨s, hs, hy⟩ := hpp a b
    obtain ⟨s', hs', hy'⟩ := exists_twE6Frame_pow_eq ht hxu c
    obtain ⟨s'', hs'', hy''⟩ := exists_twE6Frame_mul_eq hs hs' hy hy'
    exact not_kind3A2_of_twE6FixDim_ne hK3 hE₀.2 hII (mul_mem (hppE a b) (pow_mem hx c)) hs''
      hy'' hk3
  have hstab : ∀ a b : ℕ, (w₁ ^ a * w₂ ^ b) • γ = γ := fun a b =>
    MulAction.mem_stabilizer_iff.1 (mul_mem (pow_mem (MulAction.mem_stabilizer_iff.2 hγ1) a)
      (pow_mem (MulAction.mem_stabilizer_iff.2 hγ2) b))
  set F := twE6RootVecFixer K σ g0 ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ)) with hF
  have hsub : ∀ {γ₁ γ₂ : Fin TwistTag.E6.tag.rank → ℤ}, γ ∈ a2Roots γ₁ γ₂ →
      ({γ, -γ} : Set (Fin TwistTag.E6.tag.rank → ℤ)) ⊆ a2Roots γ₁ γ₂ := fun hm =>
    Set.insert_subset_iff.2 ⟨hm, Set.singleton_subset_iff.2 (neg_mem_a2Roots hm)⟩
  have hu : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (w₁ ^ i * w₂ ^ j) → x ∈ F := fun x hx t ht hxt =>
    twE6RootVecFixer_anti (hsub (hfix γ hγr (hstab i j)))
      (mem_twE6RootVecFixer_of_kind2A2 hK3 hE₀.2 hII hx ht hxt hγ h₁ h₂ hfix hμ hNj)
  have hu' : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K)
            (w₁ ^ k * w₂ ^ l) → x ∈ F := fun x hx t ht hxt =>
    twE6RootVecFixer_anti (hsub (hfix' γ hγr (hstab k l)))
      (mem_twE6RootVecFixer_of_kind2A2 hK3 hE₀.2 hII hx ht hxt hδ h₁' h₂' hfix' hμ' hNj')
  obtain ⟨s, hs, hy⟩ := hpp i j
  obtain ⟨s', hs', hy'⟩ := hpp k l
  have hyF := hu _ (hppE i j) s hs hy
  have hy'F := hu' _ (hppE k l) s' hs' hy'
  have hdiag : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) 1 →
        x ∈ F := by
    intro x hx t ht hxt
    obtain ⟨r, hr, hxr⟩ := exists_twE6Frame_mul_eq ht hs hxt hy
    rw [one_mul] at hxr
    have h := F.mul_mem (hu _ (mul_mem hx (hppE i j)) r hr hxr) (F.inv_mem hyF)
    rwa [mul_inv_cancel_right] at h
  have hEF : ∀ x ∈ E₀, x ∈ F := by
    intro x hx
    obtain ⟨t, ht, u, hxu⟩ := hmono x hx
    obtain ⟨a, b, rfl⟩ := hparts x hx t ht u hxu
    obtain ⟨c, d, hcd⟩ := exists_eq_pow_mul_pow_of_not_dvd hcomm hw₁3 hw₂3 hdet a b
    obtain ⟨r₁, hr₁, e₁⟩ := exists_twE6Frame_pow_eq hs hy c
    obtain ⟨r₂, hr₂, e₂⟩ := exists_twE6Frame_pow_eq hs' hy' d
    obtain ⟨r₃, hr₃, e₃⟩ := exists_twE6Frame_mul_eq hr₁ hr₂ e₁ e₂
    rw [← hcd] at e₃
    have hzE : (x₁ ^ i * x₂ ^ j) ^ c * (x₁ ^ k * x₂ ^ l) ^ d ∈ E₀ :=
      mul_mem (pow_mem (hppE i j) c) (pow_mem (hppE k l) d)
    have hzF : (x₁ ^ i * x₂ ^ j) ^ c * (x₁ ^ k * x₂ ^ l) ^ d ∈ F :=
      mul_mem (pow_mem hyF c) (pow_mem hy'F d)
    obtain ⟨r₄, hr₄, e₄⟩ := exists_twE6Frame_inv_eq hr₃ e₃
    obtain ⟨r₅, hr₅, e₅⟩ := exists_twE6Frame_mul_eq ht hr₄ hxu e₄
    rw [mul_inv_cancel] at e₅
    have h := F.mul_mem (hdiag _ (mul_mem hx (inv_mem hzE)) r₅ hr₅ e₅) hzF
    rwa [inv_mul_cancel_right] at h
  refine hN (normalizesRGroup_of_monomial_fixed_rootVec q K σ hK hσ hK3 E₀ Fr hFr v g0 hg0C hg0
    hγr (hv γ) fun x hx => ?_)
  obtain ⟨t, ht, u, hxu⟩ := hmono x hx
  obtain ⟨a, b, hab⟩ := hparts x hx t ht u hxu
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have hxF := mem_twE6RootVecFixer.1 (hEF x hx)
  refine ⟨c, u, hxu, ?_, hxF γ (Set.mem_insert _ _), hxF (-γ) (Set.mem_insert_of_mem _ rfl)⟩
  rw [hab]
  exact hstab a b

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
