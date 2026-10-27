module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoPeel
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6Order3Defs
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoA2KillFrame
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoCaseIAux
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixDimTw
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoShadowDim
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree

section Inputs


@[expose] def TwE6CaseITauInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {h₀ : twistedE6RootGroup K σ} (hh₀ : h₀ ∈ E₀) (hh₀1 : h₀ ≠ 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag a)
    (haΦ : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3))
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    {x₁ : twistedE6RootGroup K σ} (hx₁ : x₁ ∈ E₀)
    {t₁ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₁ : t₁ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₁ : WeylGroup TwistTag.E6.tag} (hw₁ : w₁ ≠ 1)
    (hx₁w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₁ : ModGL TwistTag.E6.tag K) *
      g0 = t₁ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁)
    (hW : TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w₁))
    {γ₁ γ₂ : Fin Tag.E6.rank → ℤ} (hk : E6Kind2A2 w₁ γ₁ γ₂)
    (hout : ∀ γ ∈ a2Roots γ₁ γ₂, ¬ (3 : ℤ) ∣ γ 3) (htau : E6TauChars w₁ γ₁)
    (hS4 : ∀ y ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₁ →
        ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (y : ModGL TwistTag.E6.tag K) * g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
            (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁) ≠
          rootVec TwistTag.E6.tag (AlgebraicClosure K) γ₁ →
        twE6FixDim K σ y = 24),
    TwE6All24PlaneIn K σ E₀ ∨ NormalizesRGroup (ringChar K) E₀

@[expose] def TwE6CaseIRankOne3A2Input : Prop :=
  ∀ (K : Type) [Field K] (σ : K ≃+* K) (hK3 : ringChar K ≠ 3)
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
    (hk : E6Kind3A2 w₁),
    TwE6All24PlaneIn K σ E₀

@[expose] def TwE6CaseIRankOne2A2Input : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ)
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
    (hin : ∀ γ ∈ a2Roots γ₁ γ₂, (3 : ℤ) ∣ γ 3),
    TwE6All24PlaneIn K σ E₀ ∨ NormalizesRGroup (ringChar K) E₀

@[expose] def TwE6CaseIRankTwoInput : Prop :=
  ∀ (hT : E6CaseITable) (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (q : ℕ) (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {h₀ : twistedE6RootGroup K σ} (hh₀ : h₀ ∈ E₀) (hh₀1 : h₀ ≠ 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag)
    (hv : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ)
    (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag a)
    (haΦ : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3))
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
    {x₂ : twistedE6RootGroup K σ} (hx₂ : x₂ ∈ E₀)
    {t₂ : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht₂ : t₂ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {w₂ : WeylGroup TwistTag.E6.tag} (hw₂ : w₂ ∉ Subgroup.zpowers w₁)
    (hx₂w : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x₂ : ModGL TwistTag.E6.tag K) *
      g0 = t₂ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₂)
    (hn₁ : E6FixesNode3 w₁) (hn₂ : E6FixesNode3 w₂),
    TwE6All24PlaneIn K σ E₀ ∨ NormalizesRGroup (ringChar K) E₀

end Inputs

private theorem twE6CI_rootChar_single {L : Type} [Field L] (a : Fin TwistTag.E6.tag.rank → Lˣ)
    (j : Fin TwistTag.E6.tag.rank) : rootChar a (Pi.single j 1) = a j := by
  have h := rootChar_nsmul_single a j 1
  rwa [one_smul, pow_one] at h

private theorem twE6CI_zpow_eq_one_iff {M : Type*} [Group M] {ζ : M} (h3 : ζ ^ 3 = 1)
    (h1 : ζ ≠ 1) (m : ℤ) : ζ ^ m = 1 ↔ (3 : ℤ) ∣ m := by
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_prime h3 h1, Nat.cast_ofNat]

private theorem twE6CI_units_pow_apply_eq_self {L M : Type*} [Field L] [AddCommGroup M]
    [Module L M] {A : (Module.End L M)ˣ} {m : M} (hA : (A : Module.End L M) m = m) (i : ℕ) :
    ((A ^ i : (Module.End L M)ˣ) : Module.End L M) m = m := by
  induction i with
  | zero => rw [pow_zero, Units.val_one, Module.End.one_apply]
  | succ i ih =>
    rw [pow_succ]
    exact units_mul_apply_eq_self ih hA

section Character


theorem twE6CaseI_rootChar_eq {L : Type} [Field L] {a : Fin TwistTag.E6.tag.rank → Lˣ}
    (ha3 : rootDiagUnit TwistTag.E6.tag a ^ 3 = 1)
    (haΦ : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3)) :
    (∀ δ : Fin TwistTag.E6.tag.rank → ℤ, rootChar a δ = a 3 ^ δ 3) ∧ a 3 ^ 3 = 1 ∧ a 3 ≠ 1 := by
  have hj : ∀ j : Fin TwistTag.E6.tag.rank, j ≠ 3 → a j = 1 := by
    intro j hj
    rw [← twE6CI_rootChar_single a j]
    refine (haΦ _ (isRoot_single _ j)).2 ?_
    rw [Pi.single_apply, if_neg (Ne.symm hj)]
    exact dvd_zero 3
  refine ⟨fun δ => ?_, ?_, fun h => ?_⟩
  · rw [rootChar, Finset.prod_eq_single (3 : Fin TwistTag.E6.tag.rank)
      (fun j _ hj3 => by rw [hj j hj3, one_zpow]) (fun h => absurd (Finset.mem_univ _) h)]
  · have h := rootChar_pow_three_of_rootDiagUnit ha3 (isRoot_single TwistTag.E6.tag 3)
    rwa [twE6CI_rootChar_single] at h
  · have h' := (haΦ _ (isRoot_single TwistTag.E6.tag 3)).1 (by rw [twE6CI_rootChar_single, h])
    rw [Pi.single_eq_same] at h'
    norm_num at h'

private theorem twE6CI_smul_apply_three_modEq {L : Type} [Field L]
    {a : Fin TwistTag.E6.tag.rank → Lˣ}
    (hrc : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ, rootChar a δ = a 3 ^ δ 3) (h3 : a 3 ^ 3 = 1)
    (h1 : a 3 ≠ 1) {u : WeylGroup TwistTag.E6.tag}
    (hu : ∀ μ : Fin TwistTag.E6.tag.rank → ℤ, rootChar a (u • μ) = rootChar a μ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) : (u • γ) 3 ≡ γ 3 [ZMOD 3] := by
  have e := hu γ
  rw [hrc, hrc] at e
  rw [Int.modEq_iff_dvd]
  refine (twE6CI_zpow_eq_one_iff h3 h1 _).1 ?_
  rw [zpow_sub, e, mul_inv_cancel]

end Character

section Frame

variable
  {K : Type} [Field K] {σ : K ≃+* K} {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}

theorem twE6CaseI_fixesNode3 {h₀ x : twistedE6RootGroup K σ} (hcomm : h₀ * x = x * h₀)
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag a)
    (hrc : ∀ δ : Fin TwistTag.E6.tag.rank → ℤ, rootChar a δ = a 3 ^ δ 3) (h3 : a 3 ^ 3 = 1)
    (h1 : a 3 ≠ 1) {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u) :
    E6FixesNode3 u := fun γ _ =>
  twE6CI_smul_apply_three_modEq hrc h3 h1 (rootChar_smul_eq_of_twE6Frame_commute hcomm ha ht hx) γ

private theorem twE6CI_fixDim_mul_eq {s x : twistedE6RootGroup K σ} (hsx3 : (s * x) ^ 3 = 1)
    (hx3 : x ^ 3 = 1)
    (hs : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (s : ModGL TwistTag.E6.tag K) *
      g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K))
    {t : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    (ht : t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)) {u : WeylGroup TwistTag.E6.tag}
    (hu3 : u ^ 3 = 1)
    (hx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
      g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u)
    (hfix : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
      ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (s : ModGL TwistTag.E6.tag K) *
          g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
        Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) :
    twE6FixDim K σ (s * x) = twE6FixDim K σ x := by
  classical
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, hc⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mul_mem hs ht)
  have hsx : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((s * x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 =
        rootDiagUnit TwistTag.E6.tag c *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u := by
    rw [twE6Frame_mul, hx, ← mul_assoc, ← hc]
  rw [twE6FixDim_eq_of_monomial_of_pow_three hsx3 hu3 hsx,
    twE6FixDim_eq_of_monomial_of_pow_three hx3 hu3 hx]
  rw [add_left_inj, add_right_inj]
  refine congrArg Finset.card (Finset.filter_congr fun γ hγ => and_congr_right fun hγu => ?_)
  have h := hfix γ (mem_rootFinset.1 hγ) hγu
  rw [twE6Frame_mul]
  constructor
  · intro h'
    have h'' := units_mul_apply_eq_self (units_inv_apply_eq_self h) h'
    rwa [inv_mul_cancel_left] at h''
  · exact units_mul_apply_eq_self h

end Frame

section Plane


theorem twE6CaseI_plane_of_fixDim {K : Type} [Field K] {σ : K ≃+* K}
    {E₀ : Subgroup (twistedE6RootGroup K σ)} (hE₀ : IsElemAbelian 3 E₀)
    (hc : Nat.card E₀ = 3 ^ 3) {h₀ : twistedE6RootGroup K σ} (hh₀ : h₀ ∈ E₀) (hh₀1 : h₀ ≠ 1)
    (hh₀24 : twE6FixDim K σ h₀ = 24) {g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K)}
    {a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ}
    (ha : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h₀ : ModGL TwistTag.E6.tag K) *
      g0 = rootDiagUnit TwistTag.E6.tag a)
    (haΦ : ∀ α : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag α →
      (rootChar a α = 1 ↔ (3 : ℤ) ∣ α 3)) :
    ∀ y ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
          (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
            (3 : ℤ) ∣ γ 3) →
          twE6FixDim K σ y = 24 → TwE6All24PlaneIn K σ E₀ := by
  intro y hy t ht u hyu hfix hy24
  have hu1 : u ≠ 1 := by
    rintro rfl
    have h := hfix _ (isRoot_single TwistTag.E6.tag 3) (one_smul _ _)
    rw [Pi.single_eq_same] at h
    norm_num at h
  have hX : ∀ z ∈ ({h₀} : Set (twistedE6RootGroup K σ)),
      ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
        ∃ w ∈ (⊥ : Subgroup (WeylGroup TwistTag.E6.tag)),
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (z : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
    rintro z rfl
    exact ⟨rootDiagUnit TwistTag.E6.tag a, rootDiagUnit_mem_torusGroup a, 1, one_mem _,
      by rw [canonicalRep_one, mul_one]; exact ha⟩
  have hyn : y ∉ Subgroup.closure {h₀} := fun hmem =>
    hu1 (Subgroup.mem_bot.1 (mem_of_twE6Frame_eq_of_mem_closure hX hmem ht hyu))
  have hu3 := pow_eq_one_of_twE6Frame_eq (hE₀.2 y hy) ht hyu
  refine twE6All24PlaneIn_of_closure_pair hE₀ hc hh₀ hy hh₀1 hyn hh₀24 fun i => ?_
  have hsT : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((h₀ ^ i : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 ∈
        torusGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    rw [twE6Frame_pow, ha]
    exact pow_mem (rootDiagUnit_mem_torusGroup a) i
  have hsfix : ∀ γ : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag γ → u • γ = γ →
      ((g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((h₀ ^ i : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 :
            ModGL TwistTag.E6.tag (AlgebraicClosure K)) :
          Module.End (AlgebraicClosure K) (RootModule TwistTag.E6.tag (AlgebraicClosure K)))
          (rootVec TwistTag.E6.tag (AlgebraicClosure K) γ) =
        rootVec TwistTag.E6.tag (AlgebraicClosure K) γ := by
    intro γ hγ hγu
    rw [twE6Frame_pow, ha]
    exact twE6CI_units_pow_apply_eq_self
      ((rootDiagUnit_apply_rootVec_eq_self_iff a hγ).2 ((haΦ γ hγ).2 (hfix γ hγ hγu))) i
  rw [twE6CI_fixDim_mul_eq (hE₀.2 _ (mul_mem (pow_mem hh₀ i) hy)) (hE₀.2 y hy) hsT ht hu3 hyu
    hsfix]
  exact hy24

end Plane

section Assembly


theorem twE6CaseIFrameH0_of_inputs (hT : E6CaseITable) (hτ : TwE6CaseITauInput)
    (h3A2 : TwE6CaseIRankOne3A2Input) (h2A2 : TwE6CaseIRankOne2A2Input)
    (hR2 : TwE6CaseIRankTwoInput) : TwE6CaseIFrameH0 := by
  intro K _ _ σ q hK hσ hq hq2 hK3 E₀ hE₀ hc hN h₀ hh₀ hh₀1 hh₀24 Fr hFr v hv g0 hg0C hg0 a ha
    haΦ hmono
  have ha3 : rootDiagUnit TwistTag.E6.tag a ^ 3 = 1 := by
    rw [← ha, ← twE6Frame_pow, hE₀.2 h₀ hh₀, twE6Frame_one]
  obtain ⟨hrc, hζ3, hζ1⟩ := twE6CaseI_rootChar_eq ha3 haΦ
  have hnode : ∀ x ∈ E₀, ∀ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∀ u : WeylGroup TwistTag.E6.tag,
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) u →
          E6FixesNode3 u := fun x hx t ht u hxu =>
    twE6CaseI_fixesNode3 (hE₀.comm hh₀ hx) ha hrc hζ3 hζ1 ht hxu
  have hplane := twE6CaseI_plane_of_fixDim hE₀ hc hh₀ hh₀1 hh₀24 ha haΦ
  by_cases hall : ∀ x ∈ E₀, g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      (x : ModGL TwistTag.E6.tag K) * g0 ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K)
  · exact Or.inr ⟨g0, hg0C, hall⟩
  obtain ⟨x₁, hx₁'⟩ := not_forall.1 hall
  obtain ⟨hx₁, hx₁T⟩ := not_imp.1 hx₁'
  obtain ⟨t₁, ht₁, w₁, hx₁w⟩ := hmono x₁ hx₁
  have hw₁1 : w₁ ≠ 1 := by
    rintro rfl
    rw [canonicalRep_one, mul_one] at hx₁w
    exact hx₁T (hx₁w ▸ ht₁)
  have hw₁3 : w₁ ^ 3 = 1 := pow_eq_one_of_twE6Frame_eq (hE₀.2 x₁ hx₁) ht₁ hx₁w
  have hn₁ := hnode x₁ hx₁ t₁ ht₁ w₁ hx₁w
  by_cases hW : TwE6WeylPartsIn K σ E₀ g0 (Subgroup.zpowers w₁)
  swap
  ·
    obtain ⟨x₂, hx₂, t₂, ht₂, w₂, hx₂w, hw₂⟩ : ∃ x₂ ∈ E₀,
        ∃ t₂ ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K), ∃ w₂ : WeylGroup TwistTag.E6.tag,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
              (x₂ : ModGL TwistTag.E6.tag K) * g0 =
            t₂ * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w₂ ∧
          w₂ ∉ Subgroup.zpowers w₁ := by
      by_contra hcon
      refine hW fun x hx t ht u hxu => ?_
      by_contra hu
      exact hcon ⟨x, hx, t, ht, u, hxu, hu⟩
    exact (hR2 hT K σ q hK hσ hK3 E₀ hE₀ hc hh₀ hh₀1 Fr hFr v hv g0 hg0C hg0 ha haΦ hmono hplane
      hx₁ ht₁ hw₁1 hx₁w hx₂ ht₂ hw₂ hx₂w hn₁ (hnode x₂ hx₂ t₂ ht₂ w₂ hx₂w)).imp_right
        fun h => absurd h hN
  rcases hT.1 w₁ hw₁3 hw₁1 hn₁ with hA2 | hk3 | ⟨γ₁, γ₂, hk, hin⟩ | ⟨γ₁, γ₂, hk, hout, htau⟩
  ·
    obtain ⟨α, β, hαβ, hw⟩ : ∃ α β : Fin TwistTag.E6.tag.rank → ℤ, IsA2Pair α β ∧
        w₁ = rootReflection α * rootReflection β := hA2
    have hW' : TwE6WeylPartsIn K σ E₀ g0
        (Subgroup.zpowers (rootReflection α * rootReflection β)) := by
      intro x hx t ht u hxu
      have h := hW x hx t ht u hxu
      rwa [hw] at h
    refine Or.inr (twE6ToralBar_of_a2Peel K σ hK3 E₀ g0 hg0C hαβ (fun x hx => ?_)
      (diag_rootChar_eq_one_of_a2Shadow K σ E₀ (fun _ hx _ hy => hE₀.comm hx hy) g0 hmono hall
        hαβ hW'))
    obtain ⟨t, ht, u, hxu⟩ := hmono x hx
    exact ⟨t, ht, u, hW' x hx t ht u hxu, hxu⟩
  ·
    exact Or.inl (h3A2 K σ hK3 E₀ hE₀ g0 hplane hx₁ ht₁ hx₁w hk3)
  ·
    exact (h2A2 K σ q hK hσ hK3 E₀ hE₀ Fr hFr v hv g0 hg0C hg0 hmono hplane hx₁ ht₁ hw₁1 hx₁w hW
      hk hin).imp_right fun h => absurd h hN
  ·
    have ⟨hγ, h₁, h₂, hfix, hμ, hNj⟩ := hk
    exact (hτ K σ q hK hσ hK3 E₀ hE₀ hc hh₀ hh₀1 Fr hFr v hv g0 hg0C hg0 ha haΦ hmono hx₁ ht₁ hw₁1
      hx₁w hW hk hout htau fun y hy t ht hyt hne =>
        (twE6FixDim_eq_24_iff_of_kind2A2 hK3 (hE₀.2 y hy) ht hw₁3 hyt hγ h₁ h₂ hfix hμ hNj).2
          hne).imp_right fun h => absurd h hN

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
