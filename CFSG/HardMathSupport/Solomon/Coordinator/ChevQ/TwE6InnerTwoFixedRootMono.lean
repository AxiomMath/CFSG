module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoFixedRoot

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcHigh CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem commute_of_mem_rootSpan_pair
    {τ : Tag} {L : Type} [Field L] {g : ModGL τ L}
    {β : Fin τ.rank → ℤ} (hp : ∀ c : L, Commute g (pinnedX τ L β c))
    (hm : ∀ c : L, Commute g (pinnedX τ L (-β) c)) :
    ∀ y ∈ rootSpan τ L {β, -β}, Commute g y := by
  have hle : rootSpan τ L {β, -β} ≤ Subgroup.centralizer {g} := by
    refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rcases hα with rfl | rfl
    · exact (hp c).eq.symm
    · exact (hm c).eq.symm
  intro y hy
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

section Generic


theorem commute_monomial_pinnedX {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ)
    (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) {ε : L}
    (hε : ∀ c : L, canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
      (canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L γ (ε * c))
    (h1 : (rootChar a γ : L) * ε = 1) (c : L) :
    Commute (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w) (pinnedX τ L γ c) := by
  have h : rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
      (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)⁻¹ = pinnedX τ L γ c := by
    calc rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
          (rootDiagUnit τ a * canonicalRep (coxeterSystem τ) L w)⁻¹
        = rootDiagUnit τ a * (canonicalRep (coxeterSystem τ) L w * pinnedX τ L γ c *
            (canonicalRep (coxeterSystem τ) L w)⁻¹) * (rootDiagUnit τ a)⁻¹ := by group
      _ = pinnedX τ L γ ((rootChar a γ : L) * (ε * c)) := by
          rw [hε, rootDiagUnit_conj_pinnedX a hγ]
      _ = pinnedX τ L γ c := by rw [← mul_assoc, h1, one_mul]
  exact eq_mul_of_mul_inv_eq h

end Generic

section FixedRoot


theorem normalizesRGroup_of_monomial_fixed_root (q : ℕ) (K : Type) [Field K] [Finite K]
    (σ : K ≃+* K) (hK : Nat.card K = q ^ 2) (hσ : ∀ c : K, σ c = c ^ q) (hr : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ))
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ q)
    (v : WeylGroup TwistTag.E6.tag) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    (hg0 : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
    {β : Fin TwistTag.E6.tag.rank → ℤ} (hβ : IsRoot TwistTag.E6.tag β)
    (hvβ : v • permLattice TwistTag.E6.perm β = -β)
    (hmono : ∀ x ∈ E₀, ∃ (a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ)
        (w : WeylGroup TwistTag.E6.tag),
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          g0 =
        rootDiagUnit TwistTag.E6.tag a *
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w ∧
      (∃ ε : AlgebraicClosure K, (∀ c : AlgebraicClosure K,
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w *
              pinnedX TwistTag.E6.tag (AlgebraicClosure K) β c *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)⁻¹ =
          pinnedX TwistTag.E6.tag (AlgebraicClosure K) β (ε * c)) ∧
        (rootChar a β : AlgebraicClosure K) * ε = 1) ∧
      ∃ ε : AlgebraicClosure K, (∀ c : AlgebraicClosure K,
          canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w *
              pinnedX TwistTag.E6.tag (AlgebraicClosure K) (-β) c *
            (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)⁻¹ =
          pinnedX TwistTag.E6.tag (AlgebraicClosure K) (-β) (ε * c)) ∧
        (rootChar a (-β) : AlgebraicClosure K) * ε = 1) :
    NormalizesRGroup (ringChar K) E₀ := by
  refine normalizesRGroup_of_fixed_killed_root q K σ hK hσ hr E₀ Fr hFr v g0 hg0C hg0 hβ hvβ
    fun x hx => ?_
  obtain ⟨a, w, hm, ⟨ε, hε, h1⟩, ⟨ε', hε', h1'⟩⟩ := hmono x hx
  rw [hm]
  exact commute_of_mem_rootSpan_pair (commute_monomial_pinnedX a w hβ hε h1)
    (commute_monomial_pinnedX a w (IsRoot.neg hβ) hε' h1')

end FixedRoot

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
