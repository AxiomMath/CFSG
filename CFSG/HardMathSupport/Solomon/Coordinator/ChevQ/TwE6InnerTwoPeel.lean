module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6InnerTwoDefs
import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeBlock
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.PlanesToralBlocks

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem peel_rootChar_neg {L : Type} [Field L] (b : Fin TwistTag.E6.tag.rank → Lˣ)
    (γ : Fin TwistTag.E6.tag.rank → ℤ) : rootChar b (-γ) = (rootChar b γ)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

section Centralizer


private theorem peel_rootSpan_le_centralizer {L : Type} [Field L]
    (b : Fin TwistTag.E6.tag.rank → Lˣ) {S : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot TwistTag.E6.tag γ ∧ rootChar b γ = 1) :
    rootSpan TwistTag.E6.tag L S ≤
      Subgroup.centralizer ({rootDiagUnit TwistTag.E6.tag b} : Set (ModGL TwistTag.E6.tag L)) := by
  refine iSup₂_le fun γ hγ => ?_
  rw [rootSubgroup]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
  have h := rootDiagUnit_conj_pinnedX (K := L) b (hS γ hγ).1 c
  rw [(hS γ hγ).2, Units.val_one, one_mul] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

end Centralizer

section Peel


theorem twE6ToralBar_of_a2Peel (K : Type) [Field K] (σ : K ≃+* K) (hK3 : ringChar K ≠ 3)
    (E₀ : Subgroup (twistedE6RootGroup K σ)) (g0 : ModGL TwistTag.E6.tag (AlgebraicClosure K))
    (hg0C : g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K))
    {α β : Fin TwistTag.E6.tag.rank → ℤ} (hαβ : IsA2Pair α β)
    (hmono : ∀ x ∈ E₀, ∃ t ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure K),
      ∃ w ∈ Subgroup.zpowers (rootReflection α * rootReflection β),
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
            g0 = t * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
    (hET : ∀ x ∈ E₀,
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) * g0 ∈
          torusGroup TwistTag.E6.tag (AlgebraicClosure K) →
        ∃ b : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
              g0 = rootDiagUnit TwistTag.E6.tag b ∧ rootChar b α = 1 ∧ rootChar b β = 1) :
    TwE6ToralBar K σ E₀ := by
  classical
  set L := AlgebraicClosure K
  set ι := baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K L) with hι
  set Φ₀ : E₀ →* ModGL TwistTag.E6.tag L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    (ι.comp ((twistedE6RootGroup K σ).subtype.comp E₀.subtype)) with hΦ₀def
  have hΦ₀ : ∀ x : E₀,
      Φ₀ x = g0⁻¹ * ι ((x : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
    intro x
    simp [hΦ₀def, MulAut.conj_apply]
  have hN : ∀ x : E₀, Φ₀ x ∈ monomialSubgroup TwistTag.E6.tag L := by
    intro x
    obtain ⟨t, ht, w, -, hw⟩ := hmono x x.2
    rw [hΦ₀, hw]
    exact mul_mem (torusGroup_le_monomialSubgroup ht) (canonicalRep_mem_monomialSubgroup L w)
  set Ψ : E₀ →* WeylGroup TwistTag.E6.tag := (weylQuotientHom TwistTag.E6.tag L).comp
    (Φ₀.codRestrict (monomialSubgroup TwistTag.E6.tag L) hN) with hΨdef
  have hΨ : ∀ x : E₀, Ψ x = weylQuotientHom TwistTag.E6.tag L ⟨Φ₀ x, hN x⟩ := fun x => rfl
  set w₀ : WeylGroup TwistTag.E6.tag := rootReflection α * rootReflection β with hw₀
  have K1 : ∀ x : E₀, Ψ x ∈ Subgroup.zpowers w₀ := by
    intro x
    obtain ⟨t, ht, w, hwA, hw⟩ := hmono x x.2
    have hn : t * canonicalRep (coxeterSystem TwistTag.E6.tag) L w ∈
        monomialSubgroup TwistTag.E6.tag L :=
      mul_mem (torusGroup_le_monomialSubgroup ht) (canonicalRep_mem_monomialSubgroup L w)
    have e : (⟨Φ₀ x, hN x⟩ : monomialSubgroup TwistTag.E6.tag L) = ⟨_, hn⟩ :=
      Subtype.ext ((hΦ₀ x).trans hw)
    rw [hΨ, e, weylQuotientHom_torus_mul ht w hn]
    exact hwA
  have K2 : ∀ x : E₀, Ψ x = 1 → Φ₀ x ∈ torusGroup TwistTag.E6.tag L :=
    fun x h => mem_torusGroup_of_weylQuotientHom_eq_one (hN x) h
  have K3 : ∀ x : E₀, Φ₀ x ∈ torusGroup TwistTag.E6.tag L →
      ∀ y ∈ rootSpan TwistTag.E6.tag L (a2Roots α β), y * Φ₀ x = Φ₀ x * y := by
    intro x hxT y hy
    obtain ⟨b, hb, h1, h2⟩ := hET x x.2 (by rw [← hΦ₀ x]; exact hxT)
    rw [← hΦ₀ x] at hb
    have hS : ∀ γ ∈ a2Roots α β, IsRoot TwistTag.E6.tag γ ∧ rootChar b γ = 1 := by
      intro γ hγ
      refine ⟨a2Roots_isRoot hαβ γ hγ, ?_⟩
      simp only [a2Roots, Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
      rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
      · exact h1
      · rw [peel_rootChar_neg, h1, inv_one]
      · exact h2
      · rw [peel_rootChar_neg, h2, inv_one]
      · rw [rootChar_add, h1, h2, one_mul]
      · rw [peel_rootChar_neg, rootChar_add, h1, h2, one_mul, inv_one]
    have hc := Subgroup.mem_centralizer_singleton_iff.1 (peel_rootSpan_le_centralizer b hS hy)
    rw [hb]
    exact hc
  unfold TwE6ToralBar
  by_cases hall : ∀ x : E₀, Ψ x = 1
  · refine ⟨g0, hg0C, fun x hx => ?_⟩
    have h := K2 ⟨x, hx⟩ (hall _)
    rw [hΦ₀] at h
    exact h
  obtain ⟨x₁, hx₁⟩ := not_forall.1 hall
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (K1 x₁)
  have hw3 : w₀ ^ (3 : ℤ) = 1 := by
    have h := hαβ.pairRefl_pow_three
    exact_mod_cast h
  have hj0 : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨c, rfl⟩
    exact hx₁ (by rw [← hj, zpow_mul, hw3, one_zpow])
  have hjj : j * j = 3 * (j * j / 3) + 1 := by
    have hm : j % 3 = 1 ∨ j % 3 = 2 := by omega
    have h2 : j * j % 3 = 1 := by
      rcases hm with hm | hm <;> rw [Int.mul_emod, hm] <;> norm_num
    generalize j * j = N at h2 ⊢
    omega
  set x₀ : E₀ := x₁ ^ j with hx₀
  have hΨ0 : Ψ x₀ = w₀ := by
    rw [hx₀, map_zpow, ← hj, ← zpow_mul, hjj, zpow_add, zpow_mul, hw3, one_zpow, one_mul,
      zpow_one]
  have hL3 : ringChar L ≠ 3 := by
    have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
    rw [ringChar.eq L (ringChar K)]
    exact hK3
  have hblk : A2BlockToral TwistTag.E6.tag := a2BlockToral_E6
  obtain ⟨m, -, hmN, hmW, hmt⟩ := hblk L hL3 α β hαβ
  have hn' : m⁻¹ * Φ₀ x₀ ∈ monomialSubgroup TwistTag.E6.tag L := mul_mem (inv_mem hmN) (hN x₀)
  have ht' : m⁻¹ * Φ₀ x₀ ∈ torusGroup TwistTag.E6.tag L := by
    refine mem_torusGroup_of_weylQuotientHom_eq_one hn' ?_
    have e : (⟨m⁻¹ * Φ₀ x₀, hn'⟩ : monomialSubgroup TwistTag.E6.tag L) =
        (⟨m, hmN⟩ : monomialSubgroup TwistTag.E6.tag L)⁻¹ * ⟨Φ₀ x₀, hN x₀⟩ := rfl
    rw [e, map_mul, map_inv, hmW, ← hΨ, hΨ0, inv_mul_cancel]
  obtain ⟨y, hyS, hyT⟩ := hmt _ ht'
  rw [mul_inv_cancel_left] at hyT
  refine ⟨g0 * y⁻¹, mul_mem hg0C (inv_mem (rootSpan_le_adjointGroup L _ hyS)), fun x hx => ?_⟩
  have e1 : (g0 * y⁻¹)⁻¹ * ι (x : ModGL TwistTag.E6.tag K) * (g0 * y⁻¹) =
      y * Φ₀ ⟨x, hx⟩ * y⁻¹ := by
    rw [hΦ₀]
    group
  rw [e1]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (K1 ⟨x, hx⟩)
  have hz : Ψ (⟨x, hx⟩ * x₀ ^ (-k)) = 1 := by
    rw [map_mul, map_zpow, hΨ0, ← hk, ← zpow_add, add_neg_cancel, zpow_zero]
  have hzT := K2 _ hz
  have hc := K3 _ hzT y hyS
  have hxz : Φ₀ ⟨x, hx⟩ = Φ₀ (⟨x, hx⟩ * x₀ ^ (-k)) * Φ₀ x₀ ^ k := by
    rw [← map_zpow, ← map_mul, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have e2 : y * Φ₀ ⟨x, hx⟩ * y⁻¹ = Φ₀ (⟨x, hx⟩ * x₀ ^ (-k)) * (y * Φ₀ x₀ * y⁻¹) ^ k := by
    rw [conj_zpow, hxz]
    calc y * (Φ₀ (⟨x, hx⟩ * x₀ ^ (-k)) * Φ₀ x₀ ^ k) * y⁻¹
        = (y * Φ₀ (⟨x, hx⟩ * x₀ ^ (-k))) * Φ₀ x₀ ^ k * y⁻¹ := by group
      _ = (Φ₀ (⟨x, hx⟩ * x₀ ^ (-k)) * y) * Φ₀ x₀ ^ k * y⁻¹ := by rw [hc]
      _ = Φ₀ (⟨x, hx⟩ * x₀ ^ (-k)) * (y * Φ₀ x₀ ^ k * y⁻¹) := by group
  rw [e2]
  exact mul_mem hzT (zpow_mem hyT k)

end Peel

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeInner

end
