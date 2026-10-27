module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidAut5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCore4

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoClassical.URigid (conjAut coe_conjAut)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Core

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₃ ι₂ ι : Type} [Fintype ι₃]
  [DecidableEq ι₃] [Fintype ι₂] [DecidableEq ι₂] [Fintype ι] [DecidableEq ι]
  {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {Q : QuadraticForm K (ι → K)} {Q₂ : QuadraticForm K (ι₂ → K)} {Q₃ : QuadraticForm K (ι₃ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe₂ (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
  (hSL : commutator SL(2, K) = ⊤)

omit [Finite K] in
theorem map_oProj_oY₂ (hle : (oY₂ oe₂).map (oKappaGL oe) ≤ StatedOmega ⇑Q) :
    (((oY₂ oe₂).map (oKappaGL oe)).subgroupOf (StatedOmega ⇑Q)).map (oProj ⇑Q) =
      ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoTwo oe₂ hQ₂ hSL))).range ⊔
        ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoOne oe₂ hQ₂ hSL))).range := by
  have h1 : (oRhoTwoGL oe₂).range.map (oKappaGL oe) ≤ StatedOmega ⇑Q :=
    (Subgroup.map_mono le_sup_left).trans hle
  have h2 : (oRhoOneGL oe₂).range.map (oKappaGL oe) ≤ StatedOmega ⇑Q :=
    (Subgroup.map_mono le_sup_right).trans hle
  rw [show (oY₂ oe₂).map (oKappaGL oe) = (oRhoTwoGL oe₂).range.map (oKappaGL oe) ⊔
      (oRhoOneGL oe₂).range.map (oKappaGL oe) from Subgroup.map_sup _ _ _,
    subgroupOf_sup h1 h2, Subgroup.map_sup]
  congr 1
  · ext z
    constructor
    · rintro ⟨g, ⟨_, ⟨A', rfl⟩, hg⟩, rfl⟩
      refine ⟨A', ?_⟩
      show oProj ⇑Q (oKappa oe hQ (oRhoTwo oe₂ hQ₂ hSL A')) = oProj ⇑Q g
      congr 1
      exact Subtype.ext hg
    · rintro ⟨A', rfl⟩
      exact ⟨oKappa oe hQ (oRhoTwo oe₂ hQ₂ hSL A'), ⟨_, ⟨A', rfl⟩, rfl⟩, rfl⟩
  · ext z
    constructor
    · rintro ⟨g, ⟨_, ⟨B, rfl⟩, hg⟩, rfl⟩
      refine ⟨B, ?_⟩
      show oProj ⇑Q (oKappa oe hQ (oRhoOne oe₂ hQ₂ hSL B)) = oProj ⇑Q g
      congr 1
      exact Subtype.ext hg
    · rintro ⟨B, rfl⟩
      exact ⟨oKappa oe hQ (oRhoOne oe₂ hQ₂ hSL B), ⟨_, ⟨B, rfl⟩, rfl⟩, rfl⟩

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {θ : ↥A →* StatedProj (StatedOmega ⇑Q)}

theorem rigidCore_orth_five (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤)
    (hnd : Q₂.polarBilin.Nondegenerate)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂)) (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K)))
    (hsimpSL : IsSimpleGroup SL(2, K)) (hsimp : IsSimpleGroup ↥(StatedOmega ⇑Q₂))
    (hcard : Nat.card ↥(StatedOmega ⇑Q₂) ≠ Nat.card SL(2, K)) {t : K} (ht0 : t ≠ 0)
    (ht1 : t ≠ 1) (hinj : Function.Injective (oProj ⇑Q))
    (hNN : NoNormalTwo (centralizer ((((oProj ⇑Q).comp ((oKappa oe hQ).comp
      (oRhoTwo oe₂ hQ₂ hSL))).range ⊔ ((oProj ⇑Q).comp ((oKappa oe hQ).comp
        (oRhoOne oe₂ hQ₂ hSL))).range : Subgroup _) : Set (StatedProj (StatedOmega ⇑Q)))))
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1))) :
    RigidCore A p
      (levLift θ ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoTwo oe₂ hQ₂ hSL))).range ⊔
        levLift θ ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoOne oe₂ hQ₂ hSL))).range) := by
  have : Nonempty ι₂ := ⟨oe₂ (.inr (.inl 0))⟩
  have hle := oXt_le_statedOmega hQ hSL ht0 ht1
  obtain ⟨Θ, hΘs, hΘ⟩ := exists_theta_oXt hQ hSL hperf₂ hnd ht0 ht1 hle hinj hθ hker hodd hpA
    hp2 hθp
  have hXA := perfectCore_inf_le A p
  set S₂ := ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoTwo oe₂ hQ₂ hSL))).range with hS₂
  set S₁ := ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoOne oe₂ hQ₂ hSL))).range with hS₁
  have hS₂perf : ⁅S₂, S₂⁆ = S₂ := commutator_range_of_perfect _ hSL
  have hS₁perf : ⁅S₁, S₁⁆ = S₁ := commutator_range_of_perfect _ hSL
  have hWperf := commutator_levLift hker hθ hS₂perf
  have hW₂perf := commutator_levLift hker hθ hS₁perf
  set W := levLift θ S₂ with hW
  set W₂ := levLift θ S₁ with hW₂
  have hYperf : ⁅W ⊔ W₂, W ⊔ W₂⁆ = W ⊔ W₂ := by
    refine le_antisymm (Subgroup.commutator_le.2 fun a ha b hb => ?_) (sup_le ?_ ?_)
    · rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    · conv_lhs => rw [← hWperf]
      exact commutator_mono le_sup_left le_sup_left
    · conv_lhs => rw [← hW₂perf]
      exact commutator_mono le_sup_right le_sup_right
  have hM₀ : θ ⟨p, hpA⟩ ∈ oBarOne oe hQ hSL := by
    rw [hθp]
    exact ⟨slTr 1, rfl⟩
  have hS₂L : S₂ ≤ oBarL oe hQ := by
    rintro _ ⟨A', rfl⟩
    exact ⟨oRhoTwo oe₂ hQ₂ hSL A', rfl⟩
  have hS₁L : S₁ ≤ oBarL oe hQ := by
    rintro _ ⟨B, rfl⟩
    exact ⟨oRhoOne oe₂ hQ₂ hSL B, rfl⟩
  have hWp : W ≤ centralizer ({p} : Set G) :=
    levLift_le_centralizer hker hpA fun s hs => oBarOne_commute_oBarL hM₀ (hS₂L hs)
  have hW₂p : W₂ ≤ centralizer ({p} : Set G) :=
    levLift_le_centralizer hker hpA fun s hs => oBarOne_commute_oBarL hM₀ (hS₁L hs)
  have hYX : W ⊔ W₂ ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect
      (le_inf (sup_le levLift_le levLift_le) (sup_le hWp hW₂p)) hYperf
  have hWX := le_sup_left.trans hYX
  have hW₂X := le_sup_right.trans hYX
  have hY₂Ω : oY₂ oe₂ ≤ StatedOmega ⇑Q₂ := oY₂_le_statedOmega oe₂ hQ₂ hSL
  have hκX : (oY₂ oe₂).map (oKappaGL oe) ≤ oXt oe Q₂ :=
    (Subgroup.map_mono hY₂Ω).trans (le_sup_right.trans le_sup_right)
  have hR₂X : (oRhoTwoGL oe₂).range.map (oKappaGL oe) ≤ oXt oe Q₂ :=
    (Subgroup.map_mono le_sup_left).trans hκX
  have hR₁X : (oRhoOneGL oe₂).range.map (oKappaGL oe) ≤ oXt oe Q₂ :=
    (Subgroup.map_mono le_sup_right).trans hκX
  have hΘW : (W.subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      ((oRhoTwoGL oe₂).range.map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := by
    refine map_theta_eq_of_levLift hXA hle hΘ hinj hWX hR₂X ?_ ?_
    · intro w hw
      obtain ⟨A', hA'⟩ := theta_mem_of_mem_levLift hw
      exact ⟨_, ⟨_, ⟨A', rfl⟩, rfl⟩, hA'.symm⟩
    · rintro _ ⟨_, ⟨A', rfl⟩, rfl⟩
      obtain ⟨w, hw, hwθ⟩ := exists_mem_levLift hθ hS₂perf
        (⟨A', rfl⟩ : ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoTwo oe₂ hQ₂ hSL))) A' ∈ S₂)
      exact ⟨w, hw, hwθ⟩
  have hΘW₂ : (W₂.subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      ((oRhoOneGL oe₂).range.map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := by
    refine map_theta_eq_of_levLift hXA hle hΘ hinj hW₂X hR₁X ?_ ?_
    · intro w hw
      obtain ⟨B, hB⟩ := theta_mem_of_mem_levLift hw
      exact ⟨_, ⟨_, ⟨B, rfl⟩, rfl⟩, hB.symm⟩
    · rintro _ ⟨_, ⟨B, rfl⟩, rfl⟩
      obtain ⟨w, hw, hwθ⟩ := exists_mem_levLift hθ hS₁perf
        (⟨B, rfl⟩ : ((oProj ⇑Q).comp ((oKappa oe hQ).comp (oRhoOne oe₂ hQ₂ hSL))) B ∈ S₁)
      exact ⟨w, hw, hwθ⟩
  have hΘY : ((W ⊔ W₂).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      ((oY₂ oe₂).map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := by
    show _ = (((oRhoTwoGL oe₂).range ⊔ (oRhoOneGL oe₂).range).map (oKappaGL oe)).subgroupOf
      (oXt oe Q₂)
    rw [subgroupOf_sup hWX hW₂X, Subgroup.map_sup, hΘW, hΘW₂, Subgroup.map_sup,
      subgroupOf_sup hR₂X hR₁X]
  intro x hXx _ _
  have hYxX : rightConjugate (W ⊔ W₂) x ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    (Subgroup.map_mono hYX).trans hXx.le
  have hYxA : rightConjugate (W ⊔ W₂) x ≤ A := hYxX.trans hXA
  have hYxperf : ⁅rightConjugate (W ⊔ W₂) x, rightConjugate (W ⊔ W₂) x⁆ =
      rightConjugate (W ⊔ W₂) x := by
    rw [rightConjugate, ← Subgroup.map_commutator, hYperf]
  obtain ⟨β, hβ⟩ := exists_beta_oXt hQ hnd hle hker hodd hΘs hΘ hXx
  have hΘYx : ((rightConjugate (W ⊔ W₂) x).subgroupOf
      (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
        (((oY₂ oe₂).map (oKappaGL oe)).subgroupOf (oXt oe Q₂)).map β.toMonoidHom := by
    rw [← hΘY, Subgroup.map_map]
    ext g
    constructor
    · rintro ⟨y, ⟨w, hw, hwy⟩, rfl⟩
      refine ⟨⟨w, hYX hw⟩, hw, ?_⟩
      change β (Θ ⟨w, hYX hw⟩) = Θ y
      rw [hβ]
      congr 1
      apply Subtype.ext
      have hwy' : x⁻¹ * w * x = (y : G) := by simpa [MulAut.conj_apply] using hwy
      rw [coe_conjAut]
      simpa using hwy'
    · rintro ⟨w, hw, rfl⟩
      refine ⟨conjAut hXx w, ⟨w, hw, ?_⟩, (hβ w).symm⟩
      rw [Subgroup.coe_subtype, coe_conjAut]
      simp
  obtain ⟨g, hgQ, hg⟩ := exists_map_oY₂_eq_conj hQ hQ₂ hle hSL₂ hO₂ hSL hperf₂ hfix hnd hsimpSL
    hsimp hcard ht0 ht1 β
  have hθYx : ((rightConjugate (W ⊔ W₂) x).subgroupOf A).map θ =
      (S₂ ⊔ S₁).map (projConj hgQ).toMonoidHom := by
    rw [map_subgroupOf_eq_map_oPsi hXA hle hΘ hYxX, hΘYx,
      ← map_oProj_oY₂ hQ hQ₂ hSL (hκX.trans hle)]
    ext z
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      have h1 : ((β w : ↥(oXt oe Q₂)) : GL ι K) ∈
          ((oY₂ oe₂).map (oKappaGL oe)).map (MulAut.conj g).toMonoidHom := by
        rw [← hg]
        exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      obtain ⟨k, hk, hkw⟩ := h1
      have hkΩ : k ∈ StatedOmega ⇑Q := hle (hκX hk)
      refine ⟨oProj ⇑Q ⟨k, hkΩ⟩, ⟨⟨k, hkΩ⟩, hk, rfl⟩, ?_⟩
      show projConj hgQ (oProj ⇑Q ⟨k, hkΩ⟩) = oPsi oe Q₂ hle (β.toMonoidHom w)
      rw [oPsi_apply, oProj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, projConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_isoConj]
      exact hkw
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      have h1 : g * (k : GL ι K) * g⁻¹ ∈ ((((oY₂ oe₂).map (oKappaGL oe)).subgroupOf
          (oXt oe Q₂)).map β.toMonoidHom).map (oXt oe Q₂).subtype := by
        rw [hg]
        exact ⟨k, hk, rfl⟩
      obtain ⟨_, ⟨w, hw, rfl⟩, hwk⟩ := h1
      refine ⟨β.toMonoidHom w, ⟨w, hw, rfl⟩, ?_⟩
      show oPsi oe Q₂ hle (β.toMonoidHom w) = projConj hgQ (oProj ⇑Q k)
      rw [oPsi_apply, oProj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, projConj_mk]
      congr 1
      apply Subtype.ext
      rw [coe_isoConj]
      exact hwk
  refine noNormalTwo_inf_centralizer_of_quot hθ hker hodd hYxA hYxperf ?_
  rw [hθYx, ← centralizer_map_mulAut]
  exact noNormalTwo_map_mulAut hNN _

end Core

end CFSG.ComponentClassification.RankTwoClassical.ORigid
