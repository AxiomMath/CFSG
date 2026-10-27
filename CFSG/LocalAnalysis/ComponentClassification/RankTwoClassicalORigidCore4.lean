module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCompl
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightChoice

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoClassical.URigid (conjAut coe_conjAut)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups

section Cen

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤)

theorem noNormalTwo_centralizer_oBarTwo_sup_oBarL (hK : 4 ≤ Nat.card K)
    (hinj : Function.Injective (oProj ⇑Q))
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega ⇑Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    NoNormalTwo (centralizer ((oBarTwo oe hQ hSL ⊔ oBarL oe hQ : Subgroup _) :
      Set (StatedProj (StatedOmega ⇑Q)))) := by
  have hCle : centralizer ((oBarTwo oe hQ hSL ⊔ oBarL oe hQ : Subgroup _) :
      Set (StatedProj (StatedOmega ⇑Q))) ≤ oBarOne oe hQ hSL := by
    intro z hz
    obtain ⟨g, rfl⟩ := oProj_surjective ⇑Q z
    obtain ⟨B, hB⟩ := exists_oRhoOne_of_commute (hQ := hQ) (hSL := hSL) hcomm hsm hw₀ ht0 ht1
      (g := g)
      (fun A' => hinj (by
        rw [map_mul, map_mul]
        exact (mem_centralizer_iff.mp hz _ (mem_sup_left ⟨A', rfl⟩)).symm))
      (fun Z => hinj (by
        rw [map_mul, map_mul]
        exact (mem_centralizer_iff.mp hz _ (mem_sup_right ⟨Z, rfl⟩)).symm))
    exact ⟨B, by rw [hB]; rfl⟩
  have hleC : oBarOne oe hQ hSL ≤ centralizer ((oBarTwo oe hQ hSL ⊔ oBarL oe hQ : Subgroup _) :
      Set (StatedProj (StatedOmega ⇑Q))) := fun z hz =>
    mem_centralizer_iff.mpr fun w hw =>
      (mem_centralizer_iff.mp (oBarTwo_sup_oBarL_le_centralizer hw) z hz).symm
  intro R hR hR2 hN
  have hRW := hR.trans hCle
  have : (R.subgroupOf (oBarOne oe hQ hSL)).Normal :=
    ⟨fun n hn g => (mem_normalizer_iff.mp (hN (hleC g.2)) n).mp hn⟩
  have h2 : IsPGroup 2 ↥(R.subgroupOf (oBarOne oe hQ hSL)) :=
    hR2.of_equiv (subgroupOfEquivOfLe hRW).symm
  have hbot := eq_bot_of_normal_isPGroup_two_of_quasisimple (isQuasisimple_oBarOne hK hinj)
    (by rw [center_oBarOne_eq_bot hinj, Subgroup.card_bot]; exact odd_one) _ h2
  rw [eq_bot_iff]
  intro r hr
  have h3 : (⟨r, hRW hr⟩ : ↥(oBarOne oe hQ hSL)) ∈ R.subgroupOf (oBarOne oe hQ hSL) := hr
  rw [hbot, mem_bot] at h3
  rw [mem_bot]
  exact congrArg Subtype.val h3

end Cen

section Theta

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)} {G : Type} [Group G] {A : Subgroup G}
  {θ : ↥A →* StatedProj (StatedOmega ⇑Q)} {X : Subgroup G} (hXA : X ≤ A)
  (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q) {Θ : ↥X →* ↥(oXt oe Q₂)}
  (hΘ : ∀ x, oPsi oe Q₂ hle (Θ x) = θ (Subgroup.inclusion hXA x))
include hΘ

theorem map_theta_eq_of_levLift (hinj : Function.Injective (oProj ⇑Q)) {W : Subgroup G}
    (hWX : W ≤ X) {S : Subgroup (GL ι K)} (hS : S ≤ oXt oe Q₂)
    (hWθ : ∀ w (hw : w ∈ W), ∃ s, ∃ hs : s ∈ S, θ ⟨w, hXA (hWX hw)⟩ =
      oProj ⇑Q ⟨s, hle (hS hs)⟩)
    (hWs : ∀ s (hs : s ∈ S), ∃ w, ∃ hw : w ∈ W, θ ⟨w, hXA (hWX hw)⟩ =
      oProj ⇑Q ⟨s, hle (hS hs)⟩) :
    (W.subgroupOf X).map Θ = S.subgroupOf (oXt oe Q₂) := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hθs⟩ := hWθ x hx
    have h1 : Θ x = ⟨s, hS hs⟩ := oPsi_injective hle hinj (by rw [hΘ]; exact hθs)
    rw [mem_subgroupOf, h1]
    exact hs
  · intro hg
    obtain ⟨w, hw, hwg⟩ := hWs (g : GL ι K) hg
    refine ⟨⟨w, hWX hw⟩, hw, oPsi_injective hle hinj ?_⟩
    rw [hΘ]
    exact hwg

theorem map_subgroupOf_eq_map_oPsi {Z : Subgroup G} (hZX : Z ≤ X) :
    (Z.subgroupOf A).map θ = ((Z.subgroupOf X).map Θ).map (oPsi oe Q₂ hle) := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Θ ⟨a, hZX ha⟩, ⟨⟨a, hZX ha⟩, ha, rfl⟩, ?_⟩
    rw [hΘ]
    rfl
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨Subgroup.inclusion hXA x, hx, (hΘ x).symm⟩

end Theta

section Core

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hSL : commutator SL(2, K) = ⊤)

omit [CharP K 2] [Finite K] in
theorem map_oProj_oL₀ (hle : oL₀ oe Q₂ ≤ StatedOmega ⇑Q) :
    ((oL₀ oe Q₂).subgroupOf (StatedOmega ⇑Q)).map (oProj ⇑Q) =
      oBarTwo oe hQ hSL ⊔ oBarL oe hQ := by
  have h1 : (oRhoTwoGL oe).range ≤ StatedOmega ⇑Q := le_sup_left.trans hle
  have h2 : (StatedOmega ⇑Q₂).map (oKappaGL oe) ≤ StatedOmega ⇑Q := le_sup_right.trans hle
  rw [show oL₀ oe Q₂ = (oRhoTwoGL oe).range ⊔ (StatedOmega ⇑Q₂).map (oKappaGL oe) from rfl,
    subgroupOf_sup h1 h2, Subgroup.map_sup]
  congr 1
  · ext z
    constructor
    · rintro ⟨g, ⟨A', hA'⟩, rfl⟩
      refine ⟨A', ?_⟩
      show oProj ⇑Q (oRhoTwo oe hQ hSL A') = oProj ⇑Q g
      congr 1
      exact Subtype.ext hA'
    · rintro ⟨A', rfl⟩
      exact ⟨oRhoTwo oe hQ hSL A', ⟨A', rfl⟩, rfl⟩
  · ext z
    constructor
    · rintro ⟨g, ⟨Y, hY, hYg⟩, rfl⟩
      refine ⟨⟨Y, hY⟩, ?_⟩
      show oProj ⇑Q (oKappa oe hQ ⟨Y, hY⟩) = oProj ⇑Q g
      congr 1
      exact Subtype.ext hYg
    · rintro ⟨Y, rfl⟩
      exact ⟨oKappa oe hQ Y, ⟨Y, Y.2, rfl⟩, rfl⟩

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {θ : ↥A →* StatedProj (StatedOmega ⇑Q)}

theorem rigidCore_orth_four (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤) [Nonempty ι₂]
    (hnd : Q₂.polarBilin.Nondegenerate)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂)) (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K)))
    (hK : 4 ≤ Nat.card K)
    (hcomm : ∀ Y : Matrix ι₂ ι₂ K,
      (∀ Z ∈ StatedOmega ⇑Q₂, Y * (Z : Matrix ι₂ ι₂ K) = (Z : Matrix ι₂ ι₂ K) * Y) →
        ∃ d : K, Y = d • 1)
    (hsm : ∀ (d : K) w, Q₂ (d • w) = d * d * Q₂ w) {w₀ : ι₂ → K} (hw₀ : Q₂ w₀ ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (hinj : Function.Injective (oProj ⇑Q))
    (hθ : Function.Surjective θ) (hker : θ.ker = center ↥A) (hodd : Odd (Nat.card (center ↥A)))
    {p : G} (hpA : p ∈ A) (hp2 : p ^ 2 = 1)
    (hθp : θ ⟨p, hpA⟩ = oProj ⇑Q (oRhoOne oe hQ hSL (slTr 1))) :
    RigidCore A p (levLift θ (oBarTwo oe hQ hSL) ⊔ levLift θ (oBarL oe hQ)) := by
  have hle := oXt_le_statedOmega hQ hSL ht0 ht1
  obtain ⟨Θ, hΘs, hΘ⟩ := exists_theta_oXt hQ hSL hperf₂ hnd ht0 ht1 hle hinj hθ hker hodd hpA
    hp2 hθp
  have hXA := perfectCore_inf_le A p
  have hWperf := commutator_levLift hker hθ
    (commutator_oBarTwo (oe := oe) (hQ := hQ) (hSL := hSL))
  have hW₀perf := commutator_levLift hker hθ (commutator_oBarL (oe := oe) (hQ := hQ) hperf₂)
  set W := levLift θ (oBarTwo oe hQ hSL) with hW
  set W₀ := levLift θ (oBarL oe hQ) with hW₀
  have hYperf : ⁅W ⊔ W₀, W ⊔ W₀⁆ = W ⊔ W₀ := by
    refine le_antisymm (commutator_le_self _) (sup_le ?_ ?_)
    · conv_lhs => rw [← hWperf]
      exact commutator_mono le_sup_left le_sup_left
    · conv_lhs => rw [← hW₀perf]
      exact commutator_mono le_sup_right le_sup_right
  have hM₀ : θ ⟨p, hpA⟩ ∈ oBarOne oe hQ hSL := by
    rw [hθp]
    exact ⟨slTr 1, rfl⟩
  have hWp : W ≤ centralizer ({p} : Set G) :=
    levLift_le_centralizer hker hpA fun s hs => oBarOne_commute_oBarTwo hM₀ hs
  have hW₀p : W₀ ≤ centralizer ({p} : Set G) :=
    levLift_le_centralizer hker hpA fun s hs => oBarOne_commute_oBarL hM₀ hs
  have hYX : W ⊔ W₀ ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    CFSG.Quasithin.le_perfectCore_of_perfect
      (le_inf (sup_le levLift_le levLift_le) (sup_le hWp hW₀p)) hYperf
  have hWX := le_sup_left.trans hYX
  have hW₀X := le_sup_right.trans hYX
  have hρX : (oRhoTwoGL oe).range ≤ oXt oe Q₂ := le_sup_left.trans le_sup_right
  have hκX : (StatedOmega ⇑Q₂).map (oKappaGL oe) ≤ oXt oe Q₂ := le_sup_right.trans le_sup_right
  have hΘW : (W.subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      (oRhoTwoGL oe).range.subgroupOf (oXt oe Q₂) := by
    refine map_theta_eq_of_levLift hXA hle hΘ hinj hWX hρX ?_ ?_
    · intro w hw
      obtain ⟨A', hA'⟩ := theta_mem_of_mem_levLift hw
      exact ⟨_, ⟨A', rfl⟩, hA'.symm⟩
    · rintro _ ⟨A', rfl⟩
      obtain ⟨w, hw, hwθ⟩ := exists_mem_levLift hθ
        (commutator_oBarTwo (oe := oe) (hQ := hQ) (hSL := hSL))
        (⟨A', rfl⟩ : (oProj ⇑Q).comp (oRhoTwo oe hQ hSL) A' ∈ oBarTwo oe hQ hSL)
      exact ⟨w, hw, hwθ⟩
  have hΘW₀ : (W₀.subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      ((StatedOmega ⇑Q₂).map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := by
    refine map_theta_eq_of_levLift hXA hle hΘ hinj hW₀X hκX ?_ ?_
    · intro w hw
      obtain ⟨Y, hY⟩ := theta_mem_of_mem_levLift hw
      exact ⟨_, ⟨Y, Y.2, rfl⟩, hY.symm⟩
    · rintro _ ⟨Y, hY, rfl⟩
      obtain ⟨w, hw, hwθ⟩ := exists_mem_levLift hθ (commutator_oBarL (oe := oe) (hQ := hQ) hperf₂)
        (⟨⟨Y, hY⟩, rfl⟩ : (oProj ⇑Q).comp (oKappa oe hQ) ⟨Y, hY⟩ ∈ oBarL oe hQ)
      exact ⟨w, hw, hwθ⟩
  have hΘY : ((W ⊔ W₀).subgroupOf (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
      (oL₀ oe Q₂).subgroupOf (oXt oe Q₂) := by
    rw [subgroupOf_sup hWX hW₀X, Subgroup.map_sup, hΘW, hΘW₀]
    exact (subgroupOf_sup hρX hκX).symm
  intro x hXx _ _
  have hYxX : rightConjugate (W ⊔ W₀) x ≤ perfectCore (A ⊓ centralizer ({p} : Set G)) :=
    (Subgroup.map_mono hYX).trans hXx.le
  have hYxA : rightConjugate (W ⊔ W₀) x ≤ A := hYxX.trans hXA
  have hYxperf : ⁅rightConjugate (W ⊔ W₀) x, rightConjugate (W ⊔ W₀) x⁆ =
      rightConjugate (W ⊔ W₀) x := by
    rw [rightConjugate, ← Subgroup.map_commutator, hYperf]
  obtain ⟨β, hβ⟩ := exists_beta_oXt hQ hnd hle hker hodd hΘs hΘ hXx
  have hΘYx : ((rightConjugate (W ⊔ W₀) x).subgroupOf
      (perfectCore (A ⊓ centralizer ({p} : Set G)))).map Θ =
        ((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map β.toMonoidHom := by
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
  obtain ⟨y, hyQ, hy⟩ := exists_map_oL₀_eq_conj hQ hle hSL₂ hO₂ hSL hperf₂ hfix ht0 ht1 β
  have hyΩ : y ∈ StatedOmega ⇑Q := hle (mem_sup_left hyQ)
  have hθYx : ((rightConjugate (W ⊔ W₀) x).subgroupOf A).map θ =
      (oBarTwo oe hQ hSL ⊔ oBarL oe hQ).map
        (MulAut.conj (oProj ⇑Q ⟨y, hyΩ⟩)⁻¹).toMonoidHom := by
    rw [map_subgroupOf_eq_map_oPsi hXA hle hΘ hYxX, hΘYx,
      ← map_oProj_oL₀ hQ hSL (le_sup_right.trans hle)]
    ext z
    constructor
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      have h1 : y * ((β l : ↥(oXt oe Q₂)) : GL ι K) * y⁻¹ ∈ oL₀ oe Q₂ := by
        rw [← hy]
        exact ⟨_, ⟨β l, ⟨l, hl, rfl⟩, rfl⟩, rfl⟩
      refine ⟨oProj ⇑Q ⟨_, hle (mem_sup_right h1)⟩, ⟨⟨_, hle (mem_sup_right h1)⟩, h1, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, oPsi_apply, ← map_inv,
        ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom]
      group
    · rintro ⟨_, ⟨l, hl, rfl⟩, rfl⟩
      have h1 : (l : GL ι K) ∈ ((((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map β.toMonoidHom).map
          (oXt oe Q₂).subtype).map (MulAut.conj y).toMonoidHom := by
        rw [hy]
        exact hl
      obtain ⟨_, ⟨_, ⟨l', hl', rfl⟩, rfl⟩, hgl⟩ := h1
      refine ⟨β l', ⟨l', hl', rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, oPsi_apply, ← map_inv,
        ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [← hgl]
      simp only [Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  refine noNormalTwo_inf_centralizer_of_quot hθ hker hodd hYxA hYxperf ?_
  rw [hθYx, ← centralizer_map_mulAut]
  exact noNormalTwo_map_mulAut
    (noNormalTwo_centralizer_oBarTwo_sup_oBarL hQ hSL hK hinj hcomm hsm hw₀ ht0 ht1) _

end Core

end CFSG.ComponentClassification.RankTwoClassical.ORigid
