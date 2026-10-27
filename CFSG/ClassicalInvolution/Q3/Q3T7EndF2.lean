module

public import CFSG.ClassicalInvolution.Q3.Q3T7EndFDih
public import CFSG.GH74.Uniqueness.Bender.Aut
public import CFSG.GH74.Uniqueness.Bender.Sylow2Special
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.GH74.Uniqueness.Bender

open scoped commutatorElement

section Basic

variable {K : Type} [Group K] [Finite K]

theorem BenderCore.mem_of_fixes_involution {q i e : ℕ} {Q : Sylow 2 K} {t : K}
    (hc : BenderCore q i e (Q : Subgroup K) t) {v : K} (hvQ : v ∈ (Q : Subgroup K)) (hv1 : v ≠ 1)
    (σ : MulAut K) (hσ : σ v = v) : ∀ s ∈ (Q : Subgroup K), σ s ∈ (Q : Subgroup K) := by
  have hsurj : Function.Surjective σ.toMonoidHom := σ.surjective
  let Q₁ : Sylow 2 K := Sylow.mapSurjective hsurj Q
  have hQ₁ : (Q₁ : Subgroup K) = (Q : Subgroup K).map σ.toMonoidHom :=
    Sylow.coe_mapSurjective hsurj Q
  have hV : Subgroup.zpowers v ≠ ⊥ := by
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact hv1
  have hVQ : Subgroup.zpowers v ≤ (Q : Subgroup K) := (Subgroup.zpowers_le).mpr hvQ
  have hVQ₁ : Subgroup.zpowers v ≤ (Q₁ : Subgroup K) := by
    rw [Subgroup.zpowers_le, hQ₁]
    exact ⟨v, hvQ, hσ⟩
  have hQQ₁ : Q₁ = Q := hc.sylow_eq_of_ne_bot hV hVQ hVQ₁
  intro s hs
  have : σ s ∈ (Q₁ : Subgroup K) := by
    rw [hQ₁]
    exact ⟨s, hs, rfl⟩
  rwa [hQQ₁] at this

end Basic

section Unitary

variable {K : Type} [Group K] [Finite K]

theorem BenderType.fixedPointFree_of_orderThree_unitary {n e : ℕ} (h : BenderType K n 3 e)
    (Q : Sylow 2 K) {t : K} (hc : BenderCore (2 ^ n) 3 e (Q : Subgroup K) t) {σ : MulAut K}
    (hσZ : ∀ c ∈ rootCenter (Q : Subgroup K), σ c = c) (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ∉ Subgroup.map (MulAut.conj : K →* MulAut K) (Q : Subgroup K)) :
    ∀ y ∈ (Q : Subgroup K), σ y * y⁻¹ ∈ rootCenter (Q : Subgroup K) →
      y ∈ rootCenter (Q : Subgroup K) := by
  set Q' : Subgroup K := (Q : Subgroup K) with hQ'
  set Z : Subgroup K := rootCenter Q' with hZ
  have hZQ : Z ≤ Q' := rootCenter_le Q'
  have hcomm : ∀ y ∈ Q', ∀ y' ∈ Q', y * y' * y⁻¹ * y'⁻¹ ∈ Z := by
    intro y hy y' hy'
    have := Subgroup.commutator_mem_commutator hy hy'
    rw [(h.lemma_3_5_a_unitary Q).1, commutatorElement_def] at this
    exact this
  have hZsq : ∀ c ∈ Z, c * c = 1 := hc.center_sq
  have hσ3y : ∀ y : K, σ (σ (σ y)) = y := by
    intro y
    have h3 : (σ * σ * σ) y = y := by rw [← pow_three', hσ3]; rfl
    exact h3
  have CL : ∀ y ∈ Q', σ y * y⁻¹ ∈ Z → σ y = y := by
    intro y _ hz
    set c := σ y * y⁻¹ with hcdef
    have hσy : σ y = c * y := by rw [hcdef]; group
    have hσc : σ c = c := hσZ c hz
    have hσ2 : σ (σ y) = y := by
      rw [hσy, map_mul, hσc, hσy, ← mul_assoc, hZsq c hz, one_mul]
    have h3 := hσ3y y
    rw [hσ2] at h3
    exact h3
  let W : Subgroup K :=
    { carrier := {y | y ∈ Q' ∧ σ y = y}
      mul_mem' := fun {a b} ha hb => ⟨Q'.mul_mem ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨Q'.one_mem, map_one σ⟩
      inv_mem' := fun {a} ha => ⟨Q'.inv_mem ha.1, by rw [map_inv, ha.2]⟩ }
  have hZW : Z ≤ W := fun c hc' => ⟨hZQ hc', hσZ c hc'⟩
  have hWQ : W ≤ Q' := fun y hy => hy.1
  have hσmem : σ ∈ autCentralizer Z := mem_autCentralizer_iff.mpr hσZ
  have hinv : ∀ d ∈ cartan Q' t, ∀ w ∈ W, d * w * d⁻¹ ∈ W := by
    intro d hd w hw
    have hdb : d ∈ borel Q' := (Subgroup.mem_inf.mp hd).1
    have hdn : ∀ y, y ∈ Q' ↔ d * y * d⁻¹ ∈ Q' := Subgroup.mem_normalizer_iff.mp hdb
    set τ : MulAut K := (MulAut.conj d)⁻¹ * σ * MulAut.conj d with hτ
    have hτapply : ∀ y, τ y = d⁻¹ * σ (d * y * d⁻¹) * d := by
      intro y
      simp [hτ, MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, MulAut.conj_symm_apply]
    have hτZ : ∀ c ∈ Z, τ c = c := by
      intro c hc'
      rw [hτapply, hσZ _ (conj_mem_rootCenter hdb hc')]
      group
    have hτ3 : τ ^ 3 = 1 := by
      have e1 : τ = (MulAut.conj d)⁻¹ * σ * ((MulAut.conj d)⁻¹)⁻¹ := by rw [hτ]; group
      rw [e1, conj_pow, hσ3]
      group
    have hτ1 : τ ∉ Subgroup.map (MulAut.conj : K →* MulAut K) Q' := by
      rintro ⟨a, ha, haτ⟩
      apply hσ1
      refine ⟨d * a * d⁻¹, (hdn a).mp ha, ?_⟩
      have e1 : σ = MulAut.conj d * τ * (MulAut.conj d)⁻¹ := by rw [hτ]; group
      rw [e1, ← haτ]
      simp [map_mul, map_inv]
    have hτmem : τ ∈ autCentralizer Z := mem_autCentralizer_iff.mpr hτZ
    obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ :=
      h.exists_eq_mul_of_orderThree_unitary Q hσmem hτmem hσ3 hτ3 hσ1 hτ1
    have hτw : τ w = a * w * a⁻¹ := by
      rcases hb with hb | hb
      · rw [hb, MulAut.mul_apply, hw.2, MulAut.conj_apply]
      · rw [hb, MulAut.mul_apply]
        have : σ⁻¹ w = w := by
          rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
          exact hw.2.symm
        rw [this, MulAut.conj_apply]
    have hyQ : d * w * d⁻¹ ∈ Q' := (hdn w).mp hw.1
    refine ⟨hyQ, CL _ hyQ ?_⟩
    have hσy : σ (d * w * d⁻¹) = d * τ w * d⁻¹ := by rw [hτapply]; group
    have hcw : a * w * a⁻¹ * w⁻¹ ∈ Z := hcomm a ha w hw.1
    have : σ (d * w * d⁻¹) * (d * w * d⁻¹)⁻¹ = d * (a * w * a⁻¹ * w⁻¹) * d⁻¹ := by
      rw [hσy, hτw]
      group
    rw [this]
    exact conj_mem_rootCenter hdb hcw
  have hirr := h.irreducible_unitary Q hc.sq_eq_one hc.not_mem W hZW hWQ hinv
  intro y hy hfp
  have hyW : y ∈ W := ⟨hy, CL y hy hfp⟩
  rcases hirr with hW | hW
  · have : y ∈ rootCenter (Q : Subgroup K) := by
      rw [← hW]
      exact hyW
    exact this
  · exfalso
    have hfix : ∀ x ∈ Q', σ x = x := fun x hx => by
      have : x ∈ W := by
        rw [hW]
        exact hx
      exact this.2
    obtain ⟨r, hr, hσr⟩ := h.lemma_3_6_a Q σ hfix
    apply hσ1
    refine ⟨r, rootCenter_le Q' hr, ?_⟩
    ext k
    rw [MulAut.conj_apply]
    exact (hσr k).symm

end Unitary

end CFSG.GH74.Uniqueness.Bender
