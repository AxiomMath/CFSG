module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCompl
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidHyp

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups

section Entry

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}

omit [CharP K 2] [Fintype ι₂] [DecidableEq ι₂] in
theorem qE_apply_ox_oy (Q₂ : QuadraticForm K (ι₂ → K)) (u : Fin 2 → ι₂ → K) (c : K) :
    qE oe Q₂ u c (ox oe 1) (oy oe 0) = c := by
  rw [qE_apply, qE_mulVec_ox, qAlpha, vU_single_oy]
  simp

omit [CharP K 2] in
theorem conj_oKappaGL_apply_ox_oy (Y : GL ι₂ K) (g : Matrix ι ι K) :
    (((oKappaGL oe Y : GL ι K) : Matrix ι ι K) * g *
      (((oKappaGL oe Y)⁻¹ : GL ι K) : Matrix ι ι K)) (ox oe 1) (oy oe 0) =
        g (ox oe 1) (oy oe 0) := by
  have hcol : ∀ (P : Matrix ι ι K) (i j : ι), P i j = (P *ᵥ Pi.single j 1) i := fun P i j => by
    rw [mulVec_single_one, col_apply]
  have hN : (((oKappaGL oe Y)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Pi.single (oy oe 0) 1 =
      Pi.single (oy oe 0) 1 := by
    rw [← map_inv, coe_oKappaGL, single_oy_eq, oblk_mulVec_eq, one_mulVec]
    refine oVec_ext oe (fun a => ?_) (fun b => ?_)
    · simp only [oVec_apply_inl, Pi.zero_apply]
      exact congrFun (mulVec_zero _) a
    · simp only [oVec_apply_inr]
  have e1 := hcol (((oKappaGL oe Y : GL ι K) : Matrix ι ι K) * g *
    (((oKappaGL oe Y)⁻¹ : GL ι K) : Matrix ι ι K)) (ox oe 1) (oy oe 0)
  have e2 := hcol g (ox oe 1) (oy oe 0)
  rw [e1, e2, ← mulVec_mulVec, ← mulVec_mulVec, hN, coe_oKappaGL, oblk_mulVec_inr, one_mulVec]

variable {Q : QuadraticForm K (ι → K)} {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem conj_oKappaGL_qEGL {Y : GL ι₂ K} (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (u : Fin 2 → ι₂ → K) (c : K) :
    oKappaGL oe Y * qEGL oe Q₂ u c * (oKappaGL oe Y)⁻¹ =
      qEGL oe Q₂ (fun t => (Y : Matrix ι₂ ι₂ K) *ᵥ u t) c := by
  obtain ⟨c', hc'⟩ := conj_qE_kappa hQ hY u c
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (ox oe 1) (oy oe 0)) hc'
  simp only [Units.val_mul, coe_qEGL] at h1
  rw [conj_oKappaGL_apply_ox_oy, qE_apply_ox_oy, qE_apply_ox_oy] at h1
  rw [hc', h1]

end Entry

section Card

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem qEGL_mem_centralizer_iff {H : Subgroup (GL ι₂ K)}
    (hH : ∀ Y ∈ H, ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) (u : Fin 2 → ι₂ → K) (c : K) :
    qEGL oe Q₂ u c ∈ centralizer ((H.map (oKappaGL oe) : Subgroup (GL ι K)) : Set (GL ι K)) ↔
      ∀ t, u t ∈ fixVec H := by
  constructor
  · intro hq t Y hY
    have h1 := mem_centralizer_iff.mp hq _ ⟨Y, hY, rfl⟩
    have h2 : oKappaGL oe Y * qEGL oe Q₂ u c * (oKappaGL oe Y)⁻¹ = qEGL oe Q₂ u c := by
      rw [h1, mul_inv_cancel_right]
    rw [conj_oKappaGL_qEGL hQ (hH Y hY)] at h2
    exact congrFun (eq_of_qEGL_eq oe Q₂ h2) t
  · intro hu
    rw [mem_centralizer_iff]
    rintro _ ⟨Y, hY, rfl⟩
    have h2 := conj_oKappaGL_qEGL hQ (hH Y hY) u c
    have hYu : (fun t => (Y : Matrix ι₂ ι₂ K) *ᵥ u t) = u := funext fun t => hu t Y hY
    rw [hYu] at h2
    calc oKappaGL oe Y * qEGL oe Q₂ u c =
        oKappaGL oe Y * qEGL oe Q₂ u c * (oKappaGL oe Y)⁻¹ * oKappaGL oe Y := by group
      _ = qEGL oe Q₂ u c * oKappaGL oe Y := by rw [h2]

omit hQ [Fintype ι₂] [DecidableEq ι₂] in
theorem eq_of_qEGL_eq_right {u : Fin 2 → ι₂ → K} {c c' : K}
    (h : qEGL oe Q₂ u c = qEGL oe Q₂ u c') : c = c' := by
  have h1 := congrArg (fun g : GL ι K => (g : Matrix ι ι K) (ox oe 1) (oy oe 0)) h
  simpa only [coe_qEGL, qE_apply_ox_oy] using h1

theorem card_oQE_inf_centralizer {H : Subgroup (GL ι₂ K)}
    (hH : ∀ Y ∈ H, ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w) :
    Nat.card ↥(oQE oe Q₂ ⊓
      centralizer ((H.map (oKappaGL oe) : Subgroup (GL ι K)) : Set (GL ι K))) =
        Nat.card ↥(fixVec H) ^ 2 * Nat.card K := by
  set Z := oQE oe Q₂ ⊓ centralizer ((H.map (oKappaGL oe) : Subgroup (GL ι K)) : Set (GL ι K))
  let F : (Fin 2 → ↥(fixVec H)) × K → ↥Z := fun p =>
    ⟨qEGL oe Q₂ (fun t => (p.1 t : ι₂ → K)) p.2, qEGL_mem_oQE oe Q₂ _ _,
      (qEGL_mem_centralizer_iff hQ hH _ _).mpr fun t => (p.1 t).2⟩
  have hF : Function.Bijective F := by
    refine ⟨fun p p' hpp' => ?_, fun z => ?_⟩
    · have h1 := congrArg Subtype.val hpp'
      change qEGL oe Q₂ (fun t => (p.1 t : ι₂ → K)) p.2 =
        qEGL oe Q₂ (fun t => (p'.1 t : ι₂ → K)) p'.2 at h1
      have hu := eq_of_qEGL_eq oe Q₂ h1
      have hc : p.2 = p'.2 := by
        refine eq_of_qEGL_eq_right (oe := oe) (Q₂ := Q₂) (u := fun t => (p.1 t : ι₂ → K)) ?_
        rw [h1, hu]
      exact Prod.ext (funext fun t => Subtype.ext (congrFun hu t)) hc
    · obtain ⟨g, hgQ, hgC⟩ := z
      obtain ⟨u, c, rfl⟩ := (mem_oQE oe Q₂).mp hgQ
      have hu := (qEGL_mem_centralizer_iff hQ hH u c).mp hgC
      exact ⟨(fun t => ⟨u t, hu t⟩, c), Subtype.ext rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod, Nat.card_fun, Nat.card_fin]

end Card

section Transfer

variable {K : Type} [Field K] [CharP K 2] [Finite K] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem finrank_fixVec_eq_of_map (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K))) (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂))
    (β : MulAut ↥(oXt oe Q₂)) {H H' : Subgroup (GL ι₂ K)} (hHΩ : H ≤ StatedOmega ⇑Q₂)
    (hH'Ω : H' ≤ StatedOmega ⇑Q₂)
    (hβ : ((H.map (oKappaGL oe)).subgroupOf (oXt oe Q₂)).map β.toMonoidHom =
      (H'.map (oKappaGL oe)).subgroupOf (oXt oe Q₂)) :
    Module.finrank K (fixVec H) = Module.finrank K (fixVec H') := by
  have hκX : ∀ {H₀ : Subgroup (GL ι₂ K)}, H₀ ≤ StatedOmega ⇑Q₂ →
      H₀.map (oKappaGL oe) ≤ oXt oe Q₂ := fun h₀ =>
    (Subgroup.map_mono h₀).trans (le_sup_right.trans le_sup_right)
  have hiso : ∀ {H₀ : Subgroup (GL ι₂ K)}, H₀ ≤ StatedOmega ⇑Q₂ →
      ∀ Y ∈ H₀, ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w :=
    fun h₀ Y hY => quad_mulVec_of_mem_statedOmega (h₀ hY)
  have hsub : ∀ (γ : MulAut ↥(oXt oe Q₂)) {H₁ H₂ : Subgroup (GL ι₂ K)},
      H₁ ≤ StatedOmega ⇑Q₂ → H₂ ≤ StatedOmega ⇑Q₂ →
      ((H₁.map (oKappaGL oe)).subgroupOf (oXt oe Q₂)).map γ.toMonoidHom =
        (H₂.map (oKappaGL oe)).subgroupOf (oXt oe Q₂) →
      Nat.card ↥(fixVec H₁) ^ 2 * Nat.card K ≤ Nat.card ↥(fixVec H₂) ^ 2 * Nat.card K := by
    intro γ H₁ H₂ h₁ h₂ hγ
    have hγQ := map_oQE hQ hle hSL₂ hO₂ γ
    rw [← card_oQE_inf_centralizer hQ (hiso h₁), ← card_oQE_inf_centralizer hQ (hiso h₂)]
    have hmem : ∀ x : ↥(oQE oe Q₂ ⊓ centralizer ((H₁.map (oKappaGL oe) : Subgroup (GL ι K)) :
        Set (GL ι K))), ((γ ⟨x, mem_sup_left x.2.1⟩ : ↥(oXt oe Q₂)) : GL ι K) ∈
          oQE oe Q₂ ⊓ centralizer ((H₂.map (oKappaGL oe) : Subgroup (GL ι K)) :
            Set (GL ι K)) := by
      intro x
      obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp x.2
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : γ ⟨x, mem_sup_left x.2.1⟩ ∈ (oQE oe Q₂).subgroupOf (oXt oe Q₂) := by
          rw [← hγQ]
          exact ⟨_, hxQ, rfl⟩
        exact h1
      · rw [mem_centralizer_iff]
        intro k hk
        have hk' : (⟨k, hκX h₂ hk⟩ : ↥(oXt oe Q₂)) ∈
            (H₂.map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := hk
        rw [← hγ] at hk'
        obtain ⟨k₁, hk₁, hk₁k⟩ := hk'
        have hc : k₁ * ⟨x, mem_sup_left x.2.1⟩ = ⟨x, mem_sup_left x.2.1⟩ * k₁ :=
          Subtype.ext (mem_centralizer_iff.mp hxC _ hk₁)
        have h2 := congrArg (fun z : ↥(oXt oe Q₂) => ((γ z : ↥(oXt oe Q₂)) : GL ι K)) hc
        simp only [map_mul] at h2
        rw [show k = ((γ k₁ : ↥(oXt oe Q₂)) : GL ι K) from (congrArg Subtype.val hk₁k).symm]
        simpa only [Subgroup.coe_mul] using h2
    refine Nat.card_le_card_of_injective (fun x => ⟨_, hmem x⟩) fun x y hxy => ?_
    have h1 := congrArg Subtype.val hxy
    have h2 : (⟨(x : GL ι K), mem_sup_left x.2.1⟩ : ↥(oXt oe Q₂)) = ⟨(y : GL ι K),
        mem_sup_left y.2.1⟩ := γ.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hβ' : ((H'.map (oKappaGL oe)).subgroupOf (oXt oe Q₂)).map β.symm.toMonoidHom =
      (H.map (oKappaGL oe)).subgroupOf (oXt oe Q₂) := by
    rw [← hβ, Subgroup.map_map]
    convert Subgroup.map_id _
    ext z
    simp
  have hcard := le_antisymm (hsub β hHΩ hH'Ω hβ) (hsub β.symm hH'Ω hHΩ hβ')
  have hK : 0 < Nat.card K := Nat.card_pos
  have h2 : Nat.card ↥(fixVec H) = Nat.card ↥(fixVec H') :=
    Nat.pow_left_injective (by norm_num) (Nat.eq_of_mul_eq_mul_right hK hcard)
  rw [Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixVec H)),
    Module.natCard_eq_pow_finrank (K := K) (V := ↥(fixVec H'))] at h2
  exact Nat.pow_right_injective (Finite.one_lt_card (α := K)) h2

end Transfer

end CFSG.ComponentClassification.RankTwoClassical.ORigid
