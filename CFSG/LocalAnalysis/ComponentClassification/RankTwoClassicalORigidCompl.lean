module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidChar

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement

section Central

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q₂ : QuadraticForm K (ι₂ → K)}

theorem qEGL_zero_commute_of_mem_oXt (a : K) {g : GL ι K} (hg : g ∈ oXt oe Q₂) :
    qEGL oe Q₂ 0 a * g = g * qEGL oe Q₂ 0 a := by
  suffices h : oXt oe Q₂ ≤ centralizer ({qEGL oe Q₂ 0 a} : Set (GL ι K)) from
    (mem_centralizer_singleton_iff.mp (h hg)).symm
  refine sup_le ?_ (sup_le ?_ ?_)
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, ← commutatorElement_eq_one_iff_mul_comm, qE_commutator]
    apply Units.ext
    rw [coe_qEGL, Units.val_one, ← qE_zero oe Q₂]
    congr 1
    simp
  · rintro _ ⟨A, rfl⟩
    rw [mem_centralizer_singleton_iff, qEGL_zero]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_oRhoTwoGL, coe_oRhoOneGL, oblk_mul, oblk_mul,
      rhoOne_mul_rhoTwo]
  · rintro _ ⟨Y, -, rfl⟩
    rw [mem_centralizer_singleton_iff, qEGL_zero]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_oKappaGL, coe_oRhoOneGL, oblk_mul, oblk_mul]
    simp only [Matrix.mul_one, Matrix.one_mul]

end Central

section Fix

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

theorem conj_qE_rhoTwo (A : SL(2, K)) (u : Fin 2 → ι₂ → K) (c : K) :
    ∃ c' : K, oRhoTwoGL oe A * qEGL oe Q₂ u c * (oRhoTwoGL oe A)⁻¹ =
      qEGL oe Q₂ (fun t => ∑ r, (A : Matrix (Fin 2) (Fin 2) K) t r • u r) c' := by
  obtain ⟨c', hc'⟩ := conj_qE_levi hQ (Y := 1) (fun w => by simp) A u c
  refine ⟨c', ?_⟩
  simpa only [map_one, one_mul, Units.val_one, one_mulVec] using hc'

theorem conj_qE_kappa {Y : GL ι₂ K} (hY : ∀ w, Q₂ ((Y : Matrix ι₂ ι₂ K) *ᵥ w) = Q₂ w)
    (u : Fin 2 → ι₂ → K) (c : K) :
    ∃ c' : K, oKappaGL oe Y * qEGL oe Q₂ u c * (oKappaGL oe Y)⁻¹ =
      qEGL oe Q₂ (fun t => (Y : Matrix ι₂ ι₂ K) *ᵥ u t) c' := by
  obtain ⟨c', hc'⟩ := conj_qE_levi hQ hY 1 u c
  refine ⟨c', ?_⟩
  have h1 : (fun t => (Y : Matrix ι₂ ι₂ K) *ᵥ
      ∑ r, ((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) t r • u r) =
        fun t => (Y : Matrix ι₂ ι₂ K) *ᵥ u t := by
    funext t
    congr 1
    fin_cases t <;> simp [Matrix.one_apply]
  rw [h1, map_one, mul_one] at hc'
  exact hc'

theorem eq_zero_of_commute_torus {t : K} (ht1 : t ≠ 1) {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) {u : Fin 2 → ι₂ → K} {c : K}
    (h : oRhoTwoGL oe A * qEGL oe Q₂ u c = qEGL oe Q₂ u c * oRhoTwoGL oe A) : u = 0 := by
  obtain ⟨c', hc'⟩ := conj_qE_rhoTwo hQ A u c
  rw [h, mul_inv_cancel_right] at hc'
  have h1 := eq_of_qEGL_eq oe Q₂ hc'
  have ht1' : t⁻¹ ≠ 1 := fun h' => ht1 (inv_eq_one.mp h')
  have hsub : ∀ {s : K}, s ≠ 1 → ∀ w : ι₂ → K, w = s • w → w = 0 := fun {s} hs w hw => by
    have h2 : (s - 1) • w = 0 := by rw [sub_smul, one_smul, ← hw, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hs)
  have e00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = t := by rw [hA]; rfl
  have e01 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := by rw [hA]; rfl
  have e10 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := by rw [hA]; rfl
  have e11 : (A : Matrix (Fin 2) (Fin 2) K) 1 1 = t⁻¹ := by rw [hA]; rfl
  have hu0 : u 0 = 0 := by
    have h2 : u 0 = ∑ r, (A : Matrix (Fin 2) (Fin 2) K) 0 r • u r := congrFun h1 0
    rw [Fin.sum_univ_two, e00, e01, zero_smul, add_zero] at h2
    exact hsub ht1 _ h2
  have hu1 : u 1 = 0 := by
    have h2 : u 1 = ∑ r, (A : Matrix (Fin 2) (Fin 2) K) 1 r • u r := congrFun h1 1
    rw [Fin.sum_univ_two, e10, e11, zero_smul, zero_add] at h2
    exact hsub ht1' _ h2
  funext r
  fin_cases r
  · exact hu0
  · exact hu1

theorem eq_zero_of_commute_kappa
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    {u : Fin 2 → ι₂ → K} {c : K}
    (h : ∀ Y ∈ StatedOmega ⇑Q₂,
      oKappaGL oe Y * qEGL oe Q₂ u c = qEGL oe Q₂ u c * oKappaGL oe Y) :
    u = 0 := by
  funext r
  refine hfix _ fun Y hY => ?_
  obtain ⟨c', hc'⟩ := conj_qE_kappa hQ (quad_mulVec_of_mem_statedOmega hY) u c
  rw [h Y hY, mul_inv_cancel_right] at hc'
  exact (congrFun (eq_of_qEGL_eq oe Q₂ hc') r).symm

theorem exists_conj_mem_torus {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) {h₀ : GL ι K}
    (hh₀ : (oRhoTwoGL oe A)⁻¹ * h₀ ∈ oQE oe Q₂) :
    ∃ x ∈ oQE oe Q₂, ∃ e : K, x * h₀ * x⁻¹ = oRhoTwoGL oe A * qEGL oe Q₂ 0 e := by
  obtain ⟨u, c, hqu⟩ := (mem_oQE oe Q₂).mp hh₀
  have hti0 : t⁻¹ ≠ 0 := inv_ne_zero ht0
  have hti1 : t⁻¹ ≠ 1 := fun h' => ht1 (inv_eq_one.mp h')
  obtain ⟨A', u', e, hA', hqc⟩ := exists_qE_eq_commutator hQ hti0 hti1 u c
  have hAA' : A' = A⁻¹ := by
    apply Subtype.ext
    rw [hA', Matrix.SpecialLinearGroup.coe_inv, hA, adjugate_fin_two_of]
    simp
  rw [hAA', map_inv, ← qEGL_zero oe Q₂, hqu, commutatorElement_def, inv_inv] at hqc
  have hc := qEGL_zero_commute_of_mem_oXt (oe := oe) (Q₂ := Q₂) e
    (mem_sup_left (qEGL_mem_oQE oe Q₂ u' 0))
  refine ⟨(qEGL oe Q₂ u' 0)⁻¹, inv_mem (qEGL_mem_oQE oe Q₂ u' 0), e, ?_⟩
  have hh : h₀ = qEGL oe Q₂ u' 0 * oRhoTwoGL oe A * (qEGL oe Q₂ u' 0)⁻¹ * qEGL oe Q₂ 0 e := by
    calc h₀ = oRhoTwoGL oe A * ((oRhoTwoGL oe A)⁻¹ * h₀) := by group
      _ = _ := by rw [hqc]; group
  rw [hh]
  calc (qEGL oe Q₂ u' 0)⁻¹ * (qEGL oe Q₂ u' 0 * oRhoTwoGL oe A * (qEGL oe Q₂ u' 0)⁻¹ *
        qEGL oe Q₂ 0 e) * (qEGL oe Q₂ u' 0)⁻¹⁻¹ =
      oRhoTwoGL oe A * ((qEGL oe Q₂ u' 0)⁻¹ * (qEGL oe Q₂ 0 e * qEGL oe Q₂ u' 0)) := by group
    _ = oRhoTwoGL oe A * qEGL oe Q₂ 0 e := by rw [hc]; group

end Fix

section Compl

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {Q : QuadraticForm K (ι → K)}
  {Q₂ : QuadraticForm K (ι₂ → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
include hQ

omit hQ in
theorem le_of_mul_qEGL_zero_mem {B H : Subgroup (GL ι K)} (hB : ⁅B, B⁆ = B)
    (hBX : B ≤ oXt oe Q₂) (h : ∀ b ∈ B, ∃ a : K, b * qEGL oe Q₂ 0 a ∈ H) : B ≤ H := by
  rw [← hB, commutator_le]
  intro b₁ hb₁ b₂ hb₂
  obtain ⟨a₁, ha₁⟩ := h b₁ hb₁
  obtain ⟨a₂, ha₂⟩ := h b₂ hb₂
  have h1 : ⁅b₁ * qEGL oe Q₂ 0 a₁, b₂ * qEGL oe Q₂ 0 a₂⁆ ∈ H := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha₁ ha₂) (inv_mem ha₁)) (inv_mem ha₂)
  rwa [commutatorElement_mul_mul_of_commute' (qEGL_zero_commute_of_mem_oXt a₁ (hBX hb₂))
    (qEGL_zero_commute_of_mem_oXt a₂ (hBX hb₁))
    (qEGL_zero_commute_of_mem_oXt a₁ (mem_sup_left (qEGL_mem_oQE oe Q₂ 0 a₂)))] at h1

theorem eq_oL₀_of_mem (hSL : commutator SL(2, K) = ⊤)
    (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    {t : K} (ht1 : t ≠ 1) {A : SL(2, K)}
    (hA : (A : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹]) {H : Subgroup (GL ι K)}
    (hH : H ≤ oXt oe Q₂) (hHQ : ∀ g ∈ H, g ∈ oQE oe Q₂ → g = 1)
    (hcov : ∀ l ∈ oL₀ oe Q₂, ∃ h ∈ H, l⁻¹ * h ∈ oQE oe Q₂) {e : K}
    (hd : oRhoTwoGL oe A * qEGL oe Q₂ 0 e ∈ H) : H = oL₀ oe Q₂ := by
  have hQX : oQE oe Q₂ ≤ oXt oe Q₂ := le_sup_left
  have hLX : oL₀ oe Q₂ ≤ oXt oe Q₂ := le_sup_right
  have hN := oXt_le_normalizer_oQE (oe := oe) (Q₂ := Q₂) hQ
  have hcomm : ∀ {g₁ g₂ l₁ l₂ : GL ι K}, g₁ ∈ H → g₂ ∈ H → l₁ ∈ oL₀ oe Q₂ →
      l₂ ∈ oL₀ oe Q₂ → l₁⁻¹ * g₁ ∈ oQE oe Q₂ → l₂⁻¹ * g₂ ∈ oQE oe Q₂ → l₁ * l₂ = l₂ * l₁ →
        g₁ * g₂ = g₂ * g₁ := by
    intro g₁ g₂ l₁ l₂ hg₁ hg₂ hl₁ hl₂ h₁ h₂ hc
    have h1 := commutatorElement_mem_of_mem_coset hQX hN (hH hg₁) (hH hg₂) (hLX hl₁) (hLX hl₂)
      h₁ h₂ hc
    have h2 : ⁅g₁, g₂⁆ ∈ H := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg₁ hg₂) (inv_mem hg₁)) (inv_mem hg₂)
    exact commutatorElement_eq_one_iff_mul_comm.mp (hHQ _ h2 h1)
  have hdL : oRhoTwoGL oe A ∈ oL₀ oe Q₂ := mem_sup_left ⟨A, rfl⟩
  have hdq : (oRhoTwoGL oe A)⁻¹ * (oRhoTwoGL oe A * qEGL oe Q₂ 0 e) ∈ oQE oe Q₂ := by
    rw [inv_mul_cancel_left]
    exact qEGL_mem_oQE oe Q₂ 0 e
  have hB : (StatedOmega ⇑Q₂).map (oKappaGL oe) ≤ H := by
    have hperfB : ⁅(StatedOmega ⇑Q₂).map (oKappaGL oe), (StatedOmega ⇑Q₂).map (oKappaGL oe)⁆ =
        (StatedOmega ⇑Q₂).map (oKappaGL oe) := by
      have h1 : (StatedOmega ⇑Q₂).map (oKappaGL oe) =
          ((oKappaGL oe).comp (StatedOmega ⇑Q₂).subtype).range := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype]
      rw [h1]
      exact commutator_range_of_perfect _ hperf₂
    refine le_of_mul_qEGL_zero_mem hperfB (le_sup_right.trans hLX) fun b hb => ?_
    obtain ⟨Y, hY, rfl⟩ := hb
    have hbL : oKappaGL oe Y ∈ oL₀ oe Q₂ := mem_sup_right ⟨Y, hY, rfl⟩
    obtain ⟨g, hg, hgq⟩ := hcov _ hbL
    obtain ⟨u, c, hu⟩ := (mem_oQE oe Q₂).mp hgq
    have hgd := hcomm hg hd hbL hdL hgq hdq (commute_oKappaGL_oRhoTwoGL Y A).eq
    have hq₀g := qEGL_zero_commute_of_mem_oXt (oe := oe) (Q₂ := Q₂) e (hH hg)
    have hgd' : g * oRhoTwoGL oe A = oRhoTwoGL oe A * g := by
      apply mul_right_cancel (b := qEGL oe Q₂ 0 e)
      calc g * oRhoTwoGL oe A * qEGL oe Q₂ 0 e = g * (oRhoTwoGL oe A * qEGL oe Q₂ 0 e) := by
            group
        _ = oRhoTwoGL oe A * qEGL oe Q₂ 0 e * g := hgd
        _ = oRhoTwoGL oe A * g * qEGL oe Q₂ 0 e := by rw [mul_assoc, hq₀g, ← mul_assoc]
    have hkd : (oKappaGL oe Y)⁻¹ * oRhoTwoGL oe A = oRhoTwoGL oe A * (oKappaGL oe Y)⁻¹ :=
      (commute_oKappaGL_oRhoTwoGL (oe := oe) Y A).inv_left.eq
    have hqd : oRhoTwoGL oe A * qEGL oe Q₂ u c = qEGL oe Q₂ u c * oRhoTwoGL oe A := by
      rw [hu]
      calc oRhoTwoGL oe A * ((oKappaGL oe Y)⁻¹ * g) =
          oRhoTwoGL oe A * (oKappaGL oe Y)⁻¹ * g := by group
        _ = (oKappaGL oe Y)⁻¹ * oRhoTwoGL oe A * g := by rw [hkd]
        _ = (oKappaGL oe Y)⁻¹ * (g * oRhoTwoGL oe A) := by rw [mul_assoc, ← hgd']
        _ = (oKappaGL oe Y)⁻¹ * g * oRhoTwoGL oe A := by group
    have hu0 := eq_zero_of_commute_torus hQ ht1 hA hqd
    refine ⟨c, ?_⟩
    have hg' : g = oKappaGL oe Y * qEGL oe Q₂ u c := by rw [hu, mul_inv_cancel_left]
    rw [hg', hu0] at hg
    exact hg
  have hAH : (oRhoTwoGL oe).range ≤ H := by
    refine le_of_mul_qEGL_zero_mem (commutator_range_of_perfect _ hSL)
      (le_sup_left.trans hLX) fun a ha => ?_
    obtain ⟨A₁, rfl⟩ := ha
    have haL : oRhoTwoGL oe A₁ ∈ oL₀ oe Q₂ := mem_sup_left ⟨A₁, rfl⟩
    obtain ⟨g, hg, hgq⟩ := hcov _ haL
    obtain ⟨u, c, hu⟩ := (mem_oQE oe Q₂).mp hgq
    have hqb : ∀ Y ∈ StatedOmega ⇑Q₂,
        oKappaGL oe Y * qEGL oe Q₂ u c = qEGL oe Q₂ u c * oKappaGL oe Y := by
      intro Y hY
      have hbH : oKappaGL oe Y ∈ H := hB ⟨Y, hY, rfl⟩
      have hbL : oKappaGL oe Y ∈ oL₀ oe Q₂ := mem_sup_right ⟨Y, hY, rfl⟩
      have hb1 : (oKappaGL oe Y)⁻¹ * oKappaGL oe Y ∈ oQE oe Q₂ := by
        rw [inv_mul_cancel]
        exact one_mem _
      have hgb := hcomm hg hbH haL hbL hgq hb1 (commute_oKappaGL_oRhoTwoGL Y A₁).eq.symm
      have hka : oKappaGL oe Y * (oRhoTwoGL oe A₁)⁻¹ = (oRhoTwoGL oe A₁)⁻¹ * oKappaGL oe Y :=
        (commute_oKappaGL_oRhoTwoGL (oe := oe) Y A₁).inv_right.eq
      rw [hu]
      calc oKappaGL oe Y * ((oRhoTwoGL oe A₁)⁻¹ * g) =
          oKappaGL oe Y * (oRhoTwoGL oe A₁)⁻¹ * g := by group
        _ = (oRhoTwoGL oe A₁)⁻¹ * oKappaGL oe Y * g := by rw [hka]
        _ = (oRhoTwoGL oe A₁)⁻¹ * (g * oKappaGL oe Y) := by rw [mul_assoc, ← hgb]
        _ = (oRhoTwoGL oe A₁)⁻¹ * g * oKappaGL oe Y := by group
    have hu0 := eq_zero_of_commute_kappa hQ hfix hqb
    refine ⟨c, ?_⟩
    have hg' : g = oRhoTwoGL oe A₁ * qEGL oe Q₂ u c := by rw [hu, mul_inv_cancel_left]
    rw [hg', hu0] at hg
    exact hg
  have hL : oL₀ oe Q₂ ≤ H := sup_le hAH hB
  refine le_antisymm (fun g hg => ?_) hL
  obtain ⟨l, hl, q, hq, rfl⟩ := exists_mul_of_mem_oXt hQ (hH hg)
  have hq1 : q = 1 := hHQ q (by simpa using mul_mem (inv_mem (hL hl)) hg) hq
  rw [hq1, mul_one]
  exact hl

theorem exists_conj_eq_oL₀ (hSL : commutator SL(2, K) = ⊤)
    (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) {H : Subgroup (GL ι K)} (hH : H ≤ oXt oe Q₂)
    (hHQ : H ⊓ oQE oe Q₂ = ⊥) (hcov : ∀ l ∈ oL₀ oe Q₂, ∃ h ∈ H, l⁻¹ * h ∈ oQE oe Q₂) :
    ∃ x ∈ oQE oe Q₂, H.map (MulAut.conj x).toMonoidHom = oL₀ oe Q₂ := by
  have hQX : oQE oe Q₂ ≤ oXt oe Q₂ := le_sup_left
  have hLX : oL₀ oe Q₂ ≤ oXt oe Q₂ := le_sup_right
  have hN := oXt_le_normalizer_oQE (oe := oe) (Q₂ := Q₂) hQ
  obtain ⟨A, hA⟩ := exists_torusSL ht0
  obtain ⟨h₀, hh₀, hq₀⟩ := hcov _ (mem_sup_left ⟨A, rfl⟩ : oRhoTwoGL oe A ∈ oL₀ oe Q₂)
  obtain ⟨x, hxQ, e, hxe⟩ := exists_conj_mem_torus hQ ht0 ht1 hA hq₀
  have hconjx : ∀ g, (MulAut.conj x).toMonoidHom g = x * g * x⁻¹ := fun g => by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨x, hxQ, eq_oL₀_of_mem hQ hSL hperf₂ hfix ht1 hA ?_ ?_ ?_ (e := e)
    ⟨h₀, hh₀, by rw [hconjx]; exact hxe⟩⟩
  · rintro _ ⟨g, hg, rfl⟩
    rw [hconjx]
    exact mul_mem (mul_mem (hQX hxQ) (hH hg)) (inv_mem (hQX hxQ))
  · rintro _ ⟨g, hg, rfl⟩ hgQ
    rw [hconjx] at hgQ ⊢
    have h1 : g ∈ oQE oe Q₂ := by
      have := mul_mem (mul_mem (inv_mem hxQ) hgQ) hxQ
      rwa [show x⁻¹ * (x * g * x⁻¹) * x = g by group] at this
    have h2 : g ∈ H ⊓ oQE oe Q₂ := ⟨hg, h1⟩
    rw [hHQ, mem_bot] at h2
    rw [h2, mul_one, mul_inv_cancel]
  · intro l hl
    obtain ⟨g, hg, hgq⟩ := hcov l hl
    refine ⟨x * g * x⁻¹, ⟨g, hg, hconjx g⟩, ?_⟩
    have h1 := (mem_normalizer_iff.mp (hN (hLX (inv_mem hl))) x).mp hxQ
    have h2 := mul_mem (mul_mem h1 hgq) (inv_mem hxQ)
    rwa [show l⁻¹ * x * l⁻¹⁻¹ * (l⁻¹ * g) * x⁻¹ = l⁻¹ * (x * g * x⁻¹) by group] at h2

theorem exists_map_oL₀_eq_conj [Finite K] (hle : oXt oe Q₂ ≤ StatedOmega ⇑Q)
    (hSL₂ : NoNormalTwo (⊤ : Subgroup SL(2, K))) (hO₂ : NoNormalTwo (StatedOmega ⇑Q₂))
    (hSL : commutator SL(2, K) = ⊤) (hperf₂ : commutator (StatedOmega ⇑Q₂) = ⊤)
    (hfix : ∀ w : ι₂ → K, (∀ Y ∈ StatedOmega ⇑Q₂, (Y : Matrix ι₂ ι₂ K) *ᵥ w = w) → w = 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) (β : MulAut ↥(oXt oe Q₂)) :
    ∃ x ∈ oQE oe Q₂, ((((oL₀ oe Q₂).subgroupOf (oXt oe Q₂)).map β.toMonoidHom).map
      (oXt oe Q₂).subtype).map (MulAut.conj x).toMonoidHom = oL₀ oe Q₂ := by
  have hQX : oQE oe Q₂ ≤ oXt oe Q₂ := le_sup_left
  have hLX : oL₀ oe Q₂ ≤ oXt oe Q₂ := le_sup_right
  have hβQ := map_oQE hQ hle hSL₂ hO₂ β
  refine exists_conj_eq_oL₀ hQ hSL hperf₂ hfix ht0 ht1 (map_subtype_le _) ?_ ?_
  · rw [eq_bot_iff]
    rintro _ ⟨⟨g, ⟨l, hl, rfl⟩, rfl⟩, hgQ⟩
    have h1 : β l ∈ (oQE oe Q₂).subgroupOf (oXt oe Q₂) := hgQ
    rw [← hβQ] at h1
    obtain ⟨q, hq, hql⟩ := h1
    have hlq : l = q := β.injective hql.symm
    have h2 : (l : GL ι K) ∈ oL₀ oe Q₂ ⊓ oQE oe Q₂ := ⟨hl, by rw [hlq]; exact hq⟩
    rw [oL₀_inf_oQE, mem_bot] at h2
    have h3 : l = 1 := Subtype.ext h2
    rw [mem_bot]
    simp [h3]
  · intro l hl
    obtain ⟨g, hg⟩ := β.surjective ⟨l, hLX hl⟩
    obtain ⟨l', hl', q, hq, hlq⟩ := exists_mul_of_mem_oXt hQ g.2
    have hg' : g = ⟨l', hLX hl'⟩ * ⟨q, hQX hq⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mk, Subgroup.coe_mk]
      exact hlq
    have hqQ : (⟨q, hQX hq⟩ : ↥(oXt oe Q₂)) ∈ (oQE oe Q₂).subgroupOf (oXt oe Q₂) := hq
    have h1 : β (⟨q, hQX hq⟩⁻¹) ∈ (oQE oe Q₂).subgroupOf (oXt oe Q₂) := by
      rw [← hβQ]
      exact ⟨_, inv_mem hqQ, rfl⟩
    have h2 : β ⟨l', hLX hl'⟩ = ⟨l, hLX hl⟩ * β (⟨q, hQX hq⟩⁻¹) := by
      rw [← hg, hg', map_inv, map_mul, mul_inv_cancel_right]
    refine ⟨((β ⟨l', hLX hl'⟩ : ↥(oXt oe Q₂)) : GL ι K),
      ⟨_, ⟨⟨l', hLX hl'⟩, hl', rfl⟩, rfl⟩, ?_⟩
    rw [h2, Subgroup.coe_mul, inv_mul_cancel_left]
    exact h1

end Compl

end CFSG.ComponentClassification.RankTwoClassical.ORigid
