module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeFus
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeAD
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeFix
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23HeI

public noncomputable section

namespace CFSG.ComponentClassification.GSThmB.CF23L34

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.CatFactsL4U4
open CFSG.ComponentClassification.CatFactsL4U4.OutInv CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.GrSLit CFSG.ComponentClassification.GrSLit.L34Facts.Real
open CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four CFSG.LieType.Multipliers.L34

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)

theorem conj_mem_D_x {p : H} (hp : p ∈ h.D) : h.x⁻¹ * p * h.x ∈ h.D :=
  mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem h.x_mem) (h.D_le_S hp)) h.x_mem,
    L34Facts.conj_mem_of_mem_normalizer (h.S_le_normalizer h.x_mem) (h.D_le_J hp)⟩

theorem t0_central
    (y : ↥hjJ) : (y : Equiv.Perm (Fin 8330)) * heGenPerm 0 = heGenPerm 0 * y := by
  have hz : hjL z₂ ∈ center ↥hjJ :=
    ker_hjQ_le_center (by rw [MonoidHom.mem_ker, hjQ_hjL, sigma_z₂])
  have h1 := congrArg Subtype.val (mem_center_iff.mp hz y)
  simpa [coe_hjL, hjLam_z₂] using h1

section Core

variable
  (hZ : center (OddBar h.K) = ⊥) {ι : ↥(NL hKa) →* Equiv.Perm (Fin 8330)}
  (hιinj : Function.Injective ι) (hιsurj : ∀ p ∈ heP, ∃ γ, ι γ = p)
  (hαN : phi hKa (abar h) ∈ NL hKa) (hια : ι ⟨phi hKa (abar h), hαN⟩ = heGenPerm 0)
  (Ψ : OddBar h.J ≃* ↥hjJ)
  (hΨ : ∀ (j : H) (hjB : j ∈ GSLit.fixedLayer h.J h.B) (hjJ : j ∈ h.J),
    (Ψ (jq h.J ⟨j, hjJ⟩) : Equiv.Perm (Fin 8330)) =
      ι (piK hKa ⟨j, fixedLayer_le_K h hKa hjB⟩))

include hZ hιinj hιsurj hια hΨ in
theorem fus23ConclW_of_ident (ha : h.a ∈ h.D) : h.Fus23ConclW := by
  have hxN : h.x ∈ normalizer (h.J : Set H) := h.S_le_normalizer h.x_mem
  have hP2 : IsPGroup 2 h.D := h.isPGroup_S.to_le h.D_le_S
  obtain ⟨g, hg⟩ := exists_psi' Ψ
  set Ψ' : OddBar h.J ≃* ↥hjJ := Ψ.trans (MulAut.conj g) with hΨ'def
  have hΨ' : ∀ y, Ψ' y = g * Ψ y * g⁻¹ := fun _ => rfl
  set βJ := betaHat h.J hxN with hβJ
  set β₀ : ↥hjJ ≃* ↥hjJ := (Ψ'.symm.trans βJ).trans Ψ' with hβ₀def
  have hβ₀ : ∀ y, β₀ (Ψ' y) = Ψ' (βJ y) := fun y => by
    change Ψ' (βJ (Ψ'.symm (Ψ' y))) = Ψ' (βJ y)
    rw [MulEquiv.symm_apply_apply]
  have hβ2 : ∀ e, β₀ (β₀ e) = e := by
    intro e
    obtain ⟨y, rfl⟩ := Ψ'.surjective e
    rw [hβ₀, hβ₀, hβJ, betaHat_x_involutive]
  have hβD : ∀ d (hdD : d ∈ h.D), βJ (jq h.J ⟨d, h.D_le_J hdD⟩) =
      jq h.J ⟨h.x⁻¹ * d * h.x, h.D_le_J (conj_mem_D_x hdD)⟩ := fun d hdD => by
    rw [hβJ, betaHat_jq]
    rfl
  have hβT : ∀ e, hjQ e ∈ T0 → hjQ (β₀ e) ∈ T0 := by
    intro e he
    obtain ⟨d, hdD, rfl⟩ := (hg e).1 he
    rw [← hΨ', hβ₀, hβD d hdD]
    exact (hg _).2 ⟨_, conj_mem_D_x hdD, rfl⟩
  have haJ := h.D_le_J ha
  have haB := CF23Diag.D_le_JB h ha
  have hΨa : (Ψ (jq h.J ⟨h.a, haJ⟩) : Equiv.Perm (Fin 8330)) = heGenPerm 0 := by
    rw [hΨ h.a haB haJ, ← hια]
    rfl
  have hΨ'a : Ψ' (jq h.J ⟨h.a, haJ⟩) = nfM hjL hjTau := by
    apply Subtype.ext
    rw [coe_nfM_hjTau, hΨ', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hΨa,
      t0_central g]
    group
  have hβt : β₀ (nfM hjL hjTau) = nfM hjL hjTau := by
    rw [← hΨ'a, hβ₀, hβD h.a ha]
    congr 2
    apply Subtype.ext
    show h.x⁻¹ * h.a * h.x = h.a
    rw [mul_assoc, ← h.x_comm_a, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨x₀, hx64, hq1, hsq, hfix, p, hpP, hpc⟩ := exists_label_fixed hβ2 hβT hβt
  have hζT : hjQ (nfM hjL x₀) ∈ T0 := by
    rw [q_nfM isQSetting_hj hx64]
    exact tg_mem_T0 _ hx64
  obtain ⟨d, hdD, hdζ⟩ := (hg _).1 hζT
  have hdζ' : Ψ' (jq h.J ⟨d, h.D_le_J hdD⟩) = nfM hjL x₀ := hdζ
  have hdJ := h.D_le_J hdD
  have hd2 : d * d = 1 := by
    apply eq_one_of_jq_eq_one h.D_le_J hP2 (mul_mem hdD hdD)
    apply Ψ'.injective
    show Ψ' (jq h.J (⟨d, hdJ⟩ * ⟨d, hdJ⟩)) = Ψ' 1
    rw [map_mul, map_mul, hdζ', hsq, map_one]
  have hdx : d * h.x = h.x * d := by
    have h1 : h.x⁻¹ * d * h.x = d := by
      apply eq_of_jq_eq h.D_le_J hP2 (conj_mem_D_x hdD) hdD
      apply Ψ'.injective
      rw [← hβD d hdD, ← hβ₀, hdζ', hfix]
    calc d * h.x = h.x * (h.x⁻¹ * d * h.x) := by group
      _ = h.x * d := by rw [h1]
  have hdP : d ∉ h.P := by
    intro hdP
    apply hq1
    have hc := jq_mem_center h hdJ (mem_inf.mp hdP).2
    have hcen : nfM hjL x₀ ∈ center ↥hjJ := by
      rw [← hdζ', mem_center_iff]
      intro y
      obtain ⟨y', rfl⟩ := Ψ'.surjective y
      rw [← map_mul, ← map_mul, mem_center_iff.mp hc y']
    exact (MonoidHom.mem_ker).1 (center_le_ker_hjQ hcen)
  have hdB := CF23Diag.D_le_JB h hdD
  have hιd : ι (piK hKa ⟨d, fixedLayer_le_K h hKa hdB⟩) =
      (g : Equiv.Perm (Fin 8330))⁻¹ * ((nfM hjL x₀ : ↥hjJ) : Equiv.Perm (Fin 8330)) * g := by
    rw [← hΨ d hdB hdJ, ← hdζ', hΨ', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hgP : (g : Equiv.Perm (Fin 8330)) ∈ heP := (mem_centralizerIn.1 (hjJ_le g.2)).1
  obtain ⟨γ', hγ'⟩ := hιsurj ((g : Equiv.Perm (Fin 8330))⁻¹ * p) (mul_mem (inv_mem hgP) hpP)
  have hgt : (g : Equiv.Perm (Fin 8330)) * heGenPerm 0 = heGenPerm 0 * g := t0_central g
  have hconj : γ' * ⟨phi hKa (abar h), hαN⟩ * γ'⁻¹ =
      ⟨phi hKa (abar h), hαN⟩ * piK hKa ⟨d, fixedLayer_le_K h hKa hdB⟩ := by
    apply hιinj
    rw [map_mul, map_mul, map_inv, hγ', hια, map_mul, hια, hιd]
    have hgt' : (g : Equiv.Perm (Fin 8330))⁻¹ * heGenPerm 0 =
        heGenPerm 0 * (g : Equiv.Perm (Fin 8330))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgt, mul_assoc, mul_inv_cancel, mul_one]
    calc (g : Equiv.Perm (Fin 8330))⁻¹ * p * heGenPerm 0 *
          ((g : Equiv.Perm (Fin 8330))⁻¹ * p)⁻¹ =
        (g : Equiv.Perm (Fin 8330))⁻¹ * (p * heGenPerm 0 * p⁻¹) * g := by group
      _ = (g : Equiv.Perm (Fin 8330))⁻¹ * (heGenPerm 0 * ((nfM hjL x₀ : ↥hjJ) : Equiv.Perm (Fin 8330))) *
          g := by rw [hpc]
      _ = ((g : Equiv.Perm (Fin 8330))⁻¹ * heGenPerm 0) *
          ((nfM hjL x₀ : ↥hjJ) : Equiv.Perm (Fin 8330)) * g := by group
      _ = heGenPerm 0 * ((g : Equiv.Perm (Fin 8330))⁻¹ * ((nfM hjL x₀ : ↥hjJ) : Equiv.Perm (Fin 8330)) *
          g) := by rw [hgt']; group
  refine fus23ConclW_of_NL hKa hZ hdD hd2 hdx hdP
    (γ := ((γ'⁻¹ : ↥(NL hKa)) : ↥(GAut hKa))) (γ'⁻¹).2 ?_
  have h1 := congrArg (fun z : ↥(NL hKa) => (z : ↥(GAut hKa))) hconj
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
  rw [Subgroup.coe_inv, inv_inv]
  exact h1

end Core

end CFSG.ComponentClassification.GSThmB.CF23L34

namespace CFSG.ComponentClassification.GSThmB

open CF23L34

theorem cf23L34HeStep_holds :
    CF23L34HeStep := by
  intro H _ _ h _ hL hKa he
  obtain ⟨e⟩ := he
  have hZ := center_oddBarK_eq_bot e
  have hαN := phi_abar_mem_NL hKa e hL
  obtain ⟨ι, hιinj, hιP, hιsurj, hια, hιJ⟩ := exists_ident hKa e hL hαN
  obtain ⟨Ψ, hΨ⟩ := exists_psi hKa hZ hιinj hιsurj hιJ
  have ha := a_mem_D_of_ident hKa hZ hιinj hιP hιsurj hαN hια hιJ Ψ hΨ
  exact fus23ConclW_of_ident hKa hZ hιinj hιsurj hαN hια Ψ hΨ ha

end CFSG.ComponentClassification.GSThmB
