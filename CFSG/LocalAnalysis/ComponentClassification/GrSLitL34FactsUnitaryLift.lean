
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryLiftBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsQuat
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFixed
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCoverAut

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

structure IsUSetting {E : Type*} [Group E]
    (q : E →* Equiv.Perm (Fin 42)) (l : Cover →* E) (β : E ≃* E) : Prop where
  qS : ∀ e, q e ∈ S
  qsurj : ∀ s ∈ S, ∃ e, q e = s
  ker : q.ker = center E
  three : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1
  ql : q.comp l = sigma
  lsurj : Function.Surjective l
  qβ : ∀ e, q (β e) = r₄ * q e * r₄⁻¹

namespace IsUSetting

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E} {β : E ≃* E}

theorem ker_le (h : IsUSetting q l β) : q.ker ≤ center E :=
  h.ker ▸ le_refl _

theorem q_l (h : IsUSetting q l β) (c : Cover) :
    q (l c) = sigma c := by
  rw [← MonoidHom.comp_apply, h.ql]

theorem l_mem_ker (h : IsUSetting q l β) {c : Cover}
    (hc : c ∈ sigma.ker) : l c ∈ q.ker := by
  rw [MonoidHom.mem_ker, h.q_l]
  exact hc

theorem psi_mem_ker
    (h : IsUSetting q l β) (d) : psi l d ∈ q.ker :=
  h.l_mem_ker (range_zHom ▸ ⟨_, rfl⟩)

theorem psi_mem_center
    (h : IsUSetting q l β) (d) : psi l d ∈ center E :=
  h.ker_le (h.psi_mem_ker d)

theorem psi_comm
    (h : IsUSetting q l β) (d) (g : E) :
    g * psi l d = psi l d * g :=
  mem_center_iff.mp (h.psi_mem_center d) g

theorem exists_psi
    (h : IsUSetting q l β) {z : E} (hz : z ∈ q.ker) :
    ∃ d, psi l d = z := by
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 hz
  exact ⟨_, psi_ofAdd l i j⟩

theorem beta_cv
    (h : IsUSetting q l β)
    (w : List (Fin 2 × Bool)) : β (l (cv w)) = l (cv (alphaU w)) := by
  obtain ⟨α, hα, hσα⟩ := exists_autLift r₄
    (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_aS coverParts.autU.1)
    (abPerm_conj_of tabRep_r₄ r₄_mul_self tabRep_bS coverParts.autU.2)
  have hext : β.toMonoidHom.comp l = l.comp α := by
    apply hom_ext_of_central commutator_cover q h.ker_le
    refine MonoidHom.ext fun c => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [h.qβ, h.q_l, h.q_l, hσα]
  have := DFunLike.congr_fun hext (cv w)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [this, hα]
  rfl

theorem beta_z₁
    (h : IsUSetting q l β) :
    β (l z₁) = (l z₁)⁻¹ := by
  rw [h.beta_cv, ← map_inv]
  congr 1
  have := alphaU_z_spec.1
  rw [cv_append] at this
  exact eq_inv_of_mul_eq_one_left this

theorem beta_z₂
    (h : IsUSetting q l β) :
    β (l z₂) = (l z₂)⁻¹ := by
  rw [h.beta_cv, ← map_inv]
  congr 1
  have := alphaU_z_spec.2
  rw [cv_append] at this
  exact eq_inv_of_mul_eq_one_left this

theorem beta_psi
    (h : IsUSetting q l β) (d) :
    β (psi l d) = psi l d⁻¹ := by
  rw [map_inv, psi_apply, map_mul, map_pow, map_pow, h.beta_z₁, h.beta_z₂, inv_pow, inv_pow,
    mul_inv_rev]
  have hc : (l z₁ ^ (Multiplicative.toAdd d.1).val)⁻¹ ∈ center E := by
    refine inv_mem (pow_mem (h.ker_le (h.l_mem_ker ?_)) _)
    exact MonoidHom.mem_ker.mpr sigma_z₁
  exact (mem_center_iff.mp hc _).symm

theorem beta_ker
    (h : IsUSetting q l β)
    {z : E} (hz : z ∈ q.ker) : β z = z⁻¹ := by
  obtain ⟨d, rfl⟩ := h.exists_psi hz
  rw [h.beta_psi, map_inv]

theorem lam_z₃'
    (h : IsUSetting q l β) : l z₃ = 1 :=
  lam_z₃ h.ql h.three

theorem eps_p₁
    (h : IsUSetting q l β) :
    (l (cv (tw 35)))⁻¹ * β (l (cv (tw 35))) = psi l (1, Multiplicative.ofAdd 3) := by
  have hs := unit_spec (d := (35, 0, 3, 0)) (by decide)
  dsimp only at hs
  rw [h.beta_cv, ← map_inv, ← map_mul, hs, map_mul, map_mul, map_pow, map_pow, map_pow,
    h.lam_z₃', psi_apply]
  simp only [toAdd_one, ZMod.val_zero, pow_zero, one_mul, mul_one, toAdd_ofAdd]
  rfl

theorem eps_p₂
    (h : IsUSetting q l β) :
    (l (cv (tw 38)))⁻¹ * β (l (cv (tw 38))) =
      psi l (Multiplicative.ofAdd 3, Multiplicative.ofAdd 1) := by
  have hs := unit_spec (d := (38, 3, 1, 0)) (by decide)
  dsimp only at hs
  rw [h.beta_cv, ← map_inv, ← map_mul, hs, map_mul, map_mul, map_pow, map_pow, map_pow,
    h.lam_z₃', psi_apply]
  simp only [pow_zero, mul_one, toAdd_ofAdd]
  rfl

theorem p₁_pow_four
    (h : IsUSetting q l β) : l (cv (tw 35)) ^ 4 = psi l (1, Multiplicative.ofAdd 2) := by
  have hs := fourth_spec (d := ([35], 0, 2, 0)) (by decide)
  dsimp only at hs
  have htw : twl [35] = tw 35 := by simp [twl]
  rw [htw] at hs
  rw [← map_pow, hs, map_mul, map_mul, map_pow, map_pow, map_pow, h.lam_z₃', psi_apply]
  simp only [toAdd_one, ZMod.val_zero, pow_zero, one_mul, mul_one, toAdd_ofAdd]
  rfl

theorem q_p₁ (h : IsUSetting q l β) :
    q (l (cv (tw 35))) = qt₁ := by
  rw [h.q_l, sigma_tw 35 (by norm_num)]

theorem q_p₂ (h : IsUSetting q l β) :
    q (l (cv (tw 38))) = qt₂ := by
  rw [h.q_l, sigma_tw 38 (by norm_num)]

theorem q_psi
    (h : IsUSetting q l β) (d) : q (psi l d) = 1 :=
  h.psi_mem_ker d

theorem exists_eps
    (h : IsUSetting q l β) {z : E} (hz : z ∈ q.ker) : ∃ p, q p ∈ Q8 ∧ z = p⁻¹ * β p := by
  set ε := epsHom q h.ker_le β r₄ h.qβ Q8 fun t ht => r₄_comm_Q8 ht with hε
  have hP₁ : l (cv (tw 35)) ∈ Q8.comap q := by rw [mem_comap, h.q_p₁]; exact qt₁_mem_Q8
  have hP₂ : l (cv (tw 38)) ∈ Q8.comap q := by rw [mem_comap, h.q_p₂]; exact qt₂_mem_Q8
  have hA : psi l (Multiplicative.ofAdd 1, 1) ∈ Q8.comap q := by
    rw [mem_comap, h.q_psi]; exact Q8.one_mem
  have hB : psi l (1, Multiplicative.ofAdd 1) ∈ Q8.comap q := by
    rw [mem_comap, h.q_psi]; exact Q8.one_mem
  have εA : ∀ d (hd : psi l d ∈ Q8.comap q), (ε ⟨psi l d, hd⟩ : E) = psi l (d⁻¹ * d⁻¹) := by
    intro d hd
    rw [hε, epsHom_apply, h.beta_psi, map_mul, map_inv]
  set P₁ : Q8.comap q := ⟨_, hP₁⟩ with hP₁d
  set P₂ : Q8.comap q := ⟨_, hP₂⟩ with hP₂d
  set A : Q8.comap q := ⟨_, hA⟩ with hAd
  set B : Q8.comap q := ⟨_, hB⟩ with hBd
  have εu : (ε (P₁ * P₂ * A) : E) = l z₁ := by
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, hAd, εA, hε, epsHom_apply,
      epsHom_apply, hP₁d, hP₂d, h.eps_p₁, h.eps_p₂, ← map_mul, ← map_mul, ← psi_a l]
    congr 1
  have εv : (ε (P₁ * B) : E) = l z₂ := by
    rw [map_mul, Subgroup.coe_mul, hBd, εA, hε, epsHom_apply, hP₁d, h.eps_p₁, ← map_mul,
      ← psi_b l]
    congr 1
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff h.ql h.lsurj h.three).1 hz
  set p : Q8.comap q := (P₁ * P₂ * A) ^ i * (P₁ * B) ^ j with hp
  refine ⟨p, p.2, ?_⟩
  have := epsHom_apply q h.ker_le β r₄ h.qβ Q8 (fun t ht => r₄_comm_Q8 ht) p
  rw [← hε] at this
  rw [← this, hp, map_mul, map_pow, map_pow, Subgroup.coe_mul, Subgroup.coe_pow,
    Subgroup.coe_pow, εu, εv]

theorem le_range_Q8
    (h : IsUSetting q l β) : Q8 ≤ q.range := fun t ht =>
  h.qsurj t (T0_le_S (Q8_le_T0 ht))

theorem card_fixed_Q8
    [Finite E] (h : IsUSetting q l β) : Nat.card {e : E // q e ∈ Q8 ∧ β e = e} = 8 := by
  rw [card_fixed_eq q h.ker_le β r₄ h.qβ (fun z hz => h.beta_ker hz) Q8
    (fun t ht => r₄_comm_Q8 ht) h.le_range_Q8 (fun z hz => ?_), card_Q8]
  obtain ⟨p, hp, hz⟩ := h.exists_eps hz
  exact ⟨p, hp, 1, one_mem _, by rw [hz]; group⟩

theorem card_fixed
    [Finite E] (h : IsUSetting q l β) : Nat.card {e : E // β e = e} = 72 := by
  have e1 : {e : E // β e = e} ≃ {e : E // q e ∈ C₄ ∧ β e = e} :=
    Equiv.subtypeEquivRight fun e => ⟨fun he => ⟨mem_C₄.2 ⟨by
      have h1 := h.qβ e
      rw [he] at h1
      calc q e * r₄ = r₄ * q e * r₄⁻¹ * r₄ := by rw [← h1]
        _ = r₄ * q e := by group, h.qS e⟩, he⟩, fun h' => h'.2⟩
  rw [Nat.card_congr e1, card_fixed_eq q h.ker_le β r₄ h.qβ (fun z hz => h.beta_ker hz) C₄
    (fun t ht => (mem_C₄.1 ht).1.symm) (fun t ht => h.qsurj t (mem_C₄.1 ht).2)
    (fun z hz => ?_), card_C₄]
  obtain ⟨p, hp, hz⟩ := h.exists_eps hz
  refine ⟨p, mem_C₄.2 ⟨(mem_Q8.1 hp).1, T0_le_S (mem_Q8.1 hp).2⟩, 1, one_mem _, ?_⟩
  rw [hz]
  group

end IsUSetting

end CFSG.ComponentClassification.GrSLit.L34Facts
