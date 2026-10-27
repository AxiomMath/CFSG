module

public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.IVK.L2.Lemma12hc
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma12hbM

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GorensteinWalter
open scoped Pointwise

namespace Lemma12hb

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] [Finite K] (e : K ≃* L2 F)

omit [Finite K] in
theorem mul_conj_mul_inv (f : MulAut K) (a : K) : f * MulAut.conj a * f⁻¹ = MulAut.conj (f a) := by
  ext y
  simp [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply]

omit [Finite F] [Finite K] in
theorem conj_twist (f : MulAut K) (a b : K) :
    MulAut.conj a * (MulAut.conj b * f) * (MulAut.conj a)⁻¹ =
      MulAut.conj (a * b * (f a)⁻¹) * f := by
  have h := mul_conj_mul_inv f a⁻¹
  have h2 : f * MulAut.conj a⁻¹ = MulAut.conj (f a⁻¹) * f := by
    rw [← h]; group
  calc MulAut.conj a * (MulAut.conj b * f) * (MulAut.conj a)⁻¹
      = MulAut.conj a * MulAut.conj b * (f * MulAut.conj a⁻¹) := by
        rw [map_inv]; group
    _ = MulAut.conj a * MulAut.conj b * (MulAut.conj (f a⁻¹) * f) := by rw [h2]
    _ = MulAut.conj (a * b * (f a)⁻¹) * f := by
        rw [map_inv f a, map_mul, map_mul]; group

omit [Finite F] [Finite K] in
theorem toPSL_fieldAut (σ : F ≃+* F) (k : K) :
    toPSL e (fieldAutHom e σ k) = psl2FieldAut F σ (toPSL e k) := by
  rw [fieldAutHom_apply']
  simp

omit [Finite F] [Finite K] in
theorem mem_fixed_iff (σ : F ≃+* F) (k : K) :
    k ∈ fixedSubgroup K (fieldAutHom e σ) ↔ psl2FieldAut F σ (toPSL e k) = toPSL e k := by
  have h1 : k ∈ fixedSubgroup K (fieldAutHom e σ) ↔ fieldAutHom e σ k = k := by
    exact Iff.rfl
  rw [h1]
  constructor
  · intro h
    rw [← toPSL_fieldAut e σ k, h]
  · intro h
    apply (toPSL e).injective
    rw [toPSL_fieldAut e σ k]
    exact h

omit [Finite F] in
theorem map_toPSL_O2 (σ : F ≃+* F) (k : K) :
    k ∈ (oResidual 2 ↥(fixedSubgroup K (fieldAutHom e σ))).map
        (fixedSubgroup K (fieldAutHom e σ)).subtype ↔
      toPSL e k ∈ (oResidual 2 ↥(fixedSubgroup (PSL2 F) (psl2FieldAut F σ))).map
        (fixedSubgroup (PSL2 F) (psl2FieldAut F σ)).subtype := by
  set Ck := fixedSubgroup K (fieldAutHom e σ) with hCk
  set Cp := fixedSubgroup (PSL2 F) (psl2FieldAut F σ) with hCp
  have hmem : ∀ k : K, k ∈ Ck ↔ toPSL e k ∈ Cp := fun k => by
    rw [hCk, hCp, mem_fixed_iff e σ k]
    exact Iff.rfl
  let ρ : ↥Ck →* ↥Cp :=
    ((toPSL e).toMonoidHom.comp Ck.subtype).codRestrict Cp (fun k => (hmem k).1 k.2)
  have hρ : Function.Surjective ρ := by
    intro g
    refine ⟨⟨(toPSL e).symm g, (hmem _).2 (by simp)⟩, ?_⟩
    apply Subtype.ext
    simp [ρ]
  have hres := Stage1.Thm6.Prod.map_oResidual ρ hρ Nat.prime_two
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hρc : ρ c ∈ oResidual 2 ↥Cp := hres ▸ Subgroup.mem_map_of_mem ρ hc
    exact ⟨ρ c, hρc, rfl⟩
  · rintro ⟨d, hd, hdk⟩
    rw [← hres] at hd
    obtain ⟨c, hc, rfl⟩ := hd
    refine ⟨c, hc, ?_⟩
    apply (toPSL e).injective
    exact hdk

omit [Finite K] in
theorem exists_sigma (N : L2Notation e) {f : MulAut K} (hf : f ∈ N.R) (hf2 : orderOf f = 2) :
    ∃ σ : F ≃+* F, fieldAutHom e σ = f ∧ σ * σ = 1 ∧ σ ≠ 1 := by
  obtain ⟨σ, hσ⟩ : f ∈ fieldAutSub e := hf.2
  have hff : f * f = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf2, pow_two] at this
  refine ⟨σ, hσ, ?_, ?_⟩
  · apply fieldAutHom_injective e
    rw [map_mul, map_one, hσ, hff]
  · rintro rfl
    rw [map_one] at hσ
    rw [← hσ, orderOf_one] at hf2
    omega

omit [Finite K] in
theorem exists_k (N : L2Notation e) {σ : F ≃+* F} (hf : fieldAutHom e σ ∈ N.R)
    (hf2 : orderOf (fieldAutHom e σ) = 2) (hσ2 : σ * σ = 1) {x : MulAut K} (hx : x ∈ N.P)
    (hxo : orderOf (x * fieldAutHom e σ) = 2) :
    ∃ k : K, x = MulAut.conj k ∧ fieldAutHom e σ k = k ∧ k * k = 1 := by
  obtain ⟨k, hk⟩ : x ∈ innAut K := hx.2
  have hxf : x * fieldAutHom e σ = fieldAutHom e σ * x := N.R_cent _ hf hf2 x hx
  have hff : fieldAutHom e σ * fieldAutHom e σ = 1 := by
    rw [← map_mul, hσ2, map_one]
  refine ⟨k, hk.symm, ?_, ?_⟩
  · apply conj_injective_of_L2 e
    rw [← mul_conj_mul_inv, hk, ← hxf]
    group
  · apply conj_injective_of_L2 e
    have h2 : (x * fieldAutHom e σ) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (x * fieldAutHom e σ)
      rwa [hxo] at this
    have h3 : x * x = 1 := by
      calc x * x = x * x * (fieldAutHom e σ * fieldAutHom e σ) := by rw [hff, mul_one]
        _ = (x * fieldAutHom e σ) ^ 2 := by
          rw [pow_two]
          calc x * x * (fieldAutHom e σ * fieldAutHom e σ)
              = x * (x * fieldAutHom e σ) * fieldAutHom e σ := by group
            _ = x * (fieldAutHom e σ * x) * fieldAutHom e σ := by rw [hxf]
            _ = x * fieldAutHom e σ * (x * fieldAutHom e σ) := by group
        _ = 1 := h2
    rw [map_mul, hk, h3, map_one]

end Lemma12hb

open Lemma12hb in
theorem ivk_1_2h_b : IVK_1_2h_b := by
  intro F _ _ hF K _ _ e N f hf hf2 z hzP hz2 hzc
  obtain ⟨σ, hσf, hσ2, hσ1⟩ := exists_sigma e N hf hf2
  subst hσf
  have hchar : ringChar F ≠ 2 := by
    have : Fintype F := Fintype.ofFinite F
    intro h
    have h2 : Fintype.card F % 2 = 0 := FiniteField.even_card_iff_char_two.1 h
    obtain ⟨k, hk⟩ := hF.1
    rw [Nat.card_eq_fintype_card] at hk
    omega
  have hzf : z * fieldAutHom e σ = fieldAutHom e σ * z := N.R_cent _ hf hf2 z hzP
  have hσf : fieldAutHom e σ ∈ fieldAutSub e := hf.2
  constructor
  ·
    intro x hxP hxL hx1 hxo
    obtain ⟨k, rfl, hfk, hkk⟩ := exists_k e N hf hf2 hσ2 hxP hxo
    have hkL : k ∈ (oResidual 2 ↥(fixedSubgroup K (fieldAutHom e σ))).map
        (fixedSubgroup K (fieldAutHom e σ)).subtype := by
      obtain ⟨l, hl, hlk⟩ := hxL
      have : l = k := conj_injective_of_L2 e hlk
      rwa [← this]
    have hk1 : k ≠ 1 := fun h => hx1 (by rw [h, map_one])
    have hg : psl2FieldAut F σ (toPSL e k) = toPSL e k := by
      rw [← toPSL_fieldAut, hfk]
    have hg2 : toPSL e k * toPSL e k = 1 := by rw [← map_mul, hkk, map_one]
    have hg1 : toPSL e k ≠ 1 := fun h => hk1 ((toPSL e).injective (by rw [h, map_one]))
    have hne := twisted_ne_one_of_mem (σ := σ) hσ2 hσ1 hchar (toPSL e k) hg hg2 hg1
      ((map_toPSL_O2 e σ k).1 hkL)
    have hdiag : MulAut.conj k ∈ innDiagSub e := innAut_le_innDiagSub e ⟨k, rfl⟩
    obtain ⟨d, hd, hdx⟩ := ivk_1_2h_c F hF K e N _ hf hf2 (MulAut.conj k) hdiag hxo
    by_cases hdi : d ∈ innAut K
    · exfalso
      obtain ⟨c', rfl⟩ := hdi
      apply hne (toPSL e c')
      rw [conj_twist] at hdx
      have h2 : c' * k * (fieldAutHom e σ c')⁻¹ = 1 := by
        apply conj_injective_of_L2 e
        have := mul_right_cancel (hdx.trans (one_mul _).symm)
        simpa using this
      have h3 := congrArg (toPSL e) h2
      rw [map_mul, map_mul, map_inv, toPSL_fieldAut, map_one] at h3
      exact h3
    · have hmem : d⁻¹ ∈ innAut K ⊔ Subgroup.zpowers N.t := by
        rw [innAut_sup_zpowers_eq e hF N.t_mem_diag N.t_not_mem_inn]
        exact inv_mem hd
      have hmul : d⁻¹ ∈ (innAut K : Set (MulAut K)) * (Subgroup.zpowers N.t : Set (MulAut K)) := by
        rw [← Subgroup.normal_mul]; exact hmem
      obtain ⟨w, hw, y, hy, hwy⟩ := hmul
      have hwy : w * y = d⁻¹ := hwy
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hy
      have hyt : y = 1 ∨ y = N.t := by
        have hk := zpow_mod_orderOf N.t j
        rw [N.t_order] at hk
        have hk' : (j % ((2 : ℕ) : ℤ)) = 0 ∨ (j % ((2 : ℕ) : ℤ)) = 1 := by omega
        rcases hk' with h0 | h1
        · left; rw [← hj, ← hk, h0]; simp
        · right; rw [← hj, ← hk, h1]; simp
      rcases hyt with rfl | rfl
      · exfalso
        apply hdi
        rw [mul_one] at hwy
        rw [← inv_inv d, ← hwy]
        exact inv_mem hw
      · have hti := ivk_1_2i_a F hF K e N _ hf hf2 z hzP hz2 hzc
        have htf : N.t * fieldAutHom e σ * N.t⁻¹ = z * fieldAutHom e σ := by
          rw [commutatorElement_def] at hti
          calc N.t * fieldAutHom e σ * N.t⁻¹
              = (N.t * fieldAutHom e σ * N.t⁻¹ * (fieldAutHom e σ)⁻¹) * fieldAutHom e σ := by group
            _ = z * fieldAutHom e σ := by rw [hti]
        have hd' : d = N.t⁻¹ * w⁻¹ := by
          rw [← inv_inv d, ← hwy]; group
        have hxd : MulAut.conj k * fieldAutHom e σ = w * (z * fieldAutHom e σ) * w⁻¹ := by
          have h1 : MulAut.conj k * fieldAutHom e σ = d⁻¹ * fieldAutHom e σ * d := by
            calc MulAut.conj k * fieldAutHom e σ
                = d⁻¹ * (d * (MulAut.conj k * fieldAutHom e σ) * d⁻¹) * d := by group
              _ = d⁻¹ * fieldAutHom e σ * d := by rw [hdx]
          rw [h1, ← hwy, hd', ← htf]
          group
        refine ⟨w⁻¹, inv_mem hw, ?_⟩
        rw [hxd, hzf]
        group
  ·
    intro x hxP hxL hxo
    obtain ⟨k, rfl, hfk, hkk⟩ := exists_k e N hf hf2 hσ2 hxP hxo
    have hk1 : k ≠ 1 := by
      rintro rfl
      apply hxL
      exact ⟨1, one_mem _, by simp⟩
    have hkL : k ∉ (oResidual 2 ↥(fixedSubgroup K (fieldAutHom e σ))).map
        (fixedSubgroup K (fieldAutHom e σ)).subtype := fun h => hxL ⟨k, h, rfl⟩
    have hg : psl2FieldAut F σ (toPSL e k) = toPSL e k := by
      rw [← toPSL_fieldAut, hfk]
    have hg2 : toPSL e k * toPSL e k = 1 := by rw [← map_mul, hkk, map_one]
    have hg1 : toPSL e k ≠ 1 := fun h => hk1 ((toPSL e).injective (by rw [h, map_one]))
    obtain ⟨c, hc⟩ := exists_twisted_eq_one (σ := σ) hσ2 hσ1 hchar (toPSL e k) hg hg2 hg1
      (fun h => hkL ((map_toPSL_O2 e σ k).2 h))
    refine ⟨MulAut.conj ((toPSL e).symm c), ⟨_, rfl⟩, ?_⟩
    rw [conj_twist]
    have h1 : (toPSL e).symm c * k * (fieldAutHom e σ ((toPSL e).symm c))⁻¹ = 1 := by
      apply (toPSL e).injective
      rw [map_mul, map_mul, map_inv, toPSL_fieldAut, MulEquiv.apply_symm_apply, map_one]
      exact hc
    rw [h1, map_one, one_mul]

end CFSG.GH74.GLS.IVK.Proofs2
