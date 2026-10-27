module

public import CFSG.GH74.GLS.IVK.L2.FixedSL
public import CFSG.GH74.GLS.IVK.L2.FixedCentralizer

public section

namespace CFSG.GH74.GLS.IVK

open Subgroup CFSG CFSG.GorensteinWalter

section Odd

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F) (σ : F ≃+* F)

@[expose] noncomputable def pslToK : PSL2 (fixedField σ) →* K :=
  ((toPSL e).symm : PSL2 F ≃* K).toMonoidHom.comp (pslIncl σ)

omit [Finite F] in
theorem pslToK_injective : Function.Injective (pslToK e σ) :=
  (toPSL e).symm.injective.comp (pslIncl_injective σ)

omit [Finite F] in
theorem toPSL_pslToK (z : PSL2 (fixedField σ)) : toPSL e (pslToK e σ z) = pslIncl σ z :=
  (toPSL e).apply_symm_apply _

omit [Finite F] in
theorem range_pslToK (hodd : Odd (orderOf σ)) :
    (pslToK e σ).range = fixedSubgroup K (fieldAutHom e σ) := by
  ext k
  constructor
  · rintro ⟨z, rfl⟩
    show fieldAutHom e σ (pslToK e σ z) = pslToK e σ z
    apply (toPSL e).injective
    rw [toPSL_fieldAutHom, toPSL_pslToK]
    exact (mem_range_pslIncl_iff σ hodd _).mp ⟨z, rfl⟩
  · intro hk
    have hk' : fieldAutHom e σ k = k := hk
    have h1 : psl2FieldAut F σ (toPSL e k) = toPSL e k := by rw [← toPSL_fieldAutHom, hk']
    obtain ⟨z, hz⟩ := (mem_range_pslIncl_iff σ hodd _).mpr h1
    refine ⟨z, ?_⟩
    apply (toPSL e).injective
    rw [toPSL_pslToK]
    exact hz

@[expose] noncomputable def fixedSubgroupEquivL2 (hodd : Odd (orderOf σ)) :
    ↥(fixedSubgroup K (fieldAutHom e σ)) ≃* L2 (fixedField σ) :=
  (MulEquiv.subgroupCongr (range_pslToK e σ hodd)).symm.trans
    ((MonoidHom.ofInjective (pslToK_injective e σ)).symm.trans
      (L2.equivPSL (fixedField σ)).symm)

omit [Finite F] in
theorem pslIncl_fixedSubgroupEquivL2 (hodd : Odd (orderOf σ))
    (k : ↥(fixedSubgroup K (fieldAutHom e σ))) :
    pslIncl σ (L2.equivPSL (fixedField σ) (fixedSubgroupEquivL2 e σ hodd k)) = toPSL e k := by
  have h := MonoidHom.apply_ofInjective_symm (pslToK_injective e σ)
    ((MulEquiv.subgroupCongr (range_pslToK e σ hodd)).symm k)
  rw [← toPSL_pslToK e]
  have h2 : (L2.equivPSL (fixedField σ)) (fixedSubgroupEquivL2 e σ hodd k) =
      (MonoidHom.ofInjective (pslToK_injective e σ)).symm
        ((MulEquiv.subgroupCongr (range_pslToK e σ hodd)).symm k) := by
    simp [fixedSubgroupEquivL2]
  rw [h2]
  exact congrArg (toPSL e) (h.trans rfl)

theorem isL2_fixedSubgroup (hodd : Odd (orderOf σ)) :
    IsL2 ↥(fixedSubgroup K (fieldAutHom e σ)) (fun q₀ => q₀ ^ orderOf σ = Nat.card F) :=
  ⟨↥(fixedField σ), inferInstance, inferInstance, fixedField_card_pow σ,
    ⟨fixedSubgroupEquivL2 e σ hodd⟩⟩

theorem card_fixedSubgroup_of_odd (hodd : Odd (orderOf σ)) (hq : Odd (Nat.card F)) :
    Nat.card ↥(fixedSubgroup K (fieldAutHom e σ)) =
      Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) / 2 :=
  (Nat.card_congr (fixedSubgroupEquivL2 e σ hodd).toEquiv).trans
    ((Nat.card_congr (L2.equivPSL (fixedField σ)).toEquiv).trans
      (psl2_card_formula _ (isOddPrimePower_of_odd_card (odd_card_fixedField σ hq))))

end Odd

section Even

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K] (e : K ≃* L2 F) (σ : F ≃+* F)

theorem mul_conj_mul_inv_eq_conj_apply (f : MulAut K) (k : K) :
    f * MulAut.conj k * f⁻¹ = MulAut.conj (f k) := by
  ext x
  simp [MulAut.conj_apply]

theorem map_conj_fixedSubgroup_eq
    (hinj : Function.Injective (MulAut.conj : K →* MulAut K)) (f : MulAut K) :
    (fixedSubgroup K f).map (MulAut.conj : K →* MulAut K) =
      innAut K ⊓ centralizer ({f} : Set (MulAut K)) := by
  ext y
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨k, rfl⟩, ?_⟩
    show MulAut.conj k ∈ centralizer ({f} : Set (MulAut K))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : f k = k := hk
    have h := mul_conj_mul_inv_eq_conj_apply f k
    rw [hk'] at h
    calc MulAut.conj k * f = f * MulAut.conj k * f⁻¹ * f := by rw [h]
      _ = f * MulAut.conj k := by group
  · rintro ⟨⟨k, rfl⟩, hy⟩
    refine ⟨k, ?_, rfl⟩
    have hy' : MulAut.conj k ∈ centralizer ({f} : Set (MulAut K)) := hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy'
    show f k = k
    apply hinj
    rw [← mul_conj_mul_inv_eq_conj_apply, ← hy']
    group

theorem map_conj_fixedSubgroup_of_even (heven : Even (orderOf σ)) :
    (fixedSubgroup K (fieldAutHom e σ)).map (MulAut.conj : K →* MulAut K) =
      centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
  have h1 := map_conj_fixedSubgroup_eq (conj_injective_of_L2 e) (fieldAutHom e σ)
  have h2 : innAut K ⊓ centralizer ({fieldAutHom e σ} : Set (MulAut K)) =
      centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
    apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (innAut_le_innDiagSub e))
    · exact le_inf (centralizer_fieldAut_le_innAut e σ heven) inf_le_left
  rw [h1, h2]

@[expose] noncomputable def fixedSubgroupToPGL : ↥(fixedSubgroup K (fieldAutHom e σ)) →* PGL2 F :=
  (kToPGL e).comp (fixedSubgroup K (fieldAutHom e σ)).subtype

omit [Finite F] in
theorem fixedSubgroupToPGL_injective : Function.Injective (fixedSubgroupToPGL e σ) :=
  (kToPGL_injective e).comp Subtype.val_injective

theorem range_fixedSubgroupToPGL (heven : Even (orderOf σ)) :
    (fixedSubgroupToPGL e σ).range = (pgl2Incl σ).range := by
  ext A
  constructor
  · rintro ⟨k, rfl⟩
    exact (kToPGL_mem_range_pgl2Incl_iff e σ k).mpr k.2
  · intro hA
    have h0 : innDiagHom e A ∈
        centralizer ({fieldAutHom e σ} : Set (MulAut K)) ⊓ innDiagSub e := by
      rw [centralizer_fieldAut_eq_map e σ]
      exact ⟨A, hA, rfl⟩
    have h1 : innDiagHom e A ∈ innAut K := centralizer_fieldAut_le_innAut e σ heven h0
    obtain ⟨y, hy⟩ := (innDiagHom_mem_innAut_iff e A).mp h1
    have hk : kToPGL e ((toPSL e).symm y) = A := by
      rw [kToPGL_apply, MulEquiv.apply_symm_apply]
      exact hy
    have hkmem : (toPSL e).symm y ∈ fixedSubgroup K (fieldAutHom e σ) := by
      rw [← kToPGL_mem_range_pgl2Incl_iff e σ, hk]
      exact hA
    exact ⟨⟨(toPSL e).symm y, hkmem⟩, hk⟩

@[expose] noncomputable def fixedSubgroupEquivPGL2 (heven : Even (orderOf σ)) :
    ↥(fixedSubgroup K (fieldAutHom e σ)) ≃* PGL2 (fixedField σ) :=
  (MonoidHom.ofInjective (fixedSubgroupToPGL_injective e σ)).trans
    ((MulEquiv.subgroupCongr (range_fixedSubgroupToPGL e σ heven)).trans
      (MonoidHom.ofInjective (pgl2Incl_injective σ)).symm)

theorem pgl2Incl_fixedSubgroupEquivPGL2 (heven : Even (orderOf σ))
    (k : ↥(fixedSubgroup K (fieldAutHom e σ))) :
    pgl2Incl σ (fixedSubgroupEquivPGL2 e σ heven k) = kToPGL e k := by
  have h := MonoidHom.apply_ofInjective_symm (pgl2Incl_injective σ)
    (MulEquiv.subgroupCongr (range_fixedSubgroupToPGL e σ heven)
      (MonoidHom.ofInjective (fixedSubgroupToPGL_injective e σ) k))
  exact h.trans rfl

theorem isPGL2_fixedSubgroup (heven : Even (orderOf σ)) :
    IsPGL2 ↥(fixedSubgroup K (fieldAutHom e σ)) (fun q₀ => q₀ ^ orderOf σ = Nat.card F) :=
  ⟨↥(fixedField σ), inferInstance, inferInstance, fixedField_card_pow σ,
    ⟨fixedSubgroupEquivPGL2 e σ heven⟩⟩

theorem card_fixedSubgroup_of_even (heven : Even (orderOf σ)) :
    Nat.card ↥(fixedSubgroup K (fieldAutHom e σ)) =
      Nat.card (fixedField σ) * (Nat.card (fixedField σ) ^ 2 - 1) :=
  (Nat.card_congr (fixedSubgroupEquivPGL2 e σ heven).toEquiv).trans (pgl2_card_formula _)

end Even

theorem ivk_1_4a : IVK_1_4a := by
  intro F _ _ hF K _ _ e σ
  refine ⟨hasSL2Model_slFixed σ, ?_, ?_⟩
  · intro hodd
    refine ⟨isL2_fixedSubgroup e σ hodd, ?_⟩
    intro N x hx
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hord : orderOf (fieldAutHom e σ) = orderOf σ :=
      orderOf_injective (fieldAutHom e) (fieldAutHom_injective e) σ
    exact (N.F_odd_cent (fieldAutHom e σ) ⟨σ, rfl⟩ (hord ▸ hodd) x hx).symm
  · intro heven
    exact isPGL2_fixedSubgroup e σ heven

end CFSG.GH74.GLS.IVK
