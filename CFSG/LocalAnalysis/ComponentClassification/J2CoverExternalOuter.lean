module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternalFactor

public section

namespace CFSG.ComponentClassification.J2Cover.External

open Subgroup CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_conj_beta_of_outer {α : MulAut P} (h2 : orderOf α = 2) (hα : α ∉ inner P) :
    ∃ g : P, α = MulAut.conj g * betaAut * (MulAut.conj g)⁻¹ := by
  obtain ⟨r, rfl⟩ := rConj_bijective.2 α
  have hr2 : orderOf (r : Equiv.Perm (Fin 315)) = 2 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective rConj rConj_injective r, h2]
  have hrP : (r : Equiv.Perm (Fin 315)) ∉ P := by
    intro h
    apply hα
    rw [← map_rConj_P]
    exact ⟨r, by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact h, rfl⟩
  have hru : permU⁻¹ * r ∈ P := (mem_P_or_coset r.2).resolve_left hrP
  obtain ⟨c, hc, hrc⟩ := outer_classes.1 r hru hr2
  refine ⟨⟨c * permB⁻¹, P.mul_mem hc (P.inv_mem permB_mem)⟩, ?_⟩
  ext q
  simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
    rConj_apply, betaAut_apply, Models.bOut_eq_permU, hrc]
  group

theorem fixSub_conj {G : Type*} [Group G] (α γ : MulAut G) :
    fixSub (α * γ * α⁻¹) = (fixSub γ).map α.toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, mem_fixSub, mem_fixSub]
  simp only [MulAut.mul_apply, MulAut.inv_def]
  constructor
  · intro h
    apply α.injective
    rw [MulEquiv.apply_symm_apply, h]
  · intro h
    rw [h, MulEquiv.apply_symm_apply]

theorem conj_beta_apply_conj (g q : P) (hq : betaAut q = q) :
    (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) (g * q * g⁻¹) = g * q * g⁻¹ := by
  simp only [MulAut.mul_apply, ← map_inv, MulAut.conj_apply]
  rw [show g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q by group, hq]

theorem fixSub_conj_beta (g : P) :
    fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) = fixC.map (MulAut.conj g).toMonoidHom :=
  fixSub_conj _ _

theorem card_fixSub_conj_beta (g : P) :
    Nat.card (fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)) = 336 := by
  rw [fixSub_conj_beta, Subgroup.card_map_of_injective (MulAut.conj g).injective, card_fixC]

theorem commutator_fixSub_conj_beta (g : P) :
    ⁅fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹),
        fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)⁆ =
      fixD.map (MulAut.conj g).toMonoidHom := by
  rw [fixSub_conj_beta, ← Subgroup.map_commutator]

@[expose] noncomputable def conjFixDEquiv (g : P) : fixD.map (MulAut.conj g).toMonoidHom ≃* fixD :=
  (fixD.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm

theorem conj_conjFixDEquiv (g : P) (d : fixD.map (MulAut.conj g).toMonoidHom) :
    g * (conjFixDEquiv g d : P) * g⁻¹ = d :=
  congrArg Subtype.val ((fixD.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).apply_symm_apply d)

theorem fixD_map_conj_perfect (g : P) :
    ⁅fixD.map (MulAut.conj g).toMonoidHom, fixD.map (MulAut.conj g).toMonoidHom⁆ =
      fixD.map (MulAut.conj g).toMonoidHom := by
  rw [← Subgroup.map_commutator, fixD_perfect]

theorem card_fixD_map_conj (g : P) : Nat.card (fixD.map (MulAut.conj g).toMonoidHom) = 168 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_fixD]

theorem card_outer_fixD_map_conj (g : P) :
    Nat.card (Outer (fixD.map (MulAut.conj g).toMonoidHom)) ∣ 2 := by
  rw [Nat.card_congr (equivalence (conjFixDEquiv g)).toEquiv]
  exact card_outer_fixD

theorem center_fixD_map_conj (g : P) : center (fixD.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have h : conjFixDEquiv g z ∈ center fixD := by
    rw [mem_center_iff] at hz ⊢
    intro d
    obtain ⟨e, rfl⟩ := (conjFixDEquiv g).surjective d
    rw [← map_mul, ← map_mul, hz e]
  rw [center_fixD, mem_bot, MulEquiv.map_eq_one_iff] at h
  exact mem_bot.2 h

theorem centralizer_fixD_map_conj_inf (g : P) :
    centralizer (fixD.map (MulAut.conj g).toMonoidHom : Set P) ⊓
      fixC.map (MulAut.conj g).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  rintro q ⟨hq1, hq2⟩
  obtain ⟨q', hq', rfl⟩ := hq2
  have hc : q' ∈ centralizer (fixD : Set P) ⊓ fixC := by
    refine mem_inf.2 ⟨mem_centralizer_iff.2 fun d hd => ?_, hq'⟩
    have := mem_centralizer_iff.1 hq1 ((MulAut.conj g).toMonoidHom d) ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have h' : g * (d * q') * g⁻¹ = g * (q' * d) * g⁻¹ := by
      calc g * (d * q') * g⁻¹ = g * d * g⁻¹ * (g * q' * g⁻¹) := by group
        _ = g * q' * g⁻¹ * (g * d * g⁻¹) := this
        _ = g * (q' * d) * g⁻¹ := by group
    simpa using h'
  rw [centralizer_fixD_inf, mem_bot] at hc
  rw [hc, map_one]
  exact one_mem _

theorem fixCount_of_mem_fixD_map_conj (g : P) {d : P}
    (hd : d ∈ fixD.map (MulAut.conj g).toMonoidHom) (h2 : orderOf d = 2) :
    Models.fixCount (d : Equiv.Perm (Fin 315)) = 11 := by
  obtain ⟨e, he, rfl⟩ := hd
  have h2' : orderOf e = 2 := by
    rw [← h2, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [Models.fixCount_conj]
  exact fixCount_of_mem_fixD he h2'

theorem conj_elemC (g : P) :
    g * elemC * g⁻¹ ∈ fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹) ∧
      g * elemC * g⁻¹ ∉ ⁅fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹),
        fixSub (MulAut.conj g * betaAut * (MulAut.conj g)⁻¹)⁆ ∧
      orderOf (g * elemC * g⁻¹) = 2 ∧
      Models.fixCount ((g * elemC * g⁻¹ : P) : Equiv.Perm (Fin 315)) = 15 := by
  refine ⟨conj_beta_apply_conj g elemC elemC_mem, ?_, ?_, ?_⟩
  · rw [commutator_fixSub_conj_beta]
    rintro ⟨e, he, hee⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hee
    have : e = elemC := by simpa using hee
    exact elemC_not_mem (this ▸ he)
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, orderOf_elemC]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [Models.fixCount_conj]
    exact fixCount_elemC

end CFSG.ComponentClassification.J2Cover.External
