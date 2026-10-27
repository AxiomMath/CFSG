module

public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalConjugacy
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverExternalFixed

public section

namespace CFSG.ComponentClassification.M12Cover.CyclicKernel

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms

variable {X : Type*} [Group X] [Finite X]

theorem external_data_of_mem_normalizer {L : Subgroup X} (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* NativeSporadic.M12)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {p : X}
    (hpN : p ∈ normalizer (L : Set X)) (hp : orderOf p = 2)
    (hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set X)) (α : MulAut NativeSporadic.M12)
    (hα : ∀ l l' : L, (l' : X) = p * l * p⁻¹ → α (π l) = π l') :
    orderOf α = 2 ∧ α ∉ inner NativeSporadic.M12 ∧
    (∃ v : L, v ^ 2 = t ∧ (v : X) * p * (v : X)⁻¹ = t * p) ∧
    (∀ q : X, q * p ∈ L → orderOf q = 2 → ∃ l : L, (l : X) * p * (l : X)⁻¹ = q) ∧
    (∃ g : NativeSporadic.M12, α = MulAut.conj g * beta * (MulAut.conj g)⁻¹) ∧
    ((centralizer {p}).subgroupOf L).map π = ⁅fixSub α, fixSub α⁆ ∧
    zpowers t ⊔ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
      (centralizer {p}).subgroupOf L ∧
    zpowers t ⊓ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ = ⊥ ∧
    ∃ e : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
        (⁅fixSub α, fixSub α⁆ : Subgroup NativeSporadic.M12),
      ∀ a, (e a : NativeSporadic.M12) = π a := by
  classical
  have hp2 : p * p = 1 := by rw [← sq, ← hp, pow_orderOf_eq_one]
  have hpL : p ∉ L := fun h => hpC p⁻¹ (inv_mem h) (by rw [inv_mul_cancel]; exact one_mem _)
  have htZ : t ∈ center L := hZ ▸ mem_zpowers t
  set H₀ : Subgroup X := L ⊔ zpowers p with hH₀
  have hLH₀ : L ≤ H₀ := le_sup_left
  have hpH₀ : p ∈ H₀ := mem_sup_right (mem_zpowers p)
  have hH₀N : H₀ ≤ normalizer (L : Set X) := sup_le le_normalizer (zpowers_le.mpr hpN)
  have hcos : ∀ x : H₀, (x : X) ∈ L ∨ (x : X) * p ∈ L := fun x =>
    mem_or_mul_mem_of_mem_sup_zpowers hpN hp2 x.2
  set L₀ : Subgroup H₀ := L.subgroupOf H₀ with hL₀
  have : L₀.Normal := (normal_subgroupOf_iff_le_normalizer hLH₀).mpr hH₀N
  set e : L₀ ≃* L := subgroupOfEquivOfLe hLH₀ with he
  have hecoe : ∀ x : L₀, ((e x : L) : X) = ((x : H₀) : X) := fun x => rfl
  have hesymm : ∀ x : L, (((e.symm x : L₀) : H₀) : X) = x := fun x =>
    subgroupOfEquivOfLe_symm_apply_coe_coe hLH₀ x
  have hL₀q : CFSG.Assembly.IsQuasisimple L₀ :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv e hLq
  set t₀ : L₀ := e.symm t with ht₀def
  have het₀ : e t₀ = t := e.apply_symm_apply t
  have ht₀X : ((t₀ : H₀) : X) = t := hesymm t
  have ht₀ : orderOf t₀ = 2 := by rw [ht₀def, MulEquiv.orderOf_eq, ht]
  have hZ₀ : center L₀ = zpowers t₀ := by
    ext x
    have h := (map_center_eq e).symm
    rw [hZ] at h
    constructor
    · intro hx
      have hx' : e x ∈ zpowers t := by
        rw [h]
        exact ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hx'
      exact mem_zpowers_iff.mpr ⟨k, e.injective (by rw [map_zpow, het₀, hk])⟩
    · intro hx
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
      exact zpow_mem (show t₀ ∈ center L₀ by
        have : t ∈ map (e : L₀ →* L) (center L₀) := by rw [← h]; exact mem_zpowers t
        obtain ⟨y, hy, hyt⟩ := this
        have : y = t₀ := e.injective (by rw [het₀]; exact hyt)
        rwa [← this]) k
  set π₀ : L₀ →* NativeSporadic.M12 := π.comp e.toMonoidHom with hπ₀def
  have hπ₀ : Function.Surjective π₀ := hπ.comp e.surjective
  have hker₀ : π₀.ker = zpowers t₀ := by
    ext x
    rw [MonoidHom.mem_ker, hπ₀def, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker,
      MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      exact mem_zpowers_iff.mpr ⟨k, e.injective (by rw [map_zpow, het₀, hk])⟩
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
      exact mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow, het₀]⟩
  have hkerZ₀ : π₀.ker = center L₀ := hker₀.trans hZ₀.symm
  set p₀ : H₀ := ⟨p, hpH₀⟩ with hp₀def
  have hp₀L : p₀ ∉ L₀ := fun h => hpL (mem_subgroupOf.mp h)
  have hp₀ : orderOf p₀ = 2 := by rw [hp₀def, Subgroup.orderOf_mk, hp]
  have hCL₀ : centralizer (L₀ : Set H₀) = zpowers (t₀ : H₀) := by
    apply le_antisymm
    · intro x hx
      have hxC : (x : X) ∈ centralizer (L : Set X) := by
        rw [mem_centralizer_iff]
        intro l hl
        exact congrArg Subtype.val
          (mem_centralizer_iff.mp hx ⟨l, hLH₀ hl⟩ (mem_subgroupOf.mpr hl))
      rcases hcos x with hxL | hxp
      · have hxZ : (⟨x, hxL⟩ : L) ∈ center L := mem_center_iff.mpr fun l =>
          Subtype.ext (mem_centralizer_iff.mp hxC l l.2)
        rw [hZ] at hxZ
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hxZ
        refine mem_zpowers_iff.mpr ⟨k, Subtype.ext ?_⟩
        rw [SubgroupClass.coe_zpow, ht₀X, ← SubgroupClass.coe_zpow, hk]
      · exact absurd (show (x : X) * p * p ∈ centralizer (L : Set X) by
          rwa [mul_assoc, hp2, mul_one]) (hpC _ hxp)
    · rw [zpowers_le, mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      simp only [Subgroup.coe_mul, ht₀X]
      exact congrArg Subtype.val (mem_center_iff.mp htZ ⟨y, mem_subgroupOf.mp hy⟩)
  have hidx : L₀.index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨p₀, fun b => ?_⟩
    rcases hcos b with hb | hb
    · refine Or.inr ⟨mem_subgroupOf.mpr hb, fun h => hpL ?_⟩
      have h' : (b : X) * p ∈ L := mem_subgroupOf.mp h
      simpa using L.mul_mem (L.inv_mem hb) h'
    · refine Or.inl ⟨mem_subgroupOf.mpr hb, fun h => hpL ?_⟩
      have h' : (b : X) ∈ L := mem_subgroupOf.mp h
      simpa using L.mul_mem (L.inv_mem h') hb
  have hα₀ : ∀ l : L₀, α (π₀ l) = π₀ (MulAut.conjNormal p₀ l) := by
    intro l
    refine hα (e l) (e (MulAut.conjNormal p₀ l)) ?_
    rw [hecoe, hecoe, MulAut.conjNormal_apply]
    rfl
  have hQ₀ : Nonempty (L₀ ⧸ center L₀ ≃* NativeSporadic.M12) :=
    ⟨CentralCover.quotientEquivOfKerEqCenter π₀ hπ₀ hkerZ₀⟩
  obtain ⟨hv, hLconj, -⟩ :=
    ctss_m12_central_double_cover_external_involution_conjugacy_frontier hL₀q ht₀ hZ₀ hQ₀ hCL₀
  obtain ⟨v, hv2, hvp, -⟩ := hv p₀ hp₀L hp₀
  have hconj : IsConj p₀ ((t₀ : H₀) * p₀) := isConj_iff.2 ⟨v, hvp⟩
  have : Group.IsPerfect L₀ := Group.isPerfect_def.2 hL₀q.1
  have hCL₀le : centralizer (L₀ : Set H₀) ≤ L₀ := by
    rw [hCL₀, zpowers_le]
    exact t₀.2
  obtain ⟨hα2, hαo⟩ := fullAction_outer_involution π₀ hπ₀ hkerZ₀ hCL₀le hp₀L hp₀
  have hθ : CentralCover.fullAction π₀ hπ₀ hkerZ₀ p₀ = α := by
    ext q
    obtain ⟨l, rfl⟩ := hπ₀ q
    rw [CentralCover.fullAction_apply, hα₀]
  rw [hθ] at hα2 hαo
  obtain ⟨hmap₀, -, -, -, ⟨g, hg⟩, -⟩ :=
    ctss_m12_central_double_cover_conjugate_lifts_have_exact_fixed_quotient hL₀q ht₀ hZ₀ π₀ hπ₀
      hker₀ hCL₀ hidx hp₀L hp₀ hconj α hα₀
  obtain ⟨-, -, hsup₀, hinf₀, -, ⟨eA₀, heA₀, -⟩, -⟩ :=
    ctss_m12_central_double_cover_external_fixed_section_frontier hL₀q ht₀ hZ₀ π₀ hπ₀ hker₀ hCL₀
      hidx hp₀L hp₀ hconj α hα₀
  have hCC₀ : ((centralizer {p₀}).subgroupOf L₀).map e.toMonoidHom =
      (centralizer {p}).subgroupOf L := by
    ext x
    rw [mem_map_equiv, mem_subgroupOf, mem_subgroupOf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff, Subtype.ext_iff, Subgroup.coe_mul, Subgroup.coe_mul, hesymm]
  have hCC : ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
      ⁅(centralizer {p₀}).subgroupOf L₀, (centralizer {p₀}).subgroupOf L₀⁆.map
        e.toMonoidHom := by
    rw [map_commutator, hCC₀]
  have hTT : zpowers t = (zpowers t₀).map e.toMonoidHom := by
    rw [MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom, het₀]
  have hinj : Function.Injective e.toMonoidHom := e.injective
  let ι := ⁅(centralizer {p₀}).subgroupOf L₀, (centralizer {p₀}).subgroupOf L₀⁆.equivMapOfInjective
    e.toMonoidHom hinj
  refine ⟨hα2, hαo, ⟨e v, ?_, ?_⟩, ?_, ⟨g, hg⟩, ?_, ?_, ?_,
    (MulEquiv.subgroupCongr hCC).trans (ι.symm.trans eA₀), fun a => ?_⟩
  · rw [← map_pow, hv2, het₀]
  · have h := congrArg Subtype.val hvp
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, ht₀X] at h
    rw [hecoe]
    exact h
  · intro q hqp hq
    have hqH₀ : q ∈ H₀ := by
      have hq' : q = q * p * p := by rw [mul_assoc, hp2, mul_one]
      rw [hq']
      exact H₀.mul_mem (hLH₀ hqp) hpH₀
    have hq₀L : (⟨q, hqH₀⟩ : H₀) ∉ L₀ := fun h => hpL (by
      simpa using L.mul_mem (L.inv_mem (mem_subgroupOf.mp h)) hqp)
    have hq₀ : orderOf (⟨q, hqH₀⟩ : H₀) = 2 := by rw [Subgroup.orderOf_mk, hq]
    obtain ⟨l, hl⟩ := hLconj p₀ ⟨q, hqH₀⟩ hp₀L hp₀ hq₀L hq₀
    refine ⟨e l, ?_⟩
    rw [hecoe]
    have h := congrArg Subtype.val hl
    simpa using h
  · rw [← hCC₀, map_map]
    exact hmap₀
  · rw [hTT, hCC, ← Subgroup.map_sup, hsup₀, hCC₀]
  · rw [hTT, hCC, ← map_inf_eq _ _ _ hinj, hinf₀, Subgroup.map_bot]
  · have h := (coe_equivMapOfInjective_apply _ e.toMonoidHom hinj
      (ι.symm (MulEquiv.subgroupCongr hCC a))).symm.trans
      (congrArg Subtype.val (ι.apply_symm_apply (MulEquiv.subgroupCongr hCC a)))
    change (eA₀ (ι.symm (MulEquiv.subgroupCongr hCC a)) : NativeSporadic.M12) = π a
    rw [heA₀]
    change π (e.toMonoidHom _) = π a
    rw [h]
    rfl

end CFSG.ComponentClassification.M12Cover.CyclicKernel
