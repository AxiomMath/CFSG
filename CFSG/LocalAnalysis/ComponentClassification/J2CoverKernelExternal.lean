module

public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverKernelBasic

public section

namespace CFSG.ComponentClassification.J2Cover.CyclicKernel

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.M12Cover.CyclicKernel (mem_or_mul_mem_of_mem_sup_zpowers
  eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two)

variable {X : Type*} [Group X] [Finite X]

theorem j2_external_data_of_mem_normalizer {L : Subgroup X}
    (hLq : CFSG.Assembly.IsQuasisimple L) {t : L} (ht : orderOf t = 2)
    (hZ : center L = zpowers t) (π : L →* P) (hπ : Function.Surjective π)
    (hker : π.ker = zpowers t) {p : X} (hpN : p ∈ normalizer (L : Set X)) (hp : orderOf p = 2)
    (hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set X)) (α : MulAut P)
    (hα : ∀ l l' : L, (l' : X) = p * l * p⁻¹ → α (π l) = π l') :
    (∀ q : X, q * p ∈ L → orderOf q = 2 → ∃ l : L, (l : X) * p * (l : X)⁻¹ = q) ∧
    Nat.card (fixSub α) = 336 ∧ Nat.card (⁅fixSub α, fixSub α⁆ : Subgroup P) = 168 ∧
    zpowers t ⊔ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ =
      (centralizer {p}).subgroupOf L ∧
    zpowers t ⊓ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ = ⊥ ∧
    (∃ e : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
        (⁅fixSub α, fixSub α⁆ : Subgroup P), ∀ a, (e a : P) = π a) ∧
    ⁅⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
        ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆⁆ =
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ ∧
    Nat.card (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) =
      168 ∧
    center (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) = ⊥ ∧
    Nat.card (Outer (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ :
      Subgroup L)) ∣ 2 ∧
    ∃ c ∈ fixSub α, c ∉ ⁅fixSub α, fixSub α⁆ ∧ orderOf c = 2 ∧
      ∀ v : L, π v = c → v ^ 2 = t ∧ p * (v : X) * p⁻¹ = v * t ∧
        (v : X) * p * (v : X)⁻¹ = t * p ∧
        (∀ a ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
          v * a * v⁻¹ ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆) ∧
        ¬ ∃ a ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
          ∀ x ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆,
            v * x * v⁻¹ = a * x * a⁻¹ := by
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
  set π₀ : L₀ →* P := π.comp e.toMonoidHom with hπ₀def
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
  have hα₀ : ∀ l : L₀, α (π₀ l) = π₀ (MulAut.conjNormal p₀ l) := by
    intro l
    refine hα (e l) (e (MulAut.conjNormal p₀ l)) ?_
    rw [hecoe, hecoe, MulAut.conjNormal_apply]
    rfl
  obtain ⟨hLconj, hfix⟩ :=
    ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section hL₀q ht₀ hZ₀ π₀ hπ₀
      hker₀ hCL₀
  obtain ⟨hF336, -, hD168, -, hsup₀, hinf₀, -, ⟨eA₀, heA₀⟩, hAperf₀, hA168₀, hAZ₀, hAout₀, c, hcF,
    hcD, hc2, -, hv₀⟩ := hfix p₀ hp₀L hp₀ α hα₀
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
  let eA := (MulEquiv.subgroupCongr hCC).trans ι.symm
  have heA : ∀ a, e (eA a : L₀) = (a : L) := by
    intro a
    have h := (coe_equivMapOfInjective_apply _ e.toMonoidHom hinj
      (ι.symm (MulEquiv.subgroupCongr hCC a))).symm.trans
      (congrArg Subtype.val (ι.apply_symm_apply (MulEquiv.subgroupCongr hCC a)))
    change e.toMonoidHom (ι.symm (MulEquiv.subgroupCongr hCC a)) = (a : L)
    rw [h]
    rfl
  have hmemA : ∀ x : L, x ∈ ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ ↔
      e.symm x ∈ ⁅(centralizer {p₀}).subgroupOf L₀, (centralizer {p₀}).subgroupOf L₀⁆ := by
    intro x
    rw [hCC, mem_map_equiv]
  refine ⟨?_, hF336, hD168, ?_, ?_, ⟨eA.trans eA₀, fun a => ?_⟩, ?_, ?_, ?_, ?_, c, hcF, hcD,
    hc2, fun v hv => ?_⟩
  ·
    intro q hqp hq
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
  · rw [hTT, hCC, ← Subgroup.map_sup, hsup₀, hCC₀]
  · rw [hTT, hCC, ← map_inf_eq _ _ _ hinj, hinf₀, Subgroup.map_bot]
  · rw [MulEquiv.trans_apply, heA₀]
    change π (e (eA a)) = π a
    rw [heA a]
  · rw [hCC, ← map_commutator, hAperf₀]
  · rw [hCC, card_map_of_injective hinj, hA168₀]
  · exact External.center_eq_bot_of_mulEquiv eA hAZ₀
  · rw [Nat.card_congr (equivalence eA).toEquiv]
    exact hAout₀
  ·
    have hv₀c : π₀ (e.symm v) = c := by
      rw [hπ₀def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hv]
    obtain ⟨hv2, hpv, hvA, hvout, hvp⟩ := hv₀ (e.symm v) hv₀c
    have hvX : (((e.symm v : L₀) : H₀) : X) = v := hesymm v
    refine ⟨?_, ?_, ?_, fun a ha => ?_, ?_⟩
    · apply e.symm.injective
      rw [map_pow, hv2, ht₀def]
    · have h := congrArg Subtype.val hpv
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hvX, ht₀X] at h
      exact h
    · have h := congrArg Subtype.val hvp
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hvX, ht₀X] at h
      exact h
    · rw [hmemA, map_mul, map_mul, map_inv]
      exact hvA _ ((hmemA a).1 ha)
    · rintro ⟨b, hb, hall⟩
      refine hvout ⟨e.symm b, (hmemA b).1 hb, fun x hx => ?_⟩
      have h := hall (e x) ((hmemA (e x)).2 (by rwa [MulEquiv.symm_apply_apply]))
      apply e.injective
      rw [map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
      exact h

theorem j2_outer_involution_fixed_factor {L : Subgroup X} (hLq : CFSG.Assembly.IsQuasisimple L)
    {t : L} (ht : orderOf t = 2) (hZ : center L = zpowers t) (π : L →* P)
    (hπ : Function.Surjective π) (hker : π.ker = zpowers t) {p : X}
    (hpN : p ∈ normalizer (L : Set X)) (hp : orderOf p = 2)
    (hpC : ∀ l ∈ L, l * p ∉ centralizer (L : Set X)) (α : MulAut P)
    (hα : ∀ l l' : L, (l' : X) = p * l * p⁻¹ → α (π l) = π l')
    {A : Subgroup X} (hA : A = ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆) :
    A ≤ L ∧ zpowers (t : X) ⊔ A = L ⊓ centralizer {p} ∧ zpowers (t : X) ⊓ A = ⊥ ∧
    ⁅A, A⁆ = A ∧ Nat.card A = 168 ∧ center A = ⊥ ∧ Nat.card (Outer A) ∣ 2 ∧
    (∀ q : X, q * p ∈ L → orderOf q = 2 → ∃ l : L, (l : X) * p * (l : X)⁻¹ = q) ∧
    ∃ v ∈ L, v ^ 2 = t ∧ p * v * p⁻¹ = v * t ∧ v * p * v⁻¹ = t * p ∧
      (∀ x ∈ A, v * x * v⁻¹ ∈ A) ∧ (¬ ∃ b ∈ A, ∀ x ∈ A, v * x * v⁻¹ = b * x * b⁻¹) ∧
      ∀ l ∈ L, p * l * p⁻¹ = l * t → v⁻¹ * l ∈ L ⊓ centralizer {p} := by
  classical
  subst hA
  obtain ⟨hfus, hF336, hD168, hsup, hinf, ⟨eC, heC⟩, hperf, hcard, hZA, hout, c, hcF, hcD, -,
    hc⟩ := j2_external_data_of_mem_normalizer hLq ht hZ π hπ hker hpN hp hpC α hα
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hAeq : ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ =
      ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆.map L.subtype := by
    rw [map_commutator, subgroupOf_map_subtype, inf_comm]
  have hAL : ⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ ≤ L := by
    rw [hAeq]
    exact map_subtype_le _
  have hTX : zpowers (t : X) = (zpowers t).map L.subtype := by
    rw [MonoidHom.map_zpowers]
    rfl
  let eAX : (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆ : Subgroup L) ≃*
      (⁅L ⊓ centralizer {p}, L ⊓ centralizer {p}⁆ : Subgroup X) :=
    (⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆.equivMapOfInjective
      L.subtype L.subtype_injective).trans (MulEquiv.subgroupCongr hAeq.symm)
  obtain ⟨v, hv⟩ := hπ c
  obtain ⟨hv2, hpv, hvp, hvA, hvout⟩ := hc v hv
  refine ⟨hAL, ?_, ?_, ?_, ?_, External.center_eq_bot_of_mulEquiv eAX.symm hZA, ?_, hfus, v, v.2,
    by rw [← SubgroupClass.coe_pow, hv2], hpv, hvp, fun x hx => ?_, ?_, fun l hl hlt => ?_⟩
  · rw [hTX, hAeq, ← Subgroup.map_sup, hsup, subgroupOf_map_subtype, inf_comm]
  · rw [hTX, hAeq, ← map_inf_eq _ _ _ L.subtype_injective, hinf, Subgroup.map_bot]
  · rw [hAeq, ← map_commutator, hperf]
  · rw [hAeq, card_map_of_injective L.subtype_injective, hcard]
  · rw [← Nat.card_congr (equivalence eAX).toEquiv]
    exact hout
  ·
    rw [hAeq] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨v * y * v⁻¹, hvA y hy, rfl⟩
  ·
    rintro ⟨b, hb, hall⟩
    rw [hAeq] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    refine hvout ⟨b', hb', fun x hx => Subtype.ext ?_⟩
    have h := hall x (by rw [hAeq]; exact ⟨x, hx, rfl⟩)
    simpa using h
  ·
    set l' : L := ⟨l, hl⟩ with hl'def
    have hplL : p * l * p⁻¹ ∈ L := (mem_normalizer_iff.mp hpN l).mp hl
    have hl'eq : (⟨p * l * p⁻¹, hplL⟩ : L) = l' * t := Subtype.ext hlt
    have hπt : π t = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact mem_zpowers t
    have hfix : π l' ∈ fixSub α := by
      rw [mem_fixSub, hα l' ⟨p * l * p⁻¹, hplL⟩ rfl, hl'eq, map_mul, hπt, mul_one]
    have hpre : ∀ x : L, π x ∈ ⁅fixSub α, fixSub α⁆ → x ∈ (centralizer {p}).subgroupOf L := by
      intro x hx
      obtain ⟨a, ha⟩ := eC.surjective ⟨π x, hx⟩
      have hπa : π a = π x := by rw [← heC a, ha]
      have hk : (a : L)⁻¹ * x ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπa, inv_mul_cancel]
      rw [hker] at hk
      have h := mul_mem (mem_sup_right a.2 : (a : L) ∈ zpowers t ⊔
        ⁅(centralizer {p}).subgroupOf L, (centralizer {p}).subgroupOf L⁆) (mem_sup_left hk)
      rwa [mul_inv_cancel_left, hsup] at h
    have hlD : π l' ∉ ⁅fixSub α, fixSub α⁆ := by
      intro h
      have h1 := hpre l' h
      rw [mem_subgroupOf, mem_centralizer_singleton_iff] at h1
      have h1' : l * p = p * l := h1
      have h2 : p * l * p⁻¹ = l := by
        rw [← h1', mul_inv_cancel_right]
      rw [h2] at hlt
      exact ht1 (Subtype.ext (mul_eq_left.mp hlt.symm))
    have hDF : ⁅fixSub α, fixSub α⁆ ≤ fixSub α := commutator_le_self _
    have hidx : ((⁅fixSub α, fixSub α⁆ : Subgroup P).subgroupOf (fixSub α)).index = 2 := by
      have h := ((⁅fixSub α, fixSub α⁆ : Subgroup P).subgroupOf (fixSub α)).card_mul_index
      rw [Nat.card_congr (subgroupOfEquivOfLe hDF).toEquiv, hD168, hF336] at h
      omega
    have hvF : π v ∈ fixSub α := hv ▸ hcF
    have hmul : (⟨(π v)⁻¹, inv_mem hvF⟩ : fixSub α) * ⟨π l', hfix⟩ ∈
        (⁅fixSub α, fixSub α⁆ : Subgroup P).subgroupOf (fixSub α) := by
      rw [mul_mem_iff_of_index_two hidx, mem_subgroupOf, mem_subgroupOf]
      refine iff_of_false (fun h => hcD ?_) hlD
      rw [← hv]
      simpa using inv_mem h
    rw [mem_subgroupOf] at hmul
    have hvl := hpre (v⁻¹ * l') (by rw [map_mul, map_inv]; exact hmul)
    rw [mem_subgroupOf] at hvl
    exact mem_inf.mpr ⟨mul_mem (inv_mem v.2) hl, by simpa using hvl⟩

end CFSG.ComponentClassification.J2Cover.CyclicKernel
