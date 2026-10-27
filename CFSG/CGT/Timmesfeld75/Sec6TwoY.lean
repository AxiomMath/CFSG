module

public import CFSG.CGT.Timmesfeld75.Sec6TwoSetup
public import CFSG.CGT.Timmesfeld75.L2Orbit
public import CFSG.CGT.Timmesfeld75.Sec4OneQuotient

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G}

omit [Finite G] in
theorem le_sup_of_map_subgroupOf_le {X N U V : Subgroup G} [(N.subgroupOf X).Normal]
    (hU : U ≤ X)
    (h : (U.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) ≤
      (V.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X))) : U ≤ V ⊔ N := by
  intro u hu
  have hmem : (QuotientGroup.mk' (N.subgroupOf X) (⟨u, hU hu⟩ : ↥X)) ∈
      (V.subgroupOf X).map (QuotientGroup.mk' (N.subgroupOf X)) :=
    h (Subgroup.mem_map.2 ⟨⟨u, hU hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩)
  obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.1 hmem
  have h1 := Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 hvu)
  have e : u = (v : G) * ((v : G)⁻¹ * u) := by group
  rw [e]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.1 hv) h1

theorem Sec3.exists_mem_conj_eq_of_le (hS : Sec3 T T₁) (hI : Sec3Iso T T₁) (hS₂ : Sec3 T T₂)
    (hle : T₂ ≤ T ⊔ T₁) (hne : T₂ ≠ T) : ∃ t ∈ T, T₂ = conjSubgroup t T₁ := by
  obtain ⟨hN, f, hf, hiso⟩ := hI
  have := hN
  have hpair := hS.isL2Pair_quotient hf hiso
  obtain ⟨x₀, hx₀, hT₁⟩ := hS.conj
  obtain ⟨z, hz, hT₂z⟩ := hS₂.conj
  have hzX : z ∈ T ⊔ T₁ := (sup_le le_sup_left hle) hz
  have hwc : IsWC T := hS.cfg.wc
  have hT2 : IsPGroup 2 T := isPGroup_two_of_isElemAbelian hwc.1
  have hM2 : IsPGroup 2 (cfgM T T₁) := isPGroup_two_of_isElemAbelian hS.cfg.isElemAbelian_cfgM
  have hXN : T ⊔ T₁ ≤ Subgroup.normalizer (cfgM T T₁ : Set G) := hS.cfg.le_normalizer_cfgM
  have e₁ : conjSubgroup (QuotientGroup.mk (⟨x₀, hx₀⟩ : ↥(T ⊔ T₁)) :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) =
      (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [conjSubgroup_map_subgroupOf (T ⊔ T₁) (cfgM T T₁) T ⟨x₀, hx₀⟩, ← hT₁]
  have e₂ : conjSubgroup (QuotientGroup.mk (⟨z, hzX⟩ : ↥(T ⊔ T₁)) :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) =
      (T₂.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [conjSubgroup_map_subgroupOf (T ⊔ T₁) (cfgM T T₁) T ⟨z, hzX⟩, ← hT₂z]
  have ha : conjSubgroup (QuotientGroup.mk (⟨x₀, hx₀⟩ : ↥(T ⊔ T₁)) :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ≠
      (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [e₁]
    exact hS.map_ne_map
  have hb : conjSubgroup (QuotientGroup.mk (⟨z, hzX⟩ : ↥(T ⊔ T₁)) :
      ↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ≠
      (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [e₂]
    intro heq
    have hP : IsPGroup 2 ↥(T ⊔ cfgM T T₁) :=
      hT2.to_sup_of_normal_right' hM2 (fun t ht => hXN (Subgroup.mem_sup_left ht))
    have hle' : T₂ ≤ T ⊔ cfgM T T₁ :=
      le_sup_of_map_subgroupOf_le hle (heq ▸ le_rfl)
    apply hne
    rw [hT₂z]
    exact eq_of_conj_le_pGroup hwc hP le_sup_left (hT₂z ▸ hle')
  obtain ⟨s, hsT, hs⟩ := hpair.exists_mem_conj_eq ha hb
  obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 hsT
  have e₃ := conjSubgroup_map_subgroupOf (T ⊔ T₁) (cfgM T T₁) T₁ t'
  have himg : (T₂.subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) =
      ((conjSubgroup (t' : G) T₁).subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [← e₂, hs, e₁]
    exact e₃
  have hle2 : T₂ ≤ conjSubgroup (t' : G) T₁ ⊔ cfgM T T₁ :=
    le_sup_of_map_subgroupOf_le hle himg.le
  have htT : (t' : G) ∈ T := Subgroup.mem_subgroupOf.1 ht'
  clear himg e₃ hs hsT e₁ e₂ ha hb ht'
  generalize (t' : G) = t at htT hle2
  have hT'eq : conjSubgroup t T₁ = conjSubgroup (t * x₀) T := by
    rw [hT₁, conjSubgroup_conjSubgroup]
  have hwc' : IsWC (conjSubgroup t T₁) := by
    rw [hT'eq]
    exact hwc.conj _
  have hT'le : conjSubgroup t T₁ ≤ T ⊔ T₁ :=
    conjSubgroup_le_of_le_of_mem le_sup_right (Subgroup.mem_sup_left htT)
  have hT'2 : IsPGroup 2 (conjSubgroup t T₁) :=
    isPGroup_two_of_isElemAbelian (isElemAbelian_conjSubgroup hS.cfg.wc₁.1 _)
  have hP' : IsPGroup 2 ↥(conjSubgroup t T₁ ⊔ cfgM T T₁) :=
    hT'2.to_sup_of_normal_right' hM2 (fun u hu => hXN (hT'le hu))
  refine ⟨t, htT, ?_⟩
  have hg : conjSubgroup (z * (t * x₀)⁻¹) (conjSubgroup t T₁) = T₂ := by
    rw [hT'eq, conjSubgroup_conjSubgroup, hT₂z]
    congr 1
    group
  have := eq_of_conj_le_pGroup hwc' hP' le_sup_left (g := z * (t * x₀)⁻¹)
    (by rw [hg]; exact hle2)
  rw [hg] at this
  exact this

section Data

variable {n m : ℕ} {x l : G}

theorem Sec62Data.eq_conj_of_le (hc : Sec6Ctx T T₁ n m) (d : Sec62Data T T₁ x l T₂)
    (hle : T₂ ≤ T ⊔ T₁) : ∃ s ∈ T, x * l = s⁻¹ * x * s := by
  have hP := hc.hy.pair
  have hI : Sec3Iso T T₁ :=
    sec3Iso_of_conj_conj hc.hI ⟨1, (conjSubgroup_one T).symm⟩ hP.conj hP.ne hP.nontriv
  obtain ⟨t, htT, hT₂t⟩ := hc.sec3.exists_mem_conj_eq_of_le hI (d.sec3₂ hc) hle (d.T₂_ne hc)
  have hyt : x * l ∈ conjSubgroup t T₁ := hT₂t ▸ d.hyT₂
  have hu : t⁻¹ * (x * l) * t ∈ T₁ := mem_conjSubgroup.1 hyt
  have hTab := hP.wc.1
  have hlt : l * t = t * l := elemAbelian_mul_comm hTab d.hl htT
  have hxN : x ∈ Subgroup.normalizer (T : Set G) := (mem_normIn.1 d.hx).2
  have hw : x⁻¹ * t⁻¹ * x * t * l ∈ T := by
    have h1 : x⁻¹ * t⁻¹ * x⁻¹⁻¹ ∈ T :=
      conj_mem_of_mem_normalizer ((Subgroup.normalizer (T : Set G)).inv_mem hxN) (T.inv_mem htT)
    have e : x⁻¹ * t⁻¹ * x * t * l = (x⁻¹ * t⁻¹ * x⁻¹⁻¹) * t * l := by group
    rw [e]
    exact T.mul_mem (T.mul_mem h1 htT) d.hl
  have hxu : x⁻¹ * (t⁻¹ * (x * l) * t) = x⁻¹ * t⁻¹ * x * t * l := by
    calc x⁻¹ * (t⁻¹ * (x * l) * t) = x⁻¹ * t⁻¹ * x * (l * t) := by group
      _ = x⁻¹ * t⁻¹ * x * (t * l) := by rw [hlt]
      _ = x⁻¹ * t⁻¹ * x * t * l := by group
  have hxT₁ : x ∈ T₁ := normIn_le _ _ d.hx
  have hmem : x⁻¹ * t⁻¹ * x * t * l ∈ T ⊓ T₁ := by
    refine ⟨hw, ?_⟩
    rw [← hxu]
    exact T₁.mul_mem (T₁.inv_mem hxT₁) hu
  rw [hc.sec3.cfg.inf, Subgroup.mem_bot] at hmem
  have hxu' : x⁻¹ * (t⁻¹ * (x * l) * t) = 1 := by rw [hxu, hmem]
  have h2 : t⁻¹ * (x * l) * t = x := by
    have := inv_mul_eq_one.1 hxu'
    exact this.symm
  refine ⟨t⁻¹, T.inv_mem htT, ?_⟩
  calc x * l = t * (t⁻¹ * (x * l) * t) * t⁻¹ := by group
    _ = t * x * t⁻¹ := by rw [h2]
    _ = t⁻¹⁻¹ * x * t⁻¹ := by rw [inv_inv]

end Data

end CFSG.CGT.Timmesfeld75
