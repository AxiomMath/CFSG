module

public import CFSG.LocalAnalysis.SteinbergBVSp6NonnormalLayer

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open Subgroup CFSG.Blueprint

section QcFactorB

variable {H : Type*} [Group H]

theorem qcMulSelf {a : H} (ha : orderOf a = 2) : a * a = 1 := by
  rw [← pow_two, ← ha, pow_orderOf_eq_one]

theorem qcConjConj {a : H} (ha : orderOf a = 2) (x : H) : a * (a * x * a⁻¹) * a⁻¹ = x := by
  have haa := qcMulSelf ha
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  rw [hainv]
  calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
    _ = x := by rw [haa, one_mul, mul_one]

theorem qcPairCentreBot {a : H} (ha : orderOf a = 2) {K J : Subgroup H} (hKs : IsSimpleGroup K)
    (hZ : center K = ⊥) [Nontrivial J]
    (hcomm : ∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj a).toMonoidHom, x * y = y * x)
    (hJa : J ≤ centralizer ({a} : Set H))
    (hJn : centralizer ({a} : Set H) ≤ normalizer (J : Set H))
    (hJW : J ≤ K ⊔ K.map (MulAut.conj a).toMonoidHom) : center J = ⊥ := by
  classical
  set c : H →* H := (MulAut.conj a).toMonoidHom with hc
  have hc_apply : ∀ x, c x = a * x * a⁻¹ := fun x => by
    rw [hc]
    simp
  have hcc : ∀ x, c (c x) = x := fun x => by
    rw [hc_apply, hc_apply]
    exact qcConjConj ha x
  have hcfix : ∀ z, c z = z ↔ z ∈ centralizer ({a} : Set H) := fun z => by
    rw [hc_apply, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc z * a = (a * z * a⁻¹) * a := by rw [h]
        _ = a * z := by group
    · intro h
      rw [← h, mul_inv_cancel_right]
  set K₁ := K.map c with hK₁def
  have hc₁ : ∀ x ∈ K, c x ∈ K₁ := fun x hx => mem_map_of_mem c hx
  have hc₂ : ∀ y ∈ K₁, c y ∈ K := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hcc]
    exact hx
  have hcap : ∀ x ∈ K, x ∈ K₁ → x = 1 := by
    intro x hx₁ hx₂
    have hz : (⟨x, hx₁⟩ : K) ∈ center K := mem_center_iff.2 fun g =>
      Subtype.ext (hcomm g g.2 x hx₂)
    rw [hZ, mem_bot] at hz
    exact congrArg Subtype.val hz
  have hsplit : ∀ d ∈ K ⊔ K₁, ∃ x ∈ K, ∃ y ∈ K₁, d = x * y := by
    intro d hd
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right K K₁
      (CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayer.le_normalizer_of_le_centralizer
        fun x hx => mem_centralizer_iff.2 fun y hy => (hcomm x hx y hy).symm)] at hd
    obtain ⟨x, hx, y, hy, rfl⟩ := hd
    exact ⟨x, hx, y, hy, rfl⟩
  let δ : K →* H :=
    { toFun := fun x => (x : H) * c x
      map_one' := by simp
      map_mul' := fun x y => by
        show ((x : H) * y) * c ((x : H) * y) = ((x : H) * c x) * ((y : H) * c y)
        rw [map_mul]
        calc (x : H) * y * (c x * c y) = x * (y * c x) * c y := by group
          _ = x * (c x * y) * c y := by rw [hcomm y y.2 (c x) (hc₁ x x.2)]
          _ = x * c x * (y * c y) := by group }
  have hδ : ∀ x : K, δ x = (x : H) * c x := fun x => rfl
  have hδinj : Function.Injective δ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hδ] at hx
    have hx' : (x : H) = (c x)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have h1 := hcap x x.2 (hx' ▸ K₁.inv_mem (hc₁ x x.2))
    exact mem_bot.2 (Subtype.ext h1)
  have hδrange : δ.range = (K ⊔ K₁) ⊓ centralizer ({a} : Set H) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨(K ⊔ K₁).mul_mem (mem_sup_left x.2) (mem_sup_right (hc₁ x x.2)), (hcfix _).1 ?_⟩
      rw [hδ, map_mul, hcc]
      exact (hcomm x x.2 (c x) (hc₁ x x.2)).symm
    · rintro d ⟨hd, hda⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := hsplit d hd
      have hcd := (hcfix _).2 hda
      rw [map_mul] at hcd
      have h1 : x⁻¹ * c y = y * (c x)⁻¹ := by
        calc x⁻¹ * c y = x⁻¹ * (c y * c x) * (c x)⁻¹ := by group
          _ = x⁻¹ * (c x * c y) * (c x)⁻¹ := by rw [hcomm (c y) (hc₂ y hy) (c x) (hc₁ x hx)]
          _ = x⁻¹ * (x * y) * (c x)⁻¹ := by rw [hcd]
          _ = y * (c x)⁻¹ := by group
      have h2 := hcap _ (K.mul_mem (K.inv_mem hx) (hc₂ y hy))
        (h1 ▸ K₁.mul_mem hy (K₁.inv_mem (hc₁ x hx)))
      have hyx : y = c x := by
        have : c y = x := by
          calc c y = x * (x⁻¹ * c y) := by group
            _ = x := by rw [h2, mul_one]
        rw [← this, hcc]
      exact ⟨⟨x, hx⟩, by rw [hδ, hyx]⟩
  have hJC : J ≤ (K ⊔ K₁) ⊓ centralizer ({a} : Set H) := le_inf hJW hJa
  have hsimpleC : IsSimpleGroup ((K ⊔ K₁) ⊓ centralizer ({a} : Set H) : Subgroup H) :=
    ((MonoidHom.ofInjective hδinj).trans (MulEquiv.subgroupCongr hδrange)).symm.isSimpleGroup
  have hJeq : J = (K ⊔ K₁) ⊓ centralizer ({a} : Set H) := by
    refine le_antisymm hJC ?_
    have hn : (J.subgroupOf ((K ⊔ K₁) ⊓ centralizer ({a} : Set H))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hJC).2 (inf_le_right.trans hJn)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (J.subgroupOf ((K ⊔ K₁) ⊓ centralizer ({a} : Set H))) with h | h
    · exfalso
      obtain ⟨j, hj1⟩ := exists_ne (1 : J)
      have hj : (⟨j, hJC j.2⟩ : ((K ⊔ K₁) ⊓ centralizer ({a} : Set H) : Subgroup H)) ∈
          J.subgroupOf ((K ⊔ K₁) ⊓ centralizer ({a} : Set H)) := j.2
      rw [h, mem_bot] at hj
      have h' : (j : H) = 1 := congrArg Subtype.val hj
      exact hj1 (Subtype.ext h')
    · intro x hx
      have : (⟨x, hx⟩ : ((K ⊔ K₁) ⊓ centralizer ({a} : Set H) : Subgroup H)) ∈
          J.subgroupOf ((K ⊔ K₁) ⊓ centralizer ({a} : Set H)) := h ▸ mem_top _
      exact this
  let e : K ≃* J :=
    (MonoidHom.ofInjective hδinj).trans (MulEquiv.subgroupCongr (hδrange.trans hJeq.symm))
  rw [eq_bot_iff]
  intro z hz
  rw [mem_bot]
  have hz' : e.symm z ∈ center K := by
    rw [mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact mem_center_iff.1 hz (e g)
  rw [hZ, mem_bot] at hz'
  rw [← e.apply_symm_apply z, hz', map_one]

theorem qcSingleFactor {a : H} {K J : Subgroup H} (hKs : IsSimpleGroup K) (hZ : center K = ⊥)
    [Nontrivial J] (hJn : centralizer ({a} : Set H) ≤ normalizer (J : Set H)) (hJK : J ≤ K) :
    center J = ⊥ ∨ ∃ d ∈ K, a⁻¹ * d * a ≠ d := by
  by_cases hd : ∃ d ∈ K, a⁻¹ * d * a ≠ d
  · exact Or.inr hd
  · left
    push Not at hd
    have hKC : K ≤ centralizer ({a} : Set H) := fun d hd' => by
      rw [mem_centralizer_singleton_iff]
      calc d * a = a * (a⁻¹ * d * a) := by group
        _ = a * d := by rw [hd d hd']
    have hKn : (J.subgroupOf K).Normal :=
      (normal_subgroupOf_iff_le_normalizer hJK).2 (hKC.trans hJn)
    have hKJ : K ≤ J := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.subgroupOf K) with h | h
      · exfalso
        obtain ⟨j, hj1⟩ := exists_ne (1 : J)
        have hj : (⟨j, hJK j.2⟩ : K) ∈ J.subgroupOf K := j.2
        rw [h, mem_bot] at hj
        have h' : (j : H) = 1 := congrArg Subtype.val hj
        exact hj1 (Subtype.ext h')
      · exact subgroupOf_eq_top.1 h
    rw [le_antisymm hJK hKJ]
    exact hZ

end QcFactorB

theorem quasi_layer_factor_of_le_pair {H : Type} [Group H] [Finite H]
    (hF : CFSG.fittingSubgroup H = ⊥) {J : Subgroup H} (hJq : CFSG.Open.IsQuasisimple ↥J)
    {a : H} (ha : orderOf a = 2) (haJ : a ∈ centralizer (J : Set H))
    (hJn : (J.subgroupOf (centralizer ({a} : Set H))).Normal) {K : Subgroup H}
    (hK : CFSG.IsComponent K) (hJK : J ≤ K ⊔ K.map (MulAut.conj a).toMonoidHom) :
    center J = ⊥ ∨
      (IsSimpleGroup ↥K ∧ a ∈ normalizer (K : Set H) ∧ J ≤ K ∧ ∃ d ∈ K, a⁻¹ * d * a ≠ d) := by
  have hZK : center K = ⊥ :=
    CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayer.center_eq_bot_of_fitting_eq_bot hF hK
  have hKs : IsSimpleGroup K :=
    (CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayer.isSimpleGroup_of_isComponent hK hZK).1
  have hJq' : CFSG.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J).1 hJq
  haveI : Nontrivial J := CFSG.LocalCores.isQuasisimple_nontrivial hJq'
  have hJa : J ≤ centralizer ({a} : Set H) := fun j hj =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 haJ j hj)
  have hJn' : centralizer ({a} : Set H) ≤ normalizer (J : Set H) :=
    (normal_subgroupOf_iff_le_normalizer hJa).1 hJn
  by_cases hKa : K.map (MulAut.conj a).toMonoidHom = K
  · have hJK' : J ≤ K := by
      rw [hKa, sup_idem] at hJK
      exact hJK
    have hmem : ∀ h, h ∈ K → a * h * a⁻¹ ∈ K := fun h hh => by
      have := mem_map_of_mem (MulAut.conj a).toMonoidHom hh
      rw [hKa] at this
      simpa using this
    have hNa : a ∈ normalizer (K : Set H) :=
      Subgroup.mem_normalizer_iff.2 fun h =>
        ⟨hmem h, fun hh => by simpa [qcConjConj ha h] using hmem _ hh⟩
    rcases qcSingleFactor hKs hZK hJn' hJK' with h | h
    · exact Or.inl h
    · exact Or.inr ⟨hKs, hNa, hJK', h⟩
  · left
    have hK₁ : CFSG.IsComponent (K.map (MulAut.conj a).toMonoidHom) :=
      CFSG.LocalCores.isComponent_map_mulEquiv _ hK
    have hcomm : ∀ x ∈ K, ∀ y ∈ K.map (MulAut.conj a).toMonoidHom, x * y = y * x := by
      intro x hx y hy
      rcases CFSG.LocalCores.distinct_components_commute hK hK₁ with h | h
      · exact absurd h.symm hKa
      · exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h hx) y hy).symm
    exact qcPairCentreBot ha hKs hZK hcomm hJa hJn' hJK

end CFSG.LocalAnalysis.EvenBN.GMSK
