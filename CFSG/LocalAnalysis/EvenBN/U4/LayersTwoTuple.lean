module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersTwoModel
import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.LocalAnalysis.EvenBN.U4.LayersFieldBound

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf card_sup_mul_card_inf_eq)

noncomputable abbrev miyamotoH2G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) (t : G)
    (Q : Subgroup G) : Subgroup G :=
  normalizer (miyamotoF2G h L η t Q : Set G) ⊓ centralizer (miyamotoI2G h L η : Set G)

@[expose] noncomputable def miyamotoIN2HomSU {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) : (h.fixedField)ˣ →* gramSU h (miyamotoJ4 K) :=
  ((miyamotoIHom h).comp ((1 : (h.fixedField)ˣ →* Kˣ).prod
    (Units.map h.fixedField.subtype.toMonoidHom))).codRestrict _ fun β =>
      miyamotoI_le_gramSU h ((miyamotoIHom_mem_miyamotoI_iff h _).2
        (miyamotoIParam_one_eq_one h (β := Units.map h.fixedField.subtype.toMonoidHom β)
          ((h.mem_fixedField).1 (β : h.fixedField).2)))

@[expose] noncomputable def miyamotoIN2Hom {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {G : Type} [Group G] (L : Subgroup G)
    (η : L ≃* gramSU h (miyamotoJ4 K)) : (h.fixedField)ˣ →* G :=
  L.subtype.comp (η.symm.toMonoidHom.comp (miyamotoIN2HomSU h))

noncomputable abbrev miyamotoIN2G {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    {G : Type} [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) : Subgroup G :=
  miyamotoIG h L η ⊓ miyamotoN2G h L η

section IN2Hom

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem coe_miyamotoIN2HomSU (β : (h.fixedField)ˣ) :
    ((miyamotoIN2HomSU h β : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoIHom h (1, Units.map h.fixedField.subtype.toMonoidHom β) :=
  rfl

theorem miyamotoIN2Hom_injective : Function.Injective (miyamotoIN2Hom h L η) := by
  intro α β e
  have e1 : miyamotoIN2HomSU h α = miyamotoIN2HomSU h β := η.symm.injective (Subtype.ext e)
  have e2 := congrArg (fun g : gramSU h (miyamotoJ4 K) => (g : GL (Fin 4) K)) e1
  simp only [coe_miyamotoIN2HomSU] at e2
  have e3 := congrArg (fun u : Kˣ => (u : K)) (Prod.ext_iff.1 (miyamotoIHom_injective h e2)).2
  exact Units.ext (Subtype.ext e3)

theorem miyamotoIN2Hom_mem (β : (h.fixedField)ˣ) :
    miyamotoIN2Hom h L η β ∈ miyamotoIN2G h L η :=
  mem_inf.2 ⟨(symm_mem_miyamotoPull_iff h L η).2
      ((miyamotoIHom_mem_miyamotoI_iff h _).2 (miyamotoIParam_one_eq_one h
        ((h.mem_fixedField).1 (β : h.fixedField).2))),
    (symm_mem_miyamotoPull_iff h L η).2
      (miyamotoIHom_one_mem_N2 h ((h.mem_fixedField).1 (β : h.fixedField).2))⟩

theorem range_miyamotoIN2Hom : (miyamotoIN2Hom h L η).range = miyamotoIN2G h L η := by
  refine le_antisymm (fun _ ⟨β, hβ⟩ => hβ ▸ miyamotoIN2Hom_mem h L η β) fun x hx => ?_
  obtain ⟨hxI, hxN⟩ := mem_inf.1 hx
  obtain ⟨g, ⟨p, hp, hpg⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hxI
  have hgN : (g : GL (Fin 4) K) ∈ miyamotoN2 h := (symm_mem_miyamotoPull_iff h L η).1 hxN
  rw [← hpg] at hgN
  obtain ⟨hp1, hp2⟩ := eq_of_miyamotoIHom_mem_N2 h hgN
  have hp20 : ((p.2 : K) : K) ≠ 0 := p.2.ne_zero
  set β : (h.fixedField)ˣ := Units.mk0 ⟨(p.2 : K), (h.mem_fixedField).2 hp2⟩
    (fun e => hp20 (congrArg Subtype.val e)) with hβ
  refine ⟨β, ?_⟩
  change ((η.symm (miyamotoIN2HomSU h β) : L) : G) = _
  congr 2
  apply Subtype.ext
  rw [coe_miyamotoIN2HomSU, ← hpg]
  congr 1
  exact Prod.ext hp1.symm (Units.ext rfl)

theorem isCyclic_miyamotoIN2G : IsCyclic (miyamotoIN2G h L η) := by
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  rw [← range_miyamotoIN2Hom h L η]
  exact isCyclic_of_surjective _ (miyamotoIN2Hom h L η).rangeRestrict_surjective

theorem card_miyamotoIN2G : Nat.card (miyamotoIN2G h L η) = 2 ^ f - 1 := by
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  rw [← range_miyamotoIN2Hom h L η, Nat.card_congr (MonoidHom.ofInjective
    (miyamotoIN2Hom_injective h L η)).toEquiv.symm, Nat.card_units, h.card_fixedField]

end IN2Hom

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

@[expose] noncomputable def rootEltB (hS : Setting h L η t Q T) (b : h.fixedField) : G :=
  ((η.symm ⟨miyamotoXGL h 0 (b : K) 0 0,
    hS.rootB_le_SU ⟨(b : K), (h.mem_fixedField).1 b.2, rfl⟩⟩ : L) : G)

theorem rootEltB_mem (hS : Setting h L η t Q T) (b : h.fixedField) :
    hS.rootEltB b ∈ miyamotoPull h L η (miyamotoRootB h) :=
  (symm_mem_miyamotoPull_iff h L η).2 ⟨(b : K), (h.mem_fixedField).1 b.2, rfl⟩

theorem exists_rootEltB_eq (hS : Setting h L η t Q T) {u : G}
    (hu : u ∈ miyamotoPull h L η (miyamotoRootB h)) : ∃ b : h.fixedField, hS.rootEltB b = u := by
  obtain ⟨g, ⟨b, hb, hgb⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hu
  refine ⟨⟨b, (h.mem_fixedField).2 hb⟩, ?_⟩
  simp only [rootEltB]
  congr 2
  exact Subtype.ext hgb.symm

theorem rootEltB_add (hS : Setting h L η t Q T) (b b' : h.fixedField) :
    hS.rootEltB (b + b') = hS.rootEltB b * hS.rootEltB b' := by
  have : CharP K 2 := h.charP
  simp only [rootEltB]
  rw [← L.coe_mul, ← map_mul]
  congr 3
  change miyamotoXGL h 0 ((b + b' : h.fixedField) : K) 0 0 =
    miyamotoXGL h 0 (b : K) 0 0 * miyamotoXGL h 0 (b' : K) 0 0
  rw [miyamotoXGL_mul h ((h.mem_fixedField).1 b.2), miyamotoXGL_inj]
  simp

theorem rootEltB_zero (hS : Setting h L η t Q T) : hS.rootEltB 0 = 1 := by
  have := hS.rootEltB_add 0 0
  rw [add_zero] at this
  exact mul_left_cancel (a := hS.rootEltB 0) (by rw [mul_one, ← this])

theorem rootEltB_mul_self (hS : Setting h L η t Q T) (b : h.fixedField) :
    hS.rootEltB b * hS.rootEltB b = 1 := by
  have : CharP K 2 := h.charP
  rw [← hS.rootEltB_add, CharTwo.add_self_eq_zero, hS.rootEltB_zero]

theorem rootEltB_injective (hS : Setting h L η t Q T) : Function.Injective hS.rootEltB := by
  intro b b' e
  have e1 := η.symm.injective (Subtype.ext e)
  have e2 := congrArg (fun g : gramSU h (miyamotoJ4 K) => (g : GL (Fin 4) K)) e1
  simp only [miyamotoXGL_inj] at e2
  exact Subtype.ext e2.2.1

theorem miyamotoIN2Hom_inv_conj_rootEltB (hS : Setting h L η t Q T) (β : (h.fixedField)ˣ)
    (b : h.fixedField) :
    (miyamotoIN2Hom h L η β)⁻¹ * hS.rootEltB b * miyamotoIN2Hom h L η β =
      hS.rootEltB ((β : h.fixedField) ^ 2 * b) := by
  simp only [miyamotoIN2Hom, rootEltB, MonoidHom.coe_comp, Function.comp_apply,
    MulEquiv.coe_toMonoidHom, coe_subtype]
  rw [← L.coe_inv, ← L.coe_mul, ← L.coe_mul, ← map_inv, ← map_mul, ← map_mul]
  congr 3
  apply Subtype.ext
  simp only [coe_mul, coe_inv, coe_miyamotoIN2HomSU]
  rw [miyamotoIHom_conj_rootB, miyamotoWeightB_one h ((h.mem_fixedField).1 (β : h.fixedField).2)]
  simp

theorem miyamotoIN2Hom_conj_rootEltB (hS : Setting h L η t Q T) (β : (h.fixedField)ˣ)
    (b : h.fixedField) :
    miyamotoIN2Hom h L η β * hS.rootEltB b * (miyamotoIN2Hom h L η β)⁻¹ =
      hS.rootEltB (((β⁻¹ : (h.fixedField)ˣ) : h.fixedField) ^ 2 * b) := by
  have e1 : miyamotoIN2Hom h L η β = (miyamotoIN2Hom h L η β⁻¹)⁻¹ := by rw [map_inv, inv_inv]
  have e2 : (miyamotoIN2Hom h L η β)⁻¹ = miyamotoIN2Hom h L η β⁻¹ := (map_inv _ β).symm
  rw [e2, e1, hS.miyamotoIN2Hom_inv_conj_rootEltB]

theorem t_mem_centralizer_I2 (hS : Setting h L η t Q T) :
    t ∈ centralizer (miyamotoI2G h L η : Set G) :=
  mem_centralizer_iff.2 fun _ hs =>
    mem_centralizer_singleton_iff.1 (hS.IG_le_C (hS.tori_le_IG.2.2.2 hs))

theorem F_le_F2 (hS : Setting h L η t Q T) :
    miyamotoFG h L η t Q ≤ miyamotoF2G h L η t Q :=
  le_inf hS.F_le_D2 hS.F_le_RG

theorem RG_le_normalizer_F2 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ≤ normalizer (miyamotoF2G h L η t Q : Set G) := fun r hr =>
  mem_normalizer_fintype fun y hy => by
    have hyR : y ∈ miyamotoRG h L η t Q := (mem_inf.1 hy).2
    rw [show r * y * r⁻¹ = (r * y * r⁻¹ * y⁻¹) * y by group]
    exact mul_mem (hS.F_le_F2 (hS.commutator_RG_mem_F hr hyR)) hy

theorem t_mem_normalizer_F2 (hS : Setting h L η t Q T) :
    t ∈ normalizer (miyamotoF2G h L η t Q : Set G) :=
  mem_normalizer_inf (le_normalizer hS.t_mem_D2) hS.t_mem_normalizer_RG

theorem t_mem_H2 (hS : Setting h L η t Q T) : t ∈ miyamotoH2G h L η t Q :=
  ⟨hS.t_mem_normalizer_F2, hS.t_mem_centralizer_I2⟩

theorem N2G_le_centralizer_I2 (_hS : Setting h L η t Q T) :
    miyamotoN2G h L η ≤ centralizer (miyamotoI2G h L η : Set G) := fun _ hn =>
  mem_centralizer_iff.2 fun _ hi => I2G_commute_N2G h L η hi hn

theorem N2G_le_H2 (hS : Setting h L η t Q T) : miyamotoN2G h L η ≤ miyamotoH2G h L η t Q :=
  le_inf (le_sup_right.trans hS.I2N2_le_normalizer_F2) hS.N2G_le_centralizer_I2

theorem N2G_le_C (hS : Setting h L η t Q T) :
    miyamotoN2G h L η ≤ centralizer ({t} : Set G) :=
  (miyamotoPull_le h L η _).trans hS.L_le_centralizer

theorem t_mem_centralizer_N2 (hS : Setting h L η t Q T) :
    t ∈ centralizer (miyamotoN2G h L η : Set G) :=
  mem_centralizer_iff.2 fun _ hn => mem_centralizer_singleton_iff.1 (hS.N2G_le_C hn)

theorem rootB_le_N2G (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootB h) ≤ miyamotoN2G h L η :=
  miyamotoPull_mono h L η (miyamotoRootB_le_N2 h)

theorem card_rootB (hS : Setting h L η t Q T) :
    Nat.card (miyamotoPull h L η (miyamotoRootB h)) = 2 ^ f := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η hS.rootB_le_SU, card_miyamotoRootB]

theorem card_N2G (_hS : Setting h L η t Q T) :
    Nat.card (miyamotoN2G h L η) = 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  have : CharP K 2 := h.charP
  have := h.finite
  have : Finite h.fixedField := Subtype.finite
  rw [card_miyamotoPull h L η (miyamotoN2_le_gramSU h),
    ← Nat.card_congr (miyamotoN2Equiv h).toEquiv,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, h.card_fixedField]

theorem isSylowOf_rootB_N2 (hS : Setting h L η t Q T) :
    IsSylowOf 2 (miyamotoPull h L η (miyamotoRootB h)) (miyamotoN2G h L η) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card hS.rootB_le_N2G ?_
  have hodd : ¬ 2 ∣ (2 ^ f) ^ 2 - 1 := by
    have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h2 : Even ((2 ^ f) ^ 2) :=
      (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩, by norm_num⟩)
    exact Nat.not_even_iff_odd.2 (Nat.Even.sub_odd h1 h2 odd_one) ∘ (even_iff_two_dvd.2)
  have hne : (2 ^ f) ^ 2 - 1 ≠ 0 := fun e => hodd (e ▸ dvd_zero 2)
  rw [hS.card_rootB, hS.card_N2G, Nat.factorization_mul (by positivity) hne,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]

theorem IN2G_le_N2G (_hS : Setting h L η t Q T) :
    miyamotoIN2G h L η ≤ miyamotoN2G h L η :=
  inf_le_right

theorem IN2G_le_C (hS : Setting h L η t Q T) :
    miyamotoIN2G h L η ≤ centralizer ({t} : Set G) :=
  inf_le_left.trans hS.IG_le_C

theorem IN2G_le_normalizer_rootB (hS : Setting h L η t Q T) :
    miyamotoIN2G h L η ≤ normalizer (miyamotoPull h L η (miyamotoRootB h) : Set G) := by
  intro d hd
  rw [← range_miyamotoIN2Hom h L η] at hd
  obtain ⟨β, rfl⟩ := hd
  refine mem_normalizer_fintype fun u hu => ?_
  obtain ⟨b, rfl⟩ := hS.exists_rootEltB_eq hu
  rw [hS.miyamotoIN2Hom_conj_rootEltB]
  exact hS.rootEltB_mem _

theorem IN2G_inf_rootB (hS : Setting h L η t Q T) :
    miyamotoIN2G h L η ⊓ miyamotoPull h L η (miyamotoRootB h) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxU⟩ := mem_inf.1 hx
  have hodd : Odd (Nat.card (miyamotoIN2G h L η)) := hS.odd_card_of_le_IG inf_le_left
  obtain ⟨b, rfl⟩ := hS.exists_rootEltB_eq hxU
  refine mem_bot.2 (eq_one_of_odd_of_pow_two_pow_eq_one hodd hxD (k := 1) ?_)
  rw [pow_one, sq, hS.rootEltB_mul_self]

theorem rootB_sup_IN2G (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootB h) ⊔ miyamotoIN2G h L η =
      miyamotoN2G h L η ⊓ normalizer (miyamotoPull h L η (miyamotoRootB h) : Set G) := by
  have : CharP K 2 := h.charP
  refine le_antisymm (sup_le (le_inf hS.rootB_le_N2G le_normalizer)
    (le_inf hS.IN2G_le_N2G hS.IN2G_le_normalizer_rootB)) fun x hx => ?_
  obtain ⟨hxN, hxU⟩ := mem_inf.1 hx
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hxN
  have hconj : (g : GL (Fin 4) K)⁻¹ * miyamotoXGL h 0 1 0 0 * g ∈ miyamotoRootB h := by
    have h1 := (mem_normalizer_iff.1 (inv_mem hxU) (hS.rootEltB 1)).1 (hS.rootEltB_mem 1)
    rw [inv_inv] at h1
    have e : ((η.symm g : L) : G)⁻¹ * hS.rootEltB 1 * ((η.symm g : L) : G) =
        ((η.symm (g⁻¹ * ⟨miyamotoXGL h 0 1 0 0,
          hS.rootB_le_SU ⟨1, map_one _, rfl⟩⟩ * g) : L) : G) := by
      simp only [rootEltB, map_mul, map_inv, coe_mul, coe_inv, OneMemClass.coe_one]
    rw [e, symm_mem_miyamotoPull_iff] at h1
    simpa using h1
  obtain ⟨c, hc, β, hβ, hcβ⟩ := exists_eq_rootB_mul_of_conj_mem h hg hconj
  have hβ0 : (β : K) ≠ 0 := β.ne_zero
  set β' : (h.fixedField)ˣ := Units.mk0 ⟨(β : K), (h.mem_fixedField).2 hβ⟩
    (fun e => hβ0 (congrArg Subtype.val e)) with hβ'
  have e : ((η.symm g : L) : G) =
      hS.rootEltB ⟨c, (h.mem_fixedField).2 hc⟩ * miyamotoIN2Hom h L η β' := by
    simp only [rootEltB, miyamotoIN2Hom, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← L.coe_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    have hβ'β : Units.map h.fixedField.subtype.toMonoidHom β' = β := Units.ext rfl
    rw [coe_mul, coe_miyamotoIN2HomSU, hβ'β]
    exact hcβ
  rw [e]
  exact mul_mem (mem_sup_left (hS.rootEltB_mem _)) (mem_sup_right (miyamotoIN2Hom_mem h L η β'))

theorem IN2G_regular_rootB (hS : Setting h L η t Q T) :
    ∀ u ∈ miyamotoPull h L η (miyamotoRootB h), u ≠ 1 →
      ∀ w ∈ miyamotoPull h L η (miyamotoRootB h), w ≠ 1 →
        ∃! d : miyamotoIN2G h L η, (d : G) * u * (d : G)⁻¹ = w := by
  have : CharP K 2 := h.charP
  intro u hu hu1 w hw hw1
  obtain ⟨a, rfl⟩ := hS.exists_rootEltB_eq hu
  obtain ⟨b, rfl⟩ := hS.exists_rootEltB_eq hw
  have ha : a ≠ 0 := fun e => hu1 (by rw [e, hS.rootEltB_zero])
  have hb : b ≠ 0 := fun e => hw1 (by rw [e, hS.rootEltB_zero])
  have ha' : (a : K) ≠ 0 := fun e => ha (Subtype.ext e)
  have hb' : (b : K) ≠ 0 := fun e => hb (Subtype.ext e)
  have key : ∀ β : (h.fixedField)ˣ, miyamotoIN2Hom h L η β * hS.rootEltB a *
      (miyamotoIN2Hom h L η β)⁻¹ = hS.rootEltB b ↔
        ((β : h.fixedField) : K) ^ 2 = (a : K) / b := by
    intro β
    rw [hS.miyamotoIN2Hom_conj_rootEltB, hS.rootEltB_injective.eq_iff, Subtype.ext_iff]
    have hβ : ((β : h.fixedField) : K) ≠ 0 := fun e => β.ne_zero (Subtype.ext e)
    simp only [Subfield.coe_mul, SubmonoidClass.coe_pow, Units.val_inv_eq_inv_val,
      Subfield.coe_inv]
    constructor
    · intro e
      rw [← e]
      field_simp
    · intro e
      rw [inv_pow, e]
      field_simp
  obtain ⟨y, hy⟩ := exists_sq_eq h ((a : K) / b)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hy
    exact div_ne_zero ha' hb' hy.symm
  have hyF : h.bar y = y := by
    have hab : h.bar ((a : K) / b) = (a : K) / b := by
      rw [map_div₀, (h.mem_fixedField).1 a.2, (h.mem_fixedField).1 b.2]
    have e : (h.bar y) ^ 2 = y ^ 2 := by rw [← map_pow, hy, hab]
    exact eq_of_sq_eq_sq e
  set γ : (h.fixedField)ˣ := Units.mk0 ⟨y, (h.mem_fixedField).2 hyF⟩
    (fun e => hy0 (congrArg Subtype.val e)) with hγ
  refine ⟨⟨_, miyamotoIN2Hom_mem h L η γ⟩, (key γ).2 hy, fun d hd => ?_⟩
  have hd' : (d : G) ∈ (miyamotoIN2Hom h L η).range := (range_miyamotoIN2Hom h L η).ge d.2
  obtain ⟨β, hβ⟩ := hd'
  dsimp only at hd
  rw [← hβ] at hd
  have h1 := (key β).1 hd
  apply Subtype.ext
  rw [← hβ]
  change miyamotoIN2Hom h L η β = miyamotoIN2Hom h L η γ
  congr 1
  exact Units.ext (Subtype.ext (eq_of_sq_eq_sq (h1.trans hy.symm)))

theorem A1G_inf_centralizer_I2 (hS : Setting h L η t Q T) :
    miyamotoA1G h L η ⊓ centralizer (miyamotoI2G h L η : Set G) =
      miyamotoPull h L η (miyamotoRootB h) := by
  have : CharP K 2 := h.charP
  rw [← miyamotoPull_inf_centralizer h L η _ (miyamotoI2_le_SU h),
    miyamotoA1_inf_centralizer_I2 h hS.two_le]

theorem V2_le_H2 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ≤ miyamotoH2G h L η t Q :=
  le_inf (inf_le_left.trans hS.RG_le_normalizer_F2) inf_le_right

theorem V2_le_F1 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ≤ miyamotoF1G h L η t := by
  rw [hS.RG_inf_centralizer_I2]
  exact inf_le_left

theorem t_mem_normalizer_V2 (hS : Setting h L η t Q T) :
    t ∈ normalizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :
      Subgroup G) : Set G) :=
  mem_normalizer_inf hS.t_mem_normalizer_RG (le_normalizer hS.t_mem_centralizer_I2)

theorem isPGroup_V2 (hS : Setting h L η t Q T) :
    IsPGroup 2 (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) : Subgroup G) :=
  hS.isPGroup_RG.to_le inf_le_left

theorem card_V2 (hS : Setting h L η t Q T) :
    Nat.card (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) : Subgroup G) =
      (2 ^ f) ^ 2 := by
  set V := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) with hV
  have hVF : V ≤ normalizer (miyamotoFG h L η t Q : Set G) :=
    inf_le_left.trans hS.RG_le_normalizer_F
  have h1 := card_sup_mul_card_inf_eq hVF
  rw [← hS.F1_eq_F_sup] at h1
  have hinf : miyamotoFG h L η t Q ⊓ V = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    rw [← hS.F_inf_centralizer_I2]
    exact mem_inf.2 ⟨(mem_inf.1 hx).1, (mem_inf.1 (mem_inf.1 hx).2).2⟩
  rw [hinf, card_bot, mul_one, hS.card_F1, hS.card_F] at h1
  have hq : 0 < (2 ^ f) ^ 6 := by positivity
  have : (2 ^ f) ^ 8 = (2 ^ f) ^ 6 * (2 ^ f) ^ 2 := by ring
  rw [this] at h1
  exact (Nat.eq_of_mul_eq_mul_left hq h1).symm

theorem V2_comm (hS : Setting h L η t Q T) {v v' : G}
    (hv : v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G))
    (hv' : v' ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) :
    v * v' = v' * v :=
  hS.F1_comm (hS.V2_le_F1 hv) (hS.V2_le_F1 hv')

theorem rootB_le_V2 (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootB h) ≤
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) := by
  rw [← hS.A1G_inf_centralizer_I2]
  exact inf_le_inf_right _ (hS.A1_le_F1.trans (le_sup_left.trans hS.P1_le_miyamotoRG))

theorem V2_inf_C (hS : Setting h L η t Q T) :
    (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) ⊓
        centralizer ({t} : Set G) = miyamotoPull h L η (miyamotoRootB h) := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.rootB_le_V2
    ((hS.rootB_le_N2G).trans hS.N2G_le_C))
  obtain ⟨hxV, hxC⟩ := mem_inf.1 hx
  rw [← hS.A1G_inf_centralizer_I2, ← hS.F1_inf_C]
  exact mem_inf.2 ⟨mem_inf.2 ⟨hS.V2_le_F1 hxV, hxC⟩, (mem_inf.1 hxV).2⟩

theorem V2_inf_N2 (hS : Setting h L η t Q T) :
    (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) ⊓ miyamotoN2G h L η =
      miyamotoPull h L η (miyamotoRootB h) := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.rootB_le_V2 hS.rootB_le_N2G)
  rw [← hS.V2_inf_C]
  exact mem_inf.2 ⟨(mem_inf.1 hx).1, hS.N2G_le_C (mem_inf.1 hx).2⟩

theorem crossed_mem_rootB_of_mem_V2 (hS : Setting h L η t Q T) {v : G}
    (hv : v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G)) :
    v⁻¹ * t * v * t ∈ miyamotoPull h L η (miyamotoRootB h) ∧
      (v⁻¹ * t * v * t = 1 ↔ v ∈ miyamotoPull h L η (miyamotoRootB h)) := by
  have hvF := hS.V2_le_F1 hv
  refine ⟨?_, ?_⟩
  · rw [← hS.A1G_inf_centralizer_I2]
    exact mem_inf.2 ⟨hS.crossed_mem_A1_of_mem_D1 (hS.F1_le_D1 hvF),
      hS.crossed_mem_centralizer hS.tori_le_IG.2.2.2 (mem_inf.1 hv).2⟩
  · rw [hS.crossed_eq_one_iff_F1 hvF, ← hS.A1G_inf_centralizer_I2]
    exact ⟨fun hA => mem_inf.2 ⟨hA, (mem_inf.1 hv).2⟩, fun hU => (mem_inf.1 hU).1⟩

theorem closure_commutator_V2 (hS : Setting h L η t Q T) :
    closure {x | ∃ v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G),
      x = v⁻¹ * (t⁻¹ * v * t)} = miyamotoPull h L η (miyamotoRootB h) ∧
    ∀ u ∈ miyamotoPull h L η (miyamotoRootB h),
      ∃ v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G),
        v⁻¹ * t * v * t = u := by
  set V := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) with hVdef
  set U := miyamotoPull h L η (miyamotoRootB h) with hUdef
  have heq : ∀ v : G, v⁻¹ * (t⁻¹ * v * t) = v⁻¹ * t * v * t := fun v => by
    rw [hS.t_inv]; group
  have hmem : ∀ v ∈ V, v⁻¹ * (t⁻¹ * v * t) ∈ U := fun v hv => by
    rw [heq]
    exact (hS.crossed_mem_rootB_of_mem_V2 hv).1
  let ψ : V →* G :=
    { toFun := fun v => (v : G)⁻¹ * (t⁻¹ * v * t)
      map_one' := by simp
      map_mul' := fun v v' => by
        simp only [coe_mul, heq]
        exact hS.crossed_mul_D1 (hS.F1_le_D1 (hS.V2_le_F1 v.2))
          (hS.F1_le_D1 (hS.V2_le_F1 v'.2)) }
  have hker : ψ.ker = (V ⊓ centralizer ({t} : Set G)).subgroupOf V := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    change (w : G)⁻¹ * (t⁻¹ * w * t) = 1 ↔ _
    rw [inv_mul_eq_one]
    constructor
    · intro e
      refine ⟨w.2, ?_⟩
      calc (w : G) * t = t * (t⁻¹ * w * t) := by group
        _ = t * w := by rw [← e]
    · intro hw
      rw [mul_assoc, hw.2, inv_mul_cancel_left]
  have hcard := Subgroup.card_ker_mul_card_range ψ
  rw [hker, Nat.card_congr (subgroupOfEquivOfLe
      (inf_le_left : V ⊓ centralizer ({t} : Set G) ≤ V)).toEquiv, hS.V2_inf_C,
    hS.card_rootB, hS.card_V2] at hcard
  have hrange : ψ.range ≤ U := by
    rintro _ ⟨w, rfl⟩
    exact hmem w w.2
  have hcardr : Nat.card ψ.range = 2 ^ f := by
    have hq : 0 < 2 ^ f := by positivity
    have e : (2 ^ f) ^ 2 = 2 ^ f * 2 ^ f := sq _
    rw [e] at hcard
    exact Nat.eq_of_mul_eq_mul_left hq hcard
  have hrU : ψ.range = U :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hS.card_rootB, hcardr])
  refine ⟨le_antisymm ((closure_le _).2 fun x ⟨v, hv, hx⟩ => hx ▸ hmem v hv) ?_, fun u hu => ?_⟩
  · rw [← hrU]
    rintro _ ⟨w, rfl⟩
    exact subset_closure ⟨w, w.2, rfl⟩
  · rw [← hrU] at hu
    obtain ⟨w, rfl⟩ := hu
    exact ⟨w, w.2, (heq w).symm⟩

theorem IN2G_le_normalizer_V2 (hS : Setting h L η t Q T) :
    miyamotoIN2G h L η ≤ normalizer ((miyamotoRG h L η t Q ⊓
      centralizer (miyamotoI2G h L η : Set G) : Subgroup G) : Set G) := fun _ hd =>
  mem_normalizer_inf (hS.IG_le_normalizer_RG (mem_inf.1 hd).1)
    (hS.IG_le_normalizer_centralizer hS.tori_le_IG.2.2.2 (mem_inf.1 hd).1)

theorem IN2G_regular_V2 (hS : Setting h L η t Q T) :
    ∀ v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G),
      v ∉ miyamotoPull h L η (miyamotoRootB h) →
      ∀ w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G),
        w ∉ miyamotoPull h L η (miyamotoRootB h) →
        ∃! d : miyamotoIN2G h L η, ((d : G) * v * (d : G)⁻¹)⁻¹ * w ∈
          miyamotoPull h L η (miyamotoRootB h) := by
  intro v hv hvU w hw hwU
  obtain ⟨hcv, hcv1⟩ := hS.crossed_mem_rootB_of_mem_V2 hv
  obtain ⟨hcw, hcw1⟩ := hS.crossed_mem_rootB_of_mem_V2 hw
  refine (existsUnique_congr fun d => ?_).2 (hS.IN2G_regular_rootB _ hcv
    (fun e => hvU (hcv1.1 e)) _ hcw (fun e => hwU (hcw1.1 e)))
  have hdV : (d : G) * v * (d : G)⁻¹ ∈
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :=
    (mem_normalizer_iff.1 (hS.IN2G_le_normalizer_V2 d.2) v).1 hv
  have hdt : (d : G) * t = t * d := mem_centralizer_singleton_iff.1 (hS.IN2G_le_C d.2)
  have hx := mul_mem (inv_mem hdV) hw
  rw [← (hS.crossed_mem_rootB_of_mem_V2 hx).2, hS.crossed_mul_D1
    (hS.F1_le_D1 (hS.V2_le_F1 (inv_mem hdV))) (hS.F1_le_D1 (hS.V2_le_F1 hw)),
    hS.crossed_inv_D1 (hS.F1_le_D1 (hS.V2_le_F1 hdV)), hS.crossed_conj_of_commute hdt,
    inv_mul_eq_one]

theorem V2_le_of_le (hS : Setting h L η t Q T) {X : Subgroup G}
    (hUX : miyamotoPull h L η (miyamotoRootB h) ≤ X) (hDX : miyamotoIN2G h L η ≤ X)
    (hVX : miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ≤
      normalizer (X : Set G)) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) ≤ X := by
  have : CharP K 2 := h.charP
  intro v hv
  obtain ⟨s, hs, hs2⟩ := exists_fixed_unit_sq_ne_one h hS.two_le
  have hs0 : (s : K) ≠ 0 := s.ne_zero
  set β : (h.fixedField)ˣ := Units.mk0 ⟨(s : K), (h.mem_fixedField).2 hs⟩
    (fun e => hs0 (congrArg Subtype.val e)) with hβdef
  have hβK : (((β⁻¹ : (h.fixedField)ˣ) : h.fixedField) : K) = (s : K)⁻¹ := by
    rw [hβdef, Units.val_inv_eq_inv_val, Units.val_mk0, Subfield.coe_inv]
  set d := miyamotoIN2Hom h L η β with hd
  have hdX : d ∈ X := hDX (miyamotoIN2Hom_mem h L η β)
  have hdt : d * t = t * d :=
    mem_centralizer_singleton_iff.1 (hS.IN2G_le_C (miyamotoIN2Hom_mem h L η β))
  obtain ⟨b, hb⟩ := hS.exists_rootEltB_eq (hS.crossed_mem_rootB_of_mem_V2 hv).1
  set c : h.fixedField := ((β⁻¹ : (h.fixedField)ˣ) : h.fixedField) ^ 2 + 1 with hc
  have hc0 : c ≠ 0 := by
    intro e
    apply hs2
    have e' : ((s : K)⁻¹) ^ 2 + 1 = 0 := by
      have := congrArg Subtype.val e
      simp only [hc, Subfield.coe_add, SubmonoidClass.coe_pow, hβK, Subfield.coe_one,
        ZeroMemClass.coe_zero] at this
      exact this
    have e'' : ((s : K)⁻¹) ^ 2 = 1 := by
      linear_combination e' - CharTwo.two_eq_zero (R := K)
    rw [inv_pow] at e''
    exact inv_eq_one.1 e''
  obtain ⟨v', hv', hv'b⟩ := hS.closure_commutator_V2.2 (hS.rootEltB (c⁻¹ * b))
    (hS.rootEltB_mem _)
  have hdv' : d * v' * d⁻¹ ∈
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :=
    (mem_normalizer_iff.1 (hS.IN2G_le_normalizer_V2 (miyamotoIN2Hom_mem h L η β)) v').1 hv'
  set x := d * v' * d⁻¹ * v'⁻¹ with hx
  have hxV : x ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) :=
    mul_mem hdv' (inv_mem hv')
  have hxX : x ∈ X := by
    have h1 : v' * d⁻¹ * v'⁻¹ ∈ X := (mem_normalizer_iff.1 (hVX hv') _).1 (inv_mem hdX)
    rw [hx, show d * v' * d⁻¹ * v'⁻¹ = d * (v' * d⁻¹ * v'⁻¹) by group]
    exact mul_mem hdX h1
  have hcx : x⁻¹ * t * x * t = v⁻¹ * t * v * t := by
    rw [hx, hS.crossed_mul_D1 (hS.F1_le_D1 (hS.V2_le_F1 hdv'))
      (hS.F1_le_D1 (hS.V2_le_F1 (inv_mem hv'))), hS.crossed_conj_of_commute hdt,
      hS.crossed_inv_D1 (hS.F1_le_D1 (hS.V2_le_F1 hv')), hv'b, ← hb,
      hS.miyamotoIN2Hom_conj_rootEltB]
    have hinv : (hS.rootEltB (c⁻¹ * b))⁻¹ = hS.rootEltB (c⁻¹ * b) :=
      inv_eq_of_mul_eq_one_right (hS.rootEltB_mul_self _)
    rw [hinv, ← hS.rootEltB_add]
    congr 1
    calc ((β⁻¹ : (h.fixedField)ˣ) : h.fixedField) ^ 2 * (c⁻¹ * b) + c⁻¹ * b =
        (((β⁻¹ : (h.fixedField)ˣ) : h.fixedField) ^ 2 + 1) * c⁻¹ * b := by ring
      _ = c * c⁻¹ * b := by rw [← hc]
      _ = b := by rw [mul_inv_cancel₀ hc0, one_mul]
  have hU : x⁻¹ * v ∈ miyamotoPull h L η (miyamotoRootB h) := by
    refine (hS.crossed_mem_rootB_of_mem_V2 (mul_mem (inv_mem hxV) hv)).2.1 ?_
    rw [hS.crossed_mul_D1 (hS.F1_le_D1 (hS.V2_le_F1 (inv_mem hxV)))
      (hS.F1_le_D1 (hS.V2_le_F1 hv)), hS.crossed_inv_D1 (hS.F1_le_D1 (hS.V2_le_F1 hxV)), hcx,
      inv_mul_cancel]
  rw [show v = x * (x⁻¹ * v) by group]
  exact mul_mem hxX (hUX hU)

theorem exists_eq_mul_of_mem_C_I2 (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hxI : x ∈ centralizer (miyamotoI2G h L η : Set G)) :
    ∃ i ∈ miyamotoI2G h L η, ∃ n ∈ miyamotoN2G h L η, ∃ c ∈ centralizer (L : Set G),
      x = i * n * c := by
  have : CharP K 2 := h.charP
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, c, hc, hx⟩ := exists_eq_miyamotoI2_N2_mul_of_mem_centralizer h
    L η hS.two_le ⟨x, hS.centralizer_le_normalizer hxC⟩ hxI
  refine ⟨((η.symm ⟨i, miyamotoI2_le_SU h hi⟩ : L) : G), (symm_mem_miyamotoPull_iff h L η).2 hi,
    ((η.symm ⟨n, miyamotoN2_le_gramSU h hn⟩ : L) : G), (symm_mem_miyamotoPull_iff h L η).2 hn,
    c, hc, ?_⟩
  simp only at hx
  rw [hx, ← L.coe_mul, ← map_mul]
  congr 3
  exact Subtype.ext hs

theorem mem_normalizer_N2_of_mem_C_I2 (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hxI : x ∈ centralizer (miyamotoI2G h L η : Set G)) :
    x ∈ normalizer (miyamotoN2G h L η : Set G) := by
  obtain ⟨i, hi, n, hn, c, hc, rfl⟩ := hS.exists_eq_mul_of_mem_C_I2 hxC hxI
  refine mem_normalizer_fintype fun y hy => ?_
  have hcy : c * y * c⁻¹ = y := by
    rw [← mem_centralizer_iff.1 hc y (miyamotoPull_le h L η _ hy), mul_inv_cancel_right]
  have hny : n * y * n⁻¹ ∈ miyamotoN2G h L η := mul_mem (mul_mem hn hy) (inv_mem hn)
  have hiy : i * (n * y * n⁻¹) * i⁻¹ = n * y * n⁻¹ := by
    rw [I2G_commute_N2G h L η hi hny, mul_inv_cancel_right]
  have e : i * n * c * y * (i * n * c)⁻¹ = n * y * n⁻¹ := by
    calc i * n * c * y * (i * n * c)⁻¹ = i * (n * (c * y * c⁻¹) * n⁻¹) * i⁻¹ := by group
      _ = n * y * n⁻¹ := by rw [hcy, hiy]
  rw [SetLike.mem_coe, e]
  exact hny

theorem exists_eq_mul_of_mem_H2 (hS : Setting h L η t Q T) {x : G}
    (hxC : x ∈ centralizer ({t} : Set G)) (hx : x ∈ miyamotoH2G h L η t Q) :
    ∃ a ∈ miyamotoN2G h L η, ∃ c ∈ miyamotoH2G h L η t Q ⊓
      centralizer (miyamotoN2G h L η : Set G), x = a * c := by
  obtain ⟨i, hi, n, hn, c, hc, rfl⟩ := hS.exists_eq_mul_of_mem_C_I2 hxC hx.2
  have hin : i * n = n * i := I2G_commute_N2G h L η hi hn
  refine ⟨n, hn, i * c, mem_inf.2 ⟨?_, ?_⟩, by rw [hin, mul_assoc]⟩
  · have e : i * c = n⁻¹ * (i * n * c) := by rw [hin]; group
    rw [e]
    exact mul_mem (inv_mem (hS.N2G_le_H2 hn)) hx
  · refine mem_centralizer_iff.2 fun y hy => ?_
    have hyL : y ∈ L := miyamotoPull_le h L η _ hy
    have h1 : y * i = i * y := (I2G_commute_N2G h L η hi hy).symm
    have h2 : y * c = c * y := mem_centralizer_iff.1 hc y hyL
    rw [← mul_assoc, h1, mul_assoc, h2, mul_assoc]

theorem isSylowOf_zpowers_H2 (hS : Setting h L η t Q T) :
    IsSylowOf 2 (zpowers t)
      (miyamotoH2G h L η t Q ⊓ centralizer (miyamotoN2G h L η : Set G)) := by
  have : CharP K 2 := h.charP
  refine CFSG.ComponentClassification.AS81.Sec2Quot.isSylowOf_of_forall_mem_normalizer
    (zpowers_le.2 ⟨hS.t_mem_H2, hS.t_mem_centralizer_N2⟩)
    (IsPGroup.of_card (n := 1) (by rw [hS.card_zpowers_t, pow_one]))
    fun c hc hcN ⟨k, hk⟩ => ?_
  have hct : c ∈ centralizer ({t} : Set G) := by
    have h1 : c * t * c⁻¹ ∈ zpowers t := (mem_normalizer_iff.1 hcN t).1 (mem_zpowers t)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 h1
    rcases hS.zpow_t_eq j with e | e
    · exfalso
      apply hS.t_ne_one
      have : c * t * c⁻¹ = 1 := by rw [← hj, e]
      calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
        _ = 1 := by rw [this]; group
    · rw [mem_centralizer_singleton_iff]
      have : c * t * c⁻¹ = t := by rw [← hj, e]
      calc c * t = c * t * c⁻¹ * c := by group
        _ = t * c := by rw [this]
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, hα⟩ := (fixes_miyamotoI2_iff h hS.two_le
    (miyamotoAct h L η ⟨c, hS.centralizer_le_normalizer hct⟩)).mp
      fun g hg => miyamotoAct_apply_of_mem_centralizer h L η _ hc.1.2 hg
  have hfix : ∀ g ∈ miyamotoN2 h, i * n * g * (i * n)⁻¹ = g := by
    intro g hg
    have e := miyamotoAct_apply_of_mem_centralizer h L η ⟨c, hS.centralizer_le_normalizer hct⟩
      hc.2 (g := ⟨g, miyamotoN2_le_gramSU h hg⟩) hg
    have e2 := congrArg (fun y : gramSU h (miyamotoJ4 K) => (y : GL (Fin 4) K)) e
    simp only at e2
    rw [hα, MulAut.conj_apply, coe_mul, coe_mul, coe_inv, hs] at e2
    exact e2
  obtain rfl := eq_one_of_fixes_N2 h hi hn hfix
  rw [mul_one] at hs
  obtain ⟨z, hzL, hcz⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ s hα
  simp only at hcz
  set i' : G := ((η.symm s : L) : G) with hi'def
  have hi' : i' ∈ miyamotoI2G h L η := (symm_mem_miyamotoPull_iff h L η).2 (hs ▸ hi)
  have hzC : z ∈ centralizer ({t} : Set G) := by
    have hi'C : i' ∈ centralizer ({t} : Set G) := hS.IG_le_C (hS.tori_le_IG.2.2.2 hi')
    have := mul_mem (inv_mem hi'C) hct
    rwa [hcz, inv_mul_cancel_left] at this
  have hzt : z ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact mem_inf.2 ⟨hzL, hzC⟩
  have hiz : i' * z = z * i' := mem_centralizer_iff.1 hzL i' (miyamotoPull_le h L η _ hi')
  have hz2 : z ^ 2 = 1 := by
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hzt
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hS.t_two,
      pow_orderOf_eq_one, one_zpow]
  have hodd : Odd (Nat.card (miyamotoI2G h L η)) := hS.odd_card_of_le_IG hS.tori_le_IG.2.2.2
  have hi'1 : i' = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_zero, pow_one, hcz] at hk
      have h1 : i' ∈ L ⊓ centralizer (L : Set G) := by
        refine mem_inf.2 ⟨miyamotoPull_le h L η _ hi', ?_⟩
        rw [eq_inv_of_mul_eq_one_left hk]
        exact inv_mem hzL
      rw [hS.inf_centralizer_eq_bot, mem_bot] at h1
      exact h1
    · have hzk : z ^ 2 ^ k = 1 := by
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [pow_succ', pow_mul, hz2, one_pow]
      have : i' ^ 2 ^ k = 1 := by
        rw [hcz, (Commute.mul_pow hiz (2 ^ k)), hzk, mul_one] at hk
        exact hk
      exact eq_one_of_odd_of_pow_two_pow_eq_one hodd hi' this
  rw [hcz, hi'1, one_mul]
  exact hzt

theorem exists_mem_V2_not_mem_rootB (hS : Setting h L η t Q T) :
    ∃ v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G),
      v ∉ miyamotoPull h L η (miyamotoRootB h) := by
  by_contra hcon
  push Not at hcon
  have hle := Subgroup.card_le_of_le (show miyamotoRG h L η t Q ⊓
    centralizer (miyamotoI2G h L η : Set G) ≤ miyamotoPull h L η (miyamotoRootB h) from hcon)
  rw [hS.card_V2, hS.card_rootB] at hle
  have h4 := hS.four_le
  have : 2 ^ f < (2 ^ f) ^ 2 := by nlinarith
  omega

theorem exists_not_commute_of_isSylowOf_H2 (hS : Setting h L η t Q T) {S : Subgroup G}
    (hS2 : IsSylowOf 2 S (miyamotoH2G h L η t Q)) : ∃ x ∈ S, x * t ≠ t * x := by
  have : CharP K 2 := h.charP
  by_contra hcon
  push Not at hcon
  set V := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI2G h L η : Set G) with hVdef
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [hS.card_zpowers_t, pow_one])
  have hB2 : IsPGroup 2 (V ⊔ zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hS.isPGroup_V2 hz (zpowers_le.2 hS.t_mem_normalizer_V2)
  have hBH : V ⊔ zpowers t ≤ miyamotoH2G h L η t Q :=
    sup_le hS.V2_le_H2 (zpowers_le.2 hS.t_mem_H2)
  obtain ⟨c, hcH, hle⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
      hS2 hB2 hBH
  have hconjS : ∀ x ∈ V ⊔ zpowers t, c⁻¹ * x * c ∈ S := fun x hx =>
    hle (CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate hx c)
  set t' := c * t * c⁻¹ with ht'def
  have hV' : ∀ v ∈ V, v * t' = t' * v := by
    intro v hv
    have h2 := hcon _ (hconjS v (mem_sup_left hv))
    calc v * t' = c * ((c⁻¹ * v * c) * t) * c⁻¹ := by rw [ht'def]; group
      _ = c * (t * (c⁻¹ * v * c)) * c⁻¹ := by rw [h2]
      _ = t' * v := by rw [ht'def]; group
  have ht' : t' * t = t * t' := by
    have h2 := hcon _ (hconjS t (mem_sup_right (mem_zpowers t)))
    calc t' * t = c * (t * (c⁻¹ * t * c)) * c⁻¹ := by rw [ht'def]; group
      _ = c * ((c⁻¹ * t * c) * t) * c⁻¹ := by rw [h2]
      _ = t * t' := by rw [ht'def]; group
  have ht'H : t' ∈ miyamotoH2G h L η t Q :=
    mul_mem (mul_mem hcH hS.t_mem_H2) (inv_mem hcH)
  have ht'C : t' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 ht'
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, hα⟩ := (fixes_miyamotoI2_iff h hS.two_le
    (miyamotoAct h L η ⟨t', hS.centralizer_le_normalizer ht'C⟩)).mp
      fun g hg => miyamotoAct_apply_of_mem_centralizer h L η _ ht'H.2 hg
  have hfix : ∀ b : K, h.bar b = b → i * n * miyamotoXGL h 0 b 0 0 * (i * n)⁻¹ =
      miyamotoXGL h 0 b 0 0 := by
    intro b hb
    have ht'U : t' ∈ centralizer (miyamotoPull h L η (miyamotoRootB h) : Set G) :=
      mem_centralizer_iff.2 fun u hu => (hV' u (hS.rootB_le_V2 hu))
    have e := miyamotoAct_apply_of_mem_centralizer h L η
      ⟨t', hS.centralizer_le_normalizer ht'C⟩ ht'U
      (g := ⟨miyamotoXGL h 0 b 0 0, hS.rootB_le_SU ⟨b, hb, rfl⟩⟩) ⟨b, hb, rfl⟩
    have e2 := congrArg (fun y : gramSU h (miyamotoJ4 K) => (y : GL (Fin 4) K)) e
    simp only at e2
    rw [hα, MulAut.conj_apply, coe_mul, coe_mul, coe_inv, hs] at e2
    exact e2
  have hnU := mem_rootB_of_fixes h hi hn hfix
  obtain ⟨z, hzL, hz'⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ s hα
  simp only at hz'
  set l : G := ((η.symm s : L) : G) with hldef
  set i' : G := ((η.symm ⟨i, miyamotoI2_le_SU h hi⟩ : L) : G) with hi'def
  set n' : G := ((η.symm ⟨n, hS.rootB_le_SU hnU⟩ : L) : G) with hn'def
  have hi' : i' ∈ miyamotoI2G h L η := (symm_mem_miyamotoPull_iff h L η).2 hi
  have hn' : n' ∈ miyamotoPull h L η (miyamotoRootB h) :=
    (symm_mem_miyamotoPull_iff h L η).2 hnU
  have hl : l = i' * n' := by
    rw [hldef, hi'def, hn'def, ← L.coe_mul, ← map_mul]
    congr 2
    exact Subtype.ext hs
  have hlV : ∀ v ∈ V, l * v = v * l := by
    intro v hv
    have h1 : i' * v = v * i' := mem_centralizer_iff.1 hv.2 i' hi'
    have h2 : n' * v = v * n' := hS.V2_comm (hS.rootB_le_V2 hn') hv
    rw [hl, mul_assoc, h2, ← mul_assoc, h1, mul_assoc]
  have hlL : l ∈ L := (η.symm s).2
  have hzC : z ∈ centralizer ({t} : Set G) := by
    have hlC : l ∈ centralizer ({t} : Set G) := hS.L_le_centralizer hlL
    have := mul_mem (inv_mem hlC) ht'C
    rwa [hz', inv_mul_cancel_left] at this
  have hzt : z ∈ zpowers t := by
    rw [← hS.kernel_eq_zpowers']
    exact mem_inf.2 ⟨hzL, hzC⟩
  obtain ⟨j, hj⟩ := mem_zpowers_iff.1 hzt
  rcases hS.zpow_t_eq j with e | e
  · apply hS.conj_not_mem_L c⁻¹
    rw [inv_inv, ← ht'def, hz', ← hj, e, mul_one]
    exact hlL
  · rw [← hj, e] at hz'
    obtain ⟨v, hv, hvU⟩ := hS.exists_mem_V2_not_mem_rootB
    apply hvU
    rw [← hS.V2_inf_C]
    refine mem_inf.2 ⟨hv, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hV' v hv
    rw [hz'] at h1
    have h2 := hlV v hv
    calc v * t = l⁻¹ * (v * (l * t)) := by
          rw [← mul_assoc v l t, ← h2]; group
      _ = l⁻¹ * (l * t * v) := by rw [h1]
      _ = t * v := by group

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
