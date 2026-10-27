module

public import CFSG.LocalAnalysis.EvenBN.U4.LayersFieldBound

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open CFSG.ComponentClassification.AschbacherTightEmbedding (rightConjugate)
open CFSG.LocalAnalysis.EvenBN.Common (mem_normalizer_inf)

@[expose] noncomputable def miyamotoDHomSU {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) : Kˣ →* gramSU h (miyamotoJ4 K) :=
  ((miyamotoIHom h).comp ((MonoidHom.id Kˣ).prod invMonoidHom)).codRestrict _ fun α =>
    miyamotoI_le_gramSU h ((miyamotoIHom_mem_miyamotoI_iff h (α, α⁻¹)).2
      (miyamotoIParam_inv_eq_one h α))

@[expose] noncomputable def miyamotoDHom {f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData 2 f K) {G : Type} [Group G] (L : Subgroup G)
    (η : L ≃* gramSU h (miyamotoJ4 K)) : Kˣ →* G :=
  L.subtype.comp (η.symm.toMonoidHom.comp (miyamotoDHomSU h))

noncomputable abbrev miyamotoDG {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type}
    [Group G] (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K)) : Subgroup G :=
  miyamotoIG h L η ⊓ miyamotoN1G h L η

section DHom

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {G : Type} [Group G]
  (L : Subgroup G) (η : L ≃* gramSU h (miyamotoJ4 K))

theorem coe_miyamotoDHomSU (α : Kˣ) :
    ((miyamotoDHomSU h α : gramSU h (miyamotoJ4 K)) : GL (Fin 4) K) =
      miyamotoIHom h (α, α⁻¹) :=
  rfl

theorem miyamotoDHom_injective : Function.Injective (miyamotoDHom h L η) := by
  intro α β e
  have e1 : miyamotoDHomSU h α = miyamotoDHomSU h β :=
    η.symm.injective (Subtype.ext e)
  have e2 := congrArg (fun g : gramSU h (miyamotoJ4 K) => (g : GL (Fin 4) K)) e1
  simp only [coe_miyamotoDHomSU] at e2
  exact (Prod.ext_iff.1 (miyamotoIHom_injective h e2)).1

theorem miyamotoDHom_mem (α : Kˣ) : miyamotoDHom h L η α ∈ miyamotoDG h L η :=
  mem_inf.2 ⟨(symm_mem_miyamotoPull_iff h L η).2
      ((miyamotoIHom_mem_miyamotoI_iff h _).2 (miyamotoIParam_inv_eq_one h α)),
    (symm_mem_miyamotoPull_iff h L η).2 (miyamotoIHom_inv_mem_N1 h α)⟩

theorem range_miyamotoDHom : (miyamotoDHom h L η).range = miyamotoDG h L η := by
  refine le_antisymm (fun _ ⟨α, hα⟩ => hα ▸ miyamotoDHom_mem h L η α) fun x hx => ?_
  obtain ⟨hxI, hxN⟩ := mem_inf.1 hx
  obtain ⟨g, ⟨p, hp, hpg⟩, rfl⟩ := (mem_miyamotoPull h L η).1 hxI
  have hgN : (g : GL (Fin 4) K) ∈ miyamotoN1 h := (symm_mem_miyamotoPull_iff h L η).1 hxN
  rw [← hpg] at hgN
  have hp2 := eq_inv_of_miyamotoIHom_mem_N1 h hgN
  refine ⟨p.1, ?_⟩
  change ((η.symm (miyamotoDHomSU h p.1) : L) : G) = _
  congr 2
  apply Subtype.ext
  rw [coe_miyamotoDHomSU, ← hpg, ← hp2]

theorem isCyclic_miyamotoDG : IsCyclic (miyamotoDG h L η) := by
  have := h.finite
  rw [← range_miyamotoDHom h L η]
  exact isCyclic_of_surjective _ (miyamotoDHom h L η).rangeRestrict_surjective

theorem card_miyamotoDG : Nat.card (miyamotoDG h L η) = (2 ^ f) ^ 2 - 1 := by
  rw [← range_miyamotoDHom h L η, Nat.card_congr (MonoidHom.ofInjective
    (miyamotoDHom_injective h L η)).toEquiv.symm, Nat.card_units, h.card_eq_sq]

end DHom

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

theorem miyamotoDHom_eq_torusElt (hS : Setting h L η t Q T) (α : Kˣ) :
    miyamotoDHom h L η α = hS.torusElt (α, α⁻¹) (miyamotoIParam_inv_eq_one h α) :=
  rfl

theorem miyamotoDHom_conj_rootElt (hS : Setting h L η t Q T) (β : Kˣ) (a : K) :
    miyamotoDHom h L η β * hS.rootElt a * (miyamotoDHom h L η β)⁻¹ =
      hS.rootElt (((β⁻¹ ^ 2 : Kˣ) : K) * a) := by
  have e1 : miyamotoDHom h L η β = (miyamotoDHom h L η β⁻¹)⁻¹ := by rw [map_inv, inv_inv]
  have e2 : (miyamotoDHom h L η β)⁻¹ = miyamotoDHom h L η β⁻¹ := (map_inv _ β).symm
  rw [e2, e1, miyamotoDHom_eq_torusElt hS β⁻¹, hS.torusElt_conj_rootElt, miyamotoWeightA_inv]

theorem crossedQ1_miyamotoDHom_conj (hS : Setting h L η t Q T) (β : Kˣ) {s : G}
    (hs : s ∈ normalizer ((miyamotoF1G h L η t ⊔ Q : Subgroup G) : Set G)) :
    hS.crossedQ1 (miyamotoDHom h L η β * s * (miyamotoDHom h L η β)⁻¹) =
      ((β⁻¹ ^ 2 : Kˣ) : K) * hS.crossedQ1 s := by
  have e1 : miyamotoDHom h L η β = (miyamotoDHom h L η β⁻¹)⁻¹ := by rw [map_inv, inv_inv]
  have e2 : (miyamotoDHom h L η β)⁻¹ = miyamotoDHom h L η β⁻¹ := (map_inv _ β).symm
  rw [e2, e1, miyamotoDHom_eq_torusElt hS β⁻¹, hS.crossedQ1_torus_conj _ _ hs,
    miyamotoWeightA_inv]

theorem rootA_le_N1G (_hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ≤ miyamotoN1G h L η :=
  miyamotoPull_mono h L η (miyamotoRootA_le_N1 h)

theorem card_rootA (hS : Setting h L η t Q T) :
    Nat.card (miyamotoPull h L η (miyamotoRootA h)) = (2 ^ f) ^ 2 := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η hS.rootA_le_SU, card_miyamotoRootA]

theorem card_N1G (_hS : Setting h L η t Q T) :
    Nat.card (miyamotoN1G h L η) = (2 ^ f) ^ 2 * ((2 ^ f) ^ 4 - 1) := by
  have : CharP K 2 := h.charP
  rw [card_miyamotoPull h L η (miyamotoN1_le_gramSU h),
    ← Nat.card_congr (miyamotoN1Equiv h).toEquiv, card_specialLinearGroup_miyamoto h]

theorem isSylowOf_rootA_N1 (hS : Setting h L η t Q T) :
    IsSylowOf 2 (miyamotoPull h L η (miyamotoRootA h)) (miyamotoN1G h L η) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine isSylowOf_of_card hS.rootA_le_N1G ?_
  have hodd : ¬ 2 ∣ (2 ^ f) ^ 4 - 1 := by
    have h1 : 1 ≤ (2 ^ f) ^ 4 := Nat.one_le_pow _ _ (by positivity)
    have h2 : Even ((2 ^ f) ^ 4) :=
      (Nat.even_pow.2 ⟨Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩, by norm_num⟩)
    exact Nat.not_even_iff_odd.2 (Nat.Even.sub_odd h1 h2 odd_one) ∘ (even_iff_two_dvd.2)
  have hne : (2 ^ f) ^ 4 - 1 ≠ 0 := fun e => hodd (e ▸ dvd_zero 2)
  rw [hS.card_rootA, hS.card_N1G, Nat.factorization_mul (by positivity) hne,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, ← pow_mul,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, pow_mul]

theorem rootElt_injective (hS : Setting h L η t Q T) : Function.Injective hS.rootElt := by
  have : CharP K 2 := h.charP
  intro a b e
  have h1 : hS.rootElt (a + b) ∈ miyamotoF1G h L η t := by
    rw [hS.rootElt_add, e, hS.rootElt_mul_self]
    exact one_mem _
  exact (eq_of_add_eq_zero_of_charTwo ((hS.rootElt_mem_F1_iff).1 h1)).symm

theorem W_le_H1 (hS : Setting h L η t Q T) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤ miyamotoH1G h L η t :=
  le_inf (inf_le_left.trans hS.RG_le_normalizer_F1) inf_le_right

theorem t_mem_normalizer_W (hS : Setting h L η t Q T) :
    t ∈ normalizer ((miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) :
      Subgroup G) : Set G) :=
  mem_normalizer_inf hS.t_mem_normalizer_RG hS.t_mem_normalizer_centralizer_I1

theorem isPGroup_W (hS : Setting h L η t Q T) :
    IsPGroup 2 (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) : Subgroup G) :=
  hS.isPGroup_RG.to_le inf_le_left

theorem W_inf_C (hS : Setting h L η t Q T) :
    (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ⊓
        centralizer ({t} : Set G) = miyamotoPull h L η (miyamotoRootA h) := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.rootA_le_W (hS.rootA_le_PG.trans hS.PG_le_C))
  obtain ⟨hxW, hxC⟩ := mem_inf.1 hx
  have hxP : x ∈ miyamotoPG h L η := by
    rw [← hS.RG_inf_C]
    exact mem_inf.2 ⟨(mem_inf.1 hxW).1, hxC⟩
  rw [← hS.W_inf_P1]
  exact mem_inf.2 ⟨hxW, mem_sup_right hxP⟩

theorem W_inf_N1 (hS : Setting h L η t Q T) :
    (miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) ⊓ miyamotoN1G h L η =
      miyamotoPull h L η (miyamotoRootA h) := by
  refine le_antisymm (fun x hx => ?_) (le_inf hS.rootA_le_W hS.rootA_le_N1G)
  rw [← hS.W_inf_C]
  exact mem_inf.2 ⟨(mem_inf.1 hx).1, hS.N1G_le_C (mem_inf.1 hx).2⟩

theorem exists_mem_W_not_mem_rootA (hS : Setting h L η t Q T) :
    ∃ w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G),
      w ∉ miyamotoPull h L η (miyamotoRootA h) := by
  by_contra hcon
  push Not at hcon
  have hle := Subgroup.card_le_of_le (show miyamotoRG h L η t Q ⊓
    centralizer (miyamotoI1G h L η : Set G) ≤ miyamotoPull h L η (miyamotoRootA h) from hcon)
  rw [hS.card_W, hS.card_rootA] at hle
  have h4 := hS.four_le
  have : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem closure_commutator_W (hS : Setting h L η t Q T) :
    closure {x | ∃ v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G),
      x = v⁻¹ * (t⁻¹ * v * t)} = miyamotoPull h L η (miyamotoRootA h) := by
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) with hWdef
  set U := miyamotoPull h L η (miyamotoRootA h) with hUdef
  have hmem : ∀ v ∈ W, v⁻¹ * (t⁻¹ * v * t) ∈ U := by
    intro v hv
    have := hS.conj_t_mul_t_mem_rootA (inv_mem hv)
    rw [inv_inv] at this
    rw [hS.t_inv, show v⁻¹ * (t * v * t) = v⁻¹ * t * v * t by group]
    exact this
  refine le_antisymm ((closure_le _).2 fun x ⟨v, hv, hx⟩ => hx ▸ hmem v hv) ?_
  let ψ : W →* G :=
    { toFun := fun w => (w : G)⁻¹ * (t⁻¹ * w * t)
      map_one' := by simp
      map_mul' := fun w w' => by
        have hc : (w : G)⁻¹ * (t⁻¹ * w * t) * w' = w' * ((w : G)⁻¹ * (t⁻¹ * w * t)) :=
          mem_centralizer_iff.1 (hS.U_le_centralizer_W (hmem w w.2)) w' w'.2 |>.symm
        simp only [coe_mul]
        calc ((w : G) * w')⁻¹ * (t⁻¹ * (w * w') * t) =
            (w' : G)⁻¹ * ((w : G)⁻¹ * (t⁻¹ * w * t) * w') * ((w' : G)⁻¹ * (t⁻¹ * w' * t)) := by
              group
          _ = (w' : G)⁻¹ * ((w' : G) * ((w : G)⁻¹ * (t⁻¹ * w * t))) *
              ((w' : G)⁻¹ * (t⁻¹ * w' * t)) := by rw [hc]
          _ = (w : G)⁻¹ * (t⁻¹ * w * t) * ((w' : G)⁻¹ * (t⁻¹ * w' * t)) := by group }
  have hker : ψ.ker = (W ⊓ centralizer ({t} : Set G)).subgroupOf W := by
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
      (inf_le_left : W ⊓ centralizer ({t} : Set G) ≤ W)).toEquiv, hS.W_inf_C,
    hS.card_rootA, hS.card_W] at hcard
  have hrange : ψ.range ≤ U := by
    rintro _ ⟨w, rfl⟩
    exact hmem w w.2
  have hcardr : Nat.card ψ.range = (2 ^ f) ^ 2 := by
    have hq : 0 < (2 ^ f) ^ 2 := by positivity
    have e : (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
    rw [e] at hcard
    exact Nat.eq_of_mul_eq_mul_left hq hcard
  have heq : ψ.range = U :=
    Subgroup.eq_of_le_of_card_ge hrange (by rw [hS.card_rootA, hcardr])
  rw [← heq]
  rintro _ ⟨w, rfl⟩
  exact subset_closure ⟨w, w.2, rfl⟩

theorem crossedQ1_eq_zero_iff_W (hS : Setting h L η t Q T) {w : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    hS.crossedQ1 w = 0 ↔ w ∈ miyamotoPull h L η (miyamotoRootA h) := by
  rw [hS.crossedQ1_eq_zero_iff (hS.miyamotoRG_le_miyamotoS hw.1), ← hS.W_inf_P1,
    ← hS.miyamotoRG_inf_Q1]
  constructor
  · intro hQ
    exact mem_inf.2 ⟨hw, mem_inf.2 ⟨hw.1, hQ⟩⟩
  · intro hx
    exact (mem_inf.1 (mem_inf.1 hx).2).2

theorem crossedQ1_mul_W (hS : Setting h L η t Q T) {w w' : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (hw' : w' ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    hS.crossedQ1 (w * w') = hS.crossedQ1 w + hS.crossedQ1 w' :=
  hS.crossedQ1_mul (hS.miyamotoRG_le_miyamotoS hw.1) (hS.miyamotoRG_le_miyamotoS hw'.1)

theorem crossedQ1_inv_mul_W (hS : Setting h L η t Q T) {w w' : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G))
    (hw' : w' ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    hS.crossedQ1 (w⁻¹ * w') = hS.crossedQ1 w' - hS.crossedQ1 w := by
  rw [hS.crossedQ1_mul_W (inv_mem hw) hw',
    hS.crossedQ1_inv (hS.miyamotoRG_le_miyamotoS hw.1)]
  ring

theorem miyamotoDHom_conj_W (hS : Setting h L η t Q T) (β : Kˣ) {w : G}
    (hw : w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)) :
    miyamotoDHom h L η β * w * (miyamotoDHom h L η β)⁻¹ ∈
        miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ∧
      hS.crossedQ1 (miyamotoDHom h L η β * w * (miyamotoDHom h L η β)⁻¹) =
        ((β⁻¹ ^ 2 : Kˣ) : K) * hS.crossedQ1 w :=
  ⟨(mem_normalizer_iff.1 (hS.IG_le_normalizer_W (miyamotoDHom_mem h L η β).1) w).1 hw,
    hS.crossedQ1_miyamotoDHom_conj β
      (hS.miyamotoS_le_normalizer_Q1 (hS.miyamotoRG_le_miyamotoS hw.1))⟩

theorem DG_le_N1G (_hS : Setting h L η t Q T) : miyamotoDG h L η ≤ miyamotoN1G h L η :=
  inf_le_right

theorem DG_le_C (hS : Setting h L η t Q T) : miyamotoDG h L η ≤ centralizer ({t} : Set G) :=
  inf_le_left.trans hS.IG_le_C

theorem DG_le_normalizer_W (hS : Setting h L η t Q T) :
    miyamotoDG h L η ≤ normalizer ((miyamotoRG h L η t Q ⊓
      centralizer (miyamotoI1G h L η : Set G) : Subgroup G) : Set G) :=
  inf_le_left.trans hS.IG_le_normalizer_W

theorem DG_le_normalizer_rootA (hS : Setting h L η t Q T) :
    miyamotoDG h L η ≤ normalizer (miyamotoPull h L η (miyamotoRootA h) : Set G) := by
  intro d hd
  rw [← range_miyamotoDHom h L η] at hd
  obtain ⟨β, rfl⟩ := hd
  refine mem_normalizer_fintype fun u hu => ?_
  obtain ⟨a, rfl⟩ := hS.exists_rootElt_eq hu
  rw [hS.miyamotoDHom_conj_rootElt]
  exact hS.rootElt_mem_rootA _

theorem DG_inf_rootA (hS : Setting h L η t Q T) :
    miyamotoDG h L η ⊓ miyamotoPull h L η (miyamotoRootA h) = ⊥ := by
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨hxD, hxU⟩ := mem_inf.1 hx
  have hodd : Odd (Nat.card (miyamotoDG h L η)) := hS.odd_card_of_le_IG inf_le_left
  obtain ⟨a, rfl⟩ := hS.exists_rootElt_eq hxU
  refine mem_bot.2 (eq_one_of_odd_of_pow_two_pow_eq_one hodd hxD (k := 1) ?_)
  rw [pow_one, sq, hS.rootElt_mul_self]

theorem rootA_sup_DG (hS : Setting h L η t Q T) :
    miyamotoPull h L η (miyamotoRootA h) ⊔ miyamotoDG h L η =
      miyamotoN1G h L η ⊓ normalizer (miyamotoPull h L η (miyamotoRootA h) : Set G) := by
  have : CharP K 2 := h.charP
  refine le_antisymm (sup_le (le_inf hS.rootA_le_N1G le_normalizer)
    (le_inf hS.DG_le_N1G hS.DG_le_normalizer_rootA)) fun x hx => ?_
  obtain ⟨hxN, hxU⟩ := mem_inf.1 hx
  obtain ⟨g, hg, rfl⟩ := (mem_miyamotoPull h L η).1 hxN
  have hconj : (g : GL (Fin 4) K)⁻¹ * miyamotoXGL h 1 0 0 0 * g ∈ miyamotoRootA h := by
    have h1 := (mem_normalizer_iff.1 (inv_mem hxU) (hS.rootElt 1)).1 (hS.rootElt_mem_rootA 1)
    rw [inv_inv] at h1
    have e : ((η.symm g : L) : G)⁻¹ * hS.rootElt 1 * ((η.symm g : L) : G) =
        ((η.symm (g⁻¹ * ⟨miyamotoXGL h 1 0 0 0, hS.rootA_le_SU ⟨1, rfl⟩⟩ * g) : L) : G) := by
      simp only [rootElt, map_mul, map_inv, coe_mul, coe_inv]
    rw [e, symm_mem_miyamotoPull_iff] at h1
    simpa using h1
  obtain ⟨c, α, hcα⟩ := exists_eq_rootA_mul_of_conj_mem h hg hconj
  have e : ((η.symm g : L) : G) = hS.rootElt c * miyamotoDHom h L η α := by
    simp only [rootElt, miyamotoDHom, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, coe_subtype]
    rw [← L.coe_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    rw [coe_mul, coe_miyamotoDHomSU, ← hcα]
  rw [e]
  exact mul_mem (mem_sup_left (hS.rootElt_mem_rootA c))
    (mem_sup_right (miyamotoDHom_mem h L η α))

theorem DG_regular_rootA (hS : Setting h L η t Q T) :
    ∀ u ∈ miyamotoPull h L η (miyamotoRootA h), u ≠ 1 →
      ∀ w ∈ miyamotoPull h L η (miyamotoRootA h), w ≠ 1 →
        ∃! d : miyamotoDG h L η, (d : G) * u * (d : G)⁻¹ = w := by
  have : CharP K 2 := h.charP
  intro u hu hu1 w hw hw1
  obtain ⟨a, rfl⟩ := hS.exists_rootElt_eq hu
  obtain ⟨b, rfl⟩ := hS.exists_rootElt_eq hw
  have ha : a ≠ 0 := fun e => hu1 (by rw [e, hS.rootElt_zero])
  have hb : b ≠ 0 := fun e => hw1 (by rw [e, hS.rootElt_zero])
  have key : ∀ β : Kˣ, miyamotoDHom h L η β * hS.rootElt a * (miyamotoDHom h L η β)⁻¹ =
      hS.rootElt b ↔ (β : K) ^ 2 = a / b := by
    intro β
    rw [hS.miyamotoDHom_conj_rootElt, hS.rootElt_injective.eq_iff]
    have hβ : (β : K) ≠ 0 := β.ne_zero
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    constructor
    · intro e
      rw [← e]
      field_simp
    · intro e
      rw [inv_pow, e]
      field_simp
  obtain ⟨y, hy⟩ := exists_sq_eq h (a / b)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hy
    exact div_ne_zero ha hb hy.symm
  have hD : ∀ d : miyamotoDG h L η, ∃ β : Kˣ, (d : G) = miyamotoDHom h L η β := by
    intro d
    have hd : (d : G) ∈ (miyamotoDHom h L η).range := (range_miyamotoDHom h L η).ge d.2
    obtain ⟨β, hβ⟩ := hd
    exact ⟨β, hβ.symm⟩
  refine ⟨⟨_, miyamotoDHom_mem h L η (Units.mk0 y hy0)⟩, (key _).2 hy, fun d hd => ?_⟩
  obtain ⟨β, hβ⟩ := hD d
  dsimp only at hd
  rw [hβ] at hd
  have h1 := (key β).1 hd
  apply Subtype.ext
  rw [hβ]
  change miyamotoDHom h L η β = miyamotoDHom h L η (Units.mk0 y hy0)
  congr 1
  exact Units.ext (eq_of_sq_eq_sq (h1.trans hy.symm))

theorem DG_regular_W (hS : Setting h L η t Q T) :
    ∀ v ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G),
      v ∉ miyamotoPull h L η (miyamotoRootA h) →
      ∀ w ∈ miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G),
        w ∉ miyamotoPull h L η (miyamotoRootA h) →
        ∃! d : miyamotoDG h L η, ((d : G) * v * (d : G)⁻¹)⁻¹ * w ∈
          miyamotoPull h L η (miyamotoRootA h) := by
  have : CharP K 2 := h.charP
  intro v hv hvU w hw hwU
  have hγv : hS.crossedQ1 v ≠ 0 := fun e => hvU ((hS.crossedQ1_eq_zero_iff_W hv).1 e)
  have hγw : hS.crossedQ1 w ≠ 0 := fun e => hwU ((hS.crossedQ1_eq_zero_iff_W hw).1 e)
  have key : ∀ β : Kˣ, (miyamotoDHom h L η β * v * (miyamotoDHom h L η β)⁻¹)⁻¹ * w ∈
      miyamotoPull h L η (miyamotoRootA h) ↔
        (β : K) ^ 2 = hS.crossedQ1 v / hS.crossedQ1 w := by
    intro β
    obtain ⟨hdv, hγ⟩ := hS.miyamotoDHom_conj_W β hv
    rw [← hS.crossedQ1_eq_zero_iff_W (mul_mem (inv_mem hdv) hw),
      hS.crossedQ1_inv_mul_W hdv hw, hγ, sub_eq_zero]
    have hβ : (β : K) ≠ 0 := β.ne_zero
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    constructor
    · intro e
      rw [e]
      field_simp
    · intro e
      rw [inv_pow, e]
      field_simp
  obtain ⟨y, hy⟩ := exists_sq_eq h (hS.crossedQ1 v / hS.crossedQ1 w)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hy
    exact div_ne_zero hγv hγw hy.symm
  refine ⟨⟨_, miyamotoDHom_mem h L η (Units.mk0 y hy0)⟩, (key _).2 hy, fun d hd => ?_⟩
  have hd' : (d : G) ∈ (miyamotoDHom h L η).range := (range_miyamotoDHom h L η).ge d.2
  obtain ⟨β, hβ⟩ := hd'
  dsimp only at hd
  rw [← hβ] at hd
  have h1 := (key β).1 hd
  apply Subtype.ext
  rw [← hβ]
  change miyamotoDHom h L η β = miyamotoDHom h L η (Units.mk0 y hy0)
  congr 1
  exact Units.ext (eq_of_sq_eq_sq (h1.trans hy.symm))

theorem W_le_of_le (hS : Setting h L η t Q T) {X : Subgroup G}
    (hUX : miyamotoPull h L η (miyamotoRootA h) ≤ X) (hDX : miyamotoDG h L η ≤ X)
    (hWX : miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤
      normalizer (X : Set G)) :
    miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) ≤ X := by
  have : CharP K 2 := h.charP
  intro w hw
  obtain ⟨s, hs, hs2⟩ := exists_fixed_unit_sq_ne_one h hS.two_le
  set c : K := ((s⁻¹ ^ 2 : Kˣ) : K) - 1 with hc
  have hc0 : c ≠ 0 := by
    rw [hc, sub_ne_zero]
    intro e
    apply hs2
    have : ((s : K) ^ 2)⁻¹ = 1 := by simpa [Units.val_pow_eq_pow_val] using e
    exact inv_eq_one.1 this
  obtain ⟨y, hy⟩ := exists_sq_eq h c⁻¹
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero] at hy
    exact inv_ne_zero hc0 hy.symm
  set d := miyamotoDHom h L η s with hd
  set d₁ := miyamotoDHom h L η (Units.mk0 y hy0)⁻¹ with hd₁
  obtain ⟨hv, hγv⟩ := hS.miyamotoDHom_conj_W (Units.mk0 y hy0)⁻¹ hw
  set v := d₁ * w * d₁⁻¹ with hvdef
  obtain ⟨hdv, hγdv⟩ := hS.miyamotoDHom_conj_W s hv
  have hcomm : d * v * d⁻¹ * v⁻¹ ∈ X := by
    have h1 : v * d⁻¹ * v⁻¹ ∈ X :=
      (mem_normalizer_iff.1 (hWX hv) _).1 (inv_mem (hDX (miyamotoDHom_mem h L η s)))
    rw [show d * v * d⁻¹ * v⁻¹ = d * (v * d⁻¹ * v⁻¹) by group]
    exact mul_mem (hDX (miyamotoDHom_mem h L η s)) h1
  have hcW : d * v * d⁻¹ * v⁻¹ ∈
      miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) :=
    mul_mem hdv (inv_mem hv)
  have hγc : hS.crossedQ1 (d * v * d⁻¹ * v⁻¹) = hS.crossedQ1 w := by
    have hc' : ((s⁻¹ : Kˣ) : K) ^ 2 = c + 1 := by
      rw [hc, Units.val_pow_eq_pow_val, sub_add_cancel]
    rw [hS.crossedQ1_mul_W hdv (inv_mem hv), hS.crossedQ1_inv
      (hS.miyamotoRG_le_miyamotoS hv.1), hγdv, hγv]
    simp only [inv_inv, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [hy, hc']
    field_simp
    ring
  have hU : (d * v * d⁻¹ * v⁻¹)⁻¹ * w ∈ miyamotoPull h L η (miyamotoRootA h) := by
    rw [← hS.crossedQ1_eq_zero_iff_W (mul_mem (inv_mem hcW) hw),
      hS.crossedQ1_inv_mul_W hcW hw, hγc, sub_self]
  rw [show w = (d * v * d⁻¹ * v⁻¹) * ((d * v * d⁻¹ * v⁻¹)⁻¹ * w) by group]
  exact mul_mem hcomm (hUX hU)

theorem exists_not_commute_of_isSylowOf (hS : Setting h L η t Q T) {S : Subgroup G}
    (hS2 : IsSylowOf 2 S (miyamotoH1G h L η t)) : ∃ x ∈ S, x * t ≠ t * x := by
  have : CharP K 2 := h.charP
  by_contra hcon
  push Not at hcon
  set W := miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G) with hWdef
  have hz : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [hS.card_zpowers_t, pow_one])
  have hB2 : IsPGroup 2 (W ⊔ zpowers t : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hS.isPGroup_W hz (zpowers_le.2 hS.t_mem_normalizer_W)
  have hBH : W ⊔ zpowers t ≤ miyamotoH1G h L η t :=
    sup_le hS.W_le_H1 (zpowers_le.2 hS.t_mem_H1)
  obtain ⟨c, hcH, hle⟩ :=
    CFSG.ComponentClassification.AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
      hS2 hB2 hBH
  have hconjS : ∀ x ∈ W ⊔ zpowers t, c⁻¹ * x * c ∈ S := fun x hx =>
    hle (CFSG.ComponentClassification.AschbacherTheorem3.conj_mem_rightConjugate hx c)
  set t' := c * t * c⁻¹ with ht'def
  have hW' : ∀ w ∈ W, w * t' = t' * w := by
    intro w hw
    have h2 := hcon _ (hconjS w (mem_sup_left hw))
    calc w * t' = c * ((c⁻¹ * w * c) * t) * c⁻¹ := by rw [ht'def]; group
      _ = c * (t * (c⁻¹ * w * c)) * c⁻¹ := by rw [h2]
      _ = t' * w := by rw [ht'def]; group
  have ht' : t' * t = t * t' := by
    have h2 := hcon _ (hconjS t (mem_sup_right (mem_zpowers t)))
    calc t' * t = c * (t * (c⁻¹ * t * c)) * c⁻¹ := by rw [ht'def]; group
      _ = c * ((c⁻¹ * t * c) * t) * c⁻¹ := by rw [h2]
      _ = t * t' := by rw [ht'def]; group
  have ht'H : t' ∈ miyamotoH1G h L η t :=
    mul_mem (mul_mem hcH hS.t_mem_H1) (inv_mem hcH)
  have ht'C : t' ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 ht'
  obtain ⟨s, ⟨i, hi, n, hn, hs⟩, φ, -, hα⟩ := hS.exists_act_eq_of_mem_H1 ht'C ht'H
  have hfix : ∀ a : K, i * n * glAut φ (miyamotoXGL h a 0 0 0) * (i * n)⁻¹ =
      miyamotoXGL h a 0 0 0 := by
    intro a
    have ht'U : t' ∈ centralizer (miyamotoPull h L η (miyamotoRootA h) : Set G) :=
      mem_centralizer_iff.2 fun u hu => (hW' u (hS.rootA_le_W hu))
    have e := miyamotoAct_apply_of_mem_centralizer h L η
      ⟨t', hS.centralizer_le_normalizer ht'C⟩ ht'U
      (g := ⟨miyamotoXGL h a 0 0 0, hS.rootA_le_SU ⟨a, rfl⟩⟩) ⟨a, rfl⟩
    have e2 := congrArg (fun y : gramSU h (miyamotoJ4 K) => (y : GL (Fin 4) K)) e
    simp only at e2
    rw [coe_act_apply_of_eq hα, hs] at e2
    exact e2
  obtain ⟨hφ, hnU⟩ := eq_refl_and_mem_rootA_of_fixes h hi hn hfix
  have hα' : miyamotoAct h L η ⟨t', hS.centralizer_le_normalizer ht'C⟩ = MulAut.conj s := by
    rw [hα, hφ, miyamotoFieldAut_refl, mul_one]
  obtain ⟨z, hzL, hz'⟩ := exists_eq_mul_of_miyamotoAct_eq_conj h L η _ s hα'
  simp only at hz'
  set l : G := ((η.symm s : L) : G) with hldef
  set i' : G := ((η.symm ⟨i, miyamotoI1_le_gramSU h hi⟩ : L) : G) with hi'def
  set n' : G := ((η.symm ⟨n, hS.rootA_le_SU hnU⟩ : L) : G) with hn'def
  have hi' : i' ∈ miyamotoI1G h L η := (symm_mem_miyamotoPull_iff h L η).2 hi
  have hn' : n' ∈ miyamotoPull h L η (miyamotoRootA h) := (symm_mem_miyamotoPull_iff h L η).2 hnU
  have hl : l = i' * n' := by
    rw [hldef, hi'def, hn'def, ← L.coe_mul, ← map_mul]
    congr 2
    exact Subtype.ext hs
  have hlW : ∀ w ∈ W, l * w = w * l := by
    intro w hw
    have h1 : i' * w = w * i' := mem_centralizer_iff.1 hw.2 i' hi'
    have h2 : n' * w = w * n' := (mem_centralizer_iff.1 (hS.U_le_centralizer_W hn') w hw).symm
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
  ·
    apply hS.conj_not_mem_L c⁻¹
    rw [inv_inv, ← ht'def, hz', ← hj, e, mul_one]
    exact hlL
  ·
    rw [← hj, e] at hz'
    obtain ⟨w, hw, hwU⟩ := hS.exists_mem_W_not_mem_rootA
    apply hwU
    rw [← hS.W_inf_C]
    refine mem_inf.2 ⟨hw, mem_centralizer_singleton_iff.2 ?_⟩
    have h1 := hW' w hw
    rw [hz'] at h1
    have h2 := hlW w hw
    calc w * t = l⁻¹ * (w * (l * t)) := by
          rw [← mul_assoc w l t, ← h2]; group
      _ = l⁻¹ * (l * t * w) := by rw [h1]
      _ = t * w := by group

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
