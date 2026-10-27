module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GH74.Generic.S3.Lem34

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank Subgroup
open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
open scoped MatrixGroups

section General

variable {G : Type} [Group G]

theorem exists_isSylowOf_ge [Finite G] {P K : Subgroup G} (hPK : P ≤ K) (hP : IsPGroup 2 ↥P) :
    ∃ S : Subgroup G, IsSylowOf 2 S K ∧ P ≤ S := by
  obtain ⟨S, hS⟩ := (hP.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup K).map K.subtype, ⟨S, rfl⟩, fun x hx => ?_⟩
  exact ⟨⟨x, hPK hx⟩, hS hx, rfl⟩

theorem isCyclic_of_isPGroup_le [Finite G] {K S P : Subgroup G} (hS : IsSylowOf 2 S K)
    (hcyc : IsCyclic ↥S) (hPK : P ≤ K) (hP : IsPGroup 2 ↥P) : IsCyclic ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_ge hPK hP
  obtain ⟨k, -, hk⟩ := hS.exists_mem_conj hS'
  let φ : ↥P →* ↥S :=
    { toFun := fun a => ⟨k⁻¹ * (a : G) * k, (hk _).1 (hPS' a.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change k⁻¹ * ((a * b : ↥P) : G) * k = (k⁻¹ * (a : G) * k) * (k⁻¹ * (b : G) * k)
        rw [Subgroup.coe_mul]
        group) }
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have h2 : k⁻¹ * (a : G) * k = k⁻¹ * (b : G) * k := congrArg Subtype.val hab
    simpa using h2
  exact isCyclic_of_injective φ hinj

theorem exists_noncyclic_two_subgroup_sl2 {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2) :
    ∃ P : Subgroup SL(2, F), IsPGroup 2 ↥P ∧ ¬ IsCyclic ↥P := by
  obtain ⟨⟨a, b, hab⟩, hrest⟩ := odd_field_two_dimensional_quaternion_matrices hF
  obtain ⟨-, -, -, -, -, Q, -, hcard, ⟨e⟩, -⟩ := hrest a b hab
  refine ⟨Q, IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num), fun hcyc => ?_⟩
  have hnc : ¬ ∀ a b : QuaternionGroup 2, a * b = b * a := by decide
  have hq8 : IsCyclic (QuaternionGroup 2) := (e.isCyclic).1 hcyc
  have hcomm : IsMulCommutative (QuaternionGroup 2) := IsCyclic.isMulCommutative
  exact hnc fun a b => hcomm.is_comm.comm a b

theorem false_of_sl2_le_cyclic_sylow [Finite G] {K S J : Subgroup G} (hS : IsSylowOf 2 S K)
    (hcyc : IsCyclic ↥S) (hJK : J ≤ K) {F : Type} [Field F] [Finite F] (hF : ringChar F ≠ 2)
    (e : SL(2, F) ≃* ↥J) : False := by
  obtain ⟨P, hP2, hPnc⟩ := exists_noncyclic_two_subgroup_sl2 hF
  let φ : SL(2, F) →* G := J.subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := J.subtype_injective.comp e.injective
  have hPmap : IsPGroup 2 ↥(P.map φ) := hP2.of_equiv (P.equivMapOfInjective φ hφ)
  have hle : P.map φ ≤ K := by
    rintro _ ⟨g, -, rfl⟩
    exact hJK (e g).2
  have hc : IsCyclic ↥(P.map φ) := isCyclic_of_isPGroup_le hS hcyc hle hPmap
  exact hPnc ((P.equivMapOfInjective φ hφ).isCyclic.2 hc)

theorem ringChar_ne_two_of_card_pow {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = p ^ f) : ringChar F ≠ 2 := by
  intro h2
  have : Fintype F := Fintype.ofFinite F
  have h := (FiniteField.even_card_iff_char_two (F := F)).mp h2
  rw [← Nat.card_eq_fintype_card, hF] at h
  have hodd : (p ^ f) % 2 = 1 := Nat.odd_iff.1 ((hp.odd_of_ne_two hp2).pow)
  omega

theorem conj_mem_centralizer_of_mem_normalizer {I : Subgroup G} {c : G} (hc : c ∈ normalizer (I : Set G))
    {d : G} (hd : d ∈ centralizer (I : Set G)) : c * d * c⁻¹ ∈ centralizer (I : Set G) := by
  apply mem_centralizer_iff.2
  intro i hi
  have hi' : c⁻¹ * i * c ∈ I := by
    have := (mem_normalizer_iff.1 ((normalizer (I : Set G)).inv_mem hc) i).1 hi
    simpa using this
  have hd' : (c⁻¹ * i * c) * d = d * (c⁻¹ * i * c) := mem_centralizer_iff.1 hd _ hi'
  calc i * (c * d * c⁻¹) = c * ((c⁻¹ * i * c) * d) * c⁻¹ := by group
    _ = c * (d * (c⁻¹ * i * c)) * c⁻¹ := by rw [hd']
    _ = (c * d * c⁻¹) * i := by group

theorem sylow_inf_centralizer [Finite G] {C T I : Subgroup G} (hT : IsSylowOf 2 T C)
    (hCI : C ≤ normalizer (I : Set G)) :
    IsSylowOf 2 (T ⊓ centralizer (I : Set G)) (C ⊓ centralizer (I : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : C ≤ normalizer ((C ⊓ centralizer (I : Set G) : Subgroup G) : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj
    · intro i hi
      exact ⟨C.mul_mem (C.mul_mem hc hi.1) (C.inv_mem hc),
        conj_mem_centralizer_of_mem_normalizer (hCI hc) hi.2⟩
    · intro i hi
      exact ⟨C.mul_mem (C.mul_mem (C.inv_mem hc) hi.1) hc, by
        simpa using conj_mem_centralizer_of_mem_normalizer
          ((normalizer (I : Set G)).inv_mem (hCI hc)) hi.2⟩
  have := hT.inf_of_le_normalizer inf_le_left hN
  rwa [← inf_assoc, inf_eq_left.2 hT.le] at this

theorem IsCompC.map_conj {I : Subgroup G} {u : G} (h : IsCompC I u) (c : G) :
    IsCompC (I.map (MulAut.conj c).toMonoidHom) (c * u * c⁻¹) := by
  have hf : ∀ y : G, (MulAut.conj c).toMonoidHom y = c * y * c⁻¹ := fun y => by simp
  have hC : (centralizer ({u} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * u * c⁻¹} : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      apply mem_centralizer_singleton_iff.2
      have hyu : y * u = u * y := mem_centralizer_singleton_iff.1 hy
      rw [hf]
      calc c * y * c⁻¹ * (c * u * c⁻¹) = c * (y * u) * c⁻¹ := by group
        _ = c * (u * y) * c⁻¹ := by rw [hyu]
        _ = c * u * c⁻¹ * (c * y * c⁻¹) := by group
    · intro hx
      refine ⟨c⁻¹ * x * c, ?_, by rw [hf]; group⟩
      apply mem_centralizer_singleton_iff.2
      have hx' : x * (c * u * c⁻¹) = (c * u * c⁻¹) * x := mem_centralizer_singleton_iff.1 hx
      calc c⁻¹ * x * c * u = c⁻¹ * (x * (c * u * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * u * c⁻¹) * x) * c := by rw [hx']
        _ = u * (c⁻¹ * x * c) := by group
  unfold IsCompC
  rw [← hC]
  refine ⟨Subgroup.map_mono h.1, ?_⟩
  have key : (I.map (MulAut.conj c).toMonoidHom).subgroupOf
        ((centralizer ({u} : Set G)).map (MulAut.conj c).toMonoidHom) =
      (I.subgroupOf (centralizer ({u} : Set G))).map
        ((MulAut.conj c).subgroupMap (centralizer ({u} : Set G))).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨l, hl, hly⟩
      obtain ⟨k, hk, hky⟩ := y.2
      have hlk : l = k := (MulAut.conj c).injective (hly.trans hky.symm)
      subst hlk
      exact ⟨⟨l, hk⟩, hl, Subtype.ext (by simpa using hly)⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp⟩
  rw [key]
  exact LocalCores.isComponent_map_mulEquiv ((MulAut.conj c).subgroupMap (centralizer ({u} : Set G))) h.2

theorem IsCompC.eq_or_commute [Finite G] {I J : Subgroup G} {u : G} (hI : IsCompC I u)
    (hJ : IsCompC J u) : I = J ∨ ∀ a ∈ I, ∀ b ∈ J, a * b = b * a := by
  rcases LocalCores.distinct_components_commute hI.2 hJ.2 with h | h
  · left
    have := (Subgroup.subgroupOf_inj).1 h
    rwa [inf_eq_left.2 hI.1, inf_eq_left.2 hJ.1] at this
  · right
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
    intro a ha b hb
    have h2 := mem_centralizer_iff.1
      (h1 (show (⟨a, hI.1 ha⟩ : ↥(centralizer ({u} : Set G))) ∈
        I.subgroupOf (centralizer ({u} : Set G)) from ha)) ⟨b, hJ.1 hb⟩ hb
    exact (congrArg Subtype.val h2).symm

theorem false_of_two_comps [Finite G] {u : G} {I J T : Subgroup G} (hI : IsNormCompC I u)
    (hJ : IsCompC J u) (huJ : u ∈ J) (hodd : Odd (Nat.card ↥(center ↥I))) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (hT : IsSylowOf 2 T (centralizer ({u} : Set G)))
    (hcyc : IsCyclic ↥(T ⊓ centralizer (I : Set G))) {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (e : SL(2, F) ≃* ↥J) : False := by
  rcases hI.1.eq_or_commute hJ with hIJ | hcomm
  · have huI : u ∈ I := by rw [hIJ]; exact huJ
    exact not_central_involution_of_odd hodd huI hu2 hu1
      (fun i hi => mem_centralizer_singleton_iff.1 (hI.1.1 hi))
  · have hJD : J ≤ centralizer ({u} : Set G) ⊓ centralizer (I : Set G) := fun j hj =>
      ⟨hJ.1 hj, mem_centralizer_iff.2 fun i hi => hcomm i hi j hj⟩
    exact false_of_sl2_le_cyclic_sylow (sylow_inf_centralizer hT hI.le_normalizer) hcyc hJD hF e

end General

namespace Nbhd3

variable {G : Type} [Group G] [Finite G] {t t' : StatedLieTag} {p f : ℕ} {x y : G}
  {Iw Iv Ivw T : Subgroup G} (h : Nbhd3 G t t' p f x y Iw Iv Ivw T)

include h

theorem not_isConj_y_x (hclass : B_L3_class) (hsyl : B_L3_sylow) : ¬ IsConj y x := by
  rw [isConj_iff]
  rintro ⟨c, hc⟩
  have hJ := h.comp_v.map_conj c
  rw [hc] at hJ
  obtain ⟨F, hFf, hFfin, hFcard, ⟨e⟩⟩ := h.Iv_iso
  have hxJ : x ∈ Iv.map (MulAut.conj c).toMonoidHom := ⟨y, h.y_Iv, by simpa using hc⟩
  exact false_of_two_comps h.comp_w hJ hxJ h.odd_w h.x_mul_self h.x_ne_one h.T_sylow
    (h.lem34 hclass hsyl).1 (ringChar_ne_two_of_card_pow h.prime.1 h.prime.2.1 hFcard)
    (e.trans (Iv.equivMapOfInjective _ (MulAut.conj c).injective))

theorem not_isConj_y_yx (hclass : B_L3_class) (hsyl : B_L3_sylow) : ¬ IsConj y (y * x) := by
  rw [isConj_iff]
  rintro ⟨c, hc⟩
  have hJ := h.comp_v.map_conj c
  rw [hc] at hJ
  obtain ⟨F, hFf, hFfin, hFcard, ⟨e⟩⟩ := h.Iv_iso
  have hyxJ : y * x ∈ Iv.map (MulAut.conj c).toMonoidHom := ⟨y, h.y_Iv, by simpa using hc⟩
  exact false_of_two_comps h.comp_vw hJ hyxJ h.odd_vw h.yx_mul_self h.yx_ne_one
    (h.T_sylow_vw hclass hsyl) (h.lem35 hsyl).1
    (ringChar_ne_two_of_card_pow h.prime.1 h.prime.2.1 hFcard)
    (e.trans (Iv.equivMapOfInjective _ (MulAut.conj c).injective))

end Nbhd3

end CFSG.GH74.Generic.S3
