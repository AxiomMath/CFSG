module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Basic
public import CFSG.GH74.GLS.Stage1.Thm4.L97b
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.GLS.IVK.Lifted32.Hyp

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5
  CFSG.GH74.GLS.Stage1.Thm4 CFSG.ABGLocalTools
open CFSG.GH74.GLS.Stage2.Local (Cen toBar barOf)
open scoped commutatorElement

section Basic

variable {G : Type} [Group G] {z : G}

theorem toBar_surjective : Function.Surjective (toBar z) := QuotientGroup.mk'_surjective _

theorem toBar_eq_one_iff {c : ↥(Cz z)} : toBar z c = 1 ↔ (c : G) ∈ Oz z := by
  rw [mem_Oz_iff]
  exact QuotientGroup.eq_one_iff c

theorem barOf_sup {X Y : Subgroup G} (hX : X ≤ Cz z) (hY : Y ≤ Cz z) :
    barOf z (X ⊔ Y) = barOf z X ⊔ barOf z Y := by
  unfold barOf
  rw [← Subgroup.map_sup]
  congr 1
  exact subgroupOf_sup hX hY

theorem mem_barOf {X : Subgroup G} {y : CentralizerBar z} :
    y ∈ barOf z X ↔ ∃ c : ↥(Cz z), (c : G) ∈ X ∧ toBar z c = y := mem_barOf_iff

theorem toBar_mem_barOf {X : Subgroup G} {c : ↥(Cz z)} (hc : (c : G) ∈ X) :
    toBar z c ∈ barOf z X := mem_barOf.2 ⟨c, hc, rfl⟩

theorem mem_normalizer_of_subgroupOf {C K : Subgroup G} (hKC : K ≤ C) {c : ↥C}
    (hc : c ∈ normalizer ((K.subgroupOf C : Subgroup ↥C) : Set ↥C)) :
    (c : G) ∈ normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hc ⊢
  intro x
  by_cases hx : x ∈ C
  · have := hc ⟨x, hx⟩
    simpa [Subgroup.mem_subgroupOf] using this
  · constructor
    · intro hxK
      exact absurd (hKC hxK) hx
    · intro h
      have : (c : G) * x * (c : G)⁻¹ ∈ C := hKC h
      have hc' : x ∈ C := by
        have h2 : (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹) * (c : G) ∈ C :=
          C.mul_mem (C.mul_mem (C.inv_mem c.2) this) c.2
        simpa [mul_assoc] using h2
      exact absurd hc' hx

theorem mem_normalizer_map_of_surjective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) {L : Subgroup A} {c : A} (hc : c ∈ normalizer (L : Set A)) :
    f c ∈ normalizer ((L.map f : Subgroup B) : Set B) := by
  rw [Subgroup.mem_normalizer_iff] at hc ⊢
  intro y
  obtain ⟨d, rfl⟩ := hf y
  constructor
  · rintro ⟨e, he, hed⟩
    refine ⟨c * e * c⁻¹, (hc e).1 he, ?_⟩
    simp only [map_mul, map_inv, hed]
  · rintro ⟨e, he, hed⟩
    refine ⟨c⁻¹ * e * c, ?_, ?_⟩
    · have := (hc (c⁻¹ * e * c)).2 (by simpa [mul_assoc] using he)
      exact this
    · have h1 : f e = f c * f d * (f c)⁻¹ := hed
      simp only [map_mul, map_inv, h1]
      group

end Basic

section BasicFin

variable {G : Type} [Group G] [Finite G] {z : G}

theorem mem_normalizer_iff_bar {K : Subgroup G} (hKC : K ≤ Cz z)
    (hK : IsPComponent 2 (K.subgroupOf (Cz z))) {c : ↥(Cz z)} :
    (c : G) ∈ normalizer (K : Set G) ↔
      toBar z c ∈ normalizer ((barOf z K : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro hc
    have hc' : c ∈ normalizer ((K.subgroupOf (Cz z) : Subgroup ↥(Cz z)) : Set ↥(Cz z)) := by
      rw [Subgroup.mem_normalizer_iff] at hc ⊢
      intro x
      simpa [Subgroup.mem_subgroupOf] using hc (x : G)
    exact mem_normalizer_map_of_surjective (toBar z) toBar_surjective hc'
  · intro hc
    have h1 := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map (p := 2)
      (L := K.subgroupOf (Cz z)) hK (d := c) hc
    exact mem_normalizer_of_subgroupOf hKC h1

end BasicFin

section Cfg

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem rigid_of_comp (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    IsRigidOfType (HatT K) z K :=
  ⟨(hC.std.comp_rigid hK).1, ⟨MulEquiv.refl _⟩⟩

theorem K_le_Cz (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) : K ≤ Cz z :=
  L97.le_cen (rigid_of_comp hC hK)

theorem pcomp_of (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    IsPComponent 2 (K.subgroupOf (Cz z)) :=
  L97.pcomp (rigid_of_comp hC hK)

theorem isComponent_bar' (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G} (hK : K = K₁ ∨ K = K₂) :
    IsComponent (barOf z K) :=
  L97.isComponent_bar (rigid_of_comp hC hK)

theorem bar_ne (hC : Cfg5 G z S K₁ K₂) : barOf z K₁ ≠ barOf z K₂ := by
  intro heq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := CFSG.ComponentClassification.UnbalancedLayer.pComponent_eq_of_map_eq (p := 2)
    (pcomp_of hC (Or.inl rfl)) (pcomp_of hC (Or.inr rfl)) heq
  apply hC.std.ne
  have := (Subgroup.subgroupOf_inj).mp h
  rwa [inf_eq_left.mpr (K_le_Cz hC (Or.inl rfl)), inf_eq_left.mpr (K_le_Cz hC (Or.inr rfl))]
    at this

theorem bar_comm (hC : Cfg5 G z S K₁ K₂) :
    barOf z K₁ ≤ centralizer ((barOf z K₂ : Subgroup (CentralizerBar z)) : Set (CentralizerBar z)) := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_bar' hC (Or.inl rfl))
    (isComponent_bar' hC (Or.inr rfl)) with h | h
  · exact absurd h (bar_ne hC)
  · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

theorem S_inf_Oz (hC : Cfg5 G z S K₁ K₂) : S ⊓ Oz z = ⊥ :=
  M.inf_eq_bot_of_pgroup_odd hC.std.sylow.isPGroup card_Oz_odd

end Cfg

section Zbar

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem odd_card_pPrimeCore : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cz z))) := by
  have h := card_Oz_odd (z := z)
  have e : Nat.card ↥(Oz z) = Nat.card ↥(pPrimeCore 2 ↥(Cz z)) := by
    unfold Oz pPrimeCoreOf
    exact Subgroup.card_map_of_injective (Cz z).subtype_injective
  rwa [e] at h

theorem orderOf_zBar (hz : orderOf z = 2) : orderOf (zBar z) = 2 := by
  have h1 : orderOf (zElt z) = 2 := by
    have := Subgroup.orderOf_coe (zElt z)
    rw [show ((zElt z : ↥(Cz z)) : G) = z from rfl] at this
    rw [← this, hz]
  exact CFSG.ComponentClassification.UnbalancedLayer.orderOf_mk_eq_two
    (R := pPrimeCore 2 ↥(Cz z)) odd_card_pPrimeCore h1

omit [Finite G] in
theorem zBar_comm (c : CentralizerBar z) : zBar z * c = c * zBar z := by
  obtain ⟨d, rfl⟩ := toBar_surjective (z := z) c
  have hd : (d : G) * z = z * d := Subgroup.mem_centralizer_singleton_iff.1 d.2
  have : zElt z * d = d * zElt z := Subtype.ext hd.symm
  exact congrArg (toBar z) this

omit [Finite G] in
theorem zBar_mem_barOf {K : Subgroup G} (hz : z ∈ K) : zBar z ∈ barOf z K :=
  toBar_mem_barOf (c := zElt z) hz

theorem z_mem_comp (hII : II4_4_4_center) (hC : Cfg5 G z S K₁ K₂) {K : Subgroup G}
    (hK : K = K₁ ∨ K = K₂) : z ∈ K :=
  (m4_of_std hII hC.std).z_mem_comp hK

end Zbar

end CFSG.GH74.GLS.IVK.Lifted32.Hyp
