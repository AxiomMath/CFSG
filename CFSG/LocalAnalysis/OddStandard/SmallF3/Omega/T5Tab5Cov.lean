module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5CoverPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.T5PocketOmega
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Inputs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

open scoped Pointwise

section CoverFacts

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}
variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {hQ : Q.Nondegenerate} {φ : ↥L →* omegaGroup hQ}

theorem t5_mul_self_eq_one_of_orderOf_eq_two {A : Type*} [Group A] {a : A}
    (h : orderOf a = 2) : a * a = 1 := by
  rw [← pow_two, ← h, pow_orderOf_eq_one]

theorem t5_map_center_le_center {A P : Type*} [Group A] [Group P] (f : A →* P)
    (hf : Function.Surjective f) :
    (Subgroup.center A).map f ≤ Subgroup.center P := by
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  obtain ⟨m, rfl⟩ := hf y
  have hx' : x ∈ Subgroup.center A := hx
  have hxm : m * x = x * m := Subgroup.mem_center_iff.mp hx' m
  calc f m * f x = f (m * x) := (map_mul f m x).symm
    _ = f (x * m) := by rw [hxm]
    _ = f x * f m := map_mul f x m

theorem t5_phi_pocket_invType (h : IsCoverMap L φ) (hL : IsOm6Z2 L) {z : G}
    (hz : IsI4PlusIn L z) (hzL : z ∈ L) :
    invType (((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) = (4, 1) := by
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hz2 : orderOf z = 2 := hz.1
  have hz'sq : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have hphisq : ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hz'sq, map_one]
    rfl
  have hphine : φ ⟨z, hzL⟩ ≠ 1 := by
    intro h1
    have hz'1 : (⟨z, hzL⟩ : ↥L) = 1 :=
      hO.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) hz'sq
    have hz1 : z = 1 := congrArg Subtype.val hz'1
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  exact (t5_isI4PlusIn_omega_iff h.finrank_eq h.quadSign_eq hphisq hphine).mp
    ((t5_isI4PlusIn_iff hL h hzL hz2).mp hz)

private theorem invType_piOrth_mul_of_type_four (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t : OGroup Q}
    (htt : t * t = 1) (ht : invType t = (4, 1)) :
    invType (piOrth Q * t) = (2, -1) := by
  have hdim4 : invDim t = 4 := congrArg Prod.fst ht
  have hsign4 : invSign t = 1 := congrArg Prod.snd ht
  have h' := invType_piOrth_mul_of_even_minus hQ htt (by rw [hdim]; decide) hsgn
  rw [h', hdim4, hsign4, hdim]
  decide

end CoverFacts

theorem asc82Tab5_pocket_kind_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ z : G, IsI4PlusIn L z → Kind5 L z 0 := by
  intro G _ _ L hL z hz
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, h⟩ := t5_exists_cover hS hL
  letI := i1; letI := i2; letI := i3
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  have hz2 : orderOf z = 2 := hz.1
  obtain ⟨K, hzK, hKL, _, _⟩ := hz.2
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hKL hzK)).1
  refine ⟨Subgroup.mem_sup_left hzL, ?_⟩
  intro hzC
  have hz_center : (⟨z, hzL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro m
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hzC (m : G) m.2
  have hphi_cent : φ ⟨z, hzL⟩ ∈ Subgroup.center (omegaGroup hQ) :=
    t5_map_center_le_center φ h.surjective (Subgroup.mem_map_of_mem φ hz_center)
  have hz'sq : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have hphine : φ ⟨z, hzL⟩ ≠ 1 := by
    intro h1
    have hz'1 : (⟨z, hzL⟩ : ↥L) = 1 :=
      hO.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) hz'sq
    have hz1 : z = 1 := congrArg Subtype.val hz'1
    rw [hz1, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  rcases t5_center_omegaGroup_six_minus hQ hdim hsgn hphi_cent with h1 | h1
  · exact hphine h1
  · have htype := t5_phi_pocket_invType h hL hz hzL
    have htypepi : invType (piOrth Q) = (6, -1) := by
      have h' := invType_piOrth hQ
      rwa [hdim, hsgn] at h'
    rw [h1] at htype
    exact absurd (htype.symm.trans htypepi) (by decide)

theorem asc82Tab5_tz_not_pocket_of (hS : Asc82SchurU43) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6Z2 L →
      ∀ t : G, t ∈ centerIn L → orderOf t = 2 → ∀ z : G, IsI4PlusIn L z →
        ¬ IsI4PlusIn L (t * z) := by
  intro G _ _ L hL t ht ht2 z hz htz
  obtain ⟨V, i1, i2, i3, Q, hQ, φ, h⟩ := t5_exists_cover hS hL
  letI := i1; letI := i2; letI := i3
  have hO : OddCentralCover φ := h.oddCentralCover hL
  have hdim : Module.finrank (ZMod 3) V = 6 := h.finrank_eq
  have hsgn : quadSign Q = -1 := h.quadSign_eq
  have hz2 : orderOf z = 2 := hz.1
  obtain ⟨K, hzK, hKL, _, _⟩ := hz.2
  have hzL : z ∈ L := (Subgroup.mem_inf.mp (hKL hzK)).1
  obtain ⟨t', ht'center, ht'val⟩ := Subgroup.mem_map.mp ht
  have htL : t ∈ L := ht'val ▸ t'.2
  have htz2 : orderOf (t * z) = 2 := htz.1
  have htzL : t * z ∈ L := mul_mem htL hzL
  have hz'sq : (⟨z, hzL⟩ : ↥L) * ⟨z, hzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, hz2])
  have htz'sq : (⟨t * z, htzL⟩ : ↥L) * ⟨t * z, htzL⟩ = 1 :=
    t5_mul_self_eq_one_of_orderOf_eq_two (by rw [Subgroup.orderOf_mk, htz2])
  have hzphi_sq : ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, hz'sq, map_one]
    rfl
  have hzphi_type : invType (((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) = (4, 1) :=
    t5_phi_pocket_invType h hL hz hzL
  have hphitz : ((φ ⟨t * z, htzL⟩ : omegaGroup hQ) : OGroup Q) =
      piOrth Q * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q) := by
    have heq : (⟨t * z, htzL⟩ : ↥L) = ⟨t, htL⟩ * ⟨z, hzL⟩ := rfl
    rw [heq, map_mul, Subgroup.coe_mul, h.map_central hL ht ht2 htL]
  have hphitz_ne : φ ⟨t * z, htzL⟩ ≠ 1 := by
    intro h1
    have h1' : (⟨t * z, htzL⟩ : ↥L) = 1 :=
      hO.eq_one_of_mul_self_eq_one (MonoidHom.mem_ker.mpr h1) htz'sq
    have h1'' : t * z = 1 := congrArg Subtype.val h1'
    rw [h1'', orderOf_one] at htz2
    exact absurd htz2 (by decide)
  have htzsq : ((φ ⟨t * z, htzL⟩ : omegaGroup hQ) : OGroup Q) *
      ((φ ⟨t * z, htzL⟩ : omegaGroup hQ) : OGroup Q) = 1 := by
    rw [← Subgroup.coe_mul, ← map_mul, htz'sq, map_one]
    rfl
  have htype4 : invType (((φ ⟨t * z, htzL⟩ : omegaGroup hQ) : OGroup Q)) = (4, 1) :=
    (t5_isI4PlusIn_omega_iff hdim hsgn htzsq hphitz_ne).mp
      ((t5_isI4PlusIn_iff hL h htzL htz2).mp htz)
  have hpiz_type : invType (piOrth Q * ((φ ⟨z, hzL⟩ : omegaGroup hQ) : OGroup Q)) = (2, -1) :=
    invType_piOrth_mul_of_type_four hQ hdim hsgn hzphi_sq hzphi_type
  have hcontra : (4, (1 : ℤˣ)) = (2, -1) := by
    have hmid : invType (((φ ⟨t * z, htzL⟩ : omegaGroup hQ) : OGroup Q)) = (2, -1) := by
      rw [hphitz]; exact hpiz_type
    exact htype4.symm.trans hmid
  exact absurd hcontra (by decide)

end CFSG.OddStandard.SmallF3.Omega
