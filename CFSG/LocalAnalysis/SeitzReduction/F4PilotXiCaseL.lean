module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCoverUnique
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Transfer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLM2

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Quasithin (perfectCore perfectCore_mono le_perfectCore_of_perfect perfectCore_le
  perfectCore_perfect map_perfectCore)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open scoped commutatorElement

local instance f4PilotXiCaseLNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance f4PilotXiCaseLNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

section Generic

theorem map_perfectCore_centralizer_subtype {X : Type*} [Group X] [Finite X] (C : Subgroup X)
    (S : Subgroup C) :
    (perfectCore (centralizer (S : Set C))).map C.subtype =
      perfectCore (C ⊓ centralizer ((S.map C.subtype : Subgroup X) : Set X)) := by
  rw [map_perfectCore]
  congr 1
  ext g
  simp only [mem_map, mem_inf, mem_centralizer_iff, SetLike.mem_coe, coe_subtype]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact congrArg Subtype.val (hy s hs)
  · rintro ⟨hg, hgS⟩
    refine ⟨⟨g, hg⟩, fun s hs => Subtype.ext (hgS _ ⟨s, hs, rfl⟩), rfl⟩

theorem le_of_le_sup_center_of_perfect {X : Type*} [Group X] {E H Z : Subgroup X}
    (hZ : Z ≤ center X) (hE : E ≤ H ⊔ Z) (hEp : ⁅E, E⁆ = E) : E ≤ H := by
  have hZN : Z ≤ normalizer (H : Set X) := fun z hz =>
    centralizer_le_normalizer _ (by
      rw [mem_centralizer_iff]
      intro h _
      exact (mem_center_iff.1 (hZ hz) h))
  rw [← hEp, commutator_le]
  intro a ha b hb
  have ha' : a ∈ ((H ⊔ Z : Subgroup X) : Set X) := hE ha
  have hb' : b ∈ ((H ⊔ Z : Subgroup X) : Set X) := hE hb
  rw [coe_mul_of_right_le_normalizer_left H Z hZN] at ha' hb'
  obtain ⟨h, hh, z, hz, rfl⟩ := ha'
  obtain ⟨h', hh', z', hz', rfl⟩ := hb'
  have hzc : ∀ y, z * y * z⁻¹ = y := fun y => by
    rw [← (mem_center_iff.1 (hZ hz) y), mul_inv_cancel_right]
  have hzc' : ∀ y, z' * y * z'⁻¹ = y := fun y => by
    rw [← (mem_center_iff.1 (hZ hz') y), mul_inv_cancel_right]
  have e : ⁅h * z, h' * z'⁆ = ⁅h, h'⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc h * z * (h' * z') * (h * z)⁻¹ * (h' * z')⁻¹ =
        h * (z * (h' * z') * z⁻¹) * h⁻¹ * (h' * z')⁻¹ := by group
      _ = h * (h' * z') * h⁻¹ * (h' * z')⁻¹ := by rw [hzc]
      _ = h * h' * (z' * (h⁻¹) * z'⁻¹) * h'⁻¹ := by group
      _ = h * h' * h⁻¹ * h'⁻¹ := by rw [hzc']
  change ⁅h * z, h' * z'⁆ ∈ H
  rw [e, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hh hh') (inv_mem hh)) (inv_mem hh')

theorem injective_of_natCard_range {X Y : Type*} [Group X] [Group Y] [Finite X] (φ : X →* Y)
    (h : Nat.card φ.range = Nat.card X) : Function.Injective φ := by
  have h1 := φ.ker.card_mul_index
  rw [Subgroup.index_ker, h] at h1
  have h2 : Nat.card φ.ker = 1 := by
    have hpos : 0 < Nat.card X := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, one_mul])
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  exact h2

theorem natCard_map_dvd {X Y : Type*} [Group X] [Group Y] (φ : X →* Y) (H : Subgroup X) :
    Nat.card (H.map φ) ∣ Nat.card H := by
  have e : H.map φ = (φ.comp H.subtype).range := by
    rw [← MonoidHom.map_range, Subgroup.range_subtype]
  rw [e]
  exact Subgroup.card_range_dvd _

end Generic

section Quot

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G} {V : Type*} [Group V] [Finite V]
  {C : Subgroup V}

@[expose] noncomputable def quotMap (eM : M ⧸ center M ≃* C) (φ : MulAut C) : M →* V :=
  C.subtype.comp (φ.toMonoidHom.comp (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))))

omit [Finite G] [Finite V] in
theorem quotMap_mem (eM : M ⧸ center M ≃* C) (φ : MulAut C) (m : M) : quotMap eM φ m ∈ C :=
  Subtype.prop _

theorem map_perfectCore_centralizer_quotMap (eM : M ⧸ center M ≃* C) (φ : MulAut C)
    (X : Subgroup M) :
    (perfectCore (centralizer (X : Set M))).map (quotMap eM φ) =
      perfectCore (C ⊓ centralizer ((X.map (quotMap eM φ) : Subgroup V) : Set V)) := by
  have h1 := map_perfectCore_centralizer_mk X
  have h2 := map_centralizer_mulEquiv eM (X.map (QuotientGroup.mk' (center M)))
  have h3 := map_centralizer_mulEquiv φ ((X.map (QuotientGroup.mk' (center M))).map eM.toMonoidHom)
  have hfin : Finite C := Finite.of_injective _ Subtype.val_injective
  rw [quotMap, ← map_map, ← map_map, ← map_map, h1, map_perfectCore, h2, map_perfectCore, h3,
    map_perfectCore_centralizer_subtype, map_map, map_map, map_map]
  rfl

end Quot

section B2

variable {G : Type} [Group G] [Finite G]

theorem map_perfectCore_subgroupOf_centralizer_eq {M : Subgroup G}
    (hZ : Odd (Nat.card (center M))) {X : Type*} [Group X] (eM : M ⧸ center M ≃* X) {t : G}
    (ht : orderOf t = 2) (htM : t ∈ normalizer (M : Set G))
    (hperf : ⁅E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩),
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)⁆ =
        E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) :
    (perfectCore ((centralizer ({t} : Set G)).subgroupOf M)).map
        (eM.toMonoidHom.comp (QuotientGroup.mk' (center M))) =
      E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩) := by
  have : Finite X := Finite.of_equiv _ eM.toEquiv
  rw [map_perfectCore, E6Pilot.map_subgroupOf_centralizer_eq_fixSubgroup hZ eM ht htM,
    CFSG.Quasithin.perfectCore_eq_self_of_perfect hperf]

theorem map_subtype_perfectCore_subgroupOf (M : Subgroup G) (t : G) :
    (perfectCore ((centralizer ({t} : Set G)).subgroupOf M)).map M.subtype =
      perfectCore (M ⊓ centralizer ({t} : Set G)) := by
  rw [map_perfectCore, subgroupOf_map_subtype, inf_comm]

end B2

section Model

open CFSG.SeitzReduction.E6Pilot (corootTuple)

structure XiCaseLModel {KC : Type} [Field KC] (C J : Subgroup (ModGL TwistTag.E6.tag KC))
    (η : MulAut C) {k : Type} [Field k] (eJ : J ≃* adjointGroup .F4 k) (A : Subgroup KCˣ)
    (x : C) : Prop where
  le_adjointGroup : C ≤ adjointGroup TwistTag.E6.tag KC
  two_eq_zero : (2 : KC) = 0
  eta_apply : ∀ h : C, (η h : ModGL TwistTag.E6.tag KC) =
    diagramMap TwistTag.E6 KC * h * (diagramMap TwistTag.E6 KC)⁻¹
  le : J ≤ C
  eta_eq_iff : ∀ g : C, η g = g ↔ (g : ModGL TwistTag.E6.tag KC) ∈ J
  three_le_card : 3 ≤ Nat.card A
  coroot : ∀ δ ∈ xiLPerpRoots, ∀ c ∈ A,
    ∃ hd : rootDiagUnit TwistTag.E6.tag (corootTuple δ c) ∈ J,
      (eJ ⟨_, hd⟩ : ModGL .F4 k) ∈ leviTorus k {1}
  short : ∀ a : k, a ≠ 0 → ∃ z : J, (eJ z : ModGL .F4 k) = pinnedX .F4 k (Pi.single 2 1) a ∧
    ∃ g : C, MulAut.conj g * η * (MulAut.conj g)⁻¹ = MulAut.conj (⟨z, le z.2⟩ : C) * η
  not_conj : ∀ φ : MulAut C, φ * η * φ⁻¹ ≠ MulAut.conj x * η
  fix_le : ∀ g : C, (MulAut.conj x * η) g = g → (g : ModGL TwistTag.E6.tag KC) ∈ J
  card_fix : Nat.card (E6Pilot.fixSubgroup (MulAut.conj x * η)) =
    Nat.card (centralizer ({yRep k .t} : Set (adjointGroup .F4 k)))
  fix_perfect : ⁅E6Pilot.fixSubgroup (MulAut.conj x * η),
    E6Pilot.fixSubgroup (MulAut.conj x * η)⁆ = E6Pilot.fixSubgroup (MulAut.conj x * η)

end Model

end CFSG.SeitzReduction.F4Pilot
