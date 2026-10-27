module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGL281Grp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] noncomputable def fgQuotAut (L : Subgroup G) (s : ↥(normalizer (L : Set G))) :
    MulAut (↥L ⧸ center ↥L) :=
  QuotientGroup.congr (center ↥L) (center ↥L) (normalizerMonoidHom L s)
    ((Subgroup.characteristic_iff_map_eq.mp inferInstance) _)

theorem fgQuotAut_mk (L : Subgroup G) (s : ↥(normalizer (L : Set G))) (l : ↥L) :
    fgQuotAut L s (QuotientGroup.mk l) = QuotientGroup.mk (normalizerMonoidHom L s l) :=
  QuotientGroup.congr_mk _ _ _ _ _

@[expose] noncomputable def fgQuotAct (L : Subgroup G) :
    ↥(normalizer (L : Set G)) →* MulAut (↥L ⧸ center ↥L) where
  toFun := fgQuotAut L
  map_one' := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [fgQuotAut_mk, map_one]
    rfl
  map_mul' s s' := by
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAut.mul_apply, fgQuotAut_mk, fgQuotAut_mk, fgQuotAut_mk, map_mul]
    rfl

theorem fgQuotAct_mk (L : Subgroup G) (s : ↥(normalizer (L : Set G))) (l l' : ↥L)
    (hl : (l' : G) = (s : G) * l * (s : G)⁻¹) :
    fgQuotAct L s (QuotientGroup.mk l) = QuotientGroup.mk l' := by
  have h : Subgroup.normalizerMonoidHom L s l = l' := Subtype.ext hl.symm
  exact (fgQuotAut_mk L s l).trans (congrArg QuotientGroup.mk h)

theorem fgQuotAct_eq_one_iff {L : Subgroup G} (hL : commutator ↥L = ⊤)
    (s : ↥(normalizer (L : Set G))) :
    fgQuotAct L s = 1 ↔ (s : G) ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    let φ : ↥L ≃* ↥L := normalizerMonoidHom L s
    have hφmk : ∀ l : ↥L, l⁻¹ * φ l ∈ center ↥L := by
      intro l
      have h1 : fgQuotAct L s (QuotientGroup.mk l) = QuotientGroup.mk (φ l) :=
        fgQuotAct_mk L s l (φ l) rfl
      rw [h, MulAut.one_apply] at h1
      exact QuotientGroup.eq.mp h1
    have hcomm : ∀ a b : ↥L, φ ⁅a, b⁆ = ⁅a, b⁆ := by
      intro a b
      have key := fg_comm_mul_central (a := a) (b := b) (hφmk a) (hφmk b)
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at key
      rw [map_commutatorElement]
      exact key
    have hK : commutator ↥L ≤ (centralizer ({(s : G)} : Set G)).comap L.subtype := by
      change ⁅(⊤ : Subgroup ↥L), ⊤⁆ ≤ _
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      change ((⁅a, b⁆ : ↥L) : G) ∈ centralizer ({(s : G)} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      rw [Set.mem_singleton_iff] at ht
      rw [ht]
      have hc : ((φ ⁅a, b⁆ : ↥L) : G) = ((⁅a, b⁆ : ↥L) : G) := congrArg Subtype.val (hcomm a b)
      change (s : G) * ↑⁅a, b⁆ * (s : G)⁻¹ = ↑⁅a, b⁆ at hc
      calc (s : G) * ↑⁅a, b⁆ = ((s : G) * ↑⁅a, b⁆ * (s : G)⁻¹) * s := by group
        _ = ↑⁅a, b⁆ * s := by rw [hc]
    have htop : (⊤ : Subgroup ↥L) ≤ (centralizer ({(s : G)} : Set G)).comap L.subtype := by
      rw [← hL]
      exact hK
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxK := htop (Subgroup.mem_top (⟨x, hx⟩ : ↥L))
    change x ∈ centralizer ({(s : G)} : Set G) at hxK
    rw [Subgroup.mem_centralizer_iff] at hxK
    exact (hxK s (Set.mem_singleton _)).symm
  · intro hc
    ext q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have hcomm : (l : G) * (s : G) = (s : G) * (l : G) :=
      Subgroup.mem_centralizer_iff.mp hc (l : G) l.2
    rw [fgQuotAct_mk L s l l (by rw [← hcomm]; group)]
    rfl

@[expose] noncomputable def fgRhoE {L : Subgroup G} {E : Type*} [Group E]
    (e : ↥L ⧸ center ↥L ≃* E) : ↥L →* E :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))

theorem fgRhoE_apply {L : Subgroup G} {E : Type*} [Group E] (e : ↥L ⧸ center ↥L ≃* E)
    (l : ↥L) : fgRhoE e l = e (QuotientGroup.mk l) := rfl

theorem fg_ker_rhoE {L : Subgroup G} {E : Type*} [Group E] (e : ↥L ⧸ center ↥L ≃* E) :
    (fgRhoE e).ker = center ↥L := by
  ext l
  rw [MonoidHom.mem_ker, fgRhoE_apply, MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]

@[expose] noncomputable def fgThetaE {L : Subgroup G} {E : Type*} [Group E]
    (e : ↥L ⧸ center ↥L ≃* E) {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) :
    ↥R →* MulAut E :=
  ((MulAut.congr e).toMonoidHom.comp (fgQuotAct L)).comp (Subgroup.inclusion hR)

theorem fg_relIndex_eq_card_range_E {L : Subgroup G} (hL : commutator ↥L = ⊤) {E : Type*}
    [Group E] (e : ↥L ⧸ center ↥L ≃* E) {R : Subgroup G} (hR : R ≤ normalizer (L : Set G)) :
    (centralizer (L : Set G)).relIndex R = Nat.card (fgThetaE e hR).range := by
  have hker : (fgThetaE e hR).ker = (centralizer (L : Set G)).subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change (MulAut.congr e) (fgQuotAct L (Subgroup.inclusion hR r)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    exact fgQuotAct_eq_one_iff hL ⟨(r : G), hR r.2⟩
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]

theorem fg_thetaE_fixes {L : Subgroup G} {E : Type*} [Group E] (e : ↥L ⧸ center ↥L ≃* E)
    {X R : Subgroup G} (hR : R ≤ normalizer (L : Set G) ⊓ centralizer (X : Set G)) :
    ∀ a ∈ (fgThetaE e (hR.trans inf_le_left)).range,
      ∀ j ∈ (X.subgroupOf L).map (fgRhoE e), a j = j := by
  rintro _ ⟨r, rfl⟩ _ ⟨x₀, hx₀, rfl⟩
  have hrC : (r : G) ∈ centralizer (X : Set G) := (hR r.2).2
  have hcomm : (x₀ : G) * (r : G) = (r : G) * (x₀ : G) := mem_centralizer_iff.mp hrC _ hx₀
  have hact : fgQuotAct L ⟨(r : G), (hR r.2).1⟩ (QuotientGroup.mk x₀) = QuotientGroup.mk x₀ :=
    fgQuotAct_mk L _ x₀ x₀ (by rw [← hcomm, mul_inv_cancel_right])
  change (MulAut.congr e (fgQuotAct L ⟨(r : G), (hR r.2).1⟩)) (e (QuotientGroup.mk x₀)) =
    e (QuotientGroup.mk x₀)
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    hact]

end CFSG.OddStandard.SmallF3.Omega
