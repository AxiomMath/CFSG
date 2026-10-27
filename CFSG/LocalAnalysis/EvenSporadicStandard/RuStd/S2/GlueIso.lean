module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.GlueThree

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Glue

open Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

@[expose] noncomputable def thetaHom (hc : Config G L t) {a : G} (ha : a ∈ L)
    (φ : CenL L ha →* M10) : CenT hc ha →* Multiplicative (ZMod 2) × M10 :=
  (MonoidHom.prod ((zpowersEquivZMod hc.orderOf_z).toMonoidHom.comp (MonoidHom.snd _ _))
    (φ.comp (MonoidHom.fst _ _))).comp (cenEquiv hc ha).toMonoidHom

theorem thetaHom_cenMul (hc : Config G L t) {a : G} (ha : a ∈ L) (φ : CenL L ha →* M10)
    (m : CenL L ha) (z : ↥(zpowers t)) :
    thetaHom hc ha φ (cenMul hc ha (m, z)) = (zpowersEquivZMod hc.orderOf_z z, φ m) := by
  have h : cenEquiv hc ha (cenMul hc ha (m, z)) = (m, z) :=
    (cenEquiv hc ha).apply_symm_apply (m, z)
  simp only [thetaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h, MonoidHom.prod_apply]
  rfl

theorem thetaHom_surjective (hc : Config G L t) {a : G} (ha : a ∈ L) (φ : CenL L ha →* M10)
    (hφ : Function.Surjective φ) : Function.Surjective (thetaHom hc ha φ) := by
  rintro ⟨e, q⟩
  obtain ⟨m, rfl⟩ := hφ q
  obtain ⟨z, rfl⟩ := (zpowersEquivZMod hc.orderOf_z).surjective e
  exact ⟨cenMul hc ha (m, z), thetaHom_cenMul hc ha φ m z⟩

theorem thetaHom_eq_one_iff_mem (hc : Config G L t) {r : G} (hrL : r ∈ L)
    (φ : CenL L hrL →* M10)
    (hker : φ.ker = (zpowers (⟨r, hrL⟩ : L)).subgroupOf (centralizer ({(⟨r, hrL⟩ : L)} : Set L)))
    (x : CenT hc hrL) : thetaHom hc hrL φ x = 1 ↔ ((x : CenG r) : G) ∈ zpowers r := by
  obtain ⟨⟨m, z⟩, hx⟩ : ∃ p, cenMul hc hrL p = x :=
    ⟨cenEquiv hc hrL x, cenMul_cenEquiv hc hrL x⟩
  subst hx
  have hval : (((cenMul hc hrL (m, z) : CenT hc hrL) : CenG r) : G) = ((m : L) : G) * (z : G) :=
    rfl
  have hmem : ∀ m : CenL L hrL, φ m = 1 ↔ ((m : L) : G) ∈ zpowers r := by
    intro m
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      exact mem_zpowers_iff.2 ⟨k, by simpa using congrArg Subtype.val hk⟩
    · intro h
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 h
      exact mem_zpowers_iff.2 ⟨k, Subtype.ext (by simpa using hk)⟩
  rw [thetaHom_cenMul, hval]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Prod.mk_eq_one.1 h
    have hz : z = 1 := (zpowersEquivZMod hc.orderOf_z).map_eq_one_iff.1 h1
    rw [hz, Subgroup.coe_one, mul_one]
    exact (hmem m).1 h2
  · intro h
    have hmz : ((m : L) : G) * (z : G) ∈ zpowers r := h
    have hz1 : (z : G) = 1 := by
      have hzL : (z : G) ∈ L := by
        have h1 : ((m : L) : G)⁻¹ * (((m : L) : G) * (z : G)) ∈ L :=
          mul_mem (inv_mem (m : L).2) (zpowers_le.2 hrL hmz)
        simpa using h1
      exact Subgroup.disjoint_def.1 hc.disjoint hzL z.2
    have hz : z = 1 := Subtype.ext hz1
    rw [hz1, mul_one] at hmz
    exact Prod.mk_eq_one.2 ⟨by rw [hz, map_one], (hmem m).2 hmz⟩

variable [Finite G]

theorem cen_iso_of (hc : Config G L t) (h3 : RuThreeFacts L) {r : G} (hrL : r ∈ L)
    (hr3 : orderOf r = 3) :
    Nonempty (↥(centralizer ({(QuotientGroup.mk (tCen hc hrL) : CenG r ⧸ CFSG.oddCore (CenG r))} :
      Set (CenG r ⧸ CFSG.oddCore (CenG r)))) ≃* (Multiplicative (ZMod 2) × M10)) := by
  have hrL3 : orderOf (⟨r, hrL⟩ : L) = 3 := by rw [Subgroup.orderOf_mk]; exact hr3
  obtain ⟨φ, hφs, hφk⟩ := h3.quot ⟨r, hrL⟩ hrL3
  set O := CFSG.oddCore (CenG r) with hO
  let Ψ : CenT hc hrL →* ↥(centralizer ({(QuotientGroup.mk (tCen hc hrL) : CenG r ⧸ O)} :
      Set (CenG r ⧸ O))) :=
    ((QuotientGroup.mk' O).comp (centralizer ({tCen hc hrL} : Set (CenG r))).subtype).codRestrict
      _ (by
        intro x
        rw [mem_centralizer_singleton_iff]
        have h := mem_centralizer_singleton_iff.1 x.2
        have := congrArg (QuotientGroup.mk' O) h
        rw [map_mul, map_mul] at this
        exact this)
  have hΨ : ∀ x : CenT hc hrL, ((Ψ x : ↥(centralizer ({(QuotientGroup.mk (tCen hc hrL) :
      CenG r ⧸ O)} : Set (CenG r ⧸ O)))) : CenG r ⧸ O) = QuotientGroup.mk (x : CenG r) :=
    fun _ => rfl
  have hΨs : Function.Surjective Ψ := by
    rintro ⟨q, hq⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
    have hcomm : (c : CenG r ⧸ O) * ↑(tCen hc hrL) = ↑(tCen hc hrL) * c :=
      mem_centralizer_singleton_iff.1 hq
    have hn : c * tCen hc hrL * c⁻¹ * (tCen hc hrL)⁻¹ ∈ O := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      calc (c : CenG r ⧸ O) * ↑(tCen hc hrL) * (c : CenG r ⧸ O)⁻¹ * (↑(tCen hc hrL))⁻¹
          = (↑(tCen hc hrL) * c) * (c : CenG r ⧸ O)⁻¹ * (↑(tCen hc hrL))⁻¹ := by rw [hcomm]
        _ = 1 := by group
    obtain ⟨s, hsO, hs⟩ := exists_lift (tCen_mul_self hc hrL)
      (fun n hn => odd_orderOf_of_mem_oddCore hn) hn
    refine ⟨⟨s⁻¹ * c, hs⟩, Subtype.ext ?_⟩
    rw [hΨ]
    have hs1 : (QuotientGroup.mk s : CenG r ⧸ O) = 1 := (QuotientGroup.eq_one_iff s).2 hsO
    simp [hs1]
  have hker : Ψ.ker = (thetaHom hc hrL φ).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, thetaHom_eq_one_iff_mem hc hrL φ hφk]
    constructor
    · intro hx
      have h1 : (x : CenG r) ∈ O := (QuotientGroup.eq_one_iff _).1
        (by rw [← hΨ]; exact congrArg Subtype.val hx)
      have hcomm : tCen hc hrL * (x : CenG r) * (tCen hc hrL)⁻¹ = x := by
        have h := mem_centralizer_singleton_iff.1 x.2
        calc tCen hc hrL * (x : CenG r) * (tCen hc hrL)⁻¹
            = ((x : CenG r) * tCen hc hrL) * (tCen hc hrL)⁻¹ := by rw [h]
          _ = x := by group
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (cen_odd_of hc h3 hrL hr3 x h1 hcomm)
      exact mem_zpowers_iff.2 ⟨k, by simpa [rCen] using congrArg Subtype.val hk⟩
    · intro hx
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
      have h1 : (x : CenG r) ∈ O := by
        have : (x : CenG r) = rCen r ^ k := Subtype.ext (by simpa [rCen] using hk.symm)
        rw [this]
        exact zpow_mem (rCen_mem_oddCore hr3) k
      exact Subtype.ext (by rw [hΨ]; exact (QuotientGroup.eq_one_iff _).2 h1)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective Ψ hΨs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective (thetaHom hc hrL φ)
        (thetaHom_surjective hc hrL φ hφs)))⟩

end CFSG.EvenSporadicStandard.RuStd.S2.Glue
