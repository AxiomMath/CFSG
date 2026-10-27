module

public import CFSG.LargeExtraspecial.S2Basic
public import CFSG.LargeExtraspecial.S4FiveL
public import CFSG.LargeExtraspecial.S6Mod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

class NQHyp (S : Setting G) (g : G) (t : S.O) : Prop where
  conj_mem : g * S.z * g⁻¹ ∈ S.QG
  comm : ∀ x ∈ Nbar S g t, ∀ y ∈ Nbar S g t, x * y * x⁻¹ * y⁻¹ ∈ zpowers t
  sq : ∀ x ∈ Nbar S g t, x * x ∈ zpowers t

instance instNormalNQ {t : S.O} [hN : NQHyp S g t] :
    ((zpowers t).subgroupOf (Nbar S g t)).Normal := by
  constructor
  intro n hn x
  rw [mem_subgroupOf] at hn ⊢
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
  have hc : (x : S.O) * t = t * x := commute_of_mem_Rbar hN.conj_mem (Nbar_le_Rbar x.2)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hk,
    (Commute.zpow_right hc k).eq, mul_inv_cancel_right]
  exact zpow_mem_zpowers t k

noncomputable instance instCommGroupNQ {t : S.O} [hN : NQHyp S g t] :
    CommGroup (↥(Nbar S g t) ⧸ (zpowers t).subgroupOf (Nbar S g t)) :=
  { (inferInstance : Group (↥(Nbar S g t) ⧸ (zpowers t).subgroupOf (Nbar S g t))) with
    mul_comm := by
      intro a b
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      have := hN.comm _ (inv_mem y.2) _ (inv_mem x.2)
      simpa [mul_assoc] using this }

noncomputable instance instModuleNQ {t : S.O} [hN : NQHyp S g t] :
    Module (ZMod 2) (Additive (↥(Nbar S g t) ⧸ (zpowers t).subgroupOf (Nbar S g t))) :=
  AddCommGroup.zmodModule fun x => by
    induction x using QuotientGroup.induction_on with | H x => ?_
    change Additive.ofMul ((QuotientGroup.mk x : ↥(Nbar S g t) ⧸ _) ^ 2) = 0
    rw [← QuotientGroup.mk_pow, pow_two]
    change Additive.ofMul _ = Additive.ofMul 1
    congr 1
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hN.sq x x.2

variable (S g) in
noncomputable abbrev NQ (t : S.O) : Type _ :=
  Additive (↥(Nbar S g t) ⧸ (zpowers t).subgroupOf (Nbar S g t))

noncomputable abbrev nqMk {t : S.O} [NQHyp S g t] (x : Nbar S g t) : NQ S g t :=
  Additive.ofMul (QuotientGroup.mk x)

theorem nqMk_mul {t : S.O} [NQHyp S g t] (x y : Nbar S g t) :
    nqMk (x * y) = nqMk x + nqMk y :=
  rfl

theorem nqMk_eq_iff {t : S.O} [NQHyp S g t] (x y : Nbar S g t) :
    nqMk x = nqMk y ↔ (x : S.O)⁻¹ * y ∈ zpowers t := by
  rw [nqMk, nqMk, EmbeddingLike.apply_eq_iff_eq, QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem nqMk_eq_zero_iff {t : S.O} [NQHyp S g t] (x : Nbar S g t) :
    nqMk x = 0 ↔ (x : S.O) ∈ zpowers t := by
  rw [nqMk, ← ofMul_one, EmbeddingLike.apply_eq_iff_eq, QuotientGroup.eq_one_iff,
    mem_subgroupOf]

theorem nqMk_surjective {t : S.O} [NQHyp S g t] (m : NQ S g t) : ∃ x, nqMk x = m := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
  exact ⟨x, by rw [nqMk, hx]; rfl⟩

@[expose] noncomputable def nConj {t : S.O} [hN : NQHyp S g t] (r : Rbar S g t) :
    Nbar S g t →* Nbar S g t where
  toFun n := ⟨r * n * (r : S.O)⁻¹, by
    obtain ⟨k, hk⟩ := MonoidHom.mem_range.mp (Rbar_le_Mbar r.2)
    have := conj_mem_Nbar hN.conj_mem (hk ▸ commute_of_mem_Rbar hN.conj_mem r.2) n.2
    rwa [hk] at this⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem coe_nConj {t : S.O} [NQHyp S g t] (r : Rbar S g t) (n : Nbar S g t) :
    ((nConj r n : Nbar S g t) : S.O) = r * n * (r : S.O)⁻¹ :=
  rfl

@[expose] noncomputable def nqLin {t : S.O} [hN : NQHyp S g t] (r : Rbar S g t) :
    NQ S g t →ₗ[ZMod 2] NQ S g t :=
  (QuotientGroup.map _ _ (nConj r) (by
    intro n hn
    rw [mem_comap, mem_subgroupOf] at *
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hn
    change (r : S.O) * n * (r : S.O)⁻¹ ∈ zpowers t
    have hc := (Commute.zpow_right (commute_of_mem_Rbar hN.conj_mem r.2) k).eq
    rw [← hk, hc, mul_inv_cancel_right]
    exact zpow_mem_zpowers t k)).toAdditive.toZModLinearMap 2

theorem nqLin_mk {t : S.O} [NQHyp S g t] (r : Rbar S g t) (n : Nbar S g t) :
    nqLin r (nqMk n) = nqMk (nConj r n) :=
  rfl

theorem nqLin_comp {t : S.O} [NQHyp S g t] (r s : Rbar S g t) (m : NQ S g t) :
    nqLin r (nqLin s m) = nqLin (r * s) m := by
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  show nqMk (nConj r (nConj s n)) = nqMk (nConj (r * s) n)
  congr 1

theorem nqLin_one {t : S.O} [NQHyp S g t] (m : NQ S g t) :
    nqLin (1 : Rbar S g t) m = m := by
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  show nqMk (nConj (1 : Rbar S g t) n) = nqMk n
  congr 1

@[expose] noncomputable def nqConj {t : S.O} [NQHyp S g t] (r : Rbar S g t) :
    NQ S g t ≃ₗ[ZMod 2] NQ S g t :=
  LinearEquiv.ofLinearMap (nqLin r) (nqLin r⁻¹)
    (LinearMap.ext fun m => by
      show nqLin r (nqLin r⁻¹ m) = m
      rw [nqLin_comp, mul_inv_cancel, nqLin_one])
    (LinearMap.ext fun m => by
      show nqLin r⁻¹ (nqLin r m) = m
      rw [nqLin_comp, inv_mul_cancel, nqLin_one])

variable (S g) in
@[expose] noncomputable def nqHom (t : S.O) [NQHyp S g t] :
    Rbar S g t →* (NQ S g t ≃ₗ[ZMod 2] NQ S g t) where
  toFun := nqConj
  map_one' := LinearEquiv.ext fun m => by
    show nqLin (1 : Rbar S g t) m = m
    exact nqLin_one m
  map_mul' r s := LinearEquiv.ext fun m => by
    show nqLin (r * s) m = nqLin r (nqLin s m)
    exact (nqLin_comp r s m).symm

theorem nqHom_mk {t : S.O} [NQHyp S g t] (r : Rbar S g t) (n : Nbar S g t) :
    nqHom S g t r (nqMk n) = nqMk (nConj r n) :=
  rfl

theorem nqHom_apply_of_mem {t : S.O} [hN : NQHyp S g t] {x : Rbar S g t}
    (hx : (x : S.O) ∈ Nbar S g t) (m : NQ S g t) : nqHom S g t x m = m := by
  obtain ⟨n, rfl⟩ := nqMk_surjective m
  rw [nqHom_mk, nqMk_eq_iff, coe_nConj]
  have h2 := hN.comm _ hx _ (inv_mem n.2)
  rw [show (x : S.O) * (n : S.O)⁻¹ * (x : S.O)⁻¹ * (n : S.O)⁻¹⁻¹ =
    ((x : S.O) * n * (x : S.O)⁻¹)⁻¹ * n by group] at h2
  exact h2

theorem nqHom_eq_one {t : S.O} [NQHyp S g t] {x : Rbar S g t}
    (hx : (x : S.O) ∈ Nbar S g t) : nqHom S g t x = 1 :=
  LinearEquiv.ext fun m => (nqHom_apply_of_mem hx m).trans (LinearEquiv.refl_apply m).symm

variable (S g) in
@[expose] noncomputable def nqRep (t : S.O) [hN : NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) :
    Y →* (NQ S g t ≃ₗ[ZMod 2] NQ S g t) :=
  (descend (resV hN.conj_mem t) (nqHom S g t) (by
    intro x hx
    rw [MonoidHom.mem_ker, resV_eq_one_iff] at hx
    exact nqHom_eq_one hx)).comp
    (MulEquiv.subgroupCongr ((range_resV hN.conj_mem t).trans hY).symm).toMonoidHom

theorem nqRep_eq {t : S.O} [hN : NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) {e : Y}
    {x : Rbar S g t} (hex : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV hN.conj_mem t x) :
    nqRep S g t hY e = nqHom S g t x := by
  unfold nqRep
  rw [MonoidHom.comp_apply]
  exact descend_apply' _ _ _
    (e := (MulEquiv.subgroupCongr ((range_resV hN.conj_mem t).trans hY).symm).toMonoidHom e) hex

theorem nqRep_apply {t : S.O} [hN : NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y) {e : Y}
    {x : Rbar S g t} (hex : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV hN.conj_mem t x)
    (n : Nbar S g t) : nqRep S g t hY e (nqMk n) = nqMk (nConj x n) := by
  rw [nqRep_eq hY hex]
  rfl

variable (S g) in
@[expose] noncomputable def nqSub (t : S.O) [NQHyp S g t] (X : Subgroup S.O) :
    Submodule (ZMod 2) (NQ S g t) where
  carrier := {m | ∃ x : Nbar S g t, (x : S.O) ∈ X ∧ nqMk x = m}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_mem hx hy, rfl⟩
  zero_mem' := ⟨1, one_mem _, rfl⟩
  smul_mem' := by
    rintro c _ ⟨x, hx, rfl⟩
    rcases zmod2_eq_zero_or_eq_one c with rfl | rfl
    · exact ⟨1, one_mem _, by rw [zero_smul]; rfl⟩
    · exact ⟨x, hx, by rw [one_smul]⟩

theorem mem_nqSub {t : S.O} [NQHyp S g t] {X : Subgroup S.O} (htX : t ∈ X) (n : Nbar S g t) :
    nqMk n ∈ nqSub S g t X ↔ (n : S.O) ∈ X := by
  constructor
  · rintro ⟨x, hx, hxn⟩
    rw [nqMk_eq_iff] at hxn
    have := mul_mem hx ((zpowers_le.mpr htX) hxn)
    rwa [mul_inv_cancel_left] at this
  · intro hn
    exact ⟨n, hn, rfl⟩

theorem isCompl_nqSub {t : S.O} [NQHyp S g t] {X Y : Subgroup S.O}
    (hprod : ∀ n : Nbar S g t, ∃ x y : Nbar S g t, (x : S.O) ∈ X ∧ (y : S.O) ∈ Y ∧ n = x * y)
    (hXY : X ⊓ Y = zpowers t) :
    IsCompl (nqSub S g t X) (nqSub S g t Y) := by
  constructor
  · rw [Submodule.disjoint_def]
    rintro m ⟨x, hx, rfl⟩ ⟨y, hy, hyx⟩
    rw [nqMk_eq_iff] at hyx
    have hxY : (x : S.O) ∈ Y := by
      have htY : t ∈ Y := (hXY.ge (mem_zpowers t)).2
      have := mul_mem hy ((zpowers_le.mpr htY) hyx)
      rwa [mul_inv_cancel_left] at this
    rw [nqMk_eq_zero_iff, ← hXY]
    exact ⟨hx, hxY⟩
  · rw [codisjoint_iff, eq_top_iff]
    intro m _
    obtain ⟨n, rfl⟩ := nqMk_surjective m
    obtain ⟨x, y, hx, hy, rfl⟩ := hprod n
    rw [nqMk_mul]
    exact Submodule.add_mem_sup ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

theorem conj_mem_zpowers_iff {t n w : S.O} (hn : n * t = t * n) :
    n * w * n⁻¹ ∈ zpowers t ↔ w ∈ zpowers t := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hc := (Commute.zpow_right hn k).eq
    rw [show w = n⁻¹ * (n * w * n⁻¹) * n by group, ← hk, mul_assoc, ← hc, inv_mul_cancel_left]
    exact zpow_mem_zpowers t k
  · intro h
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
    have hc := (Commute.zpow_right hn k).eq
    rw [← hk, hc, mul_inv_cancel_right]
    exact zpow_mem_zpowers t k

theorem nqMk_nConj_eq_iff {t : S.O} [hN : NQHyp S g t] (r : Rbar S g t) (n : Nbar S g t) :
    nqMk (nConj r n) = nqMk n ↔ (r : S.O) * n * (r : S.O)⁻¹ * (n : S.O)⁻¹ ∈ zpowers t := by
  have hn : (n : S.O)⁻¹ * t = t * (n : S.O)⁻¹ :=
    commute_inv (commute_of_mem_Rbar hN.conj_mem (Nbar_le_Rbar n.2))
  rw [nqMk_eq_iff, coe_nConj, show ((r : S.O) * n * (r : S.O)⁻¹)⁻¹ * n =
    (n : S.O)⁻¹ * ((r : S.O) * n * (r : S.O)⁻¹ * (n : S.O)⁻¹)⁻¹ * (n : S.O)⁻¹⁻¹ by group,
    conj_mem_zpowers_iff hn, inv_mem_iff]

theorem mem_fixOf_nqRep_iff {t : S.O} [hN : NQHyp S g t]
    {Y : Subgroup (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} (hY : RmodN S g t = Y)
    {T : Set (Vt S g t ≃ₗ[ZMod 2] Vt S g t)} {K : Set S.O} (hKR : K ⊆ Rbar S g t)
    (hT : ∀ e ∈ Y, e ∈ T ↔ ∃ x, ∃ hx : x ∈ K, e = resV hN.conj_mem t ⟨x, hKR hx⟩)
    (n : Nbar S g t) :
    nqMk n ∈ S2.fixOf (nqRep S g t hY) T ↔ ∀ x ∈ K, x * n * x⁻¹ * (n : S.O)⁻¹ ∈ zpowers t := by
  rw [S2.mem_fixOf]
  constructor
  · intro hfix x hx
    have he : resV hN.conj_mem t ⟨x, hKR hx⟩ ∈ Y := by
      rw [← hY, ← range_resV hN.conj_mem t]; exact ⟨_, rfl⟩
    have h1 := hfix ⟨_, he⟩ ((hT _ he).mpr ⟨x, hx, rfl⟩)
    rw [nqRep_apply hY (x := ⟨x, hKR hx⟩) rfl] at h1
    exact (nqMk_nConj_eq_iff _ n).mp h1
  · intro hK e he
    obtain ⟨x, hx, hex⟩ := (hT e e.2).mp he
    rw [nqRep_apply hY hex]
    exact (nqMk_nConj_eq_iff _ n).mpr (hK x hx)

end CFSG.LargeExtraspecial.S6
