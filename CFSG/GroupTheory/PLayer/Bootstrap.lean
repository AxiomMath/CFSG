module

public import CFSG.GroupTheory.PLayer.PermutedDiagonal
public import CFSG.GroupTheory.PLayer.Transfer
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.GroupTheory.FixedPointsCentralQuotient
public import CFSG.LocalAnalysis.GLTheoremA.S4.PGroupCover

public section

namespace CFSG

open CFSG.Open CFSG.ComponentClassification.PerfectAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.GroupActions

variable {S : Type} [Group S]

theorem map_eq_self_of_fix {a : MulAut S} {X : Subgroup S} (h : ∀ x ∈ X, a x = x) :
    X.map a.toMonoidHom = X := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : a y = y := h y hy
    change a y ∈ X
    rw [hy']
    exact hy
  · intro hx
    exact ⟨x, hx, h x hx⟩

theorem map_fixSubgroup_eq_of_commute (a β : MulAut S) (h : a * β = β * a) :
    (fixSubgroup β).map a.toMonoidHom = fixSubgroup β := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change β (a y) = a y
    have hy' : β y = y := hy
    rw [← MulAut.mul_apply, (show Commute a β from h).symm.eq, MulAut.mul_apply, hy']
  · intro hx
    refine ⟨a.symm x, ?_, a.apply_symm_apply x⟩
    change β (a.symm x) = a.symm x
    have hx' : β x = x := hx
    have hcomm : a.symm * β = β * a.symm := (show Commute a β from h).inv_left.eq
    rw [← MulAut.mul_apply, hcomm.symm, MulAut.mul_apply, hx']

theorem fixSubgroup_map_inl (β : MulAut S) :
    (fixSubgroup β).map (SemidirectProduct.inl (φ := MonoidHom.id (MulAut S))) =
      (SemidirectProduct.inl (φ := MonoidHom.id (MulAut S)) : S →* S ⋊[MonoidHom.id (MulAut S)] MulAut S).range ⊓
        Subgroup.centralizer
          ({SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β} : Set (S ⋊[MonoidHom.id (MulAut S)] MulAut S)) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨x, rfl⟩, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : SemidirectProduct.inl (β x) =
        SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β *
          SemidirectProduct.inl x * (SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β)⁻¹ := by
      simpa only [MonoidHom.id_apply, map_inv] using
        (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut S)) (g := β) (n := x))
    have hx' : β x = x := hx
    rw [hx'] at h1
    conv_lhs => rw [h1]
    group
  · rintro ⟨hz, hc⟩
    obtain ⟨x, rfl⟩ := hz
    refine ⟨x, ?_, rfl⟩
    change SemidirectProduct.inl x ∈ Subgroup.centralizer
      ({SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β} : Set (S ⋊[MonoidHom.id (MulAut S)] MulAut S)) at hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have h1 : SemidirectProduct.inl (β x) =
        SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β *
          SemidirectProduct.inl x * (SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β)⁻¹ := by
      simpa only [MonoidHom.id_apply, map_inv] using
        (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut S)) (g := β) (n := x))
    have hc' : (SemidirectProduct.inl (φ := MonoidHom.id (MulAut S)) x :
        S ⋊[MonoidHom.id (MulAut S)] MulAut S) =
        SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β *
          SemidirectProduct.inl x * (SemidirectProduct.inr (φ := MonoidHom.id (MulAut S)) β)⁻¹ := by
      rw [← hc]
      group
    have h2 : (SemidirectProduct.inl (φ := MonoidHom.id (MulAut S)) x :
        S ⋊[MonoidHom.id (MulAut S)] MulAut S) =
        SemidirectProduct.inl (φ := MonoidHom.id (MulAut S)) (β x) := hc'.trans h1.symm
    exact CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup.mpr
      (SemidirectProduct.inl_injective h2).symm

theorem glaPLayer_inf_fixSubgroup_ne_bot_of_map_ne {p : ℕ} (hp : p.Prime) [Finite S]
    {X J : Subgroup S} {a : MulAut S} (hJ : GLAPComponent p X J)
    (hX : X.map a.toMonoidHom = X) (hJa : J.map a.toMonoidHom ≠ J)
    (hap : a ^ p = 1) (ha1 : a ≠ 1) :
    GLAPLayer p (X ⊓ fixSubgroup a) ≠ ⊥ := by
  classical
  let H := S ⋊[MonoidHom.id (MulAut S)] MulAut S
  haveI : Finite H := inferInstance
  let inl : S →* H := SemidirectProduct.inl (φ := MonoidHom.id (MulAut S))
  let inr : MulAut S →* H := SemidirectProduct.inr (φ := MonoidHom.id (MulAut S))
  have hinl : Function.Injective inl := SemidirectProduct.inl_injective
  have hker : Nat.Coprime p (Nat.card ↥(X ⊓ inl.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff inl).2 hinl, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  have hJ' : GLAPComponent p (X.map inl) (J.map inl) :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_map hp inl hker hJ
  have hfixa : (fixSubgroup a).map inl =
      inl.range ⊓ Subgroup.centralizer ({inr a} : Set H) := fixSubgroup_map_inl a
  have hxN : inr a ∈ Subgroup.normalizer ((X.map inl) : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hcomp : ((MulAut.conj (inr a) : MulAut H) : H →* H).comp inl =
        inl.comp a.toMonoidHom := by
      refine MonoidHom.ext fun x => ?_
      show (MulAut.conj (inr a)) (inl x) = inl (a x)
      have h1 : inl (a x) = inr a * inl x * (inr a)⁻¹ := by
        simpa only [MonoidHom.id_apply, map_inv] using
          (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut S)) (g := a) (n := x))
      rw [MulAut.conj_apply, h1.symm]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hX]
  have hord : orderOf (inr a) = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    have haord : orderOf a = p := orderOf_eq_prime hap ha1
    exact (orderOf_injective inr SemidirectProduct.inr_injective a).trans haord
  have hJa' : (J.map inl).map (MulAut.conj (inr a)).toMonoidHom ≠ J.map inl := by
    intro heq
    apply hJa
    have hcomp : (MulEquiv.toMonoidHom (MulAut.conj (inr a))).comp inl =
        inl.comp (MulEquiv.toMonoidHom a) := by
      refine MonoidHom.ext fun x => ?_
      show (MulAut.conj (inr a)) (inl x) = inl (a x)
      have h1 : inl (a x) = inr a * inl x * (inr a)⁻¹ := by
        simpa only [MonoidHom.id_apply, map_inv] using
          (SemidirectProduct.inl_aut (φ := MonoidHom.id (MulAut S)) (g := a) (n := x))
      rw [MulAut.conj_apply, h1.symm]
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map] at heq
    exact Subgroup.map_injective hinl heq
  have hP4 := CFSG.glaPLayer_inf_centralizer_ne_bot_of_conj_ne hp hJ' hord hxN hJa'
  have heq : (X.map inl) ⊓ Subgroup.centralizer ({inr a} : Set H) =
      (X ⊓ fixSubgroup a).map inl := by
    have hle : X.map inl ≤ inl.range := Subgroup.map_le_range inl X
    calc (X.map inl) ⊓ Subgroup.centralizer ({inr a} : Set H)
        = (X.map inl) ⊓ (inl.range ⊓ Subgroup.centralizer ({inr a} : Set H)) := by
          rw [← inf_assoc, inf_eq_left.mpr hle]
      _ = (X.map inl) ⊓ (fixSubgroup a).map inl := by rw [← hfixa]
      _ = (X ⊓ fixSubgroup a).map inl := (Subgroup.map_inf X (fixSubgroup a) inl hinl).symm
  have hker2 : Nat.Coprime p (Nat.card ↥((X ⊓ fixSubgroup a) ⊓ inl.ker)) := by
    rw [(MonoidHom.ker_eq_bot_iff inl).2 hinl, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right p
  exact (CFSG.glaPLayer_ne_bot_iff_map_ne_bot_of_coprime_ker hp inl hker2
    (X := X ⊓ fixSubgroup a)).2 (by rwa [heq] at hP4)

theorem centerQuotientHom_subgroupStabRestrict_eq_one_iff {J : Subgroup S} {a : MulAut S}
    (hperf : Group.IsPerfect ↥J) (ha : a ∈ subgroupStabAut J) :
    centerQuotientHom ↥J (subgroupStabRestrict J ⟨a, ha⟩) = 1 ↔ J ≤ fixSubgroup a := by
  have hinj := centerQuotientHom_injective ↥J
  constructor
  · intro h
    have hres : subgroupStabRestrict J ⟨a, ha⟩ = 1 :=
      hinj (h.trans (map_one (centerQuotientHom ↥J)).symm)
    intro x hx
    have hx' := congrArg (fun (f : MulAut ↥J) => f ⟨x, hx⟩) hres
    simp only [MulAut.one_apply] at hx'
    have hx'' := congrArg Subtype.val hx'
    rw [mem_fixSubgroup]
    simpa [subgroupStabRestrict_apply] using hx''
  · intro h
    have hres : subgroupStabRestrict J ⟨a, ha⟩ = 1 := by
      ext x
      rw [MulAut.one_apply]
      have hx : a (x : S) = (x : S) := h x.2
      simpa [subgroupStabRestrict_apply] using hx
    rw [hres, map_one]

theorem glaPLayer_fixSubgroup_ne_bot_of_centerQuotient_ne_bot
    {J : Type} [Group J] [Finite J] {p : ℕ} (hp : p.Prime) (a : MulAut J)
    (hperf : Group.IsPerfect J)
    (hgood : GLAPLayer p (fixSubgroup (centerQuotientHom J a)) ≠ ⊥) :
    GLAPLayer p (fixSubgroup a) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let π : J →* (J ⧸ Subgroup.center J) := QuotientGroup.mk' (Subgroup.center J)
  let φ : MulAut (J ⧸ Subgroup.center J) := centerQuotientHom J a
  let M : Subgroup J := (fixSubgroup φ).comap π
  have hker : π.ker ≤ Subgroup.center J := le_of_eq (QuotientGroup.ker_mk' _)
  have hαβ : ∀ k, π (a k) = φ (π k) := fun k => onCenterQuotient_apply_mk a k
  have hMmap : M.map π = fixSubgroup φ :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hc : ∀ y ∈ M ⊓ π.ker, ∀ x ∈ M, x * y = y * x := by
    intro y hy x _
    exact Subgroup.mem_center_iff.1 (hker hy.2) x
  have hMne : GLAPLayer p M ≠ ⊥ := by
    refine (glaPLayer_ne_bot_iff_map_ne_bot hp π hc).2 ?_
    rwa [hMmap]
  obtain ⟨P, hP⟩ := (CFSG.LocalAnalysis.GLTheoremA.S3.glaPLayer_ne_bot_iff hp).1 hMne
  let δ : M →* Subgroup.center J :=
    (Subgroup.inclusion hker).comp (fixSubgroupCocycle π hker a φ hαβ)
  let H : Subgroup ↥M := (fixSubgroup a).subgroupOf M
  have hδker : δ.ker = H := by
    rw [MonoidHom.ker_comp_of_injective _ _ (Subgroup.inclusion_injective hker),
      fixSubgroupCocycle_ker]
  have hcomm : commutator ↥M ≤ H := hδker ▸ Abelianization.commutator_subset_ker δ
  have hfix_le_M : fixSubgroup a ≤ M := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx' : a x = x := hx
    refine mem_fixSubgroup.mpr ?_
    rw [← hαβ x, hx']
  have hHmap : H.map M.subtype = fixSubgroup a := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hfix_le_M hx⟩, hx, rfl⟩
  have hmapcomm : (⁅(⊤ : Subgroup ↥M), (⊤ : Subgroup ↥M)⁆).map M.subtype = ⁅M, M⁆ := by
    rw [Subgroup.map_commutator (H₁ := (⊤ : Subgroup ↥M)) (H₂ := (⊤ : Subgroup ↥M)),
      Subgroup.map_top, Subgroup.range_subtype]
  have hcommMap : ⁅M, M⁆ ≤ fixSubgroup a := by
    rw [← hmapcomm]
    exact (Subgroup.map_mono hcomm).trans (le_of_eq hHmap)
  have hPle : P ≤ fixSubgroup a := by
    rw [← CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hP]
    exact (Subgroup.commutator_mono hP.1 hP.1).trans hcommMap
  have hPcomp : GLAPComponent p (fixSubgroup a) P :=
    CFSG.LocalAnalysis.GLTheoremB.glaPComponent_of_le hp hP hPle hfix_le_M
  exact fun hbot =>
    CFSG.LocalAnalysis.GLTheoremA.glaPComponent_ne_bot' hPcomp
      (le_bot_iff.1 (hbot ▸ le_sSup hPcomp))

theorem glaPLayer_inf_fixSubgroup_ne_bot_of_centerQuotient_ne_bot
    {p : ℕ} (hp : p.Prime) [Finite S] {β : MulAut S} {J : Subgroup S} {a : MulAut S}
    (hJ : GLAPComponent p (fixSubgroup β) J) (ha : a ∈ subgroupStabAut J)
    (hgood : GLAPLayer p (fixSubgroup (centerQuotientHom ↥J
      (subgroupStabRestrict J ⟨a, ha⟩))) ≠ ⊥) :
    GLAPLayer p (fixSubgroup β ⊓ fixSubgroup a) ≠ ⊥ := by
  classical
  have hperfJ : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ)
  have hJl : GLAPLayer p (fixSubgroup (subgroupStabRestrict J ⟨a, ha⟩)) ≠ ⊥ :=
    glaPLayer_fixSubgroup_ne_bot_of_centerQuotient_ne_bot hp
      (subgroupStabRestrict J ⟨a, ha⟩) hperfJ hgood
  have hmapfix : (fixSubgroup (subgroupStabRestrict J ⟨a, ha⟩)).map J.subtype =
      J ⊓ fixSubgroup a := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Subgroup.mem_inf.2 ⟨y.2, ?_⟩
      rw [mem_fixSubgroup]
      have hy' : (subgroupStabRestrict J ⟨a, ha⟩) y = y := hy
      calc a (y : S) = ((subgroupStabRestrict J ⟨a, ha⟩) y : S) :=
            (subgroupStabRestrict_apply J ⟨a, ha⟩ y).symm
        _ = (y : S) := congrArg Subtype.val hy'
    · rintro ⟨hxJ, hxa⟩
      refine ⟨⟨x, hxJ⟩, ?_, rfl⟩
      have hxa' : a x = x := hxa
      apply Subtype.ext
      simpa [subgroupStabRestrict_apply] using hxa'
  have hlayerJ : GLAPLayer p (J ⊓ fixSubgroup a) ≠ ⊥ := by
    have hmap := glaPLayer_map_eq_of_injective hp J.subtype J.subtype_injective
      (fixSubgroup (subgroupStabRestrict J ⟨a, ha⟩))
    rw [hmapfix] at hmap
    intro hbot
    apply hJl
    have hmapbot : (GLAPLayer p (fixSubgroup (subgroupStabRestrict J ⟨a, ha⟩))).map
        J.subtype = ⊥ := by rw [hmap, hbot]
    exact (Subgroup.map_eq_bot_iff_of_injective _ J.subtype_injective).1 hmapbot
  have hsub : IsSubnormal (J ⊓ fixSubgroup a) (fixSubgroup β ⊓ fixSubgroup a) :=
    hJ.2.1.inf _
  have hle := CFSG.LocalAnalysis.GLTheoremA.glaPLayer_le_of_isSubnormal hp hsub
  exact fun hbot => hlayerJ (le_bot_iff.1 (hbot ▸ hle))

theorem card_zpowers_sup_zpowers_eq_prime_sq {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {x y : G} (hx : x ^ p = 1) (hy : y ^ p = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) (hcomm : x * y = y * x) :
    Nat.card (Subgroup.zpowers x ⊔ Subgroup.zpowers y : Subgroup G) = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hy1 : y ≠ 1 := by
    rintro rfl
    exact hyx (Subgroup.one_mem _)
  have hxp : Nat.card (Subgroup.zpowers x : Subgroup G) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx hx1]
  have hyp : Nat.card (Subgroup.zpowers y : Subgroup G) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy hy1]
  have hdisj : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    rw [inf_comm]
    exact zpowers_inf_eq_bot_of_not_mem (G := G) hp hy hy1 hyx
  have hc : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers y, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow (show Commute x y from hcomm) i j).eq
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
    (Subgroup.zpowers x) (Subgroup.zpowers y) hc
  rw [hdisj, Subgroup.card_bot, mul_one, hxp, hyp] at hcard
  simpa [pow_two] using hcard

end CFSG

end
