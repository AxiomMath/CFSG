module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.Assembly
public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.NativeFacts
public import CFSG.Monster.B.GSide.HSylowBetaClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.Open CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.GSide

@[expose] noncomputable def cD
    : commutator Eam := ⟨cE', cE'_mem_commutator⟩

theorem coe_cD :
    (cD : Eam) = cE' := rfl

theorem vStabEam_cV0_mul_lamW0H
    : vStabEam (cV0 * lamW0H) = xhatEam :=
  Subtype.ext (by rw [coe_vStabEam, coe_xhatEam, ← iotaH_apply, iotaH_cV0_mul_lamW0H])

theorem lamW0H_mem_commutator :
    lamW0H ∈ commutator (vStab cv0) :=
  (coe_mem_derivedStab_iff lamW0H).1 (clabelS_mem_derivedStab_of_adj cgraph_adj_cv0_cw0)

theorem xhatEam_mem_commutator :
    xhatEam ∈ commutator Eam := by
  rw [← vStabEam_cV0_mul_lamW0H, map_mul, vStabEam_cV0]
  refine mul_mem cE'_mem_commutator ?_
  rw [← map_commutator_vStabEam]
  exact mem_map_of_mem _ lamW0H_mem_commutator

@[expose] noncomputable def xD
    : commutator Eam := ⟨xhatEam, xhatEam_mem_commutator⟩

theorem coe_xD :
    (xD : Eam) = xhatEam := rfl

section Def

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] noncomputable def dOf
    (ι : L ≃* commutator Eam) : G := (ι.symm cD : L)

@[expose] noncomputable def zOf
    (ι : L ≃* commutator Eam) : G := (ι.symm xD : L)

end Def

@[expose] def Stroth22 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    centralizer (L : Set G) = (center L).map L.subtype → ∀ ι : L ≃* commutator Eam,
      ¬ IsConj (dOf ι) (zOf ι) ∧ ∃ g : G, IsPGroup 2 (zpowers g) ∧
        g * dOf ι * g⁻¹ = dOf ι * zOf ι ∧ g * zOf ι * g⁻¹ = zOf ι

@[expose] def InvolutionSquareTest :
    Prop :=
  ∀ u : commutator Eam, u * u = 1 → u ≠ cD → IsConj (cD * xD) u ∨
    ∃ s ∈ closure {i : commutator Eam | i * i = 1 ∧ i * u = u * i}, s * s = u

@[expose] def RootSylowData :
    Prop :=
  ¬ IsConj xhatEam (cE' * xhatEam) ∧
    ∃ T : Sylow 2 (commutator Eam), xD ∈ T ∧ ∀ b : Eam,
      (∀ t ∈ (T : Subgroup (commutator Eam)), b * (t : Eam) = (t : Eam) * b) ↔
        b = 1 ∨ b = cE' ∨ b = xhatEam ∨ b = cE' * xhatEam

theorem orderOf_cE' :
    orderOf cE' = 2 := by
  rw [← Nat.card_zpowers, natCard_zpowers_cE'_eq_two]

theorem orderOf_xhatEam :
    orderOf xhatEam = 2 := by
  rw [← Subgroup.orderOf_coe, coe_xhatEam, orderOf_xhat]

theorem cD_mem_center :
    cD ∈ center (commutator Eam) := by
  have h : (cE' : Eam) ∈ (center (commutator Eam)).map (commutator Eam).subtype := by
    rw [short_F4_derived_standard_perfect_cover.2.2.2.1]
    exact mem_zpowers _
  obtain ⟨w, hw, hwc⟩ := h
  rwa [show w = cD from Subtype.ext hwc] at hw

theorem natCard_center_commutator
    : Nat.card (center (commutator Eam)) = 2 := by
  rw [← card_map_of_injective (commutator Eam).subtype_injective,
    short_F4_derived_standard_perfect_cover.2.2.2.1, natCard_zpowers_cE'_eq_two]

theorem cD_mul_self :
    cD * cD = 1 :=
  Subtype.ext (by rw [coe_mul, coe_cD, coe_one, ← pow_two, ← orderOf_cE', pow_orderOf_eq_one])

theorem xD_mul_self :
    xD * xD = 1 :=
  Subtype.ext (by
    rw [coe_mul, coe_xD, coe_one, ← pow_two, ← orderOf_xhatEam, pow_orderOf_eq_one])

theorem xhatEam_ne_cE'
    : xhatEam ≠ cE' := fun h => CFSG.Monster.B.TwoA.Sp8.cQ_ne_xhat (by
  have h' := congrArg (fun y : Eam => (y : Dfull)) h
  simp only [coe_xhatEam] at h'
  exact h'.symm)

theorem xD_ne_cD
    : xD ≠ cD := fun h => xhatEam_ne_cE' (congrArg Subtype.val h)

theorem xD_ne_one :
    xD ≠ 1 := fun h => by
  have h' : orderOf xhatEam = 1 := by
    rw [← coe_xD, h, coe_one, orderOf_one]
  rw [orderOf_xhatEam] at h'
  exact absurd h' (by norm_num)

section Transport

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] noncomputable def phiOf
    (ι : L ≃* commutator Eam) : commutator Eam →* G :=
  L.subtype.comp ι.symm.toMonoidHom

theorem phiOf_apply
    (ι : L ≃* commutator Eam) (u : commutator Eam) :
    phiOf ι u = (ι.symm u : G) := rfl

theorem phiOf_injective
    (ι : L ≃* commutator Eam) : Function.Injective (phiOf ι) :=
  L.subtype_injective.comp ι.symm.injective

theorem phiOf_mem
    (ι : L ≃* commutator Eam) (u : commutator Eam) : phiOf ι u ∈ L :=
  (ι.symm u).2

theorem phiOf_iota
    (ι : L ≃* commutator Eam) {x : G} (hx : x ∈ L) : phiOf ι (ι ⟨x, hx⟩) = x := by
  rw [phiOf_apply, MulEquiv.symm_apply_apply]

theorem phiOf_mul
    (ι : L ≃* commutator Eam) (a b : commutator Eam) :
    phiOf ι (a * b) = phiOf ι a * phiOf ι b :=
  map_mul (phiOf ι) a b

theorem phiOf_cD
    (ι : L ≃* commutator Eam) : phiOf ι cD = dOf ι := rfl

theorem phiOf_xD
    (ι : L ≃* commutator Eam) : phiOf ι xD = zOf ι := rfl

theorem dOf_mem
    (ι : L ≃* commutator Eam) : dOf ι ∈ L := phiOf_mem ι cD

theorem zOf_mem
    (ι : L ≃* commutator Eam) : zOf ι ∈ L := phiOf_mem ι xD

theorem symm_cD_mem_center
    (ι : L ≃* commutator Eam) : ι.symm cD ∈ center L :=
  (mem_center_iff_of_mulEquiv ι).2 (by rw [MulEquiv.apply_symm_apply]; exact cD_mem_center)

theorem natCard_center_of_mulEquiv
    (ι : L ≃* commutator Eam) : Nat.card (center L) = 2 := by
  rw [← natCard_center_commutator, ← map_center_eq ι, card_map_of_injective ι.injective]

theorem orderOf_dOf
    (ι : L ≃* commutator Eam) : orderOf (dOf ι) = 2 := by
  rw [← phiOf_cD, orderOf_injective _ (phiOf_injective ι), ← Subgroup.orderOf_coe, coe_cD,
    orderOf_cE']

theorem dOf_mul_self
    (ι : L ≃* commutator Eam) : dOf ι * dOf ι = 1 := by
  rw [← phiOf_cD, ← map_mul, cD_mul_self, map_one]

theorem zOf_mul_self
    (ι : L ≃* commutator Eam) : zOf ι * zOf ι = 1 := by
  rw [← phiOf_xD, ← map_mul, xD_mul_self, map_one]

theorem zOf_ne_dOf
    (ι : L ≃* commutator Eam) : zOf ι ≠ dOf ι := fun h =>
  xD_ne_cD (phiOf_injective ι h)

theorem zOf_ne_one
    (ι : L ≃* commutator Eam) : zOf ι ≠ 1 := fun h =>
  xD_ne_one (phiOf_injective ι (h.trans (map_one _).symm))

theorem mul_self_ne_dOf
    (ι : L ≃* commutator Eam) {s : G} (hs : s ∈ L) : s * s ≠ dOf ι := by
  intro h
  apply mul_self_ne_cE' (ι ⟨s, hs⟩ : Eam)
  rw [← coe_mul, ← map_mul, ← coe_cD, show (⟨s, hs⟩ : L) * ⟨s, hs⟩ = ι.symm cD from Subtype.ext h,
    MulEquiv.apply_symm_apply]

theorem phiOf_mem_closure
    (ι : L ≃* commutator Eam) {u s : commutator Eam}
    (hs : s ∈ closure {i : commutator Eam | i * i = 1 ∧ i * u = u * i}) :
    phiOf ι s ∈ closure {i : G | i ∈ L ∧ i * i = 1 ∧ i * phiOf ι u = phiOf ι u * i} := by
  have h1 := mem_map_of_mem (phiOf ι) hs
  rw [MonoidHom.map_closure] at h1
  refine closure_mono ?_ h1
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨phiOf_mem ι i, by rw [← map_mul, hi.1, map_one], by rw [← map_mul, ← map_mul, hi.2]⟩

theorem mul_self_of_isConj {a b : G} (ha : a * a = 1) (h : IsConj a b) : b * b = 1 := by
  obtain ⟨k, rfl⟩ := isConj_iff.1 h
  calc k * a * k⁻¹ * (k * a * k⁻¹) = k * (a * a) * k⁻¹ := by group
    _ = 1 := by rw [ha]; group

end Transport

section Normalizer

variable {G : Type*} [Group G] {L : Subgroup G}

theorem centralizer_le_of_eq (hC : centralizer (L : Set G) = (center L).map L.subtype) :
    centralizer (L : Set G) ≤ L := by
  rw [hC]
  rintro _ ⟨w, -, rfl⟩
  exact w.2

theorem centralizer_subgroupOf_le (hC : centralizer (L : Set G) ≤ L) :
    centralizer ((L.subgroupOf (normalizer (L : Set G)) : Subgroup (normalizer (L : Set G))) :
      Set (normalizer (L : Set G))) ≤ L.subgroupOf (normalizer (L : Set G)) := by
  intro x hx
  rw [mem_subgroupOf]
  refine hC (mem_centralizer_iff.2 fun l hl => ?_)
  exact congrArg Subtype.val ((mem_centralizer_iff.1 hx) ⟨l, le_normalizer hl⟩
    (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hl))

@[expose] noncomputable def iotaN
    (ι : L ≃* commutator Eam) :
    L.subgroupOf (normalizer (L : Set G)) ≃* commutator Eam :=
  (subgroupOfEquivOfLe le_normalizer).trans ι

theorem iotaN_eq
    (ι : L ≃* commutator Eam) {l : L.subgroupOf (normalizer (L : Set G))} {y : L}
    (h : ((l : normalizer (L : Set G)) : G) = y) : iotaN ι l = ι y :=
  congrArg ι (Subtype.ext h)

theorem mul_inv_mem_of_index_le_two {M : Type*} [Group M] {R : Subgroup M} [R.FiniteIndex]
    (hR : R.index ≤ 2) {a b : M} (ha : a ∉ R) (hb : b ∉ R) : a * b⁻¹ ∈ R := by
  have h0 : R.index ≠ 0 := FiniteIndex.index_ne_zero
  have h1 : R.index ≠ 1 := fun h => ha ((index_eq_one.1 h) ▸ mem_top _)
  have h2 : R.index = 2 := by omega
  rw [mul_mem_iff_of_index_two h2, inv_mem_iff]
  exact iff_of_false ha hb

theorem exists_outer_of_not_mem
    (hO : CoverOuterLeTwo) {X : Type*} [Group X] {K : Subgroup X}
    [K.Normal] (hC : centralizer (K : Set X) ≤ K) (κ : K ≃* commutator Eam) {t : X}
    (ht : t ∉ K) :
    ∃ b : Eam, b ∉ commutator Eam ∧ ∀ k : K,
      ((κ (MulAut.conjNormal t k) : commutator Eam) : Eam) = b * (κ k : Eam) * b⁻¹ := by
  have hσ : MulAut.congr κ (MulAut.conjNormal t) ∉
      (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range :=
    fun h => ht (mem_of_conjNormal_mem_range hC ((congr_mem_range_conj_iff κ _).1 h))
  obtain ⟨b₀, hb₀, -⟩ := exists_mul_self_eq_one_not_mem_commutator
  have hCD : centralizer ((commutator Eam : Subgroup Eam) : Set Eam) ≤ commutator Eam := by
    rw [centralizer_commutator_Eam]
    exact zpowers_le.2 cE'_mem_commutator
  have hσ₀ : (MulAut.conjNormal b₀ : MulAut (commutator Eam)) ∉
      (MulAut.conj : commutator Eam →* MulAut (commutator Eam)).range :=
    fun h => hb₀ (mem_of_conjNormal_mem_range hCD h)
  have : Finite (MulAut (commutator Eam)) := inferInstance
  obtain ⟨e, he⟩ := mul_inv_mem_of_index_le_two hO hσ hσ₀
  refine ⟨e * b₀, fun h => hb₀ ?_, fun k => ?_⟩
  · have h' := mul_mem (inv_mem e.2) h
    rwa [inv_mul_cancel_left] at h'
  · have h1 : MulAut.congr κ (MulAut.conjNormal t) = MulAut.conj e * MulAut.conjNormal b₀ :=
      mul_inv_eq_iff_eq_mul.1 he.symm
    have h3 : MulAut.congr κ (MulAut.conjNormal t) (κ k) = κ (MulAut.conjNormal t k) := by
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    have h4 := congrArg (fun y : commutator Eam => (y : Eam))
      ((DFunLike.congr_fun h1 (κ k)).symm.trans h3)
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conjNormal_apply, coe_mul,
      coe_inv] at h4
    rw [← h4]
    group

theorem exists_outer_transport
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) {t : G} (htN : t ∈ normalizer (L : Set G)) (htL : t ∉ L) :
    ∃ b : Eam, b ∉ commutator Eam ∧ ∀ x y : L, (y : G) = t * x * t⁻¹ →
      ((ι y : commutator Eam) : Eam) = b * (ι x : Eam) * b⁻¹ := by
  have := normal_in_normalizer (H := L)
  obtain ⟨b, hb, hbk⟩ := exists_outer_of_not_mem hO (centralizer_subgroupOf_le hC) (iotaN ι)
    (t := ⟨t, htN⟩) (fun h => htL (mem_subgroupOf.1 h))
  refine ⟨b, hb, fun x y hxy => ?_⟩
  have h := hbk ⟨⟨x, le_normalizer x.2⟩, mem_subgroupOf.2 x.2⟩
  rwa [iotaN_eq ι (y := y) (by rw [MulAut.conjNormal_apply, hxy]; rfl),
    iotaN_eq ι (y := x) rfl] at h

theorem index_subgroupOf_le_two
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) : (L.subgroupOf (normalizer (L : Set G))).index ≤ 2 :=
  have := normal_in_normalizer (H := L)
  index_le_two_of_range_conj_index_le_two hO (iotaN ι) (centralizer_subgroupOf_le hC)

variable [Finite G]

theorem centralizer_dOf
    (hL : standardComponentIsStandard L) (ι : L ≃* commutator Eam) :
    centralizer {dOf ι} = normalizer (L : Set G) :=
  centralizer_eq_normalizer_of_standard hL (natCard_center_of_mulEquiv ι) (symm_cD_mem_center ι)
    (orderOf_dOf ι)

end Normalizer

section SquareTest

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mul_self_ne_dOf_of_outer
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) {y : G} (hyN : y ∈ normalizer (L : Set G)) (hyL : y ∉ L)
    (hy2 : y * y = 1) {t : G} (htN : t ∈ normalizer (L : Set G)) : t * t ≠ dOf ι := by
  have := normal_in_normalizer (H := L)
  have hle := index_subgroupOf_le_two hO hC ι
  have hyL' : (⟨y, hyN⟩ : normalizer (L : Set G)) ∉ L.subgroupOf (normalizer (L : Set G)) :=
    fun h => hyL (mem_subgroupOf.1 h)
  have hne1 : (L.subgroupOf (normalizer (L : Set G))).index ≠ 1 :=
    fun h => hyL' ((index_eq_one.1 h) ▸ mem_top _)
  have hne0 : (L.subgroupOf (normalizer (L : Set G))).index ≠ 0 := FiniteIndex.index_ne_zero
  obtain ⟨e, he⟩ := nonempty_mulEquiv_Eam_of_outer_involution hO
    (L.subgroupOf (normalizer (L : Set G))) (by omega) (iotaN ι) (centralizer_subgroupOf_le hC)
    hyL' (Subtype.ext hy2)
  intro htt
  have hdN : dOf ι ∈ normalizer (L : Set G) := le_normalizer (dOf_mem ι)
  have hd : e ⟨dOf ι, hdN⟩ = cE' := by
    have h := he ⟨⟨dOf ι, hdN⟩, mem_subgroupOf.2 (dOf_mem ι)⟩
    rw [iotaN_eq ι (y := ι.symm cD) rfl, MulEquiv.apply_symm_apply] at h
    exact h
  apply mul_self_ne_cE' (e ⟨t, htN⟩)
  rw [← map_mul, ← hd]
  exact congrArg e (Subtype.ext htt)

theorem not_isConj_of_mul_self_mem_closure
    (hO : CoverOuterLeTwo)
    (hC : centralizer (L : Set G) ≤ L) (ι : L ≃* commutator Eam)
    (hCN : centralizer {dOf ι} = normalizer (L : Set G)) {u s : G}
    (hs : s ∈ closure {i : G | i ∈ L ∧ i * i = 1 ∧ i * u = u * i}) (hsu : s * s = u) :
    ¬ IsConj (dOf ι) u := by
  intro hconj
  obtain ⟨h, hh⟩ := isConj_iff.1 hconj
  have hsC : s ∈ centralizer {u} := (closure_le _).2
    (fun i hi => mem_centralizer_singleton_iff.2 hi.2.2) hs
  set θ : G →* G := (MulAut.conj h⁻¹).toMonoidHom with hθ
  have hθapp : ∀ x, θ x = h⁻¹ * x * h := fun x => by
    rw [hθ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  have hθu : θ u = dOf ι := by rw [hθapp, ← hh]; group
  have hθC : ∀ x ∈ centralizer {u}, θ x ∈ normalizer (L : Set G) := by
    intro x hx
    rw [← hCN, mem_centralizer_singleton_iff, ← hθu, ← map_mul, ← map_mul,
      mem_centralizer_singleton_iff.1 hx]
  have hts : θ s * θ s = dOf ι := by rw [← map_mul, hsu, hθu]
  by_cases hout : ∃ y ∈ normalizer (L : Set G), y ∉ L ∧ y * y = 1
  · obtain ⟨y, hyN, hyL, hy2⟩ := hout
    exact mul_self_ne_dOf_of_outer hO hC ι hyN hyL hy2 (hθC s hsC) hts
  · push Not at hout
    have hle : (closure {i : G | i ∈ L ∧ i * i = 1 ∧ i * u = u * i}).map θ ≤ L := by
      rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨i, hi, rfl⟩
      by_contra hiL
      exact hout _ (hθC i (mem_centralizer_singleton_iff.2 hi.2.2)) hiL
        (by rw [← map_mul, hi.2.1, map_one])
    exact mul_self_ne_dOf ι (hle (mem_map_of_mem θ hs)) hts

theorem exists_isConj_mem_ne
    (hO : CoverOuterLeTwo) (hset : StandardSetting G L)
    (hC : centralizer (L : Set G) ≤ L) (ι : L ≃* commutator Eam) :
    ∃ u ∈ L, u ≠ dOf ι ∧ IsConj (dOf ι) u := by
  have := hset.simple
  have hCN := centralizer_dOf hset.standard ι
  by_contra hno
  push Not at hno
  refine false_of_fours_group hset.nonab (orderOf_dOf ι) (dOf_mem ι) ?_ ?_ ?_
  · rw [hCN]
    exact index_subgroupOf_le_two hO hC ι
  · intro y hy hc
    by_contra hne
    exact hno y hy hne hc
  · intro y hyC hyL hyc
    rw [hCN] at hyC
    have hy2 : y * y = 1 := mul_self_of_isConj (dOf_mul_self ι) hyc
    have := normal_in_normalizer (H := L)
    have hle := index_subgroupOf_le_two hO hC ι
    have hyL' : (⟨y, hyC⟩ : normalizer (L : Set G)) ∉ L.subgroupOf (normalizer (L : Set G)) :=
      fun h => hyL (mem_subgroupOf.1 h)
    have hne1 : (L.subgroupOf (normalizer (L : Set G))).index ≠ 1 :=
      fun h => hyL' ((index_eq_one.1 h) ▸ mem_top _)
    have hne0 : (L.subgroupOf (normalizer (L : Set G))).index ≠ 0 := FiniteIndex.index_ne_zero
    obtain ⟨e, he⟩ := nonempty_mulEquiv_Eam_of_outer_involution hO
      (L.subgroupOf (normalizer (L : Set G))) (by omega) (iotaN ι) (centralizer_subgroupOf_le hC)
      hyL' (Subtype.ext hy2)
    have hey : e ⟨y, hyC⟩ ∉ commutator Eam := by
      intro h
      apply hyL'
      have h1 := he ((iotaN ι).symm ⟨e ⟨y, hyC⟩, h⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      rw [← e.injective h1]
      exact ((iotaN ι).symm _).2
    have hey2 : e ⟨y, hyC⟩ * e ⟨y, hyC⟩ = 1 := by
      rw [← map_mul, show (⟨y, hyC⟩ : normalizer (L : Set G)) * ⟨y, hyC⟩ = 1 from
        Subtype.ext hy2, map_one]
    obtain ⟨V, -, hV4, hVc, hVconj⟩ := exists_fours_group_of_outer_involution hey hey2
    obtain ⟨W, -, hW4, hWc, hWconj⟩ := exists_four_map
      ((normalizer (L : Set G)).subtype.comp e.symm.toMonoidHom)
      ((normalizer (L : Set G)).subtype_injective.comp e.symm.injective) (N := ⊤) (M := ⊤)
      le_top ⟨V, le_top, hV4, hVc, hVconj⟩
    have hφ : ((normalizer (L : Set G)).subtype.comp e.symm.toMonoidHom) (e ⟨y, hyC⟩) = y := by
      simp
    rw [hφ] at hWc hWconj
    exact ⟨W, hW4, hWc, hWconj⟩

set_option maxHeartbeats 8000000 in
theorem isConj_dOf_mul_zOf
    (hO : CoverOuterLeTwo) (hset : StandardSetting G L)
    (hC : centralizer (L : Set G) ≤ L) (ι : L ≃* commutator Eam) (hT : InvolutionSquareTest) :
    IsConj (dOf ι) (dOf ι * zOf ι) := by
  obtain ⟨u, huL, hud, hdu⟩ := exists_isConj_mem_ne hO hset hC ι
  have hCN := centralizer_dOf hset.standard ι
  have hu2 : u * u = 1 := mul_self_of_isConj (dOf_mul_self ι) hdu
  have hu'2 : ι ⟨u, huL⟩ * ι ⟨u, huL⟩ = 1 := by
    rw [← map_mul, show (⟨u, huL⟩ : L) * ⟨u, huL⟩ = 1 from Subtype.ext hu2, map_one]
  have hu'c : ι ⟨u, huL⟩ ≠ cD := fun h => hud (by rw [← phiOf_iota ι huL, h, phiOf_cD])
  rcases hT _ hu'2 hu'c with h | ⟨s, hs, hs2⟩
  · have h' := (phiOf ι).map_isConj h
    rw [map_mul, phiOf_cD, phiOf_xD, phiOf_iota] at h'
    exact hdu.trans h'.symm
  · refine absurd hdu (not_isConj_of_mul_self_mem_closure hO hC ι hCN (s := phiOf ι s) ?_ ?_)
    · have h1 := phiOf_mem_closure ι hs
      rwa [phiOf_iota] at h1
    · exact (map_mul (phiOf ι) s s).symm.trans ((congrArg (phiOf ι) hs2).trans (phiOf_iota ι huL))

theorem not_isConj_dOf_zOf
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) (hCN : centralizer {dOf ι} = normalizer (L : Set G))
    (hT : InvolutionSquareTest) (hxx : ¬ IsConj xhatEam (cE' * xhatEam)) :
    ¬ IsConj (dOf ι) (zOf ι) := by
  rcases hT xD xD_mul_self xD_ne_cD with h | ⟨s, hs, hs2⟩
  · have h' : IsConj ((cD * xD : commutator Eam) : Eam) (xD : Eam) :=
      (commutator Eam).subtype.map_isConj h
    rw [coe_mul, coe_cD, coe_xD] at h'
    exact absurd h'.symm hxx
  · refine not_isConj_of_mul_self_mem_closure hO hC ι hCN (s := phiOf ι s) ?_ ?_
    · exact phiOf_mem_closure ι hs
    · exact (map_mul (phiOf ι) s s).symm.trans (congrArg (phiOf ι) hs2)

end SquareTest

section Burnside

variable {G : Type*} [Group G]

theorem natCard_centralizer_conj' (k d : G) :
    Nat.card (centralizer {k * d * k⁻¹}) = Nat.card (centralizer {d}) := by
  have e : centralizer {k * d * k⁻¹} = (centralizer {d}).map (MulAut.conj k).toMonoidHom := by
    ext x
    simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · intro hx
      refine ⟨k⁻¹ * x * k, ?_, by group⟩
      calc k⁻¹ * x * k * d = k⁻¹ * (x * (k * d * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * d * k⁻¹) * x) * k := by rw [hx]
        _ = d * (k⁻¹ * x * k) := by group
    · rintro ⟨y, hy, rfl⟩
      calc k * y * k⁻¹ * (k * d * k⁻¹) = k * (y * d) * k⁻¹ := by group
        _ = k * (d * y) * k⁻¹ := by rw [hy]
        _ = k * d * k⁻¹ * (k * y * k⁻¹) := by group
  rw [e, card_map_of_injective (MulAut.conj k).injective]

theorem relIndex_mul_card_of_le {T K : Subgroup G} (h : T ≤ K) :
    T.relIndex K * Nat.card T = Nat.card K := by
  have e := relIndex_mul_card T K
  rwa [inf_eq_left.2 h] at e

theorem isPGroup_zpowers_of_pow_two_pow {g : G} {a : ℕ} (h : g ^ 2 ^ a = 1) :
    IsPGroup 2 (zpowers g) := by
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hi])

variable [Finite G]

theorem exists_two_element_swap {d z : G} {T : Subgroup G} (hT2 : IsPGroup 2 T)
    (hTd : T ≤ centralizer {d}) (hTodd : ¬ 2 ∣ T.relIndex (centralizer {d}))
    (hzT : z ∈ T) (hTz : ∀ t ∈ T, t * z = z * t)
    (hZ : ∀ w ∈ T, (∀ t ∈ T, w * t = t * w) → w = 1 ∨ w = d ∨ w = z ∨ w = d * z)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hzd : z ≠ d)
    (hdz : IsConj d (d * z)) (hndz : ¬ IsConj d z) :
    ∃ g : G, IsPGroup 2 (zpowers g) ∧ g * d * g⁻¹ = d * z ∧ g * z * g⁻¹ = z := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := isConj_iff.1 hdz
  have hzd' : z * d = d * z := mem_centralizer_singleton_iff.1 (hTd hzT)
  set C := centralizer {d * z} with hCdef
  have hTC : T ≤ C := fun t ht => by
    rw [hCdef, mem_centralizer_singleton_iff]
    have h1 : t * d = d * t := mem_centralizer_singleton_iff.1 (hTd ht)
    have h2 := hTz t ht
    calc t * (d * z) = d * (t * z) := by rw [← mul_assoc, h1, mul_assoc]
      _ = d * z * t := by rw [h2, mul_assoc]
  have hcardC : Nat.card C = Nat.card (centralizer {d}) := by
    rw [hCdef, ← hk]
    exact natCard_centralizer_conj' k d
  have hTCodd : ¬ 2 ∣ (T.subgroupOf C).index := by
    have e1 := relIndex_mul_card_of_le hTd
    have e2 := relIndex_mul_card_of_le hTC
    have hpos : 0 < Nat.card T := Nat.card_pos
    have e3 : T.relIndex C = T.relIndex (centralizer {d}) := by
      rw [← hcardC] at e1
      exact Nat.eq_of_mul_eq_mul_right hpos (e2.trans e1.symm)
    rw [← relIndex, e3]
    exact hTodd
  set T' := T.map (MulAut.conj k).toMonoidHom with hT'def
  have hT'C : T' ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    rw [hCdef, mem_centralizer_singleton_iff, ← hk]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : t * d = d * t := mem_centralizer_singleton_iff.1 (hTd ht)
    calc k * t * k⁻¹ * (k * d * k⁻¹) = k * (t * d) * k⁻¹ := by group
      _ = k * (d * t) * k⁻¹ := by rw [h1]
      _ = k * d * k⁻¹ * (k * t * k⁻¹) := by group
  have hT'2 : IsPGroup 2 (T'.subgroupOf C) :=
    (hT2.map _).comap_of_injective C.subtype C.subtype_injective
  obtain ⟨c, hc⟩ := exists_conj_mem_of_not_dvd_index (T.subgroupOf C) hTCodd hT'2
  set n := (c : G) * k with hndef
  have hnT : ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
    intro t ht
    have h1 : (⟨k * t * k⁻¹, hT'C ⟨t, ht, rfl⟩⟩ : C) ∈ T'.subgroupOf C :=
      mem_subgroupOf.2 ⟨t, ht, rfl⟩
    have h2 := mem_subgroupOf.1 (hc _ h1)
    rw [hndef]
    simpa [mul_assoc] using h2
  have hmap : T.map (MulAut.conj n).toMonoidHom = T := by
    refine eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨t, ht, rfl⟩
      exact hnT t ht
    · rw [card_map_of_injective (MulAut.conj n).injective]
  have hnT' : ∀ w ∈ T, n⁻¹ * w * n ∈ T := by
    intro w hw
    rw [← hmap] at hw
    obtain ⟨t, ht, rfl⟩ := hw
    simpa [MulAut.conj_apply, mul_assoc] using ht
  have hnd : n * d * n⁻¹ = d * z := by
    have h1 : (c : G) * (d * z) = d * z * c := mem_centralizer_singleton_iff.1 c.2
    calc n * d * n⁻¹ = (c : G) * (k * d * k⁻¹) * (c : G)⁻¹ := by rw [hndef]; group
      _ = d * z := by rw [hk, h1, mul_inv_cancel_right]
  have hnzT : n * z * n⁻¹ ∈ T := hnT z hzT
  have hnzc : ∀ t ∈ T, n * z * n⁻¹ * t = t * (n * z * n⁻¹) := by
    intro t ht
    have h1 := hTz _ (hnT' t ht)
    calc n * z * n⁻¹ * t = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by rw [h1]
      _ = t * (n * z * n⁻¹) := by group
  have hnz : n * z * n⁻¹ = z := by
    rcases hZ _ hnzT hnzc with h | h | h | h
    · exact absurd (by simpa using h) hz1
    · exact absurd (isConj_iff.2 ⟨n⁻¹, by rw [← h]; group⟩) hndz
    · exact h
    · exfalso
      apply hzd
      have h2 : n * z * n⁻¹ = n * d * n⁻¹ := h.trans hnd.symm
      simpa using h2
  have hn2d : n * n * d * (n * n)⁻¹ = d := by
    calc n * n * d * (n * n)⁻¹ = n * (n * d * n⁻¹) * n⁻¹ := by group
      _ = n * (d * z) * n⁻¹ := by rw [hnd]
      _ = (n * d * n⁻¹) * (n * z * n⁻¹) := by group
      _ = d := by rw [hnd, hnz, mul_assoc, hz2, mul_one]
  have hn2z : n * n * z * (n * n)⁻¹ = z := by
    calc n * n * z * (n * n)⁻¹ = n * (n * z * n⁻¹) * n⁻¹ := by group
      _ = z := by rw [hnz, hnz]
  have hn2 : n * n ∈ centralizer {d} ⊓ centralizer {z} := by
    refine ⟨mem_centralizer_singleton_iff.2 ?_, mem_centralizer_singleton_iff.2 ?_⟩
    · calc n * n * d = n * n * d * (n * n)⁻¹ * (n * n) := by group
        _ = d * (n * n) := by rw [hn2d]
    · calc n * n * z = n * n * z * (n * n)⁻¹ * (n * n) := by group
        _ = z * (n * n) := by rw [hn2z]
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos n).ne'
  obtain ⟨j, rfl⟩ := hm
  refine ⟨n ^ (2 * j + 1), isPGroup_zpowers_of_pow_two_pow (a := a) ?_, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, ← ham, pow_orderOf_eq_one]
  · have hj : (n * n) ^ j ∈ centralizer {d} ⊓ centralizer {z} := pow_mem hn2 j
    have hjd : (n * n) ^ j * d = d * (n * n) ^ j := mem_centralizer_singleton_iff.1 hj.1
    have hjz : (n * n) ^ j * z = z * (n * n) ^ j := mem_centralizer_singleton_iff.1 hj.2
    have e : n ^ (2 * j + 1) = (n * n) ^ j * n := by rw [pow_succ, pow_mul, sq]
    rw [e]
    calc (n * n) ^ j * n * d * ((n * n) ^ j * n)⁻¹ =
        (n * n) ^ j * (n * d * n⁻¹) * ((n * n) ^ j)⁻¹ := by group
      _ = (n * n) ^ j * d * ((n * n) ^ j)⁻¹ * ((n * n) ^ j * z * ((n * n) ^ j)⁻¹) := by
        rw [hnd]; group
      _ = d * z := by rw [hjd, hjz, mul_inv_cancel_right, mul_inv_cancel_right]
  · have hj : (n * n) ^ j ∈ centralizer {d} ⊓ centralizer {z} := pow_mem hn2 j
    have hjz : (n * n) ^ j * z = z * (n * n) ^ j := mem_centralizer_singleton_iff.1 hj.2
    have e : n ^ (2 * j + 1) = (n * n) ^ j * n := by rw [pow_succ, pow_mul, sq]
    rw [e]
    calc (n * n) ^ j * n * z * ((n * n) ^ j * n)⁻¹ =
        (n * n) ^ j * (n * z * n⁻¹) * ((n * n) ^ j)⁻¹ := by group
      _ = z := by rw [hnz, hjz, mul_inv_cancel_right]

end Burnside

section Sylow

variable {G : Type} [Group G] {L : Subgroup G}

theorem phiOf_eq_four_of
    (ι : L ≃* commutator Eam) {w : commutator Eam}
    (h : (w : Eam) = 1 ∨ (w : Eam) = cE' ∨ (w : Eam) = xhatEam ∨ (w : Eam) = cE' * xhatEam) :
    phiOf ι w = 1 ∨ phiOf ι w = dOf ι ∨ phiOf ι w = zOf ι ∨ phiOf ι w = dOf ι * zOf ι := by
  rcases h with h | h | h | h
  · left
    rw [show w = 1 from Subtype.ext h, map_one]
  · right; left
    rw [show w = cD from Subtype.ext h, phiOf_cD]
  · right; right; left
    rw [show w = xD from Subtype.ext h, phiOf_xD]
  · right; right; right
    rw [show w = cD * xD from Subtype.ext h, phiOf_mul, phiOf_cD, phiOf_xD]

theorem iota_dOf_mul_zOf
    (ι : L ≃* commutator Eam) (h : dOf ι * zOf ι ∈ L) :
    ι ⟨dOf ι * zOf ι, h⟩ = cD * xD :=
  phiOf_injective ι ((phiOf_iota ι h).trans (phiOf_mul ι cD xD).symm)

theorem iota_zOf
    (ι : L ≃* commutator Eam) : ι ⟨zOf ι, zOf_mem ι⟩ = xD :=
  phiOf_injective ι (phiOf_iota ι (zOf_mem ι))

theorem isConj_xD_of_mem
    (ι : L ≃* commutator Eam) {t : G} (htL : t ∈ L)
    (h : t * zOf ι * t⁻¹ = dOf ι * zOf ι) :
    IsConj ((xD : commutator Eam) : Eam) ((cD * xD : commutator Eam) : Eam) := by
  have hdzL : dOf ι * zOf ι ∈ L := mul_mem (dOf_mem ι) (zOf_mem ι)
  have h1 : (⟨t, htL⟩ : L) * ⟨zOf ι, zOf_mem ι⟩ * (⟨t, htL⟩ : L)⁻¹ =
      ⟨dOf ι * zOf ι, hdzL⟩ := Subtype.ext h
  have h2 : IsConj (ι ⟨zOf ι, zOf_mem ι⟩) (ι ⟨dOf ι * zOf ι, hdzL⟩) :=
    ι.toMonoidHom.map_isConj (isConj_iff.2 ⟨_, h1⟩)
  rw [iota_zOf, iota_dOf_mul_zOf] at h2
  exact (commutator Eam).subtype.map_isConj h2

theorem isConj_xD_of_not_mem
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) {t : G} (htN : t ∈ normalizer (L : Set G)) (htL : t ∉ L)
    (h : t * zOf ι * t⁻¹ = dOf ι * zOf ι) :
    IsConj ((xD : commutator Eam) : Eam) ((cD * xD : commutator Eam) : Eam) := by
  have hdzL : dOf ι * zOf ι ∈ L := mul_mem (dOf_mem ι) (zOf_mem ι)
  obtain ⟨b, -, hbk⟩ := exists_outer_transport hO hC ι htN htL
  have h1 := hbk ⟨zOf ι, zOf_mem ι⟩ ⟨dOf ι * zOf ι, hdzL⟩ h.symm
  rw [iota_dOf_mul_zOf, iota_zOf] at h1
  exact isConj_iff.2 ⟨b, h1.symm⟩

theorem not_forall_comm_of_not_mem
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) {w : G} (hwN : w ∈ normalizer (L : Set G)) (hwL : w ∉ L)
    {T₁s : Subgroup (commutator Eam)}
    (hcent : ∀ b : Eam, (∀ t ∈ T₁s, b * (t : Eam) = (t : Eam) * b) → b ∈ commutator Eam)
    (hwc : ∀ t ∈ T₁s, w * phiOf ι t = phiOf ι t * w) : False := by
  obtain ⟨b, hb, hbk⟩ := exists_outer_transport hO hC ι hwN hwL
  refine hb (hcent b fun t ht => ?_)
  have h2 : ((ι.symm t : L) : G) = w * (ι.symm t : L) * w⁻¹ := by
    rw [← phiOf_apply, hwc t ht, mul_inv_cancel_right]
  have h3 := hbk (ι.symm t) (ι.symm t) h2
  rw [MulEquiv.apply_symm_apply] at h3
  calc b * (t : Eam) = b * (t : Eam) * b⁻¹ * b := by group
    _ = (t : Eam) * b := by rw [← h3]

variable [Finite G]

theorem exists_sylow_inf_eq
    (ι : L ≃* commutator Eam) (T₁s : Sylow 2 (commutator Eam)) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≤ normalizer (L : Set G) ∧
      ¬ 2 ∣ T.relIndex (normalizer (L : Set G)) ∧
      T ⊓ L = (T₁s : Subgroup (commutator Eam)).map (phiOf ι) := by
  have hp : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁2 : IsPGroup 2 ((T₁s : Subgroup (commutator Eam)).map (phiOf ι)) :=
    T₁s.isPGroup'.map _
  have hT₁L : (T₁s : Subgroup (commutator Eam)).map (phiOf ι) ≤ L := by
    rintro _ ⟨t, -, rfl⟩
    exact phiOf_mem ι t
  have hT₁N := hT₁L.trans (le_normalizer (H := L))
  obtain ⟨P, hP⟩ := (hT₁2.comap_of_injective (normalizer (L : Set G)).subtype
    (normalizer (L : Set G)).subtype_injective).exists_le_sylow
  refine ⟨(P : Subgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype,
    P.isPGroup'.map _, map_subtype_le _, ?_, ?_⟩
  · have e : ((P : Subgroup (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype).subgroupOf (normalizer (L : Set G)) =
        (P : Subgroup (normalizer (L : Set G))) :=
      comap_map_eq_self_of_injective (normalizer (L : Set G)).subtype_injective _
    rw [relIndex, e]
    exact P.not_dvd_index
  · have hT₁T : (T₁s : Subgroup (commutator Eam)).map (phiOf ι) ≤
        (P : Subgroup (normalizer (L : Set G))).map (normalizer (L : Set G)).subtype :=
      fun x hx => ⟨⟨x, hT₁N hx⟩, hP hx, rfl⟩
    have hcardT₁ : Nat.card ((T₁s : Subgroup (commutator Eam)).map (phiOf ι)) =
        2 ^ (Nat.card L).factorization 2 := by
      rw [card_map_of_injective (phiOf_injective ι), T₁s.card_eq_multiplicity,
        Nat.card_congr ι.toEquiv]
    symm
    refine eq_of_le_of_card_ge (le_inf hT₁T hT₁L) ?_
    have h2 : IsPGroup 2 ((((P : Subgroup (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype) ⊓ L).subgroupOf L) :=
      ((P.isPGroup'.map _).to_le inf_le_left).comap_of_injective L.subtype L.subtype_injective
    obtain ⟨S, hS⟩ := h2.exists_le_sylow
    calc Nat.card (((P : Subgroup (normalizer (L : Set G))).map
          (normalizer (L : Set G)).subtype ⊓ L : Subgroup G)) =
          Nat.card ((((P : Subgroup (normalizer (L : Set G))).map
            (normalizer (L : Set G)).subtype) ⊓ L).subgroupOf L) :=
          (Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv).symm
      _ ≤ Nat.card S := card_le_of_le hS
      _ = _ := by rw [S.card_eq_multiplicity, hcardT₁]

theorem exists_sylow_centralizer_dOf
    (hO : CoverOuterLeTwo) (hC : centralizer (L : Set G) ≤ L)
    (ι : L ≃* commutator Eam) (hCN : centralizer {dOf ι} = normalizer (L : Set G))
    (hS : RootSylowData) :
    ∃ T : Subgroup G, IsPGroup 2 T ∧ T ≤ centralizer {dOf ι} ∧
      ¬ 2 ∣ T.relIndex (centralizer {dOf ι}) ∧ zOf ι ∈ T ∧ (∀ t ∈ T, t * zOf ι = zOf ι * t) ∧
      ∀ w ∈ T, (∀ t ∈ T, w * t = t * w) →
        w = 1 ∨ w = dOf ι ∨ w = zOf ι ∨ w = dOf ι * zOf ι := by
  obtain ⟨hxx₀, T₁s, hxT, hcent⟩ := hS
  have hxx : ¬ IsConj ((xD : commutator Eam) : Eam) ((cD * xD : commutator Eam) : Eam) := by
    intro h
    rw [coe_mul, coe_cD, coe_xD] at h
    exact hxx₀ h
  have hcentE : ∀ b : Eam, (∀ t ∈ (T₁s : Subgroup (commutator Eam)),
      b * (t : Eam) = (t : Eam) * b) → b ∈ commutator Eam := by
    intro b hb
    rcases (hcent b).1 hb with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact cE'_mem_commutator
    · exact xhatEam_mem_commutator
    · exact mul_mem cE'_mem_commutator xhatEam_mem_commutator
  obtain ⟨T, hT2, hTN, hTodd, hTL⟩ := exists_sylow_inf_eq ι T₁s
  rw [hCN]
  have hT₁T : (T₁s : Subgroup (commutator Eam)).map (phiOf ι) ≤ T := by
    rw [← hTL]
    exact inf_le_left
  have hconjT₁ : ∀ t ∈ T, ∀ x ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι),
      t * x * t⁻¹ ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι) := by
    intro t ht x hx
    rw [← hTL] at hx ⊢
    obtain ⟨hxT, hxL⟩ := mem_inf.1 hx
    exact mem_inf.2 ⟨mul_mem (mul_mem ht hxT) (inv_mem ht),
      (mem_normalizer_iff.1 (hTN ht) x).1 hxL⟩
  have hcentT₁ : ∀ w ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι),
      (∀ x ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι), w * x = x * w) →
      w = 1 ∨ w = dOf ι ∨ w = zOf ι ∨ w = dOf ι * zOf ι := by
    rintro _ ⟨w', -, rfl⟩ hw
    refine phiOf_eq_four_of ι ((hcent w').1 fun t ht => ?_)
    have h1 : phiOf ι (w' * t) = phiOf ι (t * w') :=
      (phiOf_mul ι w' t).trans ((hw _ ⟨t, ht, rfl⟩).trans (phiOf_mul ι t w').symm)
    exact congrArg Subtype.val (phiOf_injective ι h1)
  have hzT₁ : zOf ι ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι) := ⟨xD, hxT, rfl⟩
  have hzc : ∀ x ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι),
      zOf ι * x = x * zOf ι := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := (hcent xhatEam).2 (Or.inr (Or.inr (Or.inl rfl))) t ht
    have h2 : xD * t = t * xD := Subtype.ext h1
    exact (phiOf_mul ι xD t).symm.trans ((congrArg (phiOf ι) h2).trans (phiOf_mul ι t xD))
  refine ⟨T, hT2, hTN, hTodd, hT₁T hzT₁, fun t ht => ?_, fun w hw hwc => ?_⟩
  ·
    have hwT₁ := hconjT₁ t ht _ hzT₁
    have hwc : ∀ x ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι),
        t * zOf ι * t⁻¹ * x = x * (t * zOf ι * t⁻¹) := by
      intro x hx
      have hx' : t⁻¹ * x * t ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι) := by
        simpa using hconjT₁ t⁻¹ (inv_mem ht) x hx
      have h1 := hzc _ hx'
      calc t * zOf ι * t⁻¹ * x = t * (zOf ι * (t⁻¹ * x * t)) * t⁻¹ := by group
        _ = t * ((t⁻¹ * x * t) * zOf ι) * t⁻¹ := by rw [h1]
        _ = x * (t * zOf ι * t⁻¹) := by group
    have htd : t * dOf ι = dOf ι * t := by
      have h1 := hTN ht
      rw [← hCN] at h1
      exact mem_centralizer_singleton_iff.1 h1
    rcases hcentT₁ _ hwT₁ hwc with h | h | h | h
    · exact absurd (by simpa using h) (zOf_ne_one ι)
    · exfalso
      apply zOf_ne_dOf ι
      calc zOf ι = t⁻¹ * (t * zOf ι * t⁻¹) * t := by group
        _ = t⁻¹ * (dOf ι * t) := by rw [h, mul_assoc]
        _ = dOf ι := by rw [← htd, inv_mul_cancel_left]
    · calc t * zOf ι = t * zOf ι * t⁻¹ * t := by group
        _ = zOf ι * t := by rw [h]
    · exfalso
      by_cases htL : t ∈ L
      · exact hxx (isConj_xD_of_mem ι htL h)
      · exact hxx (isConj_xD_of_not_mem hO hC ι (hTN ht) htL h)
  ·
    by_cases hwL : w ∈ L
    · have hwT₁ : w ∈ (T₁s : Subgroup (commutator Eam)).map (phiOf ι) := by
        rw [← hTL]
        exact ⟨hw, hwL⟩
      exact hcentT₁ w hwT₁ fun x hx => hwc x (hT₁T hx)
    · exact (not_forall_comm_of_not_mem hO hC ι (hTN hw) hwL hcentE
        fun t ht => hwc _ (hT₁T ⟨t, ht, rfl⟩)).elim

end Sylow

theorem stroth22_of_inputs
    (hO : CoverOuterLeTwo) (hT : InvolutionSquareTest)
    (hS : RootSylowData) : Stroth22 := by
  intro G _ _ L hset hZ ι
  have hC := centralizer_le_of_eq hZ
  have hCN := centralizer_dOf hset.standard ι
  have hndz := not_isConj_dOf_zOf hO hC ι hCN hT hS.1
  refine ⟨hndz, ?_⟩
  obtain ⟨T, hT2, hTd, hTodd, hzT, hTz, hZT⟩ := exists_sylow_centralizer_dOf hO hC ι hCN hS
  exact exists_two_element_swap hT2 hTd hTodd hzT hTz hZT (zOf_mul_self ι) (zOf_ne_one ι)
    (zOf_ne_dOf ι) (isConj_dOf_mul_zOf hO hset hC ι hT) hndz

end CFSG.EvenSmallLie.TwoE6
