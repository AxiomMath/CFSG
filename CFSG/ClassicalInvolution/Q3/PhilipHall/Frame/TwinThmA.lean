module

public import CFSG.ClassicalInvolution.Q3.TL3DichThmA
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Q8Twin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen
open CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem Q8Datum.t_mul_t (hd : Q8TwinDatum R S t) : t * t = 1 := by
  rw [← pow_two, ← hd.order, pow_orderOf_eq_one]

omit [Finite Y] in
theorem Q8Datum.t_inv (hd : Q8TwinDatum R S t) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_right (Q8Datum.t_mul_t hd)

theorem Q8Datum.eq_of_orderOf_eq_two (hd : Q8TwinDatum R S t) {u : Y} (hu : u ∈ R)
    (hu2 : orderOf u = 2) : u = t := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hd.quat
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ (by norm_num)⟩
  exact Nobq.eq_of_orderOf_eq_two_of_datum S e hd.mem hd.order hd.cent hu hu2

theorem Q8Datum.isUniqueInvolution_core (hd : Q8TwinDatum R S t) :
    IsUniqueInvolution (tightCore R) t := by
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order]; norm_num)
  refine ⟨Subgroup.subset_closure ⟨Subgroup.map_subtype_le _ hd.mem, ht2⟩, ?_, ?_, ?_⟩
  · intro h1
    have := hd.order
    rw [h1, orderOf_one] at this
    norm_num at this
  · rw [← pow_two]
    exact hd.order ▸ pow_orderOf_eq_one t
  · intro y hy hyy
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · right
      have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hyy) hy1
      exact Q8Datum.eq_of_orderOf_eq_two hd (tightCore_le R hy) hord

theorem Q8Datum.isSolvable (hd : Q8TwinDatum R S t) : Group.IsSolvable R := by
  have hO : Group.IsSolvable (classicalInvolutionOddCore R) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (CFSG.ComponentClassification.OddCore.odd_card R)
  have hq : Group.IsSolvable (R ⧸ classicalInvolutionOddCore R) :=
    have := hd.twoGroup.isNilpotent
    inferInstance
  exact Group.isSolvable_of_subgroup_quotient (classicalInvolutionOddCore R)

theorem Q8Datum.mem_of_ne_bot (hd : Q8TwinDatum R S t) {P : Subgroup Y} (hPR : P ≤ R)
    (hP2 : IsPGroup 2 ↥P) (hP : P ≠ ⊥) : t ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  obtain ⟨k, hk⟩ := hP2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact (Finite.one_lt_card_iff_nontrivial.mpr hnt).ne' hk
  have h2 : 2 ∣ Nat.card ↥P := by
    rw [hk]
    exact dvd_pow_self 2 hk0
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 2 h2
  have hu' : orderOf (u : Y) = 2 := by rwa [Subgroup.orderOf_coe]
  have := Q8Datum.eq_of_orderOf_eq_two hd (hPR u.2) hu'
  rw [← this]
  exact u.2

omit [Finite Y] in
theorem Q8Datum.S₀_le (_hd : Q8TwinDatum R S t) : (S : Subgroup R).map R.subtype ≤ R :=
  Subgroup.map_subtype_le _

theorem Q8Datum.q8_center (hd : Q8TwinDatum R S t)
    (e : ↥(S : Subgroup R) ≃* QuaternionGroup 2) :
    (((e.symm (QuaternionGroup.a 2) : ↥(S : Subgroup R)) : ↥R) : Y) = t := by
  set u : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a 2) with hu
  have hu2 : u * u = 1 := by
    rw [hu, ← map_mul, q8_central_sq, map_one]
  have hu1 : u ≠ 1 := by
    rw [hu]
    intro h
    exact q8_a2_ne (by simpa using congrArg e h)
  have hord : orderOf (((u : ↥R) : Y)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) hu2
      simpa using this
    · intro h
      apply hu1
      exact Subtype.ext (Subtype.ext h)
  exact Q8Datum.eq_of_orderOf_eq_two hd (u : ↥R).2 hord

theorem Q8Datum.S₀_cases (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {s : Y}
    (hs : s ∈ (S : Subgroup R).map R.subtype) : s = 1 ∨ s = t ∨ s * s = t := by
  obtain ⟨e⟩ := hq8
  obtain ⟨x, hx, rfl⟩ := hs
  have hct := Q8Datum.q8_center hd e
  rcases q8_cases (e ⟨x, hx⟩) with h | h | h
  · left
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) = 1 := e.injective (by rw [h, map_one])
    have := congrArg (fun v : ↥(S : Subgroup R) => ((v : ↥R) : Y)) this
    simpa using this
  · right; left
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) = e.symm (QuaternionGroup.a 2) := by
      rw [← h, MulEquiv.symm_apply_apply]
    rw [← hct, ← this]
    rfl
  · right; right
    have : (⟨x, hx⟩ : ↥(S : Subgroup R)) * ⟨x, hx⟩ = e.symm (QuaternionGroup.a 2) := by
      rw [← h, ← map_mul, MulEquiv.symm_apply_apply]
    rw [← hct, ← this]
    rfl

theorem Q8Datum.exists_S₀_pair (hd : Q8TwinDatum R S t)
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) :
    ∃ r₁ ∈ (S : Subgroup R).map R.subtype, ∃ r₂ ∈ (S : Subgroup R).map R.subtype,
      r₁ * r₁ = t ∧ r₂ * r₂ = t ∧ (r₁ * r₂) * (r₁ * r₂) = t := by
  obtain ⟨e⟩ := hq8
  have hct := Q8Datum.q8_center hd e
  obtain ⟨h1, h2, h3⟩ := q8_pair
  set u₁ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.a 1)
  set u₂ : ↥(S : Subgroup R) := e.symm (QuaternionGroup.xa 0)
  refine ⟨((u₁ : ↥R) : Y), ⟨u₁, u₁.2, rfl⟩, ((u₂ : ↥R) : Y), ⟨u₂, u₂.2, rfl⟩, ?_, ?_, ?_⟩
  · have : u₁ * u₁ = e.symm (QuaternionGroup.a 2) := by rw [← h1, map_mul]
    rw [← hct, ← this]
    rfl
  · have : u₂ * u₂ = e.symm (QuaternionGroup.a 2) := by rw [← h2, map_mul]
    rw [← hct, ← this]
    rfl
  · have : (u₁ * u₂) * (u₁ * u₂) = e.symm (QuaternionGroup.a 2) := by
      rw [← h3, map_mul, map_mul]
    rw [← hct, ← this]
    rfl

@[expose] noncomputable def twinGroup (R : Subgroup Y) : Subgroup Y :=
  ⨆ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), J

theorem tightCore_le_twinGroup (hd : Q8TwinDatum R S t) : tightCore R ≤ twinGroup R :=
  le_iSup₂_of_le (tightCore R)
    ⟨CoreAssembly.mem_conjClass_self _, t, Q8Datum.isUniqueInvolution_core hd,
      Q8Datum.isUniqueInvolution_core hd⟩ le_rfl

theorem conj_mem_twinGroup (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {d : Y}
    (hdC : d ∈ Subgroup.centralizer ({t} : Set Y)) {x : Y} (hx : x ∈ twinGroup R) :
    d * x * d⁻¹ ∈ twinGroup R := by
  have huniq := Q8Datum.isUniqueInvolution_core hd
  have hdz : d * t * d⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hdC
    rw [hdC, mul_inv_cancel_right]
  have hmapd : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      conjSub d J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) := by
    rintro J ⟨hJΩ, z, hzK, hzJ⟩
    have hz : z = t := hzK.eq huniq
    rw [hz] at hzJ
    refine ⟨hΩ.conjInvariant d J hJΩ, t, huniq, ?_⟩
    have := hzJ.conj d
    rwa [hdz] at this
  have hsub : (twinGroup R).map (MulAut.conj d).toMonoidHom ≤ twinGroup R := by
    unfold twinGroup
    rw [Subgroup.map_iSup]
    refine iSup_le fun J => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hJ => le_iSup₂_of_le (conjSub d J) (hmapd J hJ) le_rfl
  exact hsub ⟨x, hx, rfl⟩

theorem comm_mem_twinGroup (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {g r : Y} (hg : g * t = t * g)
    (hr : r ∈ tightCore R) : g * r * g⁻¹ * r⁻¹ ∈ twinGroup R := by
  have hgC : g ∈ Subgroup.centralizer ({t} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hg
  have h1 : g * r * g⁻¹ ∈ twinGroup R :=
    conj_mem_twinGroup hd hΩ hgC (tightCore_le_twinGroup hd hr)
  exact (twinGroup R).mul_mem h1 ((twinGroup R).inv_mem (tightCore_le_twinGroup hd hr))

omit [Finite Y] in
theorem isSolvable_conjSub_of {K : Subgroup Y} (hK : Group.IsSolvable ↥K) (g : Y) :
    Group.IsSolvable ↥(conjSub g K) := by
  let e : ↥K ≃* ↥(K.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective

theorem isSolvable_sup_of_le_normalizer_twin {G : Type*} [Group G] {N T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (N : Set G)) (hN : Group.IsSolvable N)
    (hT : Group.IsSolvable T) : Group.IsSolvable (N ⊔ T : Subgroup G) := by
  set V := N ⊔ T
  have hNV : N ≤ V := le_sup_left
  have hTV : T ≤ V := le_sup_right
  have hVN : V ≤ Subgroup.normalizer (N : Set G) := sup_le Subgroup.le_normalizer hTN
  have : (N.subgroupOf V).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNV).mpr hVN
  set π := QuotientGroup.mk' (N.subgroupOf V)
  set f : T →* V ⧸ N.subgroupOf V := π.comp (Subgroup.inclusion hTV)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hv : (v : G) ∈ ((T ⊔ N : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact v.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right T N hTN] at hv
    obtain ⟨t, ht, n, hn, htn⟩ := hv
    refine ⟨⟨t, ht⟩, ?_⟩
    change π (Subgroup.inclusion hTV ⟨t, ht⟩) = π v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h : ((Subgroup.inclusion hTV ⟨t, ht⟩)⁻¹ * v : V) = (t⁻¹ * v : G) := rfl
    rw [h, ← htn, inv_mul_cancel_left]
    exact hn
  have hNVsol : Group.IsSolvable (N.subgroupOf V) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNV).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hNV).injective
  have hQsol : Group.IsSolvable (V ⧸ N.subgroupOf V) := Group.isSolvable_of_surjective hf
  refine Group.isSolvable_of_ker_le_range (N.subgroupOf V).subtype π ?_
  rw [QuotientGroup.ker_mk', Subgroup.range_subtype]

theorem isSolvable_finset_sup_twin {T : Set (Subgroup Y)} (hT : ∀ J ∈ T, Group.IsSolvable ↥J)
    (hN : ∀ K ∈ T, ∀ J ∈ T, K ≠ J → K ≤ Subgroup.normalizer (J : Set Y))
    (F : Finset (Subgroup Y)) : (∀ J ∈ F, J ∈ T) → Group.IsSolvable ↥(F.sup id) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.sup_empty]
    infer_instance
  | @insert J F hJF ih =>
    intro hF
    rw [Finset.sup_insert, id]
    have hFJ : F.sup id ≤ Subgroup.normalizer (J : Set Y) := by
      refine Finset.sup_le fun K hK => ?_
      have hKJ : K ≠ J := fun h => hJF (h ▸ hK)
      exact hN K (hF K (Finset.mem_insert_of_mem hK)) J (hF J (Finset.mem_insert_self _ _)) hKJ
    exact isSolvable_sup_of_le_normalizer_twin hFJ (hT J (hF J (Finset.mem_insert_self _ _)))
      (ih fun K hK => hF K (Finset.mem_insert_of_mem hK))

theorem twinGroup_isSolvable (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) :
    Group.IsSolvable ↥(twinGroup R) := by
  have : Finite (Subgroup Y) :=
    Finite.of_injective (fun H : Subgroup Y => (H : Set Y)) SetLike.coe_injective
  have hK0 : Group.IsSolvable ↥(tightCore R) := by
    have := Q8Datum.isSolvable hd
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (tightCore_le R))
  have huniq := Q8Datum.isUniqueInvolution_core hd
  have hTsolv : ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      Group.IsSolvable ↥J := by
    rintro J ⟨⟨g, rfl⟩, -⟩
    exact isSolvable_conjSub_of hK0 g
  have hTN : ∀ K ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R),
      ∀ J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R), K ≠ J →
        K ≤ Subgroup.normalizer (J : Set Y) := by
    rintro K ⟨hKΩ, z, hzK0, hzK⟩ J ⟨hJΩ, z', hzK0', hzJ⟩ hKJ
    have e1 : z = t := hzK0.eq huniq
    have e2 : z' = t := hzK0'.eq huniq
    rw [e1] at hzK
    rw [e2] at hzJ
    exact le_normalizer_of_twin hΩ hKΩ hJΩ hKJ hzK hzJ
  obtain ⟨F, hF⟩ : ∃ F : Finset (Subgroup Y), ∀ J, J ∈ F ↔
      J ∈ twinSet (CoreAssembly.conjClass (tightCore R)) (tightCore R) :=
    ⟨(Set.toFinite _).toFinset, fun J => (Set.toFinite _).mem_toFinset⟩
  have hsol := isSolvable_finset_sup_twin hTsolv hTN F (fun J hJ => (hF J).mp hJ)
  have heq : twinGroup R = F.sup id := by
    unfold twinGroup
    apply le_antisymm
    · exact iSup₂_le fun J hJ => Finset.le_sup (f := id) ((hF J).mpr hJ)
    · exact Finset.sup_le fun J hJ => le_iSup₂_of_le J ((hF J).mp hJ) le_rfl
  rw [heq]
  exact hsol

theorem Q8Datum.conjSub_t_eq (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)))
    (hq8 : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2)) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) : conjSub t A = A := by
  by_contra htA
  have ht1 := Q8Datum.t_mul_t hd
  have htinv := Q8Datum.t_inv hd
  obtain ⟨r₁, hr₁, r₂, hr₂, h1, h2, h12⟩ := Q8Datum.exists_S₀_pair hd hq8
  have key : ∀ r : Y, r * r = t → conjSub r A ≠ A := by
    intro r hrr heq
    apply htA
    rw [← hrr, conjSub_mul, heq, heq]
  have hex : ∃ r ∈ (S : Subgroup R).map R.subtype,
      conjSub r A ≠ A ∧ conjSub r A ≠ conjSub t A := by
    by_contra hno
    push Not at hno
    have e1 : conjSub r₁ A = conjSub t A := hno r₁ hr₁ (key r₁ h1)
    have e2 : conjSub r₂ A = conjSub t A := hno r₂ hr₂ (key r₂ h2)
    have hr12 : r₁ * r₂ ∈ (S : Subgroup R).map R.subtype := Subgroup.mul_mem _ hr₁ hr₂
    have e12 : conjSub (r₁ * r₂) A = conjSub t A := hno _ hr12 (key _ h12)
    apply htA
    have hr1t : r₁ * t = t * r₁ := mul_t_comm_of_sq h1
    symm
    calc A = conjSub (t * t) A := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub r₁ A) := by rw [conjSub_mul, e1]
      _ = conjSub (r₁ * t) A := by rw [← conjSub_mul, hr1t]
      _ = conjSub (r₁ * r₂) A := by rw [conjSub_mul, conjSub_mul, e2]
      _ = conjSub t A := e12
  obtain ⟨r, hrS, hrA, hrtA⟩ := hex
  have hrR : r ∈ R := Q8Datum.S₀_le hd hrS
  have hrsq : r * t = t * r := by
    rcases Q8Datum.S₀_cases hd hq8 hrS with h | h | h
    · rw [h]; group
    · rw [h]
    · exact mul_t_comm_of_sq h
  have hAt : CFSG.IsComponent (conjSub t A) := AscThmA.isComponent_conjSub hA t
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  have hArt : CFSG.IsComponent (conjSub (r * t) A) := AscThmA.isComponent_conjSub hA (r * t)
  have hrtne : conjSub (r * t) A ≠ A := by
    intro heq
    apply hrtA
    have h' : conjSub t (conjSub r A) = A := by rw [← conjSub_mul, ← hrsq, heq]
    calc conjSub r A = conjSub (t * t) (conjSub r A) := by rw [ht1, conjSub_one]
      _ = conjSub t (conjSub t (conjSub r A)) := conjSub_mul _ _ _
      _ = conjSub t A := by rw [h']
  refine TightA.false_of_solvable_covers (W := twinGroup R) hA.1
    (twinGroup_isSolvable hd hΩ) fun x hx => ?_
  set d : Y := x * (t * x * t⁻¹) with hd_def
  have hxt : t * x * t⁻¹ ∈ conjSub t A := conj_mem_conjSub hx
  have hdt : d * t = t * d := by
    have hc : (t * x * t⁻¹) * x = x * (t * x * t⁻¹) := (comm_of_ne hAt hA htA hxt hx)
    rw [hd_def]
    calc x * (t * x * t⁻¹) * t = (t * x * t⁻¹) * x * t := by rw [hc]
      _ = t * (x * (t * x * t⁻¹)) := by rw [htinv]; group
  refine ⟨d * r * d⁻¹ * r⁻¹,
    comm_mem_twinGroup hd hΩ hdt (hd.sylow_core.1 hrS), fun a ha => ?_⟩
  have hu1 : r * (t * x⁻¹ * t⁻¹) * r⁻¹ ∈ conjSub (r * t) A := by
    have := conj_mem_conjSub (n := r * t) (A.inv_mem hx)
    simpa [mul_assoc] using this
  have hu2 : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hx)
  have hc1 := comm_of_ne hArt hA hrtne hu1 ha
  have hc2 := comm_of_ne hAr hA hrA hu2 ha
  have hc3 := comm_of_ne hAt hA htA hxt ha
  have e : d * r * d⁻¹ * r⁻¹ =
      x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹) := by
    rw [hd_def]; group
  rw [e]
  calc x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹) * a *
        (x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * (r * x⁻¹ * r⁻¹))⁻¹
      = x * (t * x * t⁻¹) * (r * (t * x⁻¹ * t⁻¹) * r⁻¹) * ((r * x⁻¹ * r⁻¹) * a) *
          (r * x⁻¹ * r⁻¹)⁻¹ * (r * (t * x⁻¹ * t⁻¹) * r⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        group
    _ = x * (t * x * t⁻¹) * ((r * (t * x⁻¹ * t⁻¹) * r⁻¹) * a) *
          (r * (t * x⁻¹ * t⁻¹) * r⁻¹)⁻¹ * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        rw [hc2]; group
    _ = x * ((t * x * t⁻¹) * a) * (t * x * t⁻¹)⁻¹ * x⁻¹ := by
        rw [hc1]; group
    _ = x * a * x⁻¹ := by
        rw [hc3]; group

theorem Q8Datum.not_centralizes (hd : Q8TwinDatum R S t)
    (hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R))) {A : Subgroup Y}
    (hA : CFSG.IsComponent A) {r : Y} (hrS : r ∈ (S : Subgroup R).map R.subtype)
    (hrA : conjSub r A ≠ A) (htA : ∀ x ∈ A, x * t = t * x) : False := by
  have hAr : CFSG.IsComponent (conjSub r A) := AscThmA.isComponent_conjSub hA r
  refine TightA.false_of_solvable_covers (W := twinGroup R) hA.1
    (twinGroup_isSolvable hd hΩ) fun x hx => ?_
  refine ⟨x * r * x⁻¹ * r⁻¹, comm_mem_twinGroup hd hΩ (htA x hx) (hd.sylow_core.1 hrS),
    fun a ha => ?_⟩
  have hu : r * x⁻¹ * r⁻¹ ∈ conjSub r A := conj_mem_conjSub (A.inv_mem hx)
  have hc := comm_of_ne hAr hA hrA hu ha
  calc x * r * x⁻¹ * r⁻¹ * a * (x * r * x⁻¹ * r⁻¹)⁻¹
      = x * ((r * x⁻¹ * r⁻¹) * a) * (r * x⁻¹ * r⁻¹)⁻¹ * x⁻¹ := by group
    _ = x * a * x⁻¹ := by rw [hc]; group

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
