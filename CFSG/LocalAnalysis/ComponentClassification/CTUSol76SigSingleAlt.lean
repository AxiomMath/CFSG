module

public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76SigSingleDesc
public import CFSG.LocalAnalysis.ComponentInitial.AlternatingLocalComponents

public section

namespace CFSG.ComponentClassification.Sol76.Sig

open CFSG Subgroup CFSG.ComponentClassification.FooteLit CFSG.LocalAnalysis.ComponentInitial
  Equiv
open scoped commutatorElement

theorem altNot_mem_of_odd {G : Type*} [Group G] {R : Subgroup G} (hR : Odd (Nat.card R))
    {g : G} (hg : orderOf g = 2) : g ∉ R := fun hgR => by
  have h := orderOf_dvd_natCard (⟨g, hgR⟩ : R)
  rw [Subgroup.orderOf_mk, hg] at h
  exact Nat.not_even_iff_odd.mpr hR (even_iff_two_dvd.mpr h)

theorem altPerfect_le_of_le_sup {G : Type*} [Group G] {P R J : Subgroup G} [P.Normal]
    (hR : Group.IsSolvable R) (hJ : ⁅J, J⁆ = J) (hJPR : J ≤ P ⊔ R) : J ≤ P := by
  set q := QuotientGroup.mk' P
  have hle : J.map q ≤ R.map q :=
    calc J.map q ≤ (P ⊔ R).map q := map_mono hJPR
      _ = R.map q := by
        rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff P).mpr (QuotientGroup.ker_mk' P).ge,
          bot_sup_eq]
  have : Group.IsSolvable (R.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective R)
  have : Group.IsSolvable (J.map q) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
  have : Group.IsPerfect (J.map q) := isPerfect_iff.mpr (by rw [← map_commutator, hJ])
  have hbot : J.map q = ⊥ := by
    by_contra hne
    have : Nontrivial (J.map q) := (nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (J.map q) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem altLe_of_cover {G : Type*} [Group G] {P R J : Subgroup G} [P.Normal] [R.Normal]
    [IsSimpleGroup P] (hPR : ¬ P ≤ R) (hR : Group.IsSolvable R) (hJ : ⁅J, J⁆ = J)
    (hPJR : P ≤ J ⊔ R) (hJPR : J ≤ P ⊔ R) : P ≤ J := by
  have hinf : P ⊓ R = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf P) with h | h
    · exact disjoint_iff.mp (subgroupOf_eq_bot.mp h).symm
    · exact absurd (subgroupOf_eq_top.mp h) hPR
  have hJP := altPerfect_le_of_le_sup hR hJ hJPR
  intro p hp
  obtain ⟨j, hj, r, hr, rfl⟩ := mem_sup_of_normal_right.mp (hPJR hp)
  have hrP : r ∈ P := by
    have h := P.mul_mem (P.inv_mem (hJP hj)) hp
    rwa [inv_mul_cancel_left] at h
  have hr1 : r = 1 := by
    have h : r ∈ P ⊓ R := ⟨hrP, hr⟩
    rwa [hinf, mem_bot] at h
  rwa [hr1, mul_one]

theorem altMem_fixedPoints_iff {Ω : Type*} {K : Subgroup (Perm Ω)} {g : K} {z : Ω} :
    z ∈ MulAction.fixedPoints (zpowers g) Ω ↔ (g : Perm Ω) z = z := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨g, mem_zpowers g⟩
  · rintro h ⟨k, hk⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hk
    change ((g ^ m : K) : Perm Ω) z = z
    rw [SubgroupClass.coe_zpow]
    exact Perm.zpow_apply_eq_self_of_apply_eq_self h m

theorem altExists_orderOf_eq_two {Ω : Type*} [DecidableEq Ω] {S : Set Ω} [Fintype S]
    [DecidablePred (· ∈ S)] (h : 4 ≤ Nat.card S) :
    ∃ σ ∈ (alternatingGroup S).map Perm.ofSubtype, orderOf σ = 2 := by
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 4) (β := S)
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact h)
  have hne : ∀ i j : Fin 4, i ≠ j → (f i : Ω) ≠ f j := fun i j hij h' =>
    hij (f.injective (Subtype.ext h'))
  exact ⟨_, swap_mul_swap_mem_alternatingGroup_map (f.injective.ne (by decide : (0 : Fin 4) ≠ 1))
    (f.injective.ne (by decide : (2 : Fin 4) ≠ 3)),
    orderOf_swap_mul_swap (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 0 3 (by decide))
      (hne 1 2 (by decide)) (hne 1 3 (by decide))⟩

open scoped Classical in
theorem altTwoComponent_map {T : Type} [Group T] {n : ℕ} (e : T ≃* alternatingGroup (Fin n))
    {x : T} (hx : orderOf x = 2) {P : Subgroup T}
    (hP : IsTwoComponentIn P (centralizer ({x} : Set T))) :
    5 ≤ Nat.card (MulAction.fixedPoints (zpowers (e x)) (Fin n)) ∧
      P.map ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) =
        (alternatingGroup (MulAction.fixedPoints (zpowers (e x)) (Fin n))).map
          Perm.ofSubtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hPC, hPp⟩ := hP
  set C := centralizer ({x} : Set T) with hCdef
  have hx' : orderOf (e x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
  have hC : C.map e.toMonoidHom = centralizer ({e x} : Set (alternatingGroup (Fin n))) := by
    ext y
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 := congrArg e h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h1
    · intro h
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact h
  have hN := centralizer_singleton_eq_normalizer_zpowers hx'
  let φ : C ≃* normalizer (zpowers (e x) : Set (alternatingGroup (Fin n))) :=
    (e.subgroupMap _).trans ((MulEquiv.subgroupCongr hC).trans (MulEquiv.subgroupCongr hN))
  have hL : IsPComponent 2 ((P.subgroupOf C).map φ.toMonoidHom) :=
    CatalogueBAlternating.pComponent_map_equiv 2 φ _ hPp
  obtain ⟨h5, heq, -⟩ := CatalogueBAlternating.between_normalizer_pComponent
    (alternatingGroup (Fin n)) le_rfl 2 (zpowers (e x)) (isPGroup_zpowers_of_orderOf_eq_two hx')
    _ hL
  refine ⟨h5, ?_⟩
  rw [← heq, Subgroup.map_map]
  calc P.map ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom)
      = ((P.subgroupOf C).map C.subtype).map
          ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) := by
        rw [map_subgroupOf_eq_of_le hPC]
    _ = _ := by
        rw [Subgroup.map_map]
        congr 1

open scoped Classical in
theorem altTwoComponent_normalizer {T : Type} [Group T] {n : ℕ}
    (e : T ≃* alternatingGroup (Fin n)) {x : T} (hx : orderOf x = 2) {P : Subgroup T}
    (hP : IsTwoComponentIn P (centralizer ({x} : Set T))) :
    centralizer ({x} : Set T) ≤ normalizer (P : Set T) := by
  intro c hc
  have hι : Function.Injective ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) :=
    (alternatingGroup (Fin n)).subtype_injective.comp e.injective
  have hc' := Sol76.isTwoComponentIn_map_conj hP (le_normalizer hc)
  have heq : P.map (MulAut.conj c).toMonoidHom = P := map_injective hι
    ((altTwoComponent_map e hx hc').2.trans (altTwoComponent_map e hx hP).2.symm)
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨k, hk, hkh⟩ := hh
    have hkh' : k = h := by simpa using hkh
    rwa [← hkh']

open scoped Classical in
theorem altOddCover_le {T : Type} [Group T] [Finite T] {n : ℕ}
    (e : T ≃* alternatingGroup (Fin n)) {x : T} (hx : orderOf x = 2) {Y : Subgroup T}
    (hY : OddCoverAt Y x) :
    5 ≤ Nat.card (MulAction.fixedPoints (zpowers (e x)) (Fin n)) ∧
      (alternatingGroup (MulAction.fixedPoints (zpowers (e x)) (Fin n))).map Perm.ofSubtype ≤
        Y.map ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) := by
  obtain ⟨P, R, J, hP, hRC, hRn, hRodd, hJ, hJp, hPJR, hJPR⟩ := hY
  set C := centralizer ({x} : Set T) with hCdef
  have hι : Function.Injective ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) :=
    (alternatingGroup (Fin n)).subtype_injective.comp e.injective
  obtain ⟨h5, hPι⟩ := altTwoComponent_map e hx hP
  refine ⟨h5, hPι ▸ map_mono ?_⟩
  have hPC : P ≤ C := hP.1
  have hJC : J ≤ C := hJ.trans inf_le_right
  have : (P.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hPC).mpr (altTwoComponent_normalizer e hx hP)
  have : IsSimpleGroup (alternatingGroup (MulAction.fixedPoints (zpowers (e x)) (Fin n))) :=
    alternatingGroup.isSimpleGroup h5
  have : IsSimpleGroup (P.subgroupOf C) :=
    ((((subgroupOfEquivOfLe hPC).trans (P.equivMapOfInjective _ hι)).trans
      (MulEquiv.subgroupCongr hPι)).trans
      ((alternatingGroup _).equivMapOfInjective _ Perm.ofSubtype_injective).symm).isSimpleGroup
  obtain ⟨σ, hσ, hσ2⟩ := altExists_orderOf_eq_two (le_trans (by norm_num) h5)
  rw [← hPι] at hσ
  obtain ⟨p, hp, rfl⟩ := mem_map.mp hσ
  have hp2 : orderOf p = 2 := by rwa [orderOf_injective _ hι] at hσ2
  have hPR : ¬ P.subgroupOf C ≤ R.subgroupOf C := fun h =>
    altNot_mem_of_odd hRodd hp2 (mem_subgroupOf.mp
      (h (show (⟨p, hPC hp⟩ : C) ∈ P.subgroupOf C from mem_subgroupOf.mpr hp)))
  have hRs : Group.IsSolvable (R.subgroupOf C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (by rwa [Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv])
  have hJp' : ⁅J.subgroupOf C, J.subgroupOf C⁆ = J.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hJC, hJp]
  have h1 : P.subgroupOf C ≤ J.subgroupOf C ⊔ R.subgroupOf C := by
    rw [← subgroupOf_sup hJC hRC]
    exact fun g hg => hPJR hg
  have h2 : J.subgroupOf C ≤ P.subgroupOf C ⊔ R.subgroupOf C := by
    rw [← subgroupOf_sup hPC hRC]
    exact fun g hg => hJPR hg
  have h := altLe_of_cover hPR hRs hJp' h1 h2
  intro q hq
  exact (hJ (mem_subgroupOf.mp
    (h (show (⟨q, hPC hq⟩ : C) ∈ P.subgroupOf C from mem_subgroupOf.mpr hq)))).1

theorem altCommutator_swap {Ω : Type*} [DecidableEq Ω] (τ : Perm Ω) {a b c d : Ω}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : τ a = d) (hb : τ b = b) (hc : τ c = c) :
    ⁅τ, swap a c * swap a b⁆ = swap a b * swap a d := by
  have h1 : τ * (swap a c * swap a b) * τ⁻¹ = swap (τ a) (τ c) * swap (τ a) (τ b) := by
    rw [swap_apply_apply, swap_apply_apply]
    group
  rw [commutatorElement_def, h1, ha, hb, hc, mul_inv_rev, swap_inv, swap_inv]
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

theorem altCommutator_mul_commutator {Ω : Type*} [DecidableEq Ω] {a b c d d' : Ω}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (had' : a ≠ d') (hbc : b ≠ c) (hbd : b ≠ d)
    (hbd' : b ≠ d') (hcd : c ≠ d) (hcd' : c ≠ d') (hdd' : d ≠ d') :
    ⁅swap a d * swap d d', swap a c * swap a b⁆ * ⁅swap a d' * swap d d', swap a c * swap a b⁆ =
      swap a d' * swap b d := by
  have key : ∀ e : Ω, a ≠ e → b ≠ e → c ≠ e →
      ⁅swap a e * swap d d', swap a c * swap a b⁆ = swap a b * swap a e := fun e hae hbe hce =>
    altCommutator_swap _ hab hac hae hbc hbe hce
      (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne had had', swap_apply_left])
      (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne hbd hbd',
        swap_apply_of_ne_of_ne hab.symm hbe])
      (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcd hcd',
        swap_apply_of_ne_of_ne hac.symm hce])
  rw [key d had hbd hcd, key d' had' hbd' hcd']
  ext z
  simp only [Perm.mul_apply, swap_apply_def]
  split_ifs <;> simp_all

open scoped Classical in
theorem singleComponentSimpleAt_alternating :
    SingleComponentSimpleAt
      (fun S _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) := by
  intro T _ _ _ hT X Y _ _ _ _ hXr _ hcomm hcovY hcovX
  obtain ⟨x, hxX, hx2⟩ := exists_orderOf_eq_two_of_pRank ((by norm_num : 1 ≤ 2).trans hXr)
  have hR₀ : Odd (Nat.card (oddCoreIn X)) := Nat.coprime_two_left.mp (coprime_card_oddCoreIn X)
  have hXY : ⁅X, Y⁆ ≤ oddCoreIn X := hcomm.trans inf_le_left
  obtain ⟨n, -, ⟨e⟩⟩ := hT
  have hι : Function.Injective ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) :=
    (alternatingGroup (Fin n)).subtype_injective.comp e.injective
  obtain ⟨hF, hFY⟩ := altOddCover_le e hx2 (hcovY x hxX hx2)
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin 5)
    (β := MulAction.fixedPoints (zpowers (e x)) (Fin n))
    (by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hF)
  have hne : ∀ i j : Fin 5, i ≠ j → (f i : Fin n) ≠ f j := fun i j hij h =>
    hij (f.injective (Subtype.ext h))
  obtain ⟨y, hyY, hyι⟩ := mem_map.mp (hFY (swap_mul_swap_mem_alternatingGroup_map
    (f.injective.ne (by decide : (0 : Fin 5) ≠ 1)) (f.injective.ne (by decide : (2 : Fin 5) ≠ 3))))
  have hy2 : orderOf y = 2 := by
    rw [← orderOf_injective _ hι y, hyι]
    exact orderOf_swap_mul_swap (hne 0 1 (by decide)) (hne 0 2 (by decide))
      (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
  obtain ⟨hF', hF'X⟩ := altOddCover_le e hy2 (hcovX y hyY hy2)
  have hyι' : ((e y : alternatingGroup (Fin n)) : Perm (Fin n)) =
      swap (f 0 : Fin n) (f 1) * swap (f 2 : Fin n) (f 3) := hyι
  have ha : (f 4 : Fin n) ∈ MulAction.fixedPoints (zpowers (e y)) (Fin n) := by
    rw [altMem_fixedPoints_iff, hyι', Perm.mul_apply,
      swap_apply_of_ne_of_ne (hne 4 2 (by decide)) (hne 4 3 (by decide)),
      swap_apply_of_ne_of_ne (hne 4 0 (by decide)) (hne 4 1 (by decide))]
  have hb : (f 0 : Fin n) ∉ MulAction.fixedPoints (zpowers (e y)) (Fin n) := by
    rw [altMem_fixedPoints_iff, hyι', Perm.mul_apply,
      swap_apply_of_ne_of_ne (hne 0 2 (by decide)) (hne 0 3 (by decide)), swap_apply_left]
    exact hne 1 0 (by decide)
  have hc : (f 2 : Fin n) ∉ MulAction.fixedPoints (zpowers (e y)) (Fin n) := by
    rw [altMem_fixedPoints_iff, hyι', Perm.mul_apply, swap_apply_left,
      swap_apply_of_ne_of_ne (hne 3 0 (by decide)) (hne 3 1 (by decide))]
    exact hne 3 2 (by decide)
  obtain ⟨d, d', hd, hd', hdd'⟩ := exists_two_ne_of_three_le_card (le_trans (by norm_num) hF')
    (⟨f 4, ha⟩ : MulAction.fixedPoints (zpowers (e y)) (Fin n))
  obtain ⟨s, hsY, hsι⟩ := mem_map.mp (hFY (swap_mul_swap_mem_alternatingGroup_map
    (f.injective.ne (by decide : (4 : Fin 5) ≠ 2)) (f.injective.ne (by decide : (4 : Fin 5) ≠ 0))))
  obtain ⟨t, htX, htι⟩ := mem_map.mp (hF'X (swap_mul_swap_mem_alternatingGroup_map hd.symm hdd'))
  obtain ⟨t', ht'X, ht'ι⟩ :=
    mem_map.mp (hF'X (swap_mul_swap_mem_alternatingGroup_map hd'.symm hdd'))
  have h4d : (f 4 : Fin n) ≠ d := fun h => hd (Subtype.ext h.symm)
  have h4d' : (f 4 : Fin n) ≠ d' := fun h => hd' (Subtype.ext h.symm)
  have hdd'' : (d : Fin n) ≠ d' := fun h => hdd' (Subtype.ext h)
  have h0d : (f 0 : Fin n) ≠ d := fun h => hb (h ▸ d.2)
  have h0d' : (f 0 : Fin n) ≠ d' := fun h => hb (h ▸ d'.2)
  have h2d : (f 2 : Fin n) ≠ d := fun h => hc (h ▸ d.2)
  have h2d' : (f 2 : Fin n) ≠ d' := fun h => hc (h ▸ d'.2)
  have hg : ⁅t, s⁆ * ⁅t', s⁆ ∈ oddCoreIn X :=
    hXY (mul_mem (commutator_mem_commutator htX hsY) (commutator_mem_commutator ht'X hsY))
  have hgι : ((alternatingGroup (Fin n)).subtype.comp e.toMonoidHom) (⁅t, s⁆ * ⁅t', s⁆) =
      swap (f 4 : Fin n) d' * swap (f 0 : Fin n) d := by
    rw [map_mul, map_commutatorElement, map_commutatorElement, htι, ht'ι, hsι]
    exact altCommutator_mul_commutator (hne 4 0 (by decide)) (hne 4 2 (by decide)) h4d h4d'
      (hne 0 2 (by decide)) h0d h0d' h2d h2d' hdd''
  have hg2 : orderOf (⁅t, s⁆ * ⁅t', s⁆) = 2 := by
    rw [← orderOf_injective _ hι, hgι]
    exact orderOf_swap_mul_swap h4d' (hne 4 0 (by decide)) h4d (Ne.symm h0d') (Ne.symm hdd'')
  exact altNot_mem_of_odd hR₀ hg2 hg

theorem singleComponentQuasisimpleAt_alternating :
    SingleComponentQuasisimpleAt
      (fun S _ => ∃ n : ℕ, 5 ≤ n ∧ Nonempty (S ≃* alternatingGroup (Fin n))) :=
  singleComponentQuasisimpleAt_of_simpleAt singleComponentSimpleAt_alternating

end CFSG.ComponentClassification.Sol76.Sig
