module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2HR8Kinds
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2PositionBTwo

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup Equiv

section Perm

theorem isSwap_of_le_centralizer_ten {π : Perm (Fin 10)} (hπ : orderOf π = 2)
    {A : Subgroup (Perm (Fin 10))} (hA : A ≤ centralizer {π}) (hcard : 20160 ≤ Nat.card A) :
    π.IsSwap := by
  have hle : Nat.card A ≤ Nat.card (centralizer {π}) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hA)
  obtain ⟨r, hr⟩ := Perm.cycleType_prime_order (σ := π) (by rw [hπ]; exact Nat.prime_two)
  rw [hπ] at hr
  have hsum : π.cycleType.sum ≤ 10 := by
    rw [Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  have hcent := Perm.nat_card_centralizer π
  rw [hr] at hsum hcent
  simp only [Multiset.sum_replicate, smul_eq_mul, Multiset.prod_replicate,
    Fintype.card_fin] at hsum hcent
  rw [Multiset.toFinset_replicate] at hcent
  simp only [Nat.add_one_ne_zero, ite_false, Finset.prod_singleton,
    Multiset.count_replicate_self] at hcent
  rw [Perm.isSwap_iff_cycleType, hr]
  have hr4 : r ≤ 4 := by omega
  interval_cases r
  · rfl
  all_goals (rw [hcent] at hle; norm_num [Nat.factorial] at hle; omega)

theorem apply_eq_of_le_centralizer_swap {α : Type*} [DecidableEq α] [Finite α]
    {D : Subgroup (Perm α)} (hD : IsSimpleGroup D) (hcard : 2 < Nat.card D) {a b : α}
    (hab : a ≠ b) (hDs : D ≤ centralizer {swap a b}) : ∀ d ∈ D, d a = a := by
  have hab' : ∀ d ∈ D, d a = a ∨ d a = b := by
    intro d hd
    have hc : d * swap a b = swap a b * d := mem_centralizer_singleton_iff.1 (hDs hd)
    have h1 : d b = swap a b (d a) := by
      have := congrArg (fun f : Perm α => f a) hc
      simpa [Perm.mul_apply, swap_apply_left] using this
    by_contra h
    push Not at h
    rw [swap_apply_of_ne_of_ne h.1 h.2] at h1
    exact hab (d.injective h1.symm)
  have horb : MulAction.orbit D a ⊆ ({a, b} : Set α) := by
    rintro _ ⟨d, rfl⟩
    rcases hab' d d.2 with h | h
    · left; exact h
    · right; exact h
  have hidx : (MulAction.stabilizer D a).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    calc (MulAction.orbit D a).ncard ≤ ({a, b} : Set α).ncard :=
          Set.ncard_le_ncard horb (Set.toFinite _)
      _ = 2 := Set.ncard_pair hab
  have hidx1 : (MulAction.stabilizer D a).index = 1 := by
    have hpos : (MulAction.stabilizer D a).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases Nat.lt_or_ge (MulAction.stabilizer D a).index 2 with h | h
    · omega
    · exfalso
      have h2 : (MulAction.stabilizer D a).index = 2 := by omega
      have hn := Subgroup.normal_of_index_eq_two h2
      rcases hD.eq_bot_or_eq_top_of_normal (MulAction.stabilizer D a) with hb | ht
      · rw [hb, Subgroup.index_bot] at h2
        omega
      · rw [ht, Subgroup.index_top] at h2
        omega
  intro d hd
  have htop := Subgroup.index_eq_one.1 hidx1
  have hmem : (⟨d, hd⟩ : D) ∈ MulAction.stabilizer D a := htop ▸ Subgroup.mem_top _
  exact hmem

theorem swap_eq_of_apply_eq {α : Type*} [DecidableEq α] {a b c d : α} (hab : a ≠ b)
    (h : swap c d a = b) : swap c d = swap a b := by
  by_cases hac : a = c
  · subst hac
    rw [swap_apply_left] at h
    rw [h]
  · by_cases had : a = d
    · subst had
      rw [swap_apply_right] at h
      rw [h, swap_comm]
    · rw [swap_apply_of_ne_of_ne hac had] at h
      exact absurd h hab

end Perm

section TypeFree

variable {Y : Type*} [Group Y]

theorem false_of_alternating_ten {Kc : Subgroup Y} (ε : Kc ≃* alternatingGroup (Fin 10))
    {s y : Y} (hsN : s ∈ normalizer (Kc : Set Y)) (hs2 : s * s = 1)
    (hsK : s ∉ centralizer (Kc : Set Y)) {D P : Subgroup Y} (hDK : D ≤ Kc)
    (hDs : D ≤ centralizer ({s} : Set Y)) (hDsimple : IsSimpleGroup D)
    (hDc : Nat.card D = 20160) (hyD : y ∈ D) (hy1 : y ≠ 1) (hy2 : y * y = 1) (hPK : P ≤ Kc)
    (hPs : P ≤ centralizer ({s * y} : Set Y)) (hPc : Nat.card P = 20160) : False := by
  classical
  set τ := Kc.normalizerMonoidHom ⟨s, hsN⟩ with hτ
  have hτapp : ∀ q : Kc, ((τ q : Kc) : Y) = s * q * s⁻¹ := fun q =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Kc ⟨s, hsN⟩ q
  set σ : MulAut (alternatingGroup (Fin 10)) := (ε.symm.trans τ).trans ε with hσ
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)
  obtain ⟨π, hπ⟩ := hbij.2 σ
  have key : ∀ q : Kc, π * ((ε q : alternatingGroup (Fin 10)) : Perm (Fin 10)) * π⁻¹ =
      ((ε (τ q) : alternatingGroup (Fin 10)) : Perm (Fin 10)) := by
    intro q
    have h1 := congrArg (fun φ : MulAut (alternatingGroup (Fin 10)) =>
      ((φ (ε q) : alternatingGroup (Fin 10)) : Perm (Fin 10))) hπ
    simp only [hσ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    exact h1
  have hτD : ∀ (d : Y) (hd : d ∈ D), τ ⟨d, hDK hd⟩ = ⟨d, hDK hd⟩ := fun d hd => by
    apply Subtype.ext
    rw [hτapp]
    have hds : d * s = s * d := mem_centralizer_singleton_iff.1 (hDs hd)
    calc s * d * s⁻¹ = d * s * s⁻¹ := by rw [hds]
      _ = d := by group
  have hyK : y ∈ Kc := hDK hyD
  have hτP : ∀ (p : Y) (hp : p ∈ P), τ (⟨y, hyK⟩ * ⟨p, hPK hp⟩ * ⟨y, hyK⟩⁻¹) = ⟨p, hPK hp⟩ :=
      fun p hp => by
    apply Subtype.ext
    rw [hτapp]
    have hps : p * (s * y) = (s * y) * p := mem_centralizer_singleton_iff.1 (hPs hp)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc s * (y * p * y⁻¹) * s⁻¹ = (s * y) * p * (s * y)⁻¹ := by group
      _ = p * (s * y) * (s * y)⁻¹ := by rw [hps]
      _ = p := by group
  set ι : Kc →* Perm (Fin 10) := (alternatingGroup (Fin 10)).subtype.comp ε.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (alternatingGroup (Fin 10)).subtype_injective.comp ε.injective
  set DA : Subgroup (Perm (Fin 10)) := (D.subgroupOf Kc).map ι with hDA
  set PA : Subgroup (Perm (Fin 10)) := (P.subgroupOf Kc).map ι with hPA
  have hDAc : Nat.card DA = 20160 := by
    rw [hDA, Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (D.subgroupOfEquivOfLe hDK).toEquiv, hDc]
  have hPAc : Nat.card PA = 20160 := by
    rw [hPA, Subgroup.card_map_of_injective hιinj,
      Nat.card_congr (P.subgroupOfEquivOfLe hPK).toEquiv, hPc]
  have hDAs : IsSimpleGroup DA := by
    have e1 : DA ≃* D :=
      ((D.subgroupOf Kc).equivMapOfInjective ι hιinj).symm.trans (D.subgroupOfEquivOfLe hDK)
    exact e1.isSimpleGroup
  have hDAπ : DA ≤ centralizer {π} := by
    rintro _ ⟨d, hd, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := key d
    rw [show d = ⟨(d : Y), hDK (mem_subgroupOf.1 hd)⟩ from rfl,
      hτD _ (mem_subgroupOf.1 hd)] at h1
    calc ι d * π = π * ((ε d : alternatingGroup (Fin 10)) : Perm (Fin 10)) * π⁻¹ * π := by
          rw [h1]; rfl
      _ = π * ι d := by simp [hι]
  have hτ2 : τ * τ = 1 := by
    rw [← sq]
    exact F4Pilot.normalizerMonoidHom_sq_eq_one Kc hsN (by rw [sq]; exact hs2)
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, map_one]
    ext x
    have h1 : τ (τ (ε.symm x)) = ε.symm x := by
      rw [← MulAut.mul_apply, hτ2, MulAut.one_apply]
    simp only [hσ, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply, h1,
      MulEquiv.apply_symm_apply, MulAut.one_apply]
  have hπ1 : π ≠ 1 := by
    rintro rfl
    apply hsK
    rw [mem_centralizer_iff]
    intro q hq
    have h1 := key ⟨q, hq⟩
    simp only [one_mul, inv_one, mul_one] at h1
    have h2 : τ ⟨q, hq⟩ = ⟨q, hq⟩ := hιinj (by simp only [hι, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype]; exact h1.symm)
    have h3 := congrArg Subtype.val h2
    rw [hτapp] at h3
    calc q * s = s * q * s⁻¹ * s := by rw [h3]
      _ = s * q := by group
  have hπ2 : orderOf π = 2 := orderOf_eq_prime (by rw [sq]; exact hππ) hπ1
  obtain ⟨a, b, hab, rfl⟩ := isSwap_of_le_centralizer_ten hπ2 hDAπ hDAc.ge
  set yt : Perm (Fin 10) := ι ⟨y, hyK⟩ with hyt
  have hytD : yt ∈ DA := ⟨⟨y, hyK⟩, mem_subgroupOf.2 hyD, rfl⟩
  have hya : yt a = a :=
    apply_eq_of_le_centralizer_swap hDAs (by rw [hDAc]; norm_num) hab hDAπ yt hytD
  have hyt1 : yt ≠ 1 := by
    intro h
    apply hy1
    have h1 : (⟨y, hyK⟩ : Kc) = 1 := hιinj (by rw [map_one]; exact h)
    exact congrArg Subtype.val h1
  have hytπ : yt * swap a b = swap a b * yt := mem_centralizer_singleton_iff.1 (hDAπ hytD)
  have hPAπ : PA ≤ centralizer {swap a b * yt} := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have h1 := key (⟨y, hyK⟩ * p * ⟨y, hyK⟩⁻¹)
    rw [show p = ⟨(p : Y), hPK (mem_subgroupOf.1 hp)⟩ from rfl,
      hτP _ (mem_subgroupOf.1 hp)] at h1
    have h2 : ((ε (⟨y, hyK⟩ * p * ⟨y, hyK⟩⁻¹) : alternatingGroup (Fin 10)) : Perm (Fin 10)) =
        yt * ι p * yt⁻¹ := by
      simp [hι, hyt]
    rw [h2] at h1
    have h3 : (swap a b * yt) * ι p * (swap a b * yt)⁻¹ = ι p := by
      rw [show (swap a b * yt) * ι p * (swap a b * yt)⁻¹ =
        swap a b * (yt * ι p * yt⁻¹) * (swap a b)⁻¹ by group]
      exact h1
    calc ι p * (swap a b * yt) = (swap a b * yt) * ι p * (swap a b * yt)⁻¹ * (swap a b * yt) := by
          rw [h3]
      _ = (swap a b * yt) * ι p := by group
  have hyt2 : yt * yt = 1 := by
    have h1 : (⟨y, hyK⟩ : Kc) * ⟨y, hyK⟩ = 1 := Subtype.ext hy2
    rw [← map_mul, h1, map_one]
  have hπ'π' : (swap a b * yt) * (swap a b * yt) = 1 := by
    calc (swap a b * yt) * (swap a b * yt) = swap a b * (yt * swap a b) * yt := by group
      _ = swap a b * (swap a b * yt) * yt := by rw [hytπ]
      _ = (swap a b * swap a b) * (yt * yt) := by group
      _ = 1 := by rw [swap_mul_self, hyt2, mul_one]
  have hπ'1 : swap a b * yt ≠ 1 := by
    intro h
    have h1 : yt = swap a b := by
      calc yt = (swap a b)⁻¹ * (swap a b * yt) := by group
        _ = swap a b := by rw [h, mul_one, swap_inv]
    have hsign : Perm.sign yt = 1 := (ε ⟨y, hyK⟩).2
    rw [h1, Perm.sign_swap hab] at hsign
    exact absurd hsign (by decide)
  have hπ'2 : orderOf (swap a b * yt) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hπ'π') hπ'1
  obtain ⟨c, d, -, hcd⟩ := isSwap_of_le_centralizer_ten hπ'2 hPAπ hPAc.ge
  have happ : (swap a b * yt) a = b := by
    rw [Perm.mul_apply, hya, swap_apply_left]
  have h4 : swap c d a = b := by rw [← hcd]; exact happ
  have h5 : swap a b * yt = swap a b := hcd.trans (swap_eq_of_apply_eq hab h4)
  apply hyt1
  calc yt = (swap a b)⁻¹ * (swap a b * yt) := by group
    _ = (swap a b)⁻¹ * swap a b := by rw [h5]
    _ = 1 := inv_mul_cancel _

end TypeFree

section Setting

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_solvable_of_nonempty_equiv_outside_six)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_alternating_ten_linear_two (hset : SeitzSetting G L) {K : Type} [Field K]
    (hK : Nat.card K = 2) (e : L ≃* LinearFlag.projectiveSL 6 K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin 6} (hab : a ≠ b)
    {X₀ : Subgroup (LinearFlag.projectiveSL 6 K)} (hX₀ : X₀ ≤ rootSL2 a b)
    (hX₀c : Nat.card X₀ = Nat.card K + 1)
    {X : Subgroup G} (hX : X = (X₀.map e.symm.toMonoidHom).map L.subtype)
    (htX : t ∈ centralizer (X : Set G)) {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin 6))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {Kc : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))}
    (hKc : IsComponent Kc)
    (hDK : (D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc)
    (hsN : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      normalizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hsC : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∉
      centralizer (Kc : Set (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G)))))
    (hA : Nonempty (Kc ≃* alternatingGroup (Fin 10))) : False := by
  have hK1 : Nat.card K = 2 ^ 1 := by rw [pow_one]; exact hK
  have := finite_of_card_eq_two_pow hK1
  have := charP_two_of_card_eq_two_pow hK1
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hDX, hDq, hDm, hcomp, hsyl, -, -⟩ :=
    neighbour_hyps_linear_two hset hK e (by norm_num) htC ht hab hX₀ hX₀c hX htX hDe
  obtain ⟨-, -, -, hXc, -, -, hDq', ⟨φD⟩, -, -⟩ :=
    neighbour_data_torusQ1 e (by norm_num) hab htC hX₀ hX₀c hX hDe
  obtain ⟨hSL, hZDb, ⟨eDb⟩⟩ :=
    nonempty_map_oddCore_mulEquiv_specialLinear_two hK e (by norm_num) htC hab hX₀ hX₀c hX hDe
  obtain ⟨ε⟩ := hA
  have hs : orderOf (QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩) = 2 :=
    orderOf_mk_oddCore (by rw [orderOf_mk]; exact ht)
  have hsD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ ∈
      centralizer (((D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) : Subgroup _) : Set _) :=
    mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hcomp.1 hd)
  have hOut : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer Kc) :=
    outer_solvable_of_nonempty_equiv_outside_six (Or.inr (by norm_num)) ⟨ε⟩
  have hcore := perfectCore_top_eq_of_isComponent
    (F4Pilot.pPrimeCore_two_quotient_oddCore_eq_bot _) hKc hDK hs hsD hsN hsC hsyl hOut
  have hKt := inf_centralizer_eq_zpowers hset e hK1 (by norm_num) htC ht
  have hOutL := isSolvable_outer_of_mulEquiv (by norm_num : 3 ≤ 6) e
  obtain ⟨x, z, hxz, hz, -, -, -⟩ :=
    exists_conj_eq_mul_transvection_twoSided_two hset (by norm_num) hK e htC ht
  obtain ⟨g, y, hy1, hyD, hg⟩ := exists_conj_eq_mul_mem_blockSL_compl_pair e
    (le_centralizer_of_mem_centralizer htC) (by norm_num) hab ⟨x, z, hz, hxz⟩
  have hXodd : Odd (Nat.card X) := by rw [hXc, hK]; decide
  have hXJ : X ≤ ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype :=
    hX ▸ map_mono (map_mono hX₀)
  obtain ⟨-, y₁, hy₁D, hy₁2, -, P, hP, ⟨φP⟩⟩ :=
    exists_le_centralizer_mulEquiv_of_conj_eq_mul_two hset.standardSetting hOutL hK
      (by norm_num) e ht hKt hab hXodd hXJ hyD hy1 hg
  rw [← hDe] at hy₁D φP
  have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin (6 - 2)) K) = 20160 := by
    have hq : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
    rw [Matrix.card_SL_field, hq]
    decide
  have hDbc : Nat.card ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = 20160 := by
    rw [Nat.card_congr eDb.toEquiv, hcardSL]
  have hDbs : IsSimpleGroup ((D.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := by
    have hm := lieModel_quotient_center_map_oddCore hDX hDq hDm
      (ne_bot_of_isQuasisimple hcomp.2.2)
    have hsimp := isSimpleGroup_of_lieModel_PSL hm
    exact ((QuotientGroup.quotientMulEquivOfEq hZDb).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  have hZD : center D = ⊥ := F4Pilot.center_eq_bot_congr φD.symm hSL
  have hD'q : CFSG.Open.IsQuasisimple (D.subgroupOf (centralizer (X : Set G))) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv (subgroupOfEquivOfLe hDX).symm hDq'
  have hD'Z : center (D.subgroupOf (centralizer (X : Set G))) = ⊥ :=
    F4Pilot.center_eq_bot_congr (subgroupOfEquivOfLe hDX).symm hZD
  have hDO := F4Pilot.inf_oddCore_eq_bot hD'q hD'Z
  have hPH : P ≤ centralizer (X : Set G) := hP.trans inf_le_left
  have hPq : CFSG.Open.IsQuasisimple P := F4Pilot.isQuasisimple_open_of_mulEquiv φP.symm hDq'
  have hPZ : center P = ⊥ := F4Pilot.center_eq_bot_congr φP.symm hZD
  have hP'q : CFSG.Open.IsQuasisimple (P.subgroupOf (centralizer (X : Set G))) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv (subgroupOfEquivOfLe hPH).symm hPq
  have hP'Z : center (P.subgroupOf (centralizer (X : Set G))) = ⊥ :=
    F4Pilot.center_eq_bot_congr (subgroupOfEquivOfLe hPH).symm hPZ
  let ePb := F4Pilot.mapMkEquivOfInfEqBot (oddCore (centralizer (X : Set G)))
    (P.subgroupOf (centralizer (X : Set G))) (F4Pilot.inf_oddCore_eq_bot hP'q hP'Z)
  have hy₁H : y₁ ∈ centralizer (X : Set G) := hDX hy₁D
  have hybD : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨y₁, hy₁H⟩ ∈
      (D.subgroupOf (centralizer (X : Set G))).map
        (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) :=
    ⟨⟨y₁, hy₁H⟩, mem_subgroupOf.2 hy₁D, rfl⟩
  have hyb1 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨y₁, hy₁H⟩ ≠ 1 := by
    intro h
    have hmem : (⟨y₁, hy₁H⟩ : centralizer (X : Set G)) ∈
        D.subgroupOf (centralizer (X : Set G)) ⊓ oddCore (centralizer (X : Set G)) :=
      ⟨mem_subgroupOf.2 hy₁D, (QuotientGroup.eq_one_iff _).1 h⟩
    rw [hDO] at hmem
    have h1 : y₁ = 1 := congrArg Subtype.val ((mem_bot).1 hmem)
    rw [h1, orderOf_one] at hy₁2
    exact absurd hy₁2 (by norm_num)
  have hyb2 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨y₁, hy₁H⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨y₁, hy₁H⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨y₁, hy₁H⟩ : centralizer (X : Set G)) * ⟨y₁, hy₁H⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← sq, ← hy₁2, pow_orderOf_eq_one]; rfl)
    rw [h1, map_one]
  have hs2 : QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
      QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ = 1 := by
    rw [← sq, ← hs, pow_orderOf_eq_one]
  have hPbc : Nat.card ((P.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) = 20160 := by
    rw [← Nat.card_congr ePb.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv,
      Nat.card_congr φP.toEquiv, Nat.card_congr φD.toEquiv, hcardSL]
  have hPbq : CFSG.Open.IsQuasisimple ((P.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) :=
    F4Pilot.isQuasisimple_open_of_mulEquiv ePb hP'q
  have : Group.IsPerfect ((P.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))) := ⟨hPbq.1⟩
  have hPbK : (P.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤ Kc :=
    hcore ▸ CFSG.Quasithin.le_perfectCore_of_perfect le_top (isPerfect_iff.mp this)
  have hPbs : (P.subgroupOf (centralizer (X : Set G))).map
      (QuotientGroup.mk' (oddCore (centralizer (X : Set G)))) ≤
      centralizer ({QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨t, htX⟩ *
        QuotientGroup.mk' (oddCore (centralizer (X : Set G))) ⟨y₁, hy₁H⟩} : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h1 := mem_centralizer_singleton_iff.1 (hP (mem_subgroupOf.1 hp)).2
    simpa only [Subgroup.coe_mul, mul_assoc] using h1
  exact false_of_alternating_ten ε hsN hs2 hsC hDK hcomp.1 hDbs hDbc hybD hyb1 hyb2 hPbK hPbs
    hPbc

end Setting

end CFSG.SeitzReduction.LinearPilot
