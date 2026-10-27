module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuCzModel
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuAsmNA
public import Certificates.Certificate15107
import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuNRTwist

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open Subgroup CFSG.Open CFSG.LieType.BorelTits CFSG.CosetTable CFSG.GMS78Ru CFSG.GMS78RuSim
  CFSG.GMS78RuQ CFSG.GMS78RuN CFSG.ComponentClassification.GMS78.RuPi7
  CFSG.ComponentClassification.GMS78.RuAsm CFSG.ComponentClassification.GMS78.RuN

theorem card_mul_le_of_distinct {P : Type*} [Group P] {H K : Subgroup P} [Finite H]
    (hKH : K ≤ H) {n : ℕ} (g : Fin n → P) (hg : ∀ i, g i ∈ H)
    (hd : ∀ i j, (g i)⁻¹ * g j ∈ K → i = j) : Nat.card K * n ≤ Nat.card H := by
  have hinj : Function.Injective fun i : Fin n =>
      (QuotientGroup.mk ⟨g i, hg i⟩ : H ⧸ K.subgroupOf H) := by
    intro i j h
    apply hd
    have := QuotientGroup.eq.1 h
    rwa [Subgroup.mem_subgroupOf] at this
  have hidx : n ≤ (K.subgroupOf H).index := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_fin] at this
  have h := (K.subgroupOf H).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at h
  calc Nat.card K * n ≤ Nat.card K * (K.subgroupOf H).index := Nat.mul_le_mul_left _ hidx
    _ = Nat.card H := h

@[expose] def czmX0R : Subgroup RuR where
  carrier := {x | x.m.val ∈ czmV0}
  mul_mem' := by
    intro x y hx hy
    change (x.m ^^^ y.m).val ∈ czmV0
    rw [fin256_val_xor]
    have key : ∀ a ∈ czmV0, ∀ b ∈ czmV0, a ^^^ b ∈ czmV0 := by decide
    exact key _ hx _ hy
  one_mem' := by
    change (0 : ℕ) ∈ czmV0
    decide
  inv_mem' := fun hx => hx

theorem mem_czmX0R (x : RuR) : x ∈ czmX0R ↔ x.m.val ∈ czmV0 := Iff.rfl

theorem card_czmX0R : Nat.card czmX0R = 32 := by
  have hlt : ∀ a : Fin 4, czmV0.getD a 0 < 256 := by decide
  have hmem : ∀ a : Fin 4, czmV0.getD a 0 ∈ czmV0 := by decide
  have hinj : ∀ a b : Fin 4, czmV0.getD a 0 = czmV0.getD b 0 → a = b := by decide
  have hsurj : ∀ v ∈ czmV0, ∃ a : Fin 4, czmV0.getD a 0 = v := by decide
  let F : Fin 4 × Fin 8 → czmX0R := fun p => ⟨⟨⟨czmV0.getD p.1 0, hlt p.1⟩, p.2⟩, hmem p.1⟩
  have hF : Function.Bijective F := by
    refine ⟨fun p q h => ?_, fun x => ?_⟩
    · have h1 := congrArg (fun x : czmX0R => (x : RuR).m.val) h
      have h2 := congrArg (fun x : czmX0R => (x : RuR).t) h
      exact Prod.ext (hinj _ _ h1) h2
    · obtain ⟨a, ha⟩ := hsurj _ x.2
      exact ⟨(a, (x : RuR).t), Subtype.ext (RuR.ext (Fin.ext ha) rfl)⟩
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_fin]

theorem A1R_le_czmX0R : A1R ≤ czmX0R := fun x hx => by
  rw [mem_czmX0R, (mem_A1R_iff x).1 hx]
  decide

section Cert


@[expose] noncomputable def czmX0M : Subgroup RuNModel := czmX0R.map SemidirectProduct.inl

theorem card_czmX0M : Nat.card czmX0M = 32 := by
  rw [czmX0M, Subgroup.card_map_of_injective SemidirectProduct.inl_injective, card_czmX0R]

theorem czmV0_lt {m : ℕ} (hm : m ∈ czmV0) : m < 256 := by
  revert m
  decide

theorem toModel_injOn {p q : NTrip} (hp : p.1 < 256 ∧ p.2.2 ∈ glList)
    (hq : q.1 < 256 ∧ q.2.2 ∈ glList) (h : toModel p = toModel q) : p = q := by
  rw [toModel_of_valid hp, toModel_of_valid hq] at h
  have h1 := congrArg SemidirectProduct.left h
  have h2 := congrArg (fun g : RuNModel => ((g.right : nK) : MulAut RuR)) h
  have e1 : p.1 = q.1 := congrArg (fun x : RuR => x.m.val) h1
  have e2 : p.2.1 = q.2.1 := congrArg RuR.t h1
  have e3 : p.2.2 = q.2.2 := eq_of_nAut_eq fun x => DFunLike.congr_fun h2 x
  exact Prod.ext e1 (Prod.ext e2 e3)

theorem czmX0_parts {x : NTrip} (hx : x ∈ czmX0) :
    (x.1 < 256 ∧ x.2.2 ∈ glList) ∧ toModel x ∈ czmX0M := by
  simp only [czmX0, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at hx
  obtain ⟨m, hm, t, rfl⟩ := hx
  refine ⟨⟨czmV0_lt hm, linId_mem⟩, ?_⟩
  rw [toModel_inl (czmV0_lt hm)]
  exact ⟨_, hm, rfl⟩

theorem exists_czmX0 {x : RuNModel} (hx : x ∈ czmX0M) : ∃ p ∈ czmX0, toModel p = x := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨(a.m.val, a.t, linId), ?_, ?_⟩
  · simp only [czmX0, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
    exact ⟨a.m.val, ha, a.t, rfl⟩
  · rw [toModel_inl a.m.isLt]

theorem czmInX0_parts {y : NTrip} (hy : czmInX0 y = true) :
    (y.1 < 256 ∧ y.2.2 ∈ glList) ∧ toModel y ∈ czmX0M := by
  simp only [czmInX0, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq] at hy
  obtain ⟨hm, hr⟩ := hy
  obtain ⟨m, t, r⟩ := y
  simp only at hm hr
  subst hr
  refine ⟨⟨czmV0_lt hm, linId_mem⟩, ?_⟩
  rw [toModel_inl (czmV0_lt hm)]
  exact ⟨_, hm, rfl⟩

theorem toModel_czmConj {g gi x : NTrip} (hg : g.1 < 256 ∧ g.2.2 ∈ glList)
    (hgi : gi.1 < 256 ∧ gi.2.2 ∈ glList) (hx : x.1 < 256 ∧ x.2.2 ∈ glList) :
    (((czmConj g gi x).1 < 256 ∧ (czmConj g gi x).2.2 ∈ glList)) ∧
      toModel (czmConj g gi x) = toModel g * toModel x * toModel gi := by
  have h1 := nMulT_valid hg hx
  refine ⟨nMulT_valid h1 hgi, ?_⟩
  rw [czmConj, toModel_mul h1 hgi, toModel_mul hg hx]

theorem czmZ0_valid : czmZ0.1 < 256 ∧ czmZ0.2.2 ∈ glList := ⟨by decide, linId_mem⟩

theorem toModel_czmZ0 : toModel czmZ0 = SemidirectProduct.inl ⟨0, 4⟩ := toModel_inl (by decide) 4

theorem czmSame_iff {y y' : NTrip} (hy : y.1 < 256 ∧ y.2.2 ∈ glList)
    (hy' : y'.1 < 256 ∧ y'.2.2 ∈ glList) :
    czmSame y y' = true ↔ toModel y = toModel y' ∨ toModel y = toModel y' * toModel czmZ0 := by
  simp only [czmSame, Bool.or_eq_true, beq_iff_eq]
  have hm := nMulT_valid hy' czmZ0_valid
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h, toModel_mul hy' czmZ0_valid])
  · rintro (h | h)
    · exact Or.inl (toModel_injOn hy hy' h)
    · rw [← toModel_mul hy' czmZ0_valid] at h
      exact Or.inr (toModel_injOn hy hm h)

end Cert

theorem nEvalW_ruZ0Word : nEvalW ruZ0Word = czmZ0 := by
  have h := Certificates.certificate15107.2.1
  simpa [czmZ0Check] using h

theorem czm_sub_index :
    (CFSG.CosetTable.genSub {r | r ∈ p12Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf sub9.length [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
      (CFSG.CosetTable.genSub {r | r ∈ p12Rels.map FreeGroup.mk}
        (CFSG.CosetTable.subsetOf sub9.length [0, 1, 2, 3, 4, 5])).index ≤ 24 :=
  Certificates.certificate15107.1

theorem czm_j_check : czmJCheck = true :=
  Certificates.certificate15107.2.2.2.1

theorem czm_rep_check : czmRepCheck = true :=
  Certificates.certificate15107.2.2.2.2.1

theorem czmLetter_parts {i : ℕ} (hi : i < 5) :
    nMulT (nImg.getD i nOneT) czmZ0 = nMulT czmZ0 (nImg.getD i nOneT) ∧
    ∀ x ∈ czmX0, czmInX0 (czmConj (nImg.getD i nOneT) (nImgInv.getD i nOneT) x) = true ∧
      czmInX0 (czmConj (nImgInv.getD i nOneT) (nImg.getD i nOneT) x) = true := by
  have h := Certificates.certificate15107.2.2.1
  simp only [czmLetterCheck, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    beq_iff_eq] at h
  exact h i hi

section Model


theorem ruNImg_mul_czmZ0 {i : Fin 7} (hi : i.val < 5) :
    ruNImg i * toModel czmZ0 = toModel czmZ0 * ruNImg i := by
  have hv := (nImg_parts i).1
  have e := congrArg toModel (czmLetter_parts hi).1
  rwa [toModel_mul hv czmZ0_valid, toModel_mul czmZ0_valid hv] at e

theorem ruNImg_mem_normalizer {i : Fin 7} (hi : i.val < 5) :
    ruNImg i ∈ normalizer (czmX0M : Set RuNModel) := by
  have hv := nImg_parts i
  have key : ∀ x ∈ czmX0M, ruNImg i * x * (ruNImg i)⁻¹ ∈ czmX0M ∧
      (ruNImg i)⁻¹ * x * ruNImg i ∈ czmX0M := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := exists_czmX0 hx
    obtain ⟨h1, h2⟩ := (czmLetter_parts hi).2 p hp
    have hpv := (czmX0_parts hp).1
    refine ⟨?_, ?_⟩
    · have h := (czmInX0_parts h1).2
      rw [(toModel_czmConj hv.1 hv.2.1 hpv).2, hv.2.2] at h
      exact h
    · have h := (czmInX0_parts h2).2
      rw [(toModel_czmConj hv.2.1 hv.1 hpv).2, hv.2.2] at h
      exact h
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => (key x hx).1, fun hx => ?_⟩
  have h := (key _ hx).2
  rwa [show (ruNImg i)⁻¹ * (ruNImg i * x * (ruNImg i)⁻¹) * ruNImg i = x by group] at h

end Model

theorem two_pow_le_eight : ∀ k < 8, 2 ^ k ∣ 168 → 2 ^ k ≤ 8 := by decide

section Core


theorem eq_bot_of_normal_isPGroup (M : Subgroup nK) (hMn : M.Normal) (hMp : IsPGroup 2 M) :
    M = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite nK := Nat.finite_of_card_ne_zero (by rw [card_nK]; norm_num)
  by_contra hne
  obtain ⟨k, hk⟩ := hMp.exists_card_eq
  have hdvd : Nat.card M ∣ 168 := card_nK ▸ Subgroup.card_subgroup_dvd_card M
  have hk8 : k < 8 := by
    by_contra h
    have h1 : 2 ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 := Nat.le_of_dvd (by norm_num) hdvd
    rw [hk] at h2
    omega
  have hle8 : Nat.card M ≤ 8 := hk ▸ two_pow_le_eight k hk8 (hk ▸ hdvd)
  have h2 : 2 ∣ Nat.card M := by
    rcases k with _ | k
    · exact absurd (Subgroup.eq_bot_of_card_eq M (by rw [hk, pow_zero])) hne
    · rw [hk, pow_succ]
      exact dvd_mul_left 2 _
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hu2 : orderOf (t : nK) = 2 := (Subgroup.orderOf_coe t).trans ht
  obtain ⟨r, hr⟩ : ∃ r, codeOf (t : nK) = r := ⟨_, rfl⟩
  have hrm : r ∈ glList := hr ▸ codeOf_mem _
  have hu : ∀ x, ((t : nK) : MulAut RuR) x = nAut r x := fun x => by rw [codeOf_spec, hr]
  have hrr : linComp r r = linId := by
    refine eq_of_nAut_eq fun x => ?_
    rw [← nAut_linComp hrm hrm, ← hu, ← hu, nAut_linId]
    have e := pow_orderOf_eq_one (t : nK)
    rw [hu2, pow_two] at e
    exact congrArg (fun k : nK => (k : MulAut RuR) x) e
  have hr1 : r ≠ linId := by
    intro e
    have ht1 : (t : nK) = 1 := Subtype.ext (MulEquiv.ext fun x => by
      rw [hu, e, nAut_linId]
      rfl)
    rw [ht1, orderOf_one] at hu2
    exact absurd hu2 (by norm_num)
  have hcheck : 9 ≤ (glList.map fun c => czmConjCode c r).dedup.length := by
    have h := Certificates.certificate15107.2.2.2.2.2
    simp only [czmInvolCheck, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      Bool.and_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq, decide_eq_true_eq] at h
    rcases h r hrm with (h | h) | h
    · exact absurd hrr h
    · exact absurd h hr1
    · exact h
  have hconj : ∀ c ∈ glList, ∃ v ∈ M, codeOf v = czmConjCode c r := by
    intro c hc
    let w : nK := ⟨nAutE hc, c, hc, fun _ => rfl⟩
    have hw : ∀ y, ((w : nK) : MulAut RuR) y = nAut c y := fun _ => rfl
    refine ⟨w * (t : nK) * w⁻¹, hMn.conj_mem _ t.2 w, eq_of_nAut_eq fun x => ?_⟩
    have hwinv : ((w⁻¹ : nK) : MulAut RuR) x = nAut (linInv c) x := by
      rw [Subgroup.coe_inv, MulAut.inv_apply, MulEquiv.symm_apply_eq, hw,
        nAut_linComp hc (linInv_mem hc), linComp_self_linInv hc, nAut_linId]
    rw [← codeOf_spec, Subgroup.coe_mul, Subgroup.coe_mul, MulAut.mul_apply, MulAut.mul_apply,
      hwinv, hu, hw, czmConjCode, ← nAut_linComp (linComp_mem hc hrm) (linInv_mem hc),
      ← nAut_linComp hc hrm]
  have : Fintype M := Fintype.ofFinite M
  have hsub : (glList.map fun c => czmConjCode c r).toFinset ⊆
      (Finset.univ : Finset M).image fun v : M => codeOf (v : nK) := by
    intro s hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hs)
    obtain ⟨v, hv, hvc⟩ := hconj c hc
    exact Finset.mem_image.2 ⟨⟨v, hv⟩, Finset.mem_univ _, hvc⟩
  have h1 := Finset.card_le_card hsub
  have h3 : ((Finset.univ : Finset M).image fun v : M => codeOf (v : nK)).card ≤ Nat.card M := by
    rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
    exact Finset.card_image_le
  rw [List.card_toFinset] at h1
  omega

theorem pCore_RuNModel :
    CFSG.Open.pCore 2 RuNModel = (SemidirectProduct.inl : RuR →* RuNModel).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite RuNModel := Nat.finite_of_card_ne_zero (by rw [card_RuNModel]; norm_num)
  refine le_antisymm ?_ ?_
  · have hN := CFSG.LieType.BorelTits.pCore_normal (G := RuNModel) 2
    have hp := CFSG.LieType.BorelTits.pCore_isPGroup (G := RuNModel) 2
    have hM := eq_bot_of_normal_isPGroup
      ((CFSG.Open.pCore 2 RuNModel).map SemidirectProduct.rightHom)
      (hN.map _ SemidirectProduct.rightHom_surjective) (hp.map _)
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    intro x hx
    rw [MonoidHom.mem_ker]
    have h : SemidirectProduct.rightHom x ∈
        (CFSG.Open.pCore 2 RuNModel).map SemidirectProduct.rightHom := ⟨x, hx, rfl⟩
    rwa [hM, mem_bot] at h
  · refine CFSG.LieType.BorelTits.le_pCore 2 ?_ ?_
    · rw [SemidirectProduct.range_inl_eq_ker_rightHom]
      infer_instance
    · refine IsPGroup.of_card (n := 11) ?_
      rw [show (2 : ℕ) ^ 11 = 2048 by norm_num, ← card_RuR]
      exact Nat.card_congr
        (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv.symm

end Core

theorem ruZ0_mem_ruM2 : ruZ0 ∈ ruM2 := pi7Word_mem_letterSub (by decide)

theorem czm_ruA0_le_ruM2 : ruA0 ≤ ruM2 := by
  have h : ∀ w ∈ ruA0Words, ∀ p ∈ w, p.1 ∈ ([0, 1, 2, 3, 4, 6] : List (Fin 7)) := by decide
  refine (closure_le _).2 ?_
  rintro _ ⟨w, hw, rfl⟩
  exact pi7Word_mem_letterSub (h w hw)

theorem letter_mem_ruM2 {i : Fin 7} (hi : i.val < 5) : (PresentedGroup.of i : Pi7) ∈ ruM2 := by
  refine mem_letterSub ?_
  revert hi
  revert i
  decide

section Pi7


theorem ruM2EquivModel_word {w : List (Fin 7 × Bool)} (hw : (renumber ruSub2 w).isSome = true)
    (m : ↥ruM2) (hm : (m : Pi7) = pi7Word w) : ruM2EquivModel m = toModel (nEvalW w) := by
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp hw
  have h1 := ruM2EquivModel_symm_apply (PresentedGroup.mk _ (FreeGroup.mk w'))
  rw [ruP2ToModel_mk hw', (lift_ruNImg w).2, ruP2ToPi7_mk hw'] at h1
  have e : ruM2EquivModel.symm (toModel (nEvalW w)) = m := Subtype.ext (h1.trans hm.symm)
  rw [← e, MulEquiv.apply_symm_apply]

theorem ruM2EquivModel_letter {i : Fin 7} (hi : i.val < 5) :
    ruM2EquivModel ⟨PresentedGroup.of i, letter_mem_ruM2 hi⟩ = ruNImg i := by
  have hw : (renumber ruSub2 [(i, true)]).isSome = true := by
    revert hi
    revert i
    decide
  rw [ruM2EquivModel_word hw _ (pi7Word_letter i).symm, ← (lift_ruNImg _).2]
  exact FreeGroup.lift_apply_of

theorem ruM2EquivModel_ruZ0 :
    ruM2EquivModel ⟨ruZ0, ruZ0_mem_ruM2⟩ = toModel czmZ0 := by
  rw [ruM2EquivModel_word (w := ruZ0Word) (by decide) _ rfl, nEvalW_ruZ0Word]

@[expose] noncomputable def czPre (S : Subgroup RuNModel) : Subgroup Pi7 :=
  (S.comap ruM2EquivModel.toMonoidHom).map ruM2.subtype

theorem mem_czPre {S : Subgroup RuNModel} {x : Pi7} :
    x ∈ czPre S ↔ ∃ h : x ∈ ruM2, ruM2EquivModel ⟨x, h⟩ ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hx⟩
    exact ⟨⟨x, h⟩, hx, rfl⟩

theorem czPre_le_ruM2 (S : Subgroup RuNModel) : czPre S ≤ ruM2 := fun _ hx =>
  (mem_czPre.1 hx).1

theorem czPre_mono {S T : Subgroup RuNModel} (h : S ≤ T) : czPre S ≤ czPre T :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem card_czPre (S : Subgroup RuNModel) : Nat.card (czPre S) = Nat.card S := by
  rw [czPre, Subgroup.card_map_of_injective ruM2.subtype_injective,
    Subgroup.comap_equiv_eq_map_symm', Subgroup.card_map_of_injective ruM2EquivModel.symm.injective]

theorem czPre_subgroupOf (S : Subgroup RuNModel) :
    (czPre S).subgroupOf ruM2 = S.comap ruM2EquivModel.toMonoidHom := by
  ext x
  rw [Subgroup.mem_subgroupOf, mem_czPre]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩

theorem mem_normalizer_czPre {S : Subgroup RuNModel} {g : Pi7} (hg : g ∈ ruM2)
    (h : ruM2EquivModel ⟨g, hg⟩ ∈ normalizer (S : Set RuNModel)) :
    g ∈ normalizer (czPre S : Set Pi7) := by
  refine mem_normalizer_iff.2 fun x => ?_
  by_cases hx : x ∈ ruM2
  · have hgx : g * x * g⁻¹ ∈ ruM2 := mul_mem (mul_mem hg hx) (inv_mem hg)
    have e : ruM2EquivModel ⟨g * x * g⁻¹, hgx⟩ = ruM2EquivModel ⟨g, hg⟩ *
        ruM2EquivModel ⟨x, hx⟩ * (ruM2EquivModel ⟨g, hg⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [mem_czPre, mem_czPre]
    constructor
    · rintro ⟨_, h1⟩
      refine ⟨hgx, ?_⟩
      rw [e]
      exact (mem_normalizer_iff.1 h _).1 h1
    · rintro ⟨_, h1⟩
      refine ⟨hx, (mem_normalizer_iff.1 h _).2 ?_⟩
      rw [← e]
      exact h1
  · have hgx : g * x * g⁻¹ ∉ ruM2 := fun h' => hx (by
      have := mul_mem (mul_mem (inv_mem hg) h') hg
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this)
    exact ⟨fun h' => absurd (czPre_le_ruM2 _ h') hx, fun h' => absurd (czPre_le_ruM2 _ h') hgx⟩

@[expose] noncomputable def czX0 : Subgroup Pi7 := czPre czmX0M

@[expose] noncomputable def czR0 : Subgroup Pi7 :=
  czPre (SemidirectProduct.inl : RuR →* RuNModel).range

theorem card_czX0 : Nat.card czX0 = 32 := by rw [czX0, card_czPre, card_czmX0M]

theorem czX0_le_czR0 : czX0 ≤ czR0 := czPre_mono (Subgroup.map_le_range _ _)

theorem czR0_le_ruM2 : czR0 ≤ ruM2 := czPre_le_ruM2 _

theorem czR0_subgroupOf_eq_pCore :
    czR0.subgroupOf ruM2 = CFSG.Open.pCore 2 ruM2 := by
  rw [czR0, czPre_subgroupOf, ← pCore_RuNModel, Subgroup.comap_equiv_eq_map_symm',
    CFSG.LieType.BorelTits.map_pCore_mulEquiv]

theorem ruA0_le_czX0 :
    ruA0 ≤ czX0 := fun x hx => by
  refine mem_czPre.2 ⟨czm_ruA0_le_ruM2 hx, ?_⟩
  have h := (mem_ruA0_iff_model ⟨x, czm_ruA0_le_ruM2 hx⟩).1 hx
  exact Subgroup.map_mono A1R_le_czmX0R h

theorem mem_ruA0_iff_comm_czR0
    {m : Pi7} (hm : m ∈ czR0) : (∀ r ∈ czR0, m * r = r * m) ↔ m ∈ ruA0 := by
  obtain ⟨hm2, a, ha⟩ := mem_czPre.1 hm
  have hmA : m ∈ ruA0 ↔ SemidirectProduct.inl a ∈ A1model := by
    rw [ha]
    exact mem_ruA0_iff_model ⟨m, hm2⟩
  have hA : SemidirectProduct.inl a ∈ A1model ↔ a ∈ center RuR := by
    rw [center_RuR, A1model]
    exact ⟨fun ⟨b, hb, hba⟩ => SemidirectProduct.inl_injective hba ▸ hb, fun h => ⟨a, h, rfl⟩⟩
  rw [hmA, hA, mem_center_iff]
  constructor
  · intro h b
    have hr : ((ruM2EquivModel.symm (SemidirectProduct.inl b) : ↥ruM2) : Pi7) ∈ czR0 :=
      mem_czPre.2 ⟨Subtype.coe_prop _, ⟨b, (MulEquiv.apply_symm_apply _ _).symm⟩⟩
    have e := congrArg ruM2EquivModel (Subtype.ext (h _ hr) :
      (⟨m, hm2⟩ : ↥ruM2) * ruM2EquivModel.symm (SemidirectProduct.inl b) =
        ruM2EquivModel.symm (SemidirectProduct.inl b) * ⟨m, hm2⟩)
    rw [map_mul, map_mul, ← ha, MulEquiv.apply_symm_apply, ← map_mul, ← map_mul] at e
    exact (SemidirectProduct.inl_injective e).symm
  · intro h r hr
    obtain ⟨hr2, b, hb⟩ := mem_czPre.1 hr
    have e : ruM2EquivModel (⟨m, hm2⟩ * ⟨r, hr2⟩) = ruM2EquivModel (⟨r, hr2⟩ * ⟨m, hm2⟩) := by
      rw [map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul, h b]
    exact congrArg Subtype.val (ruM2EquivModel.injective e)

end Pi7

theorem ruM12_le_of_letters {H : Subgroup Pi7}
    (h : ∀ i : Fin 7, i.val < 5 → (PresentedGroup.of i : Pi7) ∈ H) : ruM12 ≤ H := by
  have key : ∀ i : Fin 7, i ∈ ([0, 1, 2, 3, 4] : List (Fin 7)) → i.val < 5 := by decide
  refine (closure_le _).2 ?_
  rintro _ ⟨i, hi, rfl⟩
  exact h i (key i hi)

section M12


theorem ruM12_le_normalizer_czX0 : ruM12 ≤ normalizer (czX0 : Set Pi7) :=
  ruM12_le_of_letters fun i hi => mem_normalizer_czPre (letter_mem_ruM2 hi) (by
    rw [ruM2EquivModel_letter hi]
    exact ruNImg_mem_normalizer hi)

theorem ruM12_le_centralizer_ruZ0 : ruM12 ≤ centralizer ({ruZ0} : Set Pi7) :=
  ruM12_le_of_letters fun i hi => by
    rw [mem_centralizer_singleton_iff]
    have e : ruM2EquivModel (⟨_, letter_mem_ruM2 hi⟩ * ⟨ruZ0, ruZ0_mem_ruM2⟩) =
        ruM2EquivModel (⟨ruZ0, ruZ0_mem_ruM2⟩ * ⟨_, letter_mem_ruM2 hi⟩) := by
      rw [map_mul, map_mul, ruM2EquivModel_letter hi, ruM2EquivModel_ruZ0]
      exact ruNImg_mul_czmZ0 hi
    exact congrArg Subtype.val (ruM2EquivModel.injective e)

theorem ruA0Elt_injective
    {e e' : ℕ} (he : e < 8) (he' : e' < 8) (h : ruA0Elt e = ruA0Elt e') : e = e' := by
  by_contra hne
  have hne' : e ^^^ e' ≠ 0 := fun h0 => hne (xor_eq_zero_iff.mp h0)
  apply ruA0Elt_ne_one (xor_lt_eight he he') hne'
  rw [← ruA0Elt_mul he he', h, ruA0Elt_mul he' he', Nat.xor_self, ruA0Elt_zero]

theorem mem_ruM12_iff_comm_ruZ0
    {m : Pi7} (hm : m ∈ ruM2) :
    m * ruZ0 = ruZ0 * m ↔ m ∈ ruM12 := by
  have hfin : Finite Pi7 := card_pi7_le.1
  have hle : ruM12 ≤ ruM2 ⊓ centralizer ({ruZ0} : Set Pi7) :=
    le_inf (letterSub_mono (by decide)) ruM12_le_centralizer_ruZ0
  have hcardM2 : Nat.card ruM2 = 344064 := by
    rw [Nat.card_congr ruM2EquivModel.toEquiv, card_RuNModel]
  let t : Fin 7 → Pi7 := fun k => pi7Word (ruAlignTransWords.getD k [])
  have ht : ∀ k, t k ∈ ruM2 := fun k => pi7Word_mem_letterSub (ruAlignTransWords_letters k k.2)
  have hd : ∀ i j, (t i)⁻¹ * t j ∈ ruM2 ⊓ centralizer ({ruZ0} : Set Pi7) → i = j := by
    intro i j h
    have hc : (t i)⁻¹ * t j * ruZ0 = ruZ0 * ((t i)⁻¹ * t j) :=
      mem_centralizer_singleton_iff.1 h.2
    have e : t j * ruZ0 * (t j)⁻¹ = t i * ruZ0 * (t i)⁻¹ := by
      calc t j * ruZ0 * (t j)⁻¹ = t i * ((t i)⁻¹ * t j * ruZ0) * (t j)⁻¹ := by group
        _ = t i * (ruZ0 * ((t i)⁻¹ * t j)) * (t j)⁻¹ := by rw [hc]
        _ = t i * ruZ0 * (t i)⁻¹ := by group
    rw [← ruA0Elt_eq_conj j.2, ← ruA0Elt_eq_conj i.2] at e
    have := ruA0Elt_injective (by omega) (by omega) e
    exact Fin.ext (by omega)
  have h7 := card_mul_le_of_distinct inf_le_left t ht hd
  rw [hcardM2] at h7
  have hC : ruM2 ⊓ centralizer ({ruZ0} : Set Pi7) = ruM12 :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_ruM12]; omega)).symm
  constructor
  · intro h
    rw [← hC]
    exact ⟨hm, mem_centralizer_singleton_iff.2 h⟩
  · intro h
    exact mem_centralizer_singleton_iff.1 (ruM12_le_centralizer_ruZ0 h)

end M12

end CFSG.ComponentClassification.GMS78.RuCz
