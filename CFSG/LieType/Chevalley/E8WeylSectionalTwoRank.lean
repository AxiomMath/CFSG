module

public import CFSG.LieType.Chevalley.E8FrameLines
public import Certificates.Certificate20190
public import CFSG.GH74.SectionalRankCoinvariant
public import CFSG.LieType.Chevalley.SectionalTwoRankMonomial
public import CFSG.RankThree.Chevalley.EWeylLengthPolynomials

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.GH74 E8Frame E8Lines

theorem e8Frame_gensCheck : gensCheck () = true :=
  Certificates.certificate20190.1

theorem e8Frame_reflCheck : reflCheck () = true :=
  Certificates.certificate20190.2.1

theorem e8Frame_frameCheck : frameCheck () = true :=
  Certificates.certificate20190.2.2.1

theorem e8Frame_lineCheck : lineCheck () = true :=
  Certificates.certificate20190.2.2.2

namespace E8Weyl

theorem wordAct_eq (ω : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    wordAct ω v = (coxeterSystem .E8).wordProd ω • v := by
  induction ω with
  | nil => simp [wordAct]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, mul_smul, ← ih]
    exact (simple_smul i _).symm

theorem one_mem_closureList {G : Type} [Group G] [DecidableEq G] (gens : List G) (n : ℕ) :
    (1 : G) ∈ closureList gens n := by
  induction n with
  | zero => simp [closureList]
  | succ n ih =>
    simp only [closureList, Function.iterate_succ_apply'] at ih ⊢
    exact List.mem_dedup.2 (List.mem_append_left _ ih)

theorem mem_closure_of_mem_closureList {G : Type} [Group G] [DecidableEq G] (gens : List G)
    (n : ℕ) : ∀ g ∈ closureList gens n, g ∈ Subgroup.closure {x | x ∈ gens} := by
  induction n with
  | zero =>
    intro g hg
    simp only [closureList, Function.iterate_zero, id, List.mem_singleton] at hg
    rw [hg]
    exact one_mem _
  | succ n ih =>
    intro g hg
    simp only [closureList, Function.iterate_succ_apply'] at hg
    simp only [List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map] at hg
    rcases hg with hg | ⟨h, hh, s, hs, rfl⟩
    · exact ih g hg
    · exact mul_mem (ih h hh) (Subgroup.subset_closure hs)

@[expose] def listSubgroup {G : Type} [Group G] (L : List G) (h1 : 1 ∈ L)
    (hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L) (hinv : ∀ a ∈ L, a⁻¹ ∈ L) : Subgroup G where
  carrier := {g | g ∈ L}
  mul_mem' ha hb := hmul _ ha _ hb
  one_mem' := h1
  inv_mem' ha := hinv _ ha

theorem mem_listSubgroup {G : Type} [Group G] {L : List G} {h1 : 1 ∈ L}
    {hmul : ∀ a ∈ L, ∀ b ∈ L, a * b ∈ L} {hinv : ∀ a ∈ L, a⁻¹ ∈ L} {g : G} :
    g ∈ listSubgroup L h1 hmul hinv ↔ g ∈ L :=
  Iff.rfl

theorem frameNeg_lo (i : Fin 8) : frameNeg (lo i) = ⟨i.val + 8, by omega⟩ := by
  apply Fin.ext
  rw [frameNeg_val, lo_val]
  show (i.val + 8) % 16 = i.val + 8
  omega

section Contract


theorem frameGens_spec : ∀ x ∈ frameGens,
    (∀ k, (coxeterSystem .E8).wordProd x.1 • frameVec k = frameVec (x.2.1 k)) ∧
      x.2.1 * frameNeg = frameNeg * x.2.1 ∧ ∀ i, lineFun x.2.1 i = x.2.2 i := by
  have h := e8Frame_gensCheck
  simp only [gensCheck, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies] at h
  intro x hx
  obtain ⟨⟨h1, h2⟩, h3⟩ := h x hx
  exact ⟨fun k => (wordAct_eq _ _).symm.trans (h1 k), h2, fun i => Fin.ext (h3 i)⟩

theorem frameGens_refl (i : Fin 8) : ∃ x ∈ frameGens, x.2.1 = Equiv.swap (lo i) (frameNeg (lo i)) := by
  have h := e8Frame_reflCheck
  simp only [reflCheck, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies] at h
  rw [frameNeg_lo]
  exact h i

theorem frameVec_injective : Function.Injective frameVec := by
  have h := e8Frame_frameCheck
  simp only [frameCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies] at h
  exact fun k k' hk => h.1 k k' hk

theorem frameSpan (j : Fin Tag.E8.rank) :
    (∑ i : Fin 8, frameCoeff j i • frameRoot i) = (16 : ℤ) • Pi.single j 1 := by
  have h := e8Frame_frameCheck
  simp only [frameCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_implies] at h
  exact h.2 j

theorem lineCheck_spec :
    (lineList ()).length = 64 ∧ (lineList ()).Nodup ∧
    (∀ a ∈ lineList (), ∀ b ∈ lineList (), a * b ∈ lineList ()) ∧
    (∀ a ∈ lineList (), a⁻¹ ∈ lineList ()) ∧
    (∀ x ∈ frameGens, x.2.2 ∈ lineList ()) ∧
    (transList ()).length = 8 ∧ (transList ()).Nodup ∧
    (∀ a ∈ transList (), ∀ b ∈ transList (), a * b ∈ transList ()) ∧
    (∀ a ∈ transList (), a⁻¹ ∈ transList ()) ∧
    (∀ a ∈ transList (), a ∈ lineList ()) ∧
    (∀ b ∈ lineList (), ∀ a ∈ transList (), b * a * b⁻¹ ∈ transList ()) ∧
    (∃ b ∈ lineList (), b * b ∉ transList ()) ∧
    (∀ b ∈ lineList (), b = 1 ∨ fixedSigns b ≤ 2 ^ 6) ∧
    (∀ a ∈ transList (), a = 1 ∨ fixedSigns a ≤ 2 ^ 4) := by
  have h := e8Frame_lineCheck
  simp only [lineCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, and_assoc] at h
  exact h

end Contract

abbrev lineGroup : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure {σ | ∃ x ∈ frameGens, σ = x.2.2}

abbrev transGroup : Subgroup (Equiv.Perm (Fin 8)) := Subgroup.closure {σ | σ ∈ transList ()}

section Contract


theorem mem_lineGroup_iff (σ : Equiv.Perm (Fin 8)) : σ ∈ lineGroup ↔ σ ∈ lineList () := by
  obtain ⟨-, -, hmul, hinv, hgen, -⟩ := lineCheck_spec
  constructor
  · intro hσ
    have hle : lineGroup ≤ listSubgroup (lineList ()) (one_mem_closureList _ _) hmul hinv := by
      rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      exact hgen x hx
    exact mem_listSubgroup.1 (hle hσ)
  · intro hσ
    have h := mem_closure_of_mem_closureList _ _ σ hσ
    have hset : {x | x ∈ frameGens.map fun g => g.2.2} = {σ | ∃ x ∈ frameGens, σ = x.2.2} := by
      ext σ
      simp only [Set.mem_setOf_eq, List.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    rwa [hset] at h

theorem mem_transGroup_iff (σ : Equiv.Perm (Fin 8)) : σ ∈ transGroup ↔ σ ∈ transList () := by
  obtain ⟨-, -, -, -, -, -, -, hmul, hinv, -⟩ := lineCheck_spec
  constructor
  · intro hσ
    have h1 : (1 : Equiv.Perm (Fin 8)) ∈ transList () := one_mem_closureList _ _
    have hle : transGroup ≤ listSubgroup (transList ()) h1 hmul hinv :=
      (Subgroup.closure_le _).2 fun σ hσ => hσ
    exact mem_listSubgroup.1 (hle hσ)
  · exact fun hσ => Subgroup.subset_closure hσ

theorem card_lineGroup : Nat.card lineGroup = 64 := by
  obtain ⟨hlen, hnd, -⟩ := lineCheck_spec
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ =>
      (mem_lineGroup_iff σ).trans List.mem_toFinset.symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, hlen]

theorem card_transGroup : Nat.card transGroup = 8 := by
  obtain ⟨-, -, -, -, -, hlen, hnd, -⟩ := lineCheck_spec
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun σ =>
      (mem_transGroup_iff σ).trans List.mem_toFinset.symm),
    Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnd, hlen]

theorem transGroup_le_lineGroup : transGroup ≤ lineGroup := fun σ hσ => by
  obtain ⟨-, -, -, -, -, -, -, -, -, hTB, -⟩ := lineCheck_spec
  exact (mem_lineGroup_iff σ).2 (hTB σ ((mem_transGroup_iff σ).1 hσ))

theorem transGroup_normal : (transGroup.subgroupOf lineGroup).Normal := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hnorm, -⟩ := lineCheck_spec
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact (mem_transGroup_iff _).2 (hnorm _ ((mem_lineGroup_iff _).1 g.2) _
    ((mem_transGroup_iff _).1 hn))

theorem sectionalTwoRankLE_lineGroup : SectionalTwoRankLE lineGroup 5 := by
  haveI := transGroup_normal
  set N := transGroup.subgroupOf lineGroup
  have hN : Nat.card N = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe transGroup_le_lineGroup).toEquiv,
      card_transGroup]
  have hQ : Nat.card (lineGroup ⧸ N) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [card_lineGroup, hN] at h
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨b, hb, hbb⟩, -⟩ := lineCheck_spec
  have hx : (QuotientGroup.mk (⟨b, (mem_lineGroup_iff b).2 hb⟩ : lineGroup) :
      lineGroup ⧸ N) ^ 2 ≠ 1 := by
    rw [← QuotientGroup.mk_pow, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, pow_two, mem_transGroup_iff]
    exact hbb
  have h3 : SectionalTwoRankLE N 3 := sectionalTwoRankLE_of_not_two_pow_dvd (by
    rw [hN]
    norm_num)
  exact SectionalTwoRankLE.of_normal N h3 (sectionalTwoRankLE_two_of_card_eq_eight hQ hx)

theorem exists_finset_of_le_lineGroup {R : Subgroup (Equiv.Perm (Fin 8))} (hR : IsPGroup 2 R)
    (hRB : R ≤ lineGroup) :
    ∃ s : Finset (Equiv.Perm (Fin 8)), s.card ≤ 5 ∧ Subgroup.closure (s : Set _) = R := by
  classical
  have hR' : IsPGroup 2 (R.subgroupOf lineGroup) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRB).symm
  obtain ⟨s, hs, hsR⟩ := sectionalTwoRankLE_lineGroup _ hR'
  refine ⟨s.image lineGroup.subtype, Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsR, Subgroup.map_subgroupOf_eq_of_le hRB]

theorem exists_finset_of_inf_transGroup {R : Subgroup (Equiv.Perm (Fin 8))}
    (hR : IsPGroup 2 R) (hRB : R ≤ lineGroup) (hRT : ∀ σ ∈ R, σ ∈ transGroup → σ = 1) :
    ∃ s : Finset (Equiv.Perm (Fin 8)), s.card ≤ 2 ∧ Subgroup.closure (s : Set _) = R := by
  classical
  haveI := transGroup_normal
  set N := transGroup.subgroupOf lineGroup
  have hN : Nat.card N = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe transGroup_le_lineGroup).toEquiv,
      card_transGroup]
  have hQ : Nat.card (lineGroup ⧸ N) = 8 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [card_lineGroup, hN] at h
    omega
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, ⟨b, hb, hbb⟩, -⟩ := lineCheck_spec
  have hx : (QuotientGroup.mk (⟨b, (mem_lineGroup_iff b).2 hb⟩ : lineGroup) :
      lineGroup ⧸ N) ^ 2 ≠ 1 := by
    rw [← QuotientGroup.mk_pow, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow, pow_two, mem_transGroup_iff]
    exact hbb
  have h2 := sectionalTwoRankLE_two_of_card_eq_eight hQ hx
  set R' := R.subgroupOf lineGroup
  let f : R' →* lineGroup ⧸ N := (QuotientGroup.mk' N).comp R'.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro r hr
    rw [MonoidHom.mem_ker] at hr
    have hrN : (r : lineGroup) ∈ N := (QuotientGroup.eq_one_iff _).1 hr
    rw [Subgroup.mem_subgroupOf] at hrN
    have hrR : ((r : lineGroup) : Equiv.Perm (Fin 8)) ∈ R := r.2
    have h1 := hRT _ hrR hrN
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext h1)
  have hR' : IsPGroup 2 (⊤ : Subgroup R') :=
    (hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRB).symm).of_equiv Subgroup.topEquiv.symm
  obtain ⟨s, hs, hsR⟩ := SectionalTwoRankLE.of_injective f hf h2 ⊤ hR'
  refine ⟨s.image (lineGroup.subtype.comp R'.subtype), Finset.card_image_le.trans hs, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hsR, ← MonoidHom.range_eq_map,
    MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_subgroupOf_eq_of_le hRB]

end Contract

abbrev frameGroup : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure {p | ∃ x ∈ frameGens, p = x.2.1}

theorem lineFun_swap (i j : Fin 8) : lineFun (Equiv.swap (lo i) (frameNeg (lo i))) j = j := by
  apply Fin.ext
  show (Equiv.swap (lo i) (frameNeg (lo i)) (lo j)).val % 8 = j.val
  have hj := j.isLt
  by_cases hij : j = i
  · subst hij
    rw [Equiv.swap_apply_left, frameNeg_val, lo_val]
    omega
  · rw [Equiv.swap_apply_of_ne_of_ne, lo_val]
    · exact Nat.mod_eq_of_lt hj
    · intro h
      exact hij (Fin.ext (by simpa using congrArg Fin.val h))
    · intro h
      have := congrArg Fin.val h
      rw [frameNeg_val, lo_val, lo_val] at this
      have := i.isLt
      omega

theorem signVec_swap (i : Fin 8) :
    signVec (Equiv.swap (lo i) (frameNeg (lo i))) = Pi.single i 1 := by
  funext j
  by_cases hij : j = i
  · subst hij
    simp [signVec, Equiv.swap_apply_left, frameNeg_lo_ne]
  · have h1 : lo j ≠ lo i := fun h => hij (Fin.ext (by simpa using congrArg Fin.val h))
    have h2 : lo j ≠ frameNeg (lo i) := by
      intro h
      have := congrArg Fin.val h
      rw [frameNeg_val, lo_val, lo_val] at this
      have := i.isLt
      have := j.isLt
      omega
    simp [signVec, Equiv.swap_apply_of_ne_of_ne h1 h2, Pi.single_apply, hij]

section Contract


theorem frameGroup_le_negCent : frameGroup ≤ negCent := by
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.2 (frameGens_spec x hx).2.1

theorem comm_frameNeg (g : frameGroup) : (g : Equiv.Perm (Fin 16)) * frameNeg = frameNeg * g :=
  comm_of_mem_negCent (frameGroup_le_negCent g.2)

@[expose] def frameLine : frameGroup →* Equiv.Perm (Fin 8) :=
  lineHom.comp (Subgroup.inclusion frameGroup_le_negCent)

theorem coe_frameLine (g : frameGroup) : ⇑(frameLine g) = lineFun g := rfl

theorem mem_ker_frameLine (g : frameGroup) : g ∈ frameLine.ker ↔ ∀ i, lineFun g i = i :=
  (MonoidHom.mem_ker).trans (lineHom_eq_one_iff _)

theorem range_frameLine : frameLine.range = lineGroup := by
  rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage, MonoidHom.map_closure]
  congr 1
  ext σ
  constructor
  · rintro ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine ⟨x, hx, Equiv.ext fun i => ?_⟩
    rw [coe_frameLine, hgx]
    exact (frameGens_spec x hx).2.2 i
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x.2.1, Subgroup.subset_closure ⟨x, hx, rfl⟩⟩, ⟨x, hx, rfl⟩, Equiv.ext fun i => ?_⟩
    exact (frameGens_spec x hx).2.2 i

theorem frameLine_mem_lineList (g : frameGroup) : frameLine g ∈ lineList () :=
  (mem_lineGroup_iff _).1 (range_frameLine ▸ (⟨g, rfl⟩ : frameLine g ∈ frameLine.range))

@[expose] def kerSign : frameLine.ker →* Multiplicative (Fin 8 → ZMod 2) where
  toFun a := Multiplicative.ofAdd (signVec ((a : frameGroup) : Equiv.Perm (Fin 16)))
  map_one' := by
    have h : signVec 1 = 0 := by
      funext i
      simp [signVec]
    simp only [OneMemClass.coe_one, h, ofAdd_zero]
  map_mul' a b := by
    simp only [Subgroup.coe_mul]
    rw [signVec_mul (comm_frameNeg a) ((mem_ker_frameLine _).1 a.2)
      ((mem_ker_frameLine _).1 b.2), ofAdd_add]

theorem kerSign_injective : Function.Injective kerSign := fun a b h =>
  Subtype.ext (Subtype.ext (eq_of_signVec_eq (comm_frameNeg a) (comm_frameNeg b)
    ((mem_ker_frameLine _).1 a.2) ((mem_ker_frameLine _).1 b.2)
    (Multiplicative.ofAdd.injective h)))

theorem card_ker_frameLine : Nat.card frameLine.ker = 2 ^ 8 := by
  have hsingle : ∀ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)) ∈ kerSign.range := by
    intro i
    obtain ⟨x, hx, hxs⟩ := frameGens_refl i
    have hmem : x.2.1 ∈ frameGroup := Subgroup.subset_closure ⟨x, hx, rfl⟩
    have hker : (⟨x.2.1, hmem⟩ : frameGroup) ∈ frameLine.ker := by
      rw [mem_ker_frameLine]
      intro j
      show lineFun x.2.1 j = j
      rw [hxs]
      exact lineFun_swap i j
    refine ⟨⟨_, hker⟩, ?_⟩
    show Multiplicative.ofAdd (signVec x.2.1) = _
    rw [hxs, signVec_swap]
  have hrange : kerSign.range = ⊤ := by
    rw [eq_top_iff]
    intro δ _
    have hdecomp : Multiplicative.toAdd δ = ∑ i, Pi.single i (Multiplicative.toAdd δ i) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [← ofAdd_toAdd δ, hdecomp, ofAdd_sum]
    refine Subgroup.prod_mem _ fun i _ => ?_
    have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h01 (Multiplicative.toAdd δ i) with h | h <;> rw [h]
    · rw [Pi.single_zero, ofAdd_zero]
      exact one_mem _
    · exact hsingle i
  calc Nat.card frameLine.ker = Nat.card kerSign.range :=
        Nat.card_congr (MonoidHom.ofInjective kerSign_injective).toEquiv
    _ = Nat.card (⊤ : Subgroup (Multiplicative (Fin 8 → ZMod 2))) := by rw [hrange]
    _ = Nat.card (Multiplicative (Fin 8 → ZMod 2)) := Nat.card_congr Subgroup.topEquiv.toEquiv
    _ = 2 ^ 8 := by
      rw [Nat.card_eq_fintype_card]
      simp

theorem card_frameGroup : Nat.card frameGroup = 2 ^ 14 := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup frameLine.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange frameLine).toEquiv, range_frameLine,
    card_lineGroup, card_ker_frameLine] at h
  rw [h]
  norm_num

theorem card_centralizer_le (Q : Subgroup frameGroup) (t : frameGroup) :
    Nat.card ↥(Q ⊓ frameLine.ker ⊓ Subgroup.centralizer ({t} : Set frameGroup)) ≤
      fixedSigns (frameLine t) := by
  classical
  let F := Finset.univ.filter fun δ : Fin 8 → ZMod 2 => δ ∘ ⇑(frameLine t) = δ
  let f : ↥(Q ⊓ frameLine.ker ⊓ Subgroup.centralizer ({t} : Set frameGroup)) → F := fun a =>
    ⟨signVec ((a : frameGroup) : Equiv.Perm (Fin 16)), by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hat : (a : frameGroup) * t = t * a :=
        Subgroup.mem_centralizer_singleton_iff.1 a.2.2
      exact signVec_comp_lineFun (comm_frameNeg a) ((mem_ker_frameLine _).1 a.2.1.2)
        (comm_frameNeg t) (congrArg Subtype.val hat)⟩
  have hf : Function.Injective f := fun a b hab =>
    Subtype.ext (Subtype.ext (eq_of_signVec_eq (comm_frameNeg a) (comm_frameNeg b)
      ((mem_ker_frameLine _).1 a.2.1.2) ((mem_ker_frameLine _).1 b.2.1.2)
      (congrArg Subtype.val hab)))
  calc Nat.card _ ≤ Nat.card F := Nat.card_le_card_of_injective f hf
    _ = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = fixedSigns (frameLine t) := rfl

theorem sectionalTwoRankLE_frameGroup : SectionalTwoRankLE frameGroup 9 := by
  classical
  intro Q hQ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hfixB, hfixT⟩ := lineCheck_spec
  have hA : ∀ a ∈ Q ⊓ frameLine.ker, ∀ b ∈ Q ⊓ frameLine.ker, a * b = b * a := by
    intro a ha b hb
    have h2 : kerSign ⟨a, ha.2⟩ * kerSign ⟨b, hb.2⟩ = kerSign ⟨b, hb.2⟩ * kerSign ⟨a, ha.2⟩ :=
      mul_comm _ _
    rw [← map_mul, ← map_mul] at h2
    exact congrArg Subtype.val (kerSign_injective h2)
  have hmapB : Q.map frameLine ≤ lineGroup :=
    (Subgroup.map_le_range frameLine Q).trans range_frameLine.le
  have hQm : IsPGroup 2 (Q.map frameLine) := hQ.map frameLine
  by_cases hT : ∃ t ∈ Q, frameLine t ∈ transGroup ∧ frameLine t ≠ 1
  · obtain ⟨t, htQ, htT, ht1⟩ := hT
    have hk : Nat.card ↥(Q ⊓ frameLine.ker ⊓ Subgroup.centralizer ({t} : Set frameGroup)) ≤
        2 ^ 4 :=
      (card_centralizer_le Q t).trans
        ((hfixT _ ((mem_transGroup_iff _).1 htT)).resolve_left ht1)
    exact exists_finset_closure_eq_of_coinvariant frameLine hQ hA htQ
      (exists_finset_of_le_lineGroup hQm hmapB) hk
  · push Not at hT
    by_cases h1 : ∃ t ∈ Q, frameLine t ≠ 1
    · obtain ⟨t, htQ, ht1⟩ := h1
      have hRT : ∀ σ ∈ Q.map frameLine, σ ∈ transGroup → σ = 1 := by
        rintro _ ⟨u, huQ, rfl⟩ huT
        exact hT u huQ huT
      have hk : Nat.card ↥(Q ⊓ frameLine.ker ⊓ Subgroup.centralizer ({t} : Set frameGroup)) ≤
          2 ^ 6 :=
        (card_centralizer_le Q t).trans ((hfixB _ (frameLine_mem_lineList t)).resolve_left ht1)
      obtain ⟨s, hs, hsQ⟩ := exists_finset_closure_eq_of_coinvariant frameLine hQ hA htQ
        (exists_finset_of_inf_transGroup hQm hmapB hRT) hk
      exact ⟨s, hs.trans (by norm_num), hsQ⟩
    · push Not at h1
      have hbot : Q.map frameLine = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨u, huQ, rfl⟩
        exact (Subgroup.mem_bot).2 (h1 u huQ)
      have hk : Nat.card ↥(Q ⊓ frameLine.ker ⊓ Subgroup.centralizer ({1} : Set frameGroup)) ≤
          2 ^ 8 :=
        (Subgroup.card_le_of_le (inf_le_left.trans inf_le_right)).trans card_ker_frameLine.le
      obtain ⟨s, hs, hsQ⟩ := exists_finset_closure_eq_of_coinvariant (m := 0) frameLine hQ hA
        (one_mem Q) ⟨∅, by simp, by simp [hbot]⟩ hk
      exact ⟨s, hs.trans (by norm_num), hsQ⟩

end Contract

@[expose] def frameStab : Subgroup (WeylGroup .E8) where
  carrier := {w | (∀ k, ∃ k', w • frameVec k = frameVec k') ∧
    ∀ k, ∃ k', w⁻¹ • frameVec k = frameVec k'}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · obtain ⟨k1, h1⟩ := hb1 k
      obtain ⟨k2, h2⟩ := ha1 k1
      exact ⟨k2, by rw [mul_smul, h1, h2]⟩
    · obtain ⟨k1, h1⟩ := ha2 k
      obtain ⟨k2, h2⟩ := hb2 k1
      exact ⟨k2, by rw [mul_inv_rev, mul_smul, h1, h2]⟩
  one_mem' := ⟨fun k => ⟨k, one_smul _ _⟩, fun k => ⟨k, by rw [inv_one, one_smul]⟩⟩
  inv_mem' := by
    rintro a ⟨h1, h2⟩
    exact ⟨h2, by simpa using h1⟩

@[expose] def frameIdx (v : Fin Tag.E8.rank → ℤ) : Fin 16 :=
  ((List.finRange 16).find? fun k => decide (frameVec k = v)).getD 0

theorem frameVec_frameIdx {v : Fin Tag.E8.rank → ℤ} (h : ∃ k, frameVec k = v) :
    frameVec (frameIdx v) = v := by
  obtain ⟨k, rfl⟩ := h
  have hsome : ((List.finRange 16).find? fun k' => decide (frameVec k' = frameVec k)).isSome := by
    rw [List.find?_isSome]
    exact ⟨k, List.mem_finRange k, by simp⟩
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 hsome
  unfold frameIdx
  rw [hk', Option.getD_some]
  simpa using List.find?_some hk'

theorem frameVec_lo (i : Fin 8) : frameVec (lo i) = frameRoot i := by
  have hi : (lo i).val < 8 := by
    rw [lo_val]
    exact i.isLt
  have hmod : (⟨(lo i).val % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8) = i := by
    apply Fin.ext
    show (lo i).val % 8 = i.val
    rw [lo_val]
    exact Nat.mod_eq_of_lt i.isLt
  simp only [frameVec, hi, if_true, hmod]

section Contract


theorem frameVec_framePerm (w : frameStab) (k : Fin 16) :
    frameVec (frameIdx ((w : WeylGroup .E8) • frameVec k)) = (w : WeylGroup .E8) • frameVec k :=
  frameVec_frameIdx (by
    obtain ⟨k', h⟩ := w.2.1 k
    exact ⟨k', h.symm⟩)

theorem frameVec_framePerm_inv (w : frameStab) (k : Fin 16) :
    frameVec (frameIdx ((w : WeylGroup .E8)⁻¹ • frameVec k)) =
      (w : WeylGroup .E8)⁻¹ • frameVec k :=
  frameVec_frameIdx (by
    obtain ⟨k', h⟩ := w.2.2 k
    exact ⟨k', h.symm⟩)

@[expose] noncomputable def framePerm (w : frameStab) : Equiv.Perm (Fin 16) where
  toFun k := frameIdx ((w : WeylGroup .E8) • frameVec k)
  invFun k := frameIdx ((w : WeylGroup .E8)⁻¹ • frameVec k)
  left_inv k := by
    apply frameVec_injective
    have h1 := frameVec_framePerm w k
    have h2 : ∃ k', frameVec k' = (w : WeylGroup .E8)⁻¹ •
        frameVec (frameIdx ((w : WeylGroup .E8) • frameVec k)) := ⟨k, by rw [h1, inv_smul_smul]⟩
    rw [frameVec_frameIdx h2, h1, inv_smul_smul]
  right_inv k := by
    apply frameVec_injective
    have h1 := frameVec_framePerm_inv w k
    have h2 : ∃ k', frameVec k' = (w : WeylGroup .E8) •
        frameVec (frameIdx ((w : WeylGroup .E8)⁻¹ • frameVec k)) := ⟨k, by rw [h1, smul_inv_smul]⟩
    rw [frameVec_frameIdx h2, h1, smul_inv_smul]

theorem frameVec_framePerm_apply (w : frameStab) (k : Fin 16) :
    frameVec (framePerm w k) = (w : WeylGroup .E8) • frameVec k :=
  frameVec_framePerm w k

@[expose] noncomputable def framePermHom : frameStab →* Equiv.Perm (Fin 16) where
  toFun := framePerm
  map_one' := Equiv.ext fun k => frameVec_injective (by
    rw [frameVec_framePerm_apply, OneMemClass.coe_one, one_smul]
    rfl)
  map_mul' a b := Equiv.ext fun k => frameVec_injective (by
    rw [frameVec_framePerm_apply, Equiv.Perm.mul_apply, frameVec_framePerm_apply,
      frameVec_framePerm_apply, Subgroup.coe_mul, mul_smul])

theorem framePermHom_injective :
    Function.Injective framePermHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  rw [MonoidHom.mem_ker] at hw
  have hfix : ∀ k, (w : WeylGroup .E8) • frameVec k = frameVec k := fun k => by
    rw [← frameVec_framePerm_apply]
    exact congrArg frameVec (congrFun (congrArg DFunLike.coe hw) k)
  have hroot : ∀ i, (w : WeylGroup .E8) • frameRoot i = frameRoot i := fun i => by
    rw [← frameVec_lo, hfix]
  have hsingle : ∀ j : Fin Tag.E8.rank, (w : WeylGroup .E8) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) =
      (1 : WeylGroup .E8) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := fun j => by
    rw [one_smul]
    have h16 : (16 : ℤ) • ((w : WeylGroup .E8) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) =
        (16 : ℤ) • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) := by
      rw [← smul_comm, ← frameSpan j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_comm, hroot]
    exact smul_right_injective (Fin Tag.E8.rank → ℤ) (by norm_num : (16 : ℤ) ≠ 0) h16
  rw [Subgroup.mem_bot]
  exact Subtype.ext (ext_single hsingle)

theorem wordProd_mem_frameStab {x} (hx : x ∈ frameGens) :
    (coxeterSystem .E8).wordProd x.1 ∈ frameStab := by
  have h := (frameGens_spec x hx).1
  refine ⟨fun k => ⟨x.2.1 k, h k⟩, fun k => ⟨x.2.1⁻¹ k, ?_⟩⟩
  rw [inv_smul_eq_iff, h, ← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply]

theorem framePermHom_wordProd {x} (hx : x ∈ frameGens) :
    framePermHom ⟨_, wordProd_mem_frameStab hx⟩ = x.2.1 :=
  Equiv.ext fun k => frameVec_injective (by
    show frameVec (framePerm _ k) = _
    rw [frameVec_framePerm_apply]
    exact (frameGens_spec x hx).1 k)

end Contract

abbrev frameSylow' : Subgroup frameStab :=
  Subgroup.closure {w | ∃ x ∈ frameGens, (w : WeylGroup .E8) = (coxeterSystem .E8).wordProd x.1}

section Contract


theorem map_frameSylow' : frameSylow'.map framePermHom = frameGroup := by
  rw [MonoidHom.map_closure]
  congr 1
  ext p
  constructor
  · rintro ⟨w, ⟨x, hx, hwx⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    have hw : w = ⟨_, wordProd_mem_frameStab hx⟩ := Subtype.ext hwx
    rw [hw, framePermHom_wordProd hx]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨_, wordProd_mem_frameStab hx⟩, ⟨x, hx, rfl⟩, framePermHom_wordProd hx⟩

end Contract

private theorem card_weylGroup_E8_eq :
    Nat.card (WeylGroup .E8) = 696729600 := by
  have : Fintype (WeylGroup .E8) := Fintype.ofFinite _
  have h := CFSG.RankThree.Chevalley.sum_length_E8_eq 1
  simp at h
  rw [Nat.card_eq_fintype_card, h]


end E8Weyl

open E8Weyl in
theorem sectionalTwoRankLE_weylGroup_E8 :
    SectionalTwoRankLE (WeylGroup .E8) 9 := by
  classical
  set S := frameSylow'.map frameStab.subtype
  have hcardS0 : Nat.card frameSylow' = 2 ^ 14 := by
    rw [← card_frameGroup, ← map_frameSylow', Subgroup.card_map_of_injective framePermHom_injective]
  have hcardS : Nat.card S = 2 ^ 14 := by
    rw [Subgroup.card_map_of_injective frameStab.subtype_injective, hcardS0]
  have hidx : S.index = 42525 := by
    have h := S.index_mul_card
    rw [hcardS, card_weylGroup_E8_eq] at h
    norm_num at h
    omega
  refine sectionalTwoRankLE_of_odd_index S (by rw [hidx]; exact ⟨21262, by norm_num⟩) ?_
  let f : frameSylow' →* frameGroup :=
    (framePermHom.comp frameSylow'.subtype).codRestrict frameGroup fun w => by
      rw [← map_frameSylow']
      exact ⟨w, w.2, rfl⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (framePermHom_injective (congrArg Subtype.val h))
  exact SectionalTwoRankLE.of_mulEquiv
    (Subgroup.equivMapOfInjective frameSylow' frameStab.subtype frameStab.subtype_injective)
    (SectionalTwoRankLE.of_injective f hf sectionalTwoRankLE_frameGroup)



end CFSG.LieType.Chevalley

end
