module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafLocU43Pairs
public import Certificates.Data.U43TwinCheck

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.U43

open CFSG.LieType.Multipliers.U43 (F9)
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43
open CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf.LocU43.Check
open CFSG.Monster.B.Fischer
open CFSG.GH74.GLS.C3.Layer1.EndN.U43 (hud P43)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.AschbacherTheorem5.DeltaLocal
open Certificates.U43Twin

theorem rawValid_of_valid {x : Array ℕ} (h : valid x = true) : rawValid x = true :=
  ((valid_iff x).1 h).1

theorem commC_iff {x y : Array ℕ} (hx : rawValid x = true) (hy : rawValid y = true) :
    commC x y = true ↔ ev x * ev y = ev y * ev x := by
  unfold commC
  rw [eqZ_iff_ev (rawValid_mulRaw hx hy) (rawValid_mulRaw hy hx), ev_mulRaw hx hy,
    ev_mulRaw hy hx]

theorem invertC_spec {c : Array ℕ} (h : invertC c = true) :
    rawValid c = true ∧ rawValid (conjT c) = true ∧ ev (conjT c) = (ev c)⁻¹ := by
  simp only [invertC, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, ev_inv_of_isZ h1 h2 h3⟩

theorem conjBy_spec {c x : Array ℕ} (hc : invertC c = true) (hx : rawValid x = true) :
    rawValid (conjBy c x) = true ∧ ev (conjBy c x) = ev c * ev x * (ev c)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := invertC_spec hc
  unfold conjBy
  refine ⟨rawValid_mulRaw (rawValid_mulRaw h1 hx) h2, ?_⟩
  rw [ev_mulRaw (rawValid_mulRaw h1 hx) h2, ev_mulRaw h1 hx, h3]

theorem memL_iff {x : Array ℕ} {L : List (Array ℕ)} (hx : rawValid x = true)
    (hL : ∀ y ∈ L, rawValid y = true) : memL x L = true ↔ ∃ y ∈ L, ev x = ev y := by
  unfold memL
  rw [List.any_eq_true]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, (eqZ_iff_ev hx (hL y hy)).1 h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, (eqZ_iff_ev hx (hL y hy)).2 h⟩

theorem innerShape_mem_inner {x : Array ℕ} (hx : rawValid x = true) (h : innerShape x = true) :
    ev x ∈ inner P43 := by
  simp only [innerShape, Bool.and_eq_true, beq_iff_eq] at h
  exact ev_mem_inner hx h.1 h.2

theorem evenC_spec {w : Array ℕ} (hw : rawValid w = true) (h : evenC w = true) :
    Even (orderOf (ev w)) := by
  unfold evenC at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h
  have h2 := powRaw_spec hw 2
  have h4 := powRaw_spec hw 4
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine even_orderOf_of_pow (j := 1) ?_ ?_
    · rw [pow_one, ← h2.2]
      exact (ev_eq_one_iff h2.1).2 ha
    · rw [pow_one]
      intro h1
      rw [(ev_eq_one_iff hw).1 h1] at hb
      exact Bool.false_ne_true hb.symm
  · refine even_orderOf_of_pow (j := 2) ?_ ?_
    · rw [← pow_mul, ← h4.2]
      exact (ev_eq_one_iff h4.1).2 ha
    · intro h1
      rw [← h2.2, ev_eq_one_iff h2.1] at h1
      rw [h1] at hb
      exact Bool.false_ne_true hb.symm

theorem ev_powRaw {x : Array ℕ} (hx : rawValid x = true) (n : ℕ) : ev (powRaw x n) = ev x ^ n :=
  (powRaw_spec hx n).2

@[expose] def q8List {X : Type} [Group X] (p q : X) : List X :=
  [1, p, p ^ 2, p ^ 3, q, q * p, q * p ^ 2, q * p ^ 3]

theorem q8Elts_valid {p q : Array ℕ} (hp : rawValid p = true) (hq : rawValid q = true) :
    ∀ y ∈ q8Elts p q, rawValid y = true := by
  have h2 := (powRaw_spec hp 2).1
  have h3 := (powRaw_spec hp 3).1
  intro y hy
  simp only [q8Elts, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rawValid_idCode
  · exact hp
  · exact h2
  · exact h3
  · exact hq
  · exact rawValid_mulRaw hq hp
  · exact rawValid_mulRaw hq h2
  · exact rawValid_mulRaw hq h3

theorem map_ev_q8Elts {p q : Array ℕ} (hp : rawValid p = true) (hq : rawValid q = true) :
    (q8Elts p q).map ev = q8List (ev p) (ev q) := by
  have h2 := powRaw_spec hp 2
  have h3 := powRaw_spec hp 3
  simp only [q8Elts, q8List, List.map_cons, List.map_nil, ev_idCode, h2.2, h3.2,
    ev_mulRaw hq hp, ev_mulRaw hq h2.1, ev_mulRaw hq h3.1]

theorem q8_cases : ∀ g : QuaternionGroup 2, g = .a 0 ∨ g = .a 1 ∨ g = .a 2 ∨ g = .a 3 ∨
    g = .xa 0 ∨ g = .xa 1 ∨ g = .xa 2 ∨ g = .xa 3 := by
  decide

theorem closure_pair_eq_range {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) :
    Subgroup.closure ({p, q} : Set X) = (q8Hom h).range := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨QuaternionGroup.a 1, by
        show zmod4Pow x 1 = x
        unfold zmod4Pow
        rw [show (1 : ZMod 4).val = 1 from rfl, pow_one]⟩
    · exact ⟨QuaternionGroup.xa 0, by
        show x * zmod4Pow p 0 = x
        rw [zmod4Pow_zero, mul_one]⟩
  · rintro _ ⟨g, rfl⟩
    have hp : p ∈ Subgroup.closure ({p, q} : Set X) := Subgroup.subset_closure (by simp)
    have hq : q ∈ Subgroup.closure ({p, q} : Set X) := Subgroup.subset_closure (by simp)
    cases g with
    | a i => exact Subgroup.pow_mem _ hp _
    | xa i => exact Subgroup.mul_mem _ hq (Subgroup.pow_mem _ hp _)

theorem mem_closure_pair_iff {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) (x : X) :
    x ∈ Subgroup.closure ({p, q} : Set X) ↔ x ∈ q8List p q := by
  rw [closure_pair_eq_range h]
  have e : ∀ i : ZMod 4, q8Hom h (QuaternionGroup.a i) = p ^ i.val := fun i => rfl
  have e' : ∀ i : ZMod 4, q8Hom h (QuaternionGroup.xa i) = q * p ^ i.val := fun i => rfl
  have v0 : (0 : ZMod 4).val = 0 := by decide
  have v1 : (1 : ZMod 4).val = 1 := by decide
  have v2 : (2 : ZMod 4).val = 2 := by decide
  have v3 : (3 : ZMod 4).val = 3 := by decide
  constructor
  · rintro ⟨g, rfl⟩
    rcases q8_cases g with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [e, e', v0, v1, v2, v3, pow_zero, pow_one, mul_one, q8List, List.mem_cons,
        List.not_mem_nil, true_or, or_true]
  · intro hx
    simp only [q8List, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨QuaternionGroup.a 1, by rw [e, v1, pow_one]⟩
    · exact ⟨QuaternionGroup.a 2, by rw [e, v2]⟩
    · exact ⟨QuaternionGroup.a 3, by rw [e, v3]⟩
    · exact ⟨QuaternionGroup.xa 0, by rw [e', v0, pow_zero, mul_one]⟩
    · exact ⟨QuaternionGroup.xa 1, by rw [e', v1, pow_one]⟩
    · exact ⟨QuaternionGroup.xa 2, by rw [e', v2]⟩
    · exact ⟨QuaternionGroup.xa 3, by rw [e', v3]⟩

theorem card_closure_pair {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) :
    Nat.card (Subgroup.closure ({p, q} : Set X)) = 8 := by
  rw [closure_pair_eq_range h, ← Nat.card_congr (MonoidHom.ofInjective (q8Hom_injective h)).toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem q8_pow_four : ∀ g : QuaternionGroup 2, g ^ 4 = 1 := by decide

theorem pow_four_of_mem_closure_pair {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) {x : X}
    (hx : x ∈ Subgroup.closure ({p, q} : Set X)) : x ^ 4 = 1 := by
  rw [closure_pair_eq_range h] at hx
  obtain ⟨g, rfl⟩ := hx
  rw [← map_pow, q8_pow_four, map_one]

theorem isQ8Pair_of_rel {X : Type} [Group X] {p q t : X} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hp : p ^ 2 = t) (hq : q ^ 2 = t) (hqp : q * p = t * p * q) : IsQ8Pair p q := by
  have h4 : p ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hp, pow_two, ht]
  have hinv : p⁻¹ = t * p := by
    calc p⁻¹ = p⁻¹ * p ^ 4 := by rw [h4, mul_one]
      _ = p ^ 2 * p := by group
      _ = t * p := by rw [hp]
  refine ⟨h4, hq.trans hp.symm, ?_, by rw [hp]; exact ht1⟩
  rw [hinv, hqp]
  group

theorem rel_of_isQ8Pair {X : Type} [Group X] {p q t : X} (h : IsQ8Pair p q) (hp : p ^ 2 = t) :
    q ^ 2 = t ∧ q * p = t * p * q := by
  refine ⟨h.2.1.trans hp, ?_⟩
  have h1 : q * p * q⁻¹ = p⁻¹ := h.2.2.1
  have hinv : p⁻¹ = t * p := by
    have h4 : p ^ 4 = 1 := h.1
    rw [← hp]
    calc p⁻¹ = p⁻¹ * p ^ 4 := by rw [h4, mul_one]
      _ = p ^ 2 * p := by group
  calc q * p = (q * p * q⁻¹) * q := by group
    _ = t * p * q := by rw [h1, hinv]

theorem isQ8Pair_conj {X : Type} [Group X] {p q : X} (h : IsQ8Pair p q) (d : X) :
    IsQ8Pair (d * p * d⁻¹) (d * q * d⁻¹) := by
  have e := h.map (MulAut.conj d).toMonoidHom (MulAut.conj d).injective
  simpa [MulAut.conj_apply] using e

theorem map_conj_closure_pair {X : Type} [Group X] (p q d : X) :
    (Subgroup.closure ({p, q} : Set X)).map (MulAut.conj d).toMonoidHom =
      Subgroup.closure ({d * p * d⁻¹, d * q * d⁻¹} : Set X) := by
  rw [MonoidHom.map_closure]
  congr 1
  simp [Set.image_insert_eq, Set.image_singleton, MulAut.conj_apply]

@[expose] noncomputable def codeSub (gens : Array (Array ℕ)) : Subgroup (MulAut P43) :=
  Subgroup.closure ((fun k => ev gens[k]!) '' {k | k < gens.size})

theorem codeSub_spec {gens : Array (Array ℕ)} {c : ArrCert}
    (hg : ∀ k < gens.size, rawValid gens[k]! = true)
    (hc : arrCertOK (act gens) gens.size valid keyOf idCode c = true) :
    (∀ g : MulAut P43, g ∈ codeSub gens ↔ ∃ i < c.pts.size, ev c.pts[i]! = g) ∧
      Nat.card (codeSub gens) = c.pts.size ∧ (∀ i < c.pts.size, valid c.pts[i]! = true) := by
  have hact : ∀ k < gens.size, ∀ a, valid a = true → ev (act gens k a) = ev gens[k]! * ev a := by
    intro k hk a ha
    obtain ⟨hav, -⟩ := (valid_iff a).1 ha
    have hm := rawValid_mulRaw (hg k hk) hav
    unfold act
    rw [ev_normalize hm, ev_mulRaw (hg k hk) hav]
  have hkey : ∀ a b, valid a = true → valid b = true → ev a = ev b → keyOf a = keyOf b := by
    intro a b ha hb hab
    obtain ⟨hav, hna⟩ := (valid_iff a).1 ha
    obtain ⟨hbv, hnb⟩ := (valid_iff b).1 hb
    have := normalize_eq_of_ev_eq hav hbv hab
    rw [hna, hnb] at this
    rw [this]
  obtain ⟨hmem, hcard⟩ := card_closure_of_arrCertOK (G := MulAut P43) (dec := ev)
    (gens := fun k => ev gens[k]!) hc hact hkey ev_idCode
  exact ⟨hmem, hcard, fun i hi => arrCertOK_valid hc hi⟩

theorem orb_parts {G Gi : Array (Array ℕ)} {f : ℕ → Array ℕ → Array ℕ} {root : Array ℕ}
    {c : ArrCert} {n : ℕ}
    (h : ((List.range G.size).all (fun k => rawValid G[k]! && rawValid Gi[k]! &&
      innerShape G[k]! && isZ (mulRaw G[k]! Gi[k]!)) &&
      (arrCertOK f G.size valid keyOf root c && c.pts.size == n)) = true) :
    (∀ k < G.size, rawValid G[k]! = true ∧ rawValid Gi[k]! = true ∧
      innerShape G[k]! = true ∧ isZ (mulRaw G[k]! Gi[k]!) = true) ∧
    arrCertOK f G.size valid keyOf root c = true ∧ c.pts.size = n := by
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨hg, hc, hs⟩ := h
  refine ⟨fun k hk => ?_, hc, hs⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hg k hk
  exact ⟨h1, h2, h3, h4⟩

theorem orbOK_parts (h : orbOK () = true) :
    (∀ k < gI.size, rawValid gI[k]! = true ∧ rawValid gIinv[k]! = true ∧
      innerShape gI[k]! = true ∧ isZ (mulRaw gI[k]! gIinv[k]!) = true) ∧
    arrCertOK actConj gI.size valid keyOf T0 (orbCert ()) = true ∧ (orbCert ()).pts.size = 2835 :=
  orb_parts h

theorem ncard_orbit_t0 (h : orbOK () = true) :
    (MulAction.orbit (Subgroup.closure
      ((fun k => ConjAct.toConjAct (ev gI[k]!)) '' {k | k < gI.size})) (ev T0)).ncard = 2835 := by
  obtain ⟨hg, hc, hs⟩ := orbOK_parts h
  have hact : ∀ k < gI.size, ∀ a, valid a = true →
      ev (actConj k a) = ConjAct.toConjAct (ev gI[k]!) • ev a := by
    intro k hk a ha
    obtain ⟨hv, hvi, -, hz⟩ := hg k hk
    have hav := rawValid_of_valid ha
    have hm := rawValid_mulRaw (rawValid_mulRaw hv hav) hvi
    unfold actConj
    rw [ev_normalize hm, ev_mulRaw (rawValid_mulRaw hv hav) hvi, ev_mulRaw hv hav,
      ev_inv_of_isZ hv hvi hz, ConjAct.toConjAct_smul]
  have hkey : ∀ a b, valid a = true → valid b = true → ev a = ev b → keyOf a = keyOf b := by
    intro a b ha hb hab
    obtain ⟨hav, hna⟩ := (valid_iff a).1 ha
    obtain ⟨hbv, hnb⟩ := (valid_iff b).1 hb
    have := normalize_eq_of_ev_eq hav hbv hab
    rw [hna, hnb] at this
    rw [this]
  rw [ncard_orbit_of_arrCertOK (G := ConjAct (MulAut P43)) (X := MulAut P43) (dec := ev)
    (gens := fun k => ConjAct.toConjAct (ev gI[k]!)) hc hact hkey, hs]

theorem card_inner_centralizer_le (h : orbOK () = true) :
    Nat.card ↥(inner P43 ⊓ Subgroup.centralizer ({ev T0} : Set (MulAut P43))) ≤ 1152 := by
  classical
  obtain ⟨hg, -, -⟩ := orbOK_parts h
  set I' : Subgroup (ConjAct (MulAut P43)) :=
    (inner P43).map (ConjAct.toConjAct : MulAut P43 ≃* ConjAct (MulAut P43)).toMonoidHom with hI'
  set G' : Subgroup (ConjAct (MulAut P43)) :=
    Subgroup.closure ((fun k => ConjAct.toConjAct (ev gI[k]!)) '' {k | k < gI.size}) with hG'
  have hle : G' ≤ I' := by
    rw [hG', Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨hv, -, hin, -⟩ := hg k hk
    exact ⟨ev gI[k]!, innerShape_mem_inner hv hin, rfl⟩
  have hsub : MulAction.orbit G' (ev T0) ⊆ MulAction.orbit I' (ev T0) := by
    rintro _ ⟨g, rfl⟩
    exact ⟨⟨g, hle g.2⟩, rfl⟩
  have h2835 : 2835 ≤ (MulAction.orbit I' (ev T0)).ncard := by
    rw [← ncard_orbit_t0 h]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hidx := MulAction.index_stabilizer I' (ev T0)
  have hmul := Subgroup.card_mul_index (MulAction.stabilizer I' (ev T0))
  have hcardI : Nat.card I' ≤ 3265920 := by
    rw [hI', Subgroup.card_map_of_injective (ConjAct.toConjAct :
      MulAut P43 ≃* ConjAct (MulAut P43)).injective]
    have := card_inner_dvd
    rw [card_P43] at this
    exact Nat.le_of_dvd (by norm_num) this
  have hinj : Nat.card ↥(inner P43 ⊓ Subgroup.centralizer ({ev T0} : Set (MulAut P43))) ≤
      Nat.card (MulAction.stabilizer I' (ev T0)) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨ConjAct.toConjAct (x : MulAut P43), ⟨x, (Subgroup.mem_inf.mp x.2).1, rfl⟩⟩, ?_⟩)
      ?_
    · rw [MulAction.mem_stabilizer_iff]
      change ConjAct.toConjAct (x : MulAut P43) • ev T0 = ev T0
      rw [ConjAct.toConjAct_smul]
      have hx := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2
      rw [hx, mul_inv_cancel_right]
    · intro x y hxy
      have := congrArg (fun z : MulAction.stabilizer I' (ev T0) =>
        ConjAct.ofConjAct ((z : I') : ConjAct (MulAut P43))) hxy
      simp only [ConjAct.ofConjAct_toConjAct] at this
      exact Subtype.ext this
  rw [hidx] at hmul
  have : Nat.card (MulAction.stabilizer I' (ev T0)) * 2835 ≤ 3265920 :=
    (Nat.mul_le_mul_left _ h2835).trans (hmul.le.trans hcardI)
  omega

theorem exists_conj_le {G : Type*} [Group G] [Finite G] {H T P : Subgroup G} (hTH : T ≤ H)
    (hT : IsPGroup 2 T) (hidx : ¬ 2 ∣ T.relIndex H) (hPH : P ≤ H) (hP : IsPGroup 2 P) :
    ∃ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT' : IsPGroup 2 (T.subgroupOf H) := hT.comap_subtype
  have hP' : IsPGroup 2 (P.subgroupOf H) := hP.comap_subtype
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H (hT'.toSylow hidx) Q
  refine ⟨((g⁻¹ : H) : G), (g⁻¹ : H).2, fun x hx => ?_⟩
  have hxQ : (⟨x, hPH hx⟩ : H) ∈ (Q : Subgroup H) := hQ hx
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hxQ
  obtain ⟨s, hs, hsx⟩ := hxQ
  have hs' : s = g⁻¹ * ⟨x, hPH hx⟩ * g := by
    rw [← hsx]
    simp [MulAut.conj_apply, mul_assoc]
  have hsT : (s : G) ∈ T := by
    have hs2 : s ∈ T.subgroupOf H := (IsPGroup.mem_toSylow hT' hidx).mp hs
    exact Subgroup.mem_subgroupOf.mp hs2
  rw [hs'] at hsT
  simpa [mul_assoc] using hsT

@[expose] def Viol {X : Type} [Group X] (Q : Subgroup X) (c : X) : Prop :=
  (∃ x ∈ Q, c * x * c⁻¹ ∉ Q) ∧
    ((∃ x ∈ Q, ∃ z ∈ Q, x * (c * z * c⁻¹) ≠ (c * z * c⁻¹) * x) ∨
      ∃ z ∈ Q, c * z * c⁻¹ ∈ Q ∧ (c * z * c⁻¹) * (c * z * c⁻¹) ≠ 1)

theorem Viol.of_map {X : Type} [Group X] {Q : Subgroup X} {c d : X}
    (h : Viol (Q.map (MulAut.conj d).toMonoidHom) c) : Viol Q (d⁻¹ * c * d) := by
  have hmem : ∀ y : X, y ∈ Q.map (MulAut.conj d).toMonoidHom ↔ d⁻¹ * y * d ∈ Q := by
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hx
    · intro hy
      exact ⟨d⁻¹ * y * d, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hconj : ∀ x : X, d * x * d⁻¹ ∈ Q.map (MulAut.conj d).toMonoidHom ↔ x ∈ Q := by
    intro x
    rw [hmem]
    simp [mul_assoc]
  obtain ⟨⟨x, hx, hx'⟩, h2⟩ := h
  rw [hmem] at hx hx'
  refine ⟨⟨d⁻¹ * x * d, hx, ?_⟩, ?_⟩
  · intro hc
    apply hx'
    have e : d⁻¹ * (c * x * c⁻¹) * d = d⁻¹ * c * d * (d⁻¹ * x * d) * (d⁻¹ * c * d)⁻¹ := by group
    rw [e]
    exact hc
  · rcases h2 with ⟨x, hx, z, hz, hxz⟩ | ⟨z, hz, hzQ, hz2⟩
    · rw [hmem] at hx hz
      refine Or.inl ⟨d⁻¹ * x * d, hx, d⁻¹ * z * d, hz, fun hc => hxz ?_⟩
      have e1 : d⁻¹ * x * d * (d⁻¹ * c * d * (d⁻¹ * z * d) * (d⁻¹ * c * d)⁻¹) =
          d⁻¹ * (x * (c * z * c⁻¹)) * d := by group
      have e2 : d⁻¹ * c * d * (d⁻¹ * z * d) * (d⁻¹ * c * d)⁻¹ * (d⁻¹ * x * d) =
          d⁻¹ * ((c * z * c⁻¹) * x) * d := by group
      rw [e1, e2] at hc
      have := congrArg (fun w => d * w * d⁻¹) hc
      simpa [mul_assoc] using this
    · rw [hmem] at hz hzQ
      refine Or.inr ⟨d⁻¹ * z * d, hz, ?_, fun hc => hz2 ?_⟩
      · have e : d⁻¹ * c * d * (d⁻¹ * z * d) * (d⁻¹ * c * d)⁻¹ = d⁻¹ * (c * z * c⁻¹) * d := by
          group
        rw [e]
        exact hzQ
      · have e : d⁻¹ * c * d * (d⁻¹ * z * d) * (d⁻¹ * c * d)⁻¹ *
            (d⁻¹ * c * d * (d⁻¹ * z * d) * (d⁻¹ * c * d)⁻¹) =
            d⁻¹ * ((c * z * c⁻¹) * (c * z * c⁻¹)) * d := by group
        rw [e] at hc
        have := congrArg (fun w => d * w * d⁻¹) hc
        simpa [mul_assoc] using this

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.U43
