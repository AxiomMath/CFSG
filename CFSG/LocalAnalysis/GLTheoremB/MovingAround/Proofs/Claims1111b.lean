module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1112
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec10Closed4
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KEvenSLTwo

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1111b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1112b
open scoped commutatorElement

section Plane

theorem coe_commutatorElement' {R : Type} [Group R] {T : Subgroup R} (x y : ↥T) :
    ((⁅x, y⁆ : ↥T) : R) = (x : R) * y * (x : R)⁻¹ * (y : R)⁻¹ := rfl

theorem card_map_mk'_mul {R : Type} [Group R] {Z N : Subgroup R} [Z.Normal] (hZN : Z ≤ N) :
    Nat.card (N.map (QuotientGroup.mk' Z)) * Nat.card Z = Nat.card N := by
  have h1 : Nat.card (N.map (QuotientGroup.mk' Z)) = (Z.subgroupOf N).index := by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
    rfl
  rw [h1, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZN).toEquiv, mul_comm]
  exact Subgroup.card_mul_index _

theorem exists_of_le {p : ℕ} [hp : Fact p.Prime] {R : Type} [Group R] [Finite R] (hR : IsPGroup p R)
    {N W : Subgroup R} (hW : W.Normal) (hWN : W ≤ N) (hcard : p ^ 2 ≤ Nat.card W)
    (hexp : ∀ x ∈ W, x ^ p = 1) :
    ∃ U : Subgroup R, U.Normal ∧ U ≤ N ∧ Nat.card U = p ^ 2 ∧ ∀ x ∈ U, x ^ p = 1 := by
  haveI : Fact (IsPGroup p R) := ⟨hR⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hR.to_subgroup W)
  have hk2 : 2 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).1 hcard
  obtain ⟨U, hU, hUW, hUc⟩ := CFSG.exists_normal_subgroup_card_pow_of_normal W hW hk 2 hk2
  exact ⟨U, hU, hUW.trans hWN, hUc, fun x hx => hexp x (hUW hx)⟩

theorem exists_of_preimage {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {R : Type} [Group R] [Finite R]
    (hR : IsPGroup p R) {Z N : Subgroup R} [Z.Normal] (hZN : Z ≤ N) (hZc : Nat.card Z = p)
    (hZcen : Z ≤ Subgroup.center R) {Ubar : Subgroup (R ⧸ Z)} (hUn : Ubar.Normal)
    (hUN : Ubar ≤ N.map (QuotientGroup.mk' Z)) (hUc : Nat.card Ubar = p ^ 2)
    (hUexp : ∀ x ∈ Ubar, x ^ p = 1) :
    ∃ U : Subgroup R, U.Normal ∧ U ≤ N ∧ Nat.card U = p ^ 2 ∧ ∀ x ∈ U, x ^ p = 1 := by
  set q : R →* R ⧸ Z := QuotientGroup.mk' Z with hq
  set T : Subgroup R := Ubar.comap q with hT
  have hTn : T.Normal := hUn.comap q
  have hZT : Z ≤ T := by
    intro z hz
    show q z ∈ Ubar
    rw [hq, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).2 hz]
    exact Ubar.one_mem
  have hTN : T ≤ N := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 (hUN hx)
    have h1 : y⁻¹ * x ∈ Z := by
      have : q (y⁻¹ * x) = 1 := by rw [map_mul, map_inv, hyx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).1 this
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact N.mul_mem hy (hZN h1)
  have hTmap : T.map q = Ubar := Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective Z) Ubar
  have hTcard : Nat.card T = p ^ 3 := by
    have h := card_map_mk'_mul hZT
    rw [← hq, hTmap, hUc, hZc] at h
    rw [← h]
    ring
  have hUcomm : ∀ u ∈ Ubar, ∀ v ∈ Ubar, u * v = v * u := by
    intro u hu v hv
    have := IsPGroup.commutative_of_card_eq_prime_sq hUc ⟨u, hu⟩ ⟨v, hv⟩
    exact congrArg Subtype.val this
  have hcommZ : ∀ x ∈ T, ∀ y ∈ T, x * y * x⁻¹ * y⁻¹ ∈ Z := by
    intro x hx y hy
    have : q (x * y * x⁻¹ * y⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hUcomm _ hx _ hy]
      group
    exact (QuotientGroup.eq_one_iff _).1 this
  have hTp : IsPGroup p ↥T := hR.to_subgroup T
  haveI : Fact (IsPGroup p ↥T) := ⟨hTp⟩
  have hZT_cen : ∀ t : ↥T, (t : R) ∈ Z → t ∈ Subgroup.center ↥T := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (hZcen ht)) (s : R))
  have hder : _root_.commutator ↥T ≤ Z.subgroupOf T := by
    rw [_root_.commutator, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_subgroupOf, coe_commutatorElement']
    exact hcommZ x x.2 y y.2
  have hclass : NilpotencyClassLe 2 ↥T := by
    unfold NilpotencyClassLe
    rw [eq_top_iff]
    intro x _
    rw [show (2 : ℕ) = 1 + 1 from rfl, mem_upperCentralSeries_succ_iff, upperCentralSeries_one]
    intro y
    refine hZT_cen _ ?_
    rw [coe_commutatorElement']
    exact hcommZ x x.2 y y.2
  have hZpow : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZc] at this
    exact congrArg Subtype.val this
  have hderΩ : _root_.commutator ↥T ≤ CFSG.omega₁ (G := ↥T) (p := p) := by
    refine hder.trans fun t ht => Subgroup.subset_closure ?_
    show t ^ (p ^ 1) = 1
    rw [pow_one]
    exact Subtype.ext (by simpa using hZpow _ (Subgroup.mem_subgroupOf.1 ht))
  obtain ⟨φ, hφ⟩ := CFSG.proposition_4_3_b (R := ↥T) (p := p) hp2 (Or.inl hclass) hderΩ
  have hrange : φ.range ≤ Z.subgroupOf T := by
    rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_subgroupOf, hφ x]
    have hx : q (x : R) ∈ Ubar := x.2
    have : q ((x : R) ^ p) = 1 := by rw [map_pow]; exact hUexp _ hx
    simpa using (QuotientGroup.eq_one_iff _).1 this
  have hZTcard : Nat.card (Z.subgroupOf T) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZT).toEquiv, hZc]
  have hker : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    have h2 : Nat.card φ.range ≤ p := hZTcard ▸ Subgroup.card_le_of_le hrange
    rw [hTcard] at h1
    have hp0 : 0 < p := hp.out.pos
    have h3 : p ^ 2 * p ≤ Nat.card φ.ker * p := by
      calc p ^ 2 * p = p ^ 3 := by ring
        _ = Nat.card φ.ker * Nat.card φ.range := h1.symm
        _ ≤ Nat.card φ.ker * p := Nat.mul_le_mul_left _ h2
    exact Nat.le_of_mul_le_mul_right h3 hp0
  set W : Subgroup R := φ.ker.map T.subtype with hW
  have hWmem : ∀ x, x ∈ W ↔ x ∈ T ∧ x ^ p = 1 := by
    intro x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.2, ?_⟩
      have : φ t = 1 := ht
      rw [hφ t] at this
      simpa using congrArg Subtype.val this
    · rintro ⟨hxT, hxp⟩
      refine ⟨⟨x, hxT⟩, ?_, rfl⟩
      show φ _ = 1
      rw [hφ]
      exact Subtype.ext (by simpa using hxp)
  have hWn : W.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hnT, hnp⟩ := (hWmem n).1 hn
    refine (hWmem _).2 ⟨hTn.conj_mem n hnT g, ?_⟩
    rw [conj_pow, hnp]
    group
  have hWcard : p ^ 2 ≤ Nat.card W := by
    rw [hW, Subgroup.card_map_of_injective T.subtype_injective]
    exact hker
  exact exists_of_le hR hWn ((show W ≤ T from fun x hx => ((hWmem x).1 hx).1).trans hTN) hWcard
    (fun x hx => ((hWmem x).1 hx).2)

theorem exists_of_cyclic {p : ℕ} [hp : Fact p.Prime] {R : Type} [Group R] [Finite R]
    (hR : IsPGroup p R) {Z N : Subgroup R} [Z.Normal] (hN : N.Normal) (hNc : ¬ IsCyclic N)
    (hZN : Z ≤ N) (hZc : Nat.card Z = p) (hZcen : Z ≤ Subgroup.center R)
    (hcyc : IsCyclic (N.map (QuotientGroup.mk' Z))) :
    ∃ U : Subgroup R, U.Normal ∧ U ≤ N ∧ Nat.card U = p ^ 2 ∧ ∀ x ∈ U, x ^ p = 1 := by
  set q : R →* R ⧸ Z := QuotientGroup.mk' Z with hq
  obtain ⟨gbar, hgbar⟩ := IsCyclic.exists_generator (α := ↥(N.map q))
  obtain ⟨g, hgN, hgq⟩ := Subgroup.mem_map.1 gbar.2
  have hdec : ∀ x ∈ N, ∃ k : ℤ, (g ^ k)⁻¹ * x ∈ Z := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hgbar ⟨q x, Subgroup.mem_map_of_mem q hx⟩)
    refine ⟨k, (QuotientGroup.eq_one_iff _).1 ?_⟩
    have hk' : q (g ^ k) = q x := by
      rw [map_zpow, hgq]
      exact congrArg Subtype.val hk
    show q ((g ^ k)⁻¹ * x) = 1
    rw [map_mul, map_inv, hk', inv_mul_cancel]
  have hcen : ∀ z ∈ Z, ∀ y : R, z * y = y * z := fun z hz y =>
    (Subgroup.mem_center_iff.1 (hZcen hz) y).symm
  have hNcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, hi⟩ := hdec x hx
    obtain ⟨j, hj⟩ := hdec y hy
    have ex : x = g ^ i * ((g ^ i)⁻¹ * x) := by group
    have ey : y = g ^ j * ((g ^ j)⁻¹ * y) := by group
    have hc : Commute (g ^ i * ((g ^ i)⁻¹ * x)) (g ^ j * ((g ^ j)⁻¹ * y)) :=
      ((Commute.zpow_zpow_self g i j).mul_right (show Commute _ _ from (hcen _ hj (g ^ i)).symm)).mul_left
        (show Commute _ _ from hcen _ hi _)
    rw [← ex, ← ey] at hc
    exact hc
  let W : Subgroup R :=
    { carrier := {x | x ∈ N ∧ x ^ p = 1}
      one_mem' := ⟨N.one_mem, one_pow p⟩
      mul_mem' := by
        rintro x y ⟨hx, hxp⟩ ⟨hy, hyp⟩
        refine ⟨N.mul_mem hx hy, ?_⟩
        rw [(Commute.mul_pow (hNcomm x hx y hy) p), hxp, hyp, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxp⟩
        exact ⟨N.inv_mem hx, by rw [inv_pow, hxp, inv_one]⟩ }
  have hWmem : ∀ x, x ∈ W ↔ x ∈ N ∧ x ^ p = 1 := fun x => Iff.rfl
  have hWn : W.Normal := by
    refine ⟨fun n hn h => ?_⟩
    obtain ⟨hnN, hnp⟩ := (hWmem n).1 hn
    refine (hWmem _).2 ⟨hN.conj_mem n hnN h, ?_⟩
    rw [conj_pow, hnp]
    group
  have hZpow : ∀ z ∈ Z, z ^ p = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := ↥Z) (x := ⟨z, hz⟩)
    rw [hZc] at this
    exact congrArg Subtype.val this
  have hZW : Z ≤ W := fun z hz => (hWmem z).2 ⟨hZN hz, hZpow z hz⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hR) g
  have hNle : ¬ Z ≤ Subgroup.zpowers g := by
    intro hle
    apply hNc
    have : N ≤ Subgroup.zpowers g := by
      intro x hx
      obtain ⟨k, hk⟩ := hdec x hx
      have : x = g ^ k * ((g ^ k)⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers g k) (hle hk)
    exact Subgroup.isCyclic_of_le this
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hm
    subst hm
    apply hNc
    have hN1 : N ≤ Z := by
      intro x hx
      obtain ⟨k, hk⟩ := hdec x hx
      simpa using hk
    haveI : IsCyclic ↥Z := isCyclic_of_prime_card hZc
    exact Subgroup.isCyclic_of_le hN1
  set u : R := g ^ (p ^ (m - 1)) with hu
  have hup : u ^ p = 1 := by
    rw [hu, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0), ← hm]
    exact pow_orderOf_eq_one g
  have hu1 : u ≠ 1 := by
    refine pow_ne_one_of_lt_orderOf (pow_ne_zero _ hp.out.ne_zero) ?_
    rw [hm]
    exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  have huW : u ∈ W := (hWmem u).2 ⟨N.pow_mem hgN _, hup⟩
  have huZ : u ∉ Z := by
    intro huZ
    apply hNle
    have hle : Subgroup.zpowers u ≤ Z := Subgroup.zpowers_le.2 huZ
    have hZu : Subgroup.zpowers u = Z := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Nat.card_zpowers, orderOf_eq_prime hup hu1, hZc])
    rw [← hZu]
    exact Subgroup.zpowers_le.2 (Subgroup.npow_mem_zpowers g _)
  have hWcard : p ^ 2 ≤ Nat.card W := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hR.to_subgroup W)
    rw [hk]
    refine Nat.pow_le_pow_right hp.out.pos ?_
    by_contra hk2
    push Not at hk2
    have hle : Nat.card W ≤ Nat.card Z := by
      rw [hk, hZc]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.out.pos (by omega)
        _ = p := pow_one p
    have hZW' : Z = W := Subgroup.eq_of_le_of_card_ge hZW hle
    exact huZ (hZW' ▸ huW)
  exact exists_of_le hR hWn (fun x hx => ((hWmem x).1 hx).1) hWcard (fun x hx => ((hWmem x).1 hx).2)

theorem exists_normal_plane {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) (n : ℕ) :
    ∀ (R : Type) [Group R] [Finite R], IsPGroup p R → ∀ N : Subgroup R, N.Normal →
      Nat.card N = n → ¬ IsCyclic N →
        ∃ U : Subgroup R, U.Normal ∧ U ≤ N ∧ Nat.card U = p ^ 2 ∧ ∀ x ∈ U, x ^ p = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro R _ _ hR N hN hNn hNc
  haveI : Fact (IsPGroup p R) := ⟨hR⟩
  haveI : N.Normal := hN
  have hNbot : N ≠ ⊥ := by
    rintro rfl
    exact hNc (by infer_instance)
  obtain ⟨Z, hZn, hZN, hZc, hZcen⟩ :=
    CFSG.exists_central_normal_subgroup_card_eq_prime_of_nontrivial_normal (p := p) N hNbot
  haveI : Z.Normal := hZn
  set q : R →* R ⧸ Z := QuotientGroup.mk' Z with hq
  by_cases hbarc : IsCyclic (N.map q)
  · exact exists_of_cyclic hR hN hNc hZN hZc hZcen hbarc
  · have hcardbar : Nat.card (N.map q) * p = Nat.card N := by
      rw [← hZc]
      exact card_map_mk'_mul hZN
    have hlt : Nat.card (N.map q) < n := by
      rw [← hNn, ← hcardbar]
      exact lt_mul_of_one_lt_right Nat.card_pos hp.out.one_lt
    obtain ⟨Ubar, hUn, hUN, hUc, hUexp⟩ := ih _ hlt (R ⧸ Z) (hR.to_quotient Z) (N.map q)
      (hN.map q (QuotientGroup.mk'_surjective Z)) rfl hbarc
    exact exists_of_preimage hp2 hR hZN hZc hZcen hUn hUN hUc hUexp

end Plane

theorem input31_5_holds : Claims1112.Input31_5 := by
  intro G _ _ p hp hp2 R Q hR hQR hQn hQc
  haveI : Fact p.Prime := ⟨hp⟩
  have hc : ¬ IsCyclic ↥(Q.subgroupOf R) := fun h =>
    hQc ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hQR)).1 h)
  obtain ⟨U, hUn, hUQ, hUc, hUexp⟩ := exists_normal_plane hp2 _ ↥R hR (Q.subgroupOf R) hQn rfl hc
  refine ⟨U.map R.subtype, ?_, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hUQ hu)
  · refine ⟨⟨fun x y => ?_⟩⟩
    have e : ↥(U.map R.subtype) ≃* ↥U :=
      (Subgroup.equivMapOfInjective U R.subtype R.subtype_injective).symm
    apply e.injective
    rw [map_mul, map_mul]
    exact IsPGroup.commutative_of_card_eq_prime_sq hUc _ _
  · rintro _ ⟨u, hu, rfl⟩
    simpa using congrArg Subtype.val (hUexp u hu)
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hUc]
  · intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨r, hr⟩ * u * ⟨r, hr⟩⁻¹, hUn.conj_mem u hu _, by simp⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨⟨r, hr⟩⁻¹ * v * ⟨r, hr⟩, ?_, ?_⟩
      · have := hUn.conj_mem v hv ⟨r, hr⟩⁻¹
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hvx ⊢
        rw [hvx]
        group

section SL34

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.PartTwo.KFacts.L34

theorem exists_mulEquiv_sl {Y : Type} [Group Y] (h : IsSLThreeFour Y) :
    ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
      Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 3) K) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
  exact ⟨K, inferInstance, hK,
    ⟨φ.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm⟩⟩

theorem card_map_proj {K : Type} [Field K] (hK : Nat.card K = 4)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hZP : scalars 3 K ≤ P)
    (hP : Nat.card P = 27) : Nat.card (P.map (proj 3 K)) = 9 := by
  have h : Nat.card (P.map (proj 3 K)) * Nat.card (scalars 3 K) = Nat.card P :=
    card_map_mk'_mul hZP
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hK, hP] at h
  omega

theorem mem_scalars_of_commute {K : Type} [Field K] (hK : Nat.card K = 4)
    {P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hZP : scalars 3 K ≤ P)
    (hP : Nat.card P = 27) {y : Matrix.SpecialLinearGroup (Fin 3) K}
    (hy : ∀ x ∈ P, y * x = x * y) : y ∈ scalars 3 K := by
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hK
  set E := P.map (proj 3 K) with hE
  have hker : (proj 3 K).ker ≤ P := by rw [ker_proj]; exact hZP
  have hcomap : E.comap (proj 3 K) = P := Subgroup.comap_map_eq_self hker
  have hE9 : Nat.card E = 9 := card_map_proj hK hZP hP
  obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (show E ≠ ⊥ by
    intro h
    rw [h, Subgroup.card_bot] at hE9
    omega)
  have hC := centralizer_eq_of_card_eq_nine hK hE9 x.2 (fun h => hx1 (Subtype.ext h))
  have hyE : proj 3 K y ∈ E := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.1 x.2
    rw [← hwx, ← map_mul, ← map_mul, hy w hw]
  have hyP : y ∈ P := by
    rw [← hcomap]
    exact hyE
  obtain ⟨⟨-, -, -, hZc⟩, -, -⟩ := isHeisThree_comap_proj hK hE9
  rw [hcomap] at hZc
  have hle : (scalars 3 K).subgroupOf P ≤ Subgroup.center ↥P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext ((Subgroup.mem_center_iff.1
      (scalars_le_center 3 K (Subgroup.mem_subgroupOf.1 hz))) (w : _))
  have heq : (scalars 3 K).subgroupOf P = Subgroup.center ↥P := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hZc, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hK]
  have hyc : (⟨y, hyP⟩ : ↥P) ∈ Subgroup.center ↥P := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (hy w w.2).symm
  rw [← heq] at hyc
  exact Subgroup.mem_subgroupOf.1 hyc

theorem exists_normalizer_conj_sl {K : Type} [Field K] (hK : Nat.card K = 4)
    {P U U' : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)} (hZP : scalars 3 K ≤ P)
    (hP : Nat.card P = 27) (hUP : U ≤ P) (hU'P : U' ≤ P) (hU : Nat.card U = 9)
    (hU' : Nat.card U' = 9) :
    ∃ n ∈ Subgroup.normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 3) K)),
      ∀ z, z ∈ U ↔ n * z * n⁻¹ ∈ U' := by
  haveI := CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour.finite_of_card_eq_four hK
  set E := P.map (proj 3 K) with hE
  have hE9 : Nat.card E = 9 := card_map_proj hK hZP hP
  have hZU := scalars_le_of_card_eq_nine hK hU
  have hZU' := scalars_le_of_card_eq_nine hK hU'
  have hbar : ∀ {V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}, scalars 3 K ≤ V →
      Nat.card V = 9 → ∃ v ∈ V.map (proj 3 K), v ≠ 1 ∧
        Subgroup.zpowers v = V.map (proj 3 K) := by
    intro V hZV hV
    have h : Nat.card (V.map (proj 3 K)) * Nat.card (scalars 3 K) = Nat.card V :=
      card_map_mk'_mul hZV
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine.card_scalars hK, hV] at h
    have h3 : Nat.card (V.map (proj 3 K)) = 3 := by omega
    obtain ⟨v, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 (show V.map (proj 3 K) ≠ ⊥ by
      intro hb
      rw [hb, Subgroup.card_bot] at h3
      omega)
    have hv1' : (v : projectiveSL 3 K) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hv3 : (v : projectiveSL 3 K) ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥(V.map (proj 3 K))) (x := v)
      rw [h3] at this
      exact congrArg Subtype.val this
    refine ⟨v, v.2, hv1', Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 v.2) ?_⟩
    rw [Nat.card_zpowers, orderOf_eq_prime hv3 hv1', h3]
  obtain ⟨u, huU, hu1, hu⟩ := hbar hZU hU
  obtain ⟨u', hu'U, hu'1, hu'⟩ := hbar hZU' hU'
  obtain ⟨nbar, hnbar, hconj⟩ := exists_mem_normalizer_conj_eq_of_card_eq_nine hK hE9
    (Subgroup.map_mono hUP huU) hu1 (Subgroup.map_mono hU'P hu'U) hu'1
  obtain ⟨n, rfl⟩ := proj_surjective 3 K nbar
  have hmem : ∀ {V : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K)}, scalars 3 K ≤ V →
      ∀ w, w ∈ V ↔ proj 3 K w ∈ V.map (proj 3 K) := by
    intro V hZV w
    have hker : (proj 3 K).ker ≤ V := by rw [ker_proj]; exact hZV
    conv_lhs => rw [← Subgroup.comap_map_eq_self hker]
    rfl
  refine ⟨n, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [hmem hZP, hmem hZP, map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.1 hnbar _
  · intro z
    rw [hmem hZU, hmem hZU', map_mul, map_mul, map_inv, ← hu, ← hu', Subgroup.mem_zpowers_iff,
      Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hconj, ← hk, conj_zpow]
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      rw [← hconj, conj_zpow] at hk
      have := congrArg (fun w => (proj 3 K n)⁻¹ * w * proj 3 K n) hk
      simpa [mul_assoc] using this

end SL34

theorem exists_normalizer_conj_of_isSLThreeFour {Y : Type} [Group Y] (hY : IsSLThreeFour Y)
    {P U U' : Subgroup Y} (hZP : Subgroup.center Y ≤ P) (hP : Nat.card P = 27) (hUP : U ≤ P)
    (hU'P : U' ≤ P) (hU : Nat.card U = 9) (hU' : Nat.card U' = 9) :
    ∃ n ∈ Subgroup.normalizer (P : Set Y), ∀ z, z ∈ U ↔ n * z * n⁻¹ ∈ U' := by
  obtain ⟨K, _, hK, ⟨e⟩⟩ := exists_mulEquiv_sl hY
  have hZP' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K ≤ P.map e.toMonoidHom := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K,
      ← Subgroup.map_center_eq e]
    exact Subgroup.map_mono hZP
  have hc : ∀ V : Subgroup Y, Nat.card (V.map e.toMonoidHom) = Nat.card V := fun V =>
    Subgroup.card_map_of_injective e.injective
  obtain ⟨n, hn, hnU⟩ := exists_normalizer_conj_sl hK hZP' ((hc P).trans hP)
    (Subgroup.map_mono hUP) (Subgroup.map_mono hU'P) ((hc U).trans hU) ((hc U').trans hU')
  refine ⟨e.symm n, ?_, fun z => ?_⟩
  · rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro z
    have := hn (e z)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at this
    simpa using this
  · have := hnU (e z)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at this
    simpa using this

theorem inputSL34SylowCent_holds : Claims1112.InputSL34SylowCent := by
  intro Y _ _ hY P _ hZP hP y hy
  obtain ⟨K, _, hK, ⟨e⟩⟩ := exists_mulEquiv_sl hY
  have hZP' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K ≤ P.map e.toMonoidHom := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K,
      ← Subgroup.map_center_eq e]
    exact Subgroup.map_mono hZP
  have hP' : Nat.card (P.map e.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective e.injective, hP]
  have hy' : ∀ x ∈ P.map e.toMonoidHom, e y * x = x * e y := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hy x hx]
  have h := mem_scalars_of_commute hK hZP' hP' hy'
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K] at h
  rw [Subgroup.mem_center_iff]
  intro g
  apply e.injective
  rw [map_mul, map_mul]
  exact (Subgroup.mem_center_iff.1 h (e g))

theorem inputSL34PlaneTransitive_holds : Claims1112.InputSL34PlaneTransitive := by
  intro G _ _ J S hSL hS U U' hUS hU'S hU hU'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSJ : S ≤ J := hS.1
  have hS3 : IsPGroup 3 ↥S := hS.2.1
  set π : ↥J →* CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 J :=
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) with hπ
  set ψ : ↥S →* CFSG.HardMathSupport.Solomon.LocalBalance.barOf 3 J :=
    π.comp (Subgroup.inclusion hSJ) with hψ
  have hψinj : Function.Injective ψ := by
    intro s t hst
    exact Subtype.ext (Claims1112.piK_inj hS3 s.2 t.2 (hSJ s.2) (hSJ t.2) hst)
  have hrange : ψ.range = (S.subgroupOf J).map π := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨Subgroup.inclusion hSJ s, Subgroup.mem_subgroupOf.2 s.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, Subgroup.mem_subgroupOf.1 hj⟩, rfl⟩
  obtain ⟨-, hZS, hS27⟩ := Claims1112.sylow_image_facts hSL hS
  rw [← hrange] at hZS hS27
  have hcardU : ∀ {V : Subgroup G}, V ≤ S → IsPPlane 3 V →
      Nat.card ((V.subgroupOf S).map ψ) = 9 := by
    intro V hVS hV
    rw [Subgroup.card_map_of_injective hψinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVS).toEquiv, hV.2]
    norm_num
  obtain ⟨mbar, hmN, hmU⟩ := exists_normalizer_conj_of_isSLThreeFour hSL hZS hS27
    (Subgroup.map_le_range ψ _) (Subgroup.map_le_range ψ _) (hcardU hUS hU) (hcardU hU'S hU')
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥J) mbar
  have hψmem : ∀ {V : Subgroup G}, V ≤ S → ∀ (w : G) (hw : w ∈ J), w ∈ S →
      (π ⟨w, hw⟩ ∈ (V.subgroupOf S).map ψ ↔ w ∈ V) := by
    intro V hVS w hw hwS
    constructor
    · rintro ⟨v, hv, hveq⟩
      have : (v : G) = w := Claims1112.piK_inj hS3 v.2 hwS (hSJ v.2) hw hveq
      rw [← this]
      exact Subgroup.mem_subgroupOf.1 hv
    · intro hwV
      exact ⟨⟨w, hwS⟩, Subgroup.mem_subgroupOf.2 hwV, rfl⟩
  set Y : Subgroup G := (ψ.range.comap π).map J.subtype with hY
  have hYJ : Y ≤ J := by
    rintro _ ⟨j, -, rfl⟩
    exact j.2
  have hSY : S ≤ Y := fun s hs => ⟨⟨s, hSJ hs⟩, ⟨⟨s, hs⟩, rfl⟩, rfl⟩
  have hSYs : IsSylowIn 3 Y S :=
    ⟨hSY, hS3, fun R' hR'Y hR'3 hSR' => hS.2.2 R' (hR'Y.trans hYJ) hR'3 hSR'⟩
  have hπS : ∀ (s : G) (hs : s ∈ S), π ⟨s, hSJ hs⟩ ∈ ψ.range := fun s hs => ⟨⟨s, hs⟩, rfl⟩
  set R : Subgroup G := GLBConj (m : G)⁻¹ S with hR
  have hRY : R ≤ Y := by
    intro r hr
    rw [hR, mem_gLBConj, inv_inv] at hr
    have hrJ : r ∈ J := by
      have : r = (m : G) * ((m : G)⁻¹ * r * (m : G)) * (m : G)⁻¹ := by group
      rw [this]
      exact J.mul_mem (J.mul_mem m.2 (hSJ hr)) (J.inv_mem m.2)
    refine ⟨⟨r, hrJ⟩, ?_, rfl⟩
    show π ⟨r, hrJ⟩ ∈ ψ.range
    have he : (⟨r, hrJ⟩ : ↥J) = m * ⟨(m : G)⁻¹ * r * (m : G), hSJ hr⟩ * m⁻¹ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    rw [he, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 hmN _).1 (hπS _ hr)
  have hR3 : IsPGroup 3 ↥R := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hS3
    exact (IsPGroup.iff_card).2 ⟨k, by rw [hR, Lemma1112b.card_glbConj, hk]⟩
  obtain ⟨y, hyY, hy⟩ := Claims1112.exists_conj_le_of_isSylowIn hSYs hRY hR3
  obtain ⟨y', hy'π, rfl⟩ := hyY
  obtain ⟨s₀, hs₀⟩ := hy'π
  set x' : G := (s₀ : G) * (y' : G)⁻¹ * (m : G) with hx'
  have hx'J : x' ∈ J := J.mul_mem (J.mul_mem (hSJ s₀.2) (J.inv_mem y'.2)) m.2
  have hx'S : ∀ t ∈ S, x' * t * x'⁻¹ ∈ S := by
    intro t ht
    have h1 : (m : G) * t * (m : G)⁻¹ ∈ R := by
      rw [hR, mem_gLBConj, inv_inv]
      have : (m : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) * (m : G) = t := by group
      rw [this]
      exact ht
    have h2 := hy _ h1
    have : x' * t * x'⁻¹ = (s₀ : G) * ((y' : G)⁻¹ * ((m : G) * t * (m : G)⁻¹) * (y' : G)) *
        (s₀ : G)⁻¹ := by
      rw [hx']
      group
    rw [this]
    exact S.mul_mem (S.mul_mem s₀.2 h2) (S.inv_mem s₀.2)
  have hx'N : x' ∈ Subgroup.normalizer (S : Set G) := Subgroup.mem_normalizer_fintype hx'S
  have hx'π : π ⟨x', hx'J⟩ = π m := by
    have he : (⟨x', hx'J⟩ : ↥J) = Subgroup.inclusion hSJ s₀ * y'⁻¹ * m :=
      Subtype.ext (by simp [hx'])
    rw [he, map_mul, map_mul, map_inv]
    have : π (Subgroup.inclusion hSJ s₀) = π y' := hs₀
    rw [this, mul_inv_cancel, one_mul]
  have hkey : ∀ w : G, w ∈ U ↔ x' * w * x'⁻¹ ∈ U' := by
    intro w
    constructor
    · intro hwU
      have hwS := hUS hwU
      have hcS := hx'S w hwS
      have hcJ : x' * w * x'⁻¹ ∈ J := hSJ hcS
      refine (hψmem hU'S _ hcJ hcS).1 ?_
      have he : (⟨x' * w * x'⁻¹, hcJ⟩ : ↥J) = ⟨x', hx'J⟩ * ⟨w, hSJ hwS⟩ * ⟨x', hx'J⟩⁻¹ :=
        Subtype.ext (by simp)
      rw [he, map_mul, map_mul, map_inv, hx'π]
      exact (hmU _).1 ((hψmem hUS w (hSJ hwS) hwS).2 hwU)
    · intro hcU
      have hcS := hU'S hcU
      have hwS : w ∈ S := by
        have h1 : x'⁻¹ * (x' * w * x'⁻¹) * x'⁻¹⁻¹ ∈ S :=
          (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hx'N) _).1 hcS
        have : x'⁻¹ * (x' * w * x'⁻¹) * x'⁻¹⁻¹ = w := by group
        rwa [this] at h1
      have hcJ : x' * w * x'⁻¹ ∈ J := hSJ hcS
      refine (hψmem hUS w (hSJ hwS) hwS).1 ((hmU _).2 ?_)
      have he : (⟨x' * w * x'⁻¹, hcJ⟩ : ↥J) = ⟨x', hx'J⟩ * ⟨w, hSJ hwS⟩ * ⟨x', hx'J⟩⁻¹ :=
        Subtype.ext (by simp)
      have := (hψmem hU'S _ hcJ hcS).2 hcU
      rwa [he, map_mul, map_mul, map_inv, hx'π] at this
  refine ⟨x'⁻¹, J.inv_mem hx'J, Subgroup.inv_mem _ hx'N, ?_⟩
  ext w
  rw [mem_gLBConj, inv_inv, hkey]
  have : x' * (x'⁻¹ * w * x') * x'⁻¹ = w := by group
  rw [this]

section P2Many

variable {G : Type} [Group G] [Finite G]

theorem sylow_facts_sl {J S : Subgroup G} (hSL : IsSLThreeFour (barOf 3 J)) (hS : IsSylowIn 3 J S) :
    Nat.card S = 27 ∧ (∀ x ∈ S, x ^ 3 = 1) ∧ ∃ x ∈ S, ∃ y ∈ S, x * y ≠ y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSJ : S ≤ J := hS.1
  have hS3 : IsPGroup 3 ↥S := hS.2.1
  set π : ↥J →* barOf 3 J := QuotientGroup.mk' (GLAPPrimeCore 3 ↥J) with hπ
  set ψ : ↥S →* barOf 3 J := π.comp (Subgroup.inclusion hSJ) with hψ
  have hψinj : Function.Injective ψ := fun s t hst =>
    Subtype.ext (Claims1112.piK_inj hS3 s.2 t.2 (hSJ s.2) (hSJ t.2) hst)
  have hrange : ψ.range = (S.subgroupOf J).map π := by
    ext z
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨Subgroup.inclusion hSJ s, Subgroup.mem_subgroupOf.2 s.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, Subgroup.mem_subgroupOf.1 hj⟩, rfl⟩
  obtain ⟨-, hZS, hS27⟩ := Claims1112.sylow_image_facts hSL hS
  rw [← hrange] at hZS hS27
  have hcard : Nat.card S = 27 := by
    rw [← hS27]
    exact Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv
  obtain ⟨K, _, hK, ⟨e⟩⟩ := exists_mulEquiv_sl hSL
  have hZP' : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars 3 K ≤
      ψ.range.map e.toMonoidHom := by
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center 3 K,
      ← Subgroup.map_center_eq e]
    exact Subgroup.map_mono hZS
  have hP' : Nat.card (ψ.range.map e.toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective e.injective, hS27]
  obtain ⟨⟨x, hx, y, hy, hxy⟩, hexp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.heis_of_card_sl hK hZP' hP'
  refine ⟨hcard, fun s hs => ?_, ?_⟩
  · have h1 := hexp (e (ψ ⟨s, hs⟩)) ⟨ψ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, rfl⟩
    have h2 : ψ (⟨s, hs⟩ ^ 3) = ψ 1 := by
      apply e.injective
      rw [map_pow, map_pow, h1, map_one, map_one]
    have h3 := hψinj h2
    simpa using congrArg Subtype.val h3
  · obtain ⟨_, ⟨s, rfl⟩, rfl⟩ := hx
    obtain ⟨_, ⟨t, rfl⟩, rfl⟩ := hy
    refine ⟨s, s.2, t, t.2, fun hst => hxy ?_⟩
    have : s * t = t * s := Subtype.ext hst
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, this]

theorem card_centerOf_eq_three {P : Subgroup G} (hP : Nat.card P = 27) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hnc : ∃ x ∈ P, ∃ y ∈ P, x * y ≠ y * x) : Nat.card (centerOf P) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : IsPGroup 3 ↥P := IsPGroup.of_card (n := 3) (by rw [hP]; norm_num)
  have hnc' : ¬ IsMulCommutative ↥P := by
    rintro ⟨⟨hcomm⟩⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hnc
    exact hxy (congrArg Subtype.val (hcomm ⟨x, hx⟩ ⟨y, hy⟩))
  have hx := CFSG.RankThree.PartTwo.isExtraspecialPGroup_of_card_eq_pow_three h3
    (fun x => Subtype.ext (by simpa using hexp x x.2)) (by rw [hP]; norm_num) hnc'
  rw [centerOf, Subgroup.card_map_of_injective P.subtype_injective]
  exact hx.2.2.2

theorem exists_le_card_nine {P : Subgroup G} (hP : Nat.card P = 27) (hexp : ∀ x ∈ P, x ^ 3 = 1) :
    ∃ U : Subgroup G, U ≤ P ∧ IsElemAbelian 3 U ∧ Nat.card U = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U', hU'⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥P) 3 (n := 2)
    (by rw [hP]; norm_num)
  have hc : Nat.card ↥(U'.map P.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective, hU']
  refine ⟨U'.map P.subtype, Subgroup.map_subtype_le U', ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩, ?_⟩
  · exact IsPGroup.commutative_of_card_eq_prime_sq hc x y
  · rintro _ ⟨u, -, rfl⟩
    exact hexp _ u.2
  · rw [hc]
    norm_num

theorem four_le_pRank {X T J₁ J₂ J₃ : Subgroup G} (hT : IsPGroup 3 ↥T)
    (h₁ : GLAPComponent 3 X J₁) (h₂ : GLAPComponent 3 X J₂) (h₃ : GLAPComponent 3 X J₃)
    (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h23 : J₂ ≠ J₃)
    (hP₁ : Nat.card ↥(T ⊓ J₁) = 27 ∧ (∀ x ∈ T ⊓ J₁, x ^ 3 = 1) ∧
      ∃ x ∈ T ⊓ J₁, ∃ y ∈ T ⊓ J₁, x * y ≠ y * x)
    (hP₂ : Nat.card ↥(T ⊓ J₂) = 27 ∧ (∀ x ∈ T ⊓ J₂, x ^ 3 = 1))
    (hP₃ : Nat.card ↥(T ⊓ J₃) = 27 ∧ (∀ x ∈ T ⊓ J₃, x ^ 3 = 1) ∧
      ∃ x ∈ T ⊓ J₃, ∃ y ∈ T ⊓ J₃, x * y ≠ y * x) :
    4 ≤ CFSG.Open.pRank 3 T := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ∀ {Ki Kj : Subgroup G}, GLAPComponent 3 X Ki → GLAPComponent 3 X Kj → Ki ≠ Kj →
      ∀ r ∈ T ⊓ Ki, ∀ s ∈ T ⊓ Kj, r * s = s * r := fun hi hj hne r hr s hs =>
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.comm_of_inf hT hi hj hne hr hs
  obtain ⟨U₁, hU₁P, hU₁e, hU₁c⟩ := exists_le_card_nine hP₁.1 hP₁.2.1
  obtain ⟨U₂, hU₂P, hU₂e, hU₂c⟩ := exists_le_card_nine hP₂.1 hP₂.2
  obtain ⟨U₃, hU₃P, hU₃e, hU₃c⟩ := exists_le_card_nine hP₃.1 hP₃.2.1
  have hZ₁ := card_centerOf_eq_three hP₁.1 hP₁.2.1 hP₁.2.2
  have hZ₃ := card_centerOf_eq_three hP₃.1 hP₃.2.1 hP₃.2.2
  have hc12 : ∀ x ∈ U₁, ∀ y ∈ U₂, x * y = y * x := fun x hx y hy =>
    hc h₁ h₂ h12 x (hU₁P hx) y (hU₂P hy)
  have hU12e : IsElemAbelian 3 (U₁ ⊔ U₂) := Lemma1111.isElemAbelian_sup hU₁e hU₂e hc12
  have hcent12 : U₁ ≤ Subgroup.centralizer (U₂ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hc12 x hx y hy).symm
  have hcard12 := input31_card_sup_mul_card_inf hcent12
  have hinf12 : Nat.card (U₁ ⊓ U₂ : Subgroup G) ≤ 3 := by
    rw [← hZ₁]
    refine Subgroup.card_le_of_le fun w hw => (Lemma1111.mem_centerOf_iff _ w).2
      ⟨hU₁P hw.1, fun r hr => hc h₁ h₂ h12 r hr w (hU₂P hw.2)⟩
  have hle3 : U₁ ⊔ U₂ ≤ Subgroup.centralizer ((T ⊓ J₃ : Subgroup G) : Set G) := sup_le
    (fun u hu => Subgroup.mem_centralizer_iff.2 fun z hz => (hc h₁ h₃ h13 u (hU₁P hu) z hz).symm)
    (fun u hu => Subgroup.mem_centralizer_iff.2 fun z hz => (hc h₂ h₃ h23 u (hU₂P hu) z hz).symm)
  have hc3 : ∀ x ∈ U₁ ⊔ U₂, ∀ y ∈ T ⊓ J₃, x * y = y * x := fun x hx y hy =>
    ((Subgroup.mem_centralizer_iff.1 (hle3 hx)) y hy).symm
  have hW : IsElemAbelian 3 (U₁ ⊔ U₂ ⊔ U₃) :=
    Lemma1111.isElemAbelian_sup hU12e hU₃e (fun x hx y hy => hc3 x hx y (hU₃P hy))
  have hcent3 : U₁ ⊔ U₂ ≤ Subgroup.centralizer (U₃ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy => (hc3 x hx y (hU₃P hy)).symm
  have hcard3 := input31_card_sup_mul_card_inf hcent3
  have hinf3 : Nat.card ((U₁ ⊔ U₂) ⊓ U₃ : Subgroup G) ≤ 3 := by
    rw [← hZ₃]
    refine Subgroup.card_le_of_le fun w hw => (Lemma1111.mem_centerOf_iff _ w).2
      ⟨hU₃P hw.2, fun r hr => (hc3 w hw.1 r hr).symm⟩
  have hWcard : 81 ≤ Nat.card (U₁ ⊔ U₂ ⊔ U₃ : Subgroup G) := by
    rw [hU₁c, hU₂c] at hcard12
    rw [hU₃c] at hcard3
    have hpos1 : 0 < Nat.card (U₁ ⊓ U₂ : Subgroup G) := Nat.card_pos
    have hpos3 : 0 < Nat.card ((U₁ ⊔ U₂) ⊓ U₃ : Subgroup G) := Nat.card_pos
    have h27 : 27 ≤ Nat.card (U₁ ⊔ U₂ : Subgroup G) := by nlinarith
    nlinarith
  have hWT : U₁ ⊔ U₂ ⊔ U₃ ≤ T :=
    sup_le (sup_le (hU₁P.trans inf_le_left) (hU₂P.trans inf_le_left)) (hU₃P.trans inf_le_left)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hT.to_le hWT)
  have hk4 : 4 ≤ k := by
    rw [hk] at hWcard
    by_contra hlt
    push Not at hlt
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact hk4.trans (Lemma1112b.le_pRank_of_card hWT hW hk)

theorem le_of_frattini {X N P M : Subgroup G} (hXN : ∀ g ∈ X, ∀ n ∈ N, g * n * g⁻¹ ∈ N)
    (hP : IsSylowIn 3 N P) (hNM : N ≤ M) (hPM : Subgroup.normalizer (P : Set G) ≤ M) : X ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro g hg
  have hR : GLBConj g⁻¹ P ≤ N := by
    intro r hr
    rw [mem_gLBConj, inv_inv] at hr
    have := hXN g hg _ (hP.1 hr)
    have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
    rwa [e] at this
  have hR3 : IsPGroup 3 ↥(GLBConj g⁻¹ P) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP.2.1
    exact (IsPGroup.iff_card).2 ⟨k, by rw [card_glbConj, hk]⟩
  obtain ⟨y, hyN, hy⟩ := Claims1112.exists_conj_le_of_isSylowIn hP hR hR3
  have hn : y⁻¹ * g ∈ Subgroup.normalizer (P : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun p hp => ?_
    have h1 : g * p * g⁻¹ ∈ GLBConj g⁻¹ P := by
      rw [mem_gLBConj, inv_inv]
      have e : g⁻¹ * (g * p * g⁻¹) * g = p := by group
      rw [e]
      exact hp
    have e : y⁻¹ * g * p * (y⁻¹ * g)⁻¹ = y⁻¹ * (g * p * g⁻¹) * y := by group
    rw [e]
    exact hy _ h1
  have e : g = y * (y⁻¹ * g) := by group
  rw [e]
  exact M.mul_mem (hNM hyN) (hPM hn)

theorem le_of_normalizes_component (h104v : Lemma104_vStatement) {m : ℕ}
    {B M E A : Subgroup G} (h : Sec11 G m 3 B M E A) (hA3 : CFSG.Open.pRank 3 A = 3)
    (hE4 : 4 ≤ CFSG.Open.pRank 3 E) {R : Subgroup G} (hR : IsSylowIn 3 M R) (hER : E ≤ R)
    {H : Subgroup G} (hRH : IsSylowIn 3 H R) {J : Subgroup G} (hJH : J ≤ H)
    (hHN : H ≤ Subgroup.normalizer (J : Set G)) (hJSL : IsSLThreeFour (barOf 3 J)) (hJM : J ≤ M) :
    H ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hJnorm : ∀ y ∈ H, ∀ n ∈ J, y * n * y⁻¹ ∈ J := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.1 (hHN hy) n).1 hn
  have hSsyl : IsSylowIn 3 J (R ⊓ J) := Claims1112.isSylowIn_inf_of_normal hRH hJH hJnorm
  obtain ⟨-, -, ⟨x₀, hx₀, y₀, hy₀, hxy⟩⟩ := sylow_facts_sl hJSL hSsyl
  have hSnorm : ((R ⊓ J).subgroupOf R).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨-, hnJ⟩ := Subgroup.mem_inf.1 hn
    exact Subgroup.mem_inf.2 ⟨R.mul_mem (R.mul_mem g.2 n.2) (R.inv_mem g.2),
      (Subgroup.mem_normalizer_iff.1 (hHN (hRH.1 g.2)) n).1 hnJ⟩⟩
  have hnc : ¬ IsCyclic ↥(R ⊓ J) := by
    intro hcyc
    letI : CommGroup ↥(R ⊓ J) := IsCyclic.commGroup
    exact hxy (congrArg Subtype.val (mul_comm (⟨x₀, hx₀⟩ : ↥(R ⊓ J)) ⟨y₀, hy₀⟩))
  obtain ⟨U, hUS, hU, hUN⟩ := input31_5_holds G 3 Nat.prime_three (by norm_num) R (R ⊓ J)
    hRH.2.1 inf_le_left hSnorm hnc
  have hNU : Subgroup.normalizer (U : Set G) ≤ M :=
    Claims1112.normalizer_le_of_normal_plane h104v h hA3 hE4 hR hER hU (hUS.trans inf_le_left) hUN
  intro g hg
  have hgN : g ∈ Subgroup.normalizer (J : Set G) := hHN hg
  set S : Subgroup G := R ⊓ J with hSdef
  have hS₁J : GLBConj g⁻¹ S ≤ J := by
    intro r hr
    rw [mem_gLBConj] at hr
    have hrJ : g⁻¹ * r * g⁻¹⁻¹ ∈ J := (Subgroup.mem_inf.1 hr).2
    have := (Subgroup.mem_normalizer_iff.1 hgN _).1 hrJ
    have e : g * (g⁻¹ * r * g⁻¹⁻¹) * g⁻¹ = r := by group
    rwa [e] at this
  have hS₁3 : IsPGroup 3 ↥(GLBConj g⁻¹ S) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hSsyl.2.1
    exact (IsPGroup.iff_card).2 ⟨n, by rw [card_glbConj, hn]⟩
  obtain ⟨j, hjJ, hj⟩ := Claims1112.exists_conj_le_of_isSylowIn hSsyl hS₁J hS₁3
  have hg'S : ∀ s ∈ S, (j⁻¹ * g) * s * (j⁻¹ * g)⁻¹ ∈ S := by
    intro s hs
    have hs₁ : g * s * g⁻¹ ∈ GLBConj g⁻¹ S := by
      rw [mem_gLBConj]
      have e : g⁻¹ * (g * s * g⁻¹) * g⁻¹⁻¹ = s := by group
      rw [e]
      exact hs
    have := hj _ hs₁
    have e : (j⁻¹ * g) * s * (j⁻¹ * g)⁻¹ = j⁻¹ * (g * s * g⁻¹) * j := by group
    rw [e]
    exact this
  set g' : G := j⁻¹ * g with hg'
  have hg'N : g' ∈ Subgroup.normalizer (S : Set G) := Subgroup.mem_normalizer_fintype hg'S
  have hU' : IsPPlane 3 (GLBConj g'⁻¹ U) :=
    ⟨isElemAbelian_glbConj hU.1 _, by rw [card_glbConj]; exact hU.2⟩
  have hU'S : GLBConj g'⁻¹ U ≤ S := by
    intro z hz
    rw [mem_gLBConj] at hz
    have h1 : g'⁻¹ * z * g'⁻¹⁻¹ ∈ S := hUS hz
    have h2 := (Subgroup.mem_normalizer_iff.1 hg'N _).1 h1
    have e : g' * (g'⁻¹ * z * g'⁻¹⁻¹) * g'⁻¹ = z := by group
    rwa [e] at h2
  obtain ⟨x, hxJ, -, hxU⟩ := inputSL34PlaneTransitive_holds G J S hJSL hSsyl _ U hU'S hUS hU' hU
  have hnU : g'⁻¹ * x ∈ Subgroup.normalizer (U : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    have h1 : z ∈ U ↔ z ∈ GLBConj x (GLBConj g'⁻¹ U) := by rw [hxU]
    rw [h1, mem_gLBConj, mem_gLBConj]
    have e : g'⁻¹ * (x * z * x⁻¹) * g'⁻¹⁻¹ = g'⁻¹ * x * z * (g'⁻¹ * x)⁻¹ := by group
    rw [e]
  have hgeq : g = j * x * (g'⁻¹ * x)⁻¹ := by
    rw [hg']
    group
  rw [hgeq]
  exact M.mul_mem (M.mul_mem (hJM hjJ) (hJM hxJ)) (M.inv_mem (hNU hnU))

theorem mem_of_mul_self_mem {H : Subgroup G} {x : G} (hx : ∃ k : ℕ, orderOf x = 3 ^ k)
    (h : x * x ∈ H) : x ∈ H := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨t, ht⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have e : (x * x) ^ (t + 1) = x := by
    rw [← sq, ← pow_mul, show 2 * (t + 1) = 3 ^ k + 1 by omega, pow_succ, ← hk,
      pow_orderOf_eq_one, one_mul]
  rw [← e]
  exact H.pow_mem h _

end P2Many

theorem lemma1111P2Many_of_inputs (h1110 : Lemma1110Statement) (h119 : Lemma119Statement) :
    Claims1112.Lemma1111P2Many := by
  intro G _ _ m B M E A a K h hSL R hR hER e he he1 J hJ hJSL hJN
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsc := lemma104_ii_holds h.toCex117Base.toSec11.toSec10Fails h.pair
  have hRtop : IsSylowIn 3 ⊤ R :=
    (lemma104_iv_holds h.toCex117Base.toSec11.toSec10Fails h.pair (h119 h).1 hR).2.2
  have heEA : e ∈ E ⊓ A := Claims1112.mem_inf_of_omegaOne hsc.1 hsc.2 (le_sup_left.trans hER)
    (le_sup_right.trans hER) he
  have heE : e ∈ E := (Subgroup.mem_inf.1 heEA).1
  have hA3 : CFSG.Open.pRank 3 A = 3 := by
    have hT := h1110 h
    unfold Type117c at hT
    exact hT.2.1
  have hE4 : 4 ≤ CFSG.Open.pRank 3 E :=
    lemma113_i_holds h.toCex117Base.toSec11 h.ha.1 h.ha.2 (fun hx => h.notD hx)
  have hReC : R ≤ Cg e := Claims1112.le_cg_of_omegaOne he
  have hRC : IsSylowIn 3 (Cg e) R :=
    ⟨hReC, hRtop.2.1, fun R' _ hR'3 hRR' => hRtop.2.2 R' le_top hR'3 hRR'⟩
  have hcore : GLBCore 3 4 R ≤ M :=
    (lemma104_v_holds h.toCex117Base.toSec11.toSec10Fails h.pair (Or.inr hA3) hR).2
  have hcompM : ∀ L, GLAPComponent 3 (Cg e) L → IsSLThreeFour (barOf 3 L) → L ≤ M :=
    fun L hL hLSL => h.pair.1.1.2.clause_e rfl e heE he1 L hL (Or.inr hLSL)
  have hconjC : ∀ c ∈ Cg e, GLBConj c (Cg e) = Cg e := fun c hc =>
    gLBConj_eq_of_mem_normalizer (Subgroup.le_normalizer hc)
  have hconjcomp : ∀ c ∈ Cg e, ∀ L, GLAPComponent 3 (Cg e) L → IsSLThreeFour (barOf 3 L) →
      GLAPComponent 3 (Cg e) (GLBConj c L) ∧ IsSLThreeFour (barOf 3 (GLBConj c L)) := by
    intro c hc L hL hLSL
    refine ⟨?_, CFSG.HardMathSupport.Solomon.UniquenessMaximal.EvenSL.isSLThreeFour_of_mulEquiv
      (conjQuotEquiv 3 c L).symm hLSL⟩
    have := glaPComponent_gLBConj hL c
    rwa [hconjC c hc] at this
  have hEel : IsElemAbelian 3 E := h.pair.1.1.1.1.2.1
  obtain ⟨W, hWE, hWel, hWcard⟩ := exists_le_isElemAbelian_card hEel (n := 4) (by
    rw [Lemma1112.card_eq_pow_pRank hEel]
    exact pow_dvd_pow 3 hE4)
  have hR4 : 4 ≤ CFSG.Open.pRank 3 R :=
    Lemma1112b.le_pRank_of_card (hWE.trans (le_sup_left.trans hER)) hWel hWcard
  have hGinj : ∀ {g : G} {X Y : Subgroup G}, GLBConj g X = GLBConj g Y → X = Y := by
    intro g X Y hXY
    have := congrArg (GLBConj g⁻¹) hXY
    rwa [gLBConj_gLBConj, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one, gLBConj_one] at this
  by_cases hcase : ∃ c₁ ∈ Cg e, ∃ c₂ ∈ Cg e,
      GLBConj c₁ J ≠ J ∧ GLBConj c₂ J ≠ J ∧ GLBConj c₁ J ≠ GLBConj c₂ J
  ·
    obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, h12⟩ := hcase
    set 𝒮 : Set (Subgroup G) := {L | GLAPComponent 3 (Cg e) L ∧ IsSLThreeFour (barOf 3 L)}
      with h𝒮
    set N : Subgroup G := sSup 𝒮 with hN
    have hNM : N ≤ M := sSup_le fun L hL => hcompM L hL.1 hL.2
    have hNC : N ≤ Cg e := sSup_le fun L hL => hL.1.1
    have hNn : ∀ d ∈ Cg e, ∀ x ∈ N, d * x * d⁻¹ ∈ N := by
      intro d hd x hx
      have hle : N ≤ GLBConj d N := sSup_le fun L hL w hw => by
        rw [mem_gLBConj]
        have hmem : d * w * d⁻¹ ∈ GLBConj d⁻¹ L := by
          rw [mem_gLBConj]
          have e : d⁻¹ * (d * w * d⁻¹) * d⁻¹⁻¹ = w := by group
          rw [e]
          exact hw
        exact (le_sSup (show GLBConj d⁻¹ L ∈ 𝒮 from hconjcomp d⁻¹ (Subgroup.inv_mem _ hd) L hL.1 hL.2) :
          GLBConj d⁻¹ L ≤ N) hmem
      exact mem_gLBConj.1 (hle hx)
    have hLn : ∀ L ∈ 𝒮, ∀ y ∈ N, ∀ n ∈ L, y * n * y⁻¹ ∈ L := by
      intro L hL y hy n hn
      have hle : N ≤ Subgroup.normalizer (L : Set G) := sSup_le fun L' hL' => by
        by_cases hLL : L' = L
        · rw [hLL]
          exact Subgroup.le_normalizer
        · exact CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.q_le_normalizer_of_ne hL'.1 hL.1
            hLL
      exact (Subgroup.mem_normalizer_iff.1 (hle hy) n).1 hn
    set T : Subgroup G := R ⊓ N with hTdef
    have hT : IsSylowIn 3 N T := Claims1112.isSylowIn_inf_of_normal hRC hNC hNn
    have hJ1 : J ∈ 𝒮 := ⟨hJ, hJSL⟩
    have hJ2 : GLBConj c₁ J ∈ 𝒮 := hconjcomp c₁ hc₁ J hJ hJSL
    have hJ3 : GLBConj c₂ J ∈ 𝒮 := hconjcomp c₂ hc₂ J hJ hJSL
    have hfacts : ∀ L ∈ 𝒮, Nat.card ↥(T ⊓ L) = 27 ∧ (∀ x ∈ T ⊓ L, x ^ 3 = 1) ∧
        ∃ x ∈ T ⊓ L, ∃ y ∈ T ⊓ L, x * y ≠ y * x := fun L hL =>
      sylow_facts_sl hL.2 (Claims1112.isSylowIn_inf_of_normal hT (le_sSup hL) (hLn L hL))
    have h4 : 4 ≤ CFSG.Open.pRank 3 T :=
      four_le_pRank hT.2.1 hJ1.1 hJ2.1 hJ3.1 (Ne.symm h1) (Ne.symm h2) h12 (hfacts _ hJ1)
        ⟨(hfacts _ hJ2).1, (hfacts _ hJ2).2.1⟩ (hfacts _ hJ3)
    have hNT : Subgroup.normalizer (T : Set G) ≤ M :=
      (le_sSup ⟨T, inf_le_left, h4, rfl⟩ : Subgroup.normalizer (T : Set G) ≤ GLBCore 3 4 R).trans
        hcore
    exact le_of_frattini hNn hT hNM hNT
  ·
    push Not at hcase
    obtain ⟨y₀, hy₀C, hy₀⟩ : ∃ y₀ ∈ Cg e, GLBConj y₀ J ≠ J := by
      by_contra hc
      push Not at hc
      exact hJN fun c hc' => mem_normalizer_iff_gLBConj_eq.2 (hc c hc')
    set J' : Subgroup G := GLBConj y₀ J with hJ'
    have hdich : ∀ c ∈ Cg e, GLBConj c J = J ∨ GLBConj c J = J' := by
      intro c hc
      by_cases hcJ : GLBConj c J = J
      · exact Or.inl hcJ
      · exact Or.inr (hcase c hc y₀ hy₀C hcJ hy₀)
    set N₀ : Subgroup G := Cg e ⊓ Subgroup.normalizer (J : Set G) with hN₀
    have hfixJ : ∀ g ∈ N₀, GLBConj g J = J := fun g hg =>
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.mem_inf.1 hg).2
    have hfixJ' : ∀ g ∈ N₀, GLBConj g J' = J' := by
      intro g hg
      have hgC : g ∈ Cg e := (Subgroup.mem_inf.1 hg).1
      have he1 : GLBConj g J' = GLBConj (y₀ * g) J := gLBConj_gLBConj g y₀ J
      rcases hdich (y₀ * g) (Subgroup.mul_mem _ hy₀C hgC) with h1 | h1
      · exfalso
        apply hy₀
        apply hGinj (g := g)
        calc GLBConj g J' = GLBConj (y₀ * g) J := he1
          _ = J := h1
          _ = GLBConj g J := (hfixJ g hg).symm
      · rw [he1, h1]
    have hN₀n : ∀ c ∈ Cg e, ∀ g ∈ N₀, c * g * c⁻¹ ∈ N₀ := by
      intro c hc g hg
      have hgC : g ∈ Cg e := (Subgroup.mem_inf.1 hg).1
      refine Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hgC)
        (Subgroup.inv_mem _ hc), mem_normalizer_iff_gLBConj_eq.2 ?_⟩
      have hL : GLBConj g (GLBConj c J) = GLBConj c J := by
        rcases hdich c hc with h1 | h1
        · rw [h1, hfixJ g hg]
        · rw [h1, hfixJ' g hg]
      rw [← gLBConj_gLBConj, ← gLBConj_gLBConj, hL, gLBConj_gLBConj, mul_inv_cancel, gLBConj_one]
    have hRN₀ : R ≤ N₀ := by
      intro x hx
      refine Subgroup.mem_inf.2 ⟨hReC hx, ?_⟩
      have hxC : x ∈ Cg e := hReC hx
      have hsq : x * x ∈ Subgroup.normalizer (J : Set G) := by
        rw [mem_normalizer_iff_gLBConj_eq]
        by_cases hxJ : GLBConj x J = J
        · rw [← gLBConj_gLBConj, hxJ, hxJ]
        · have hxJ' : GLBConj x J = J' := (hdich x hxC).resolve_left hxJ
          rcases hdich (x * x) (Subgroup.mul_mem _ hxC hxC) with h1 | h1
          · exact h1
          · exfalso
            apply hy₀
            apply hGinj (g := x)
            calc GLBConj x J' = GLBConj x (GLBConj x J) := by rw [hxJ']
              _ = GLBConj (x * x) J := gLBConj_gLBConj x x J
              _ = J' := h1
              _ = GLBConj x J := hxJ'.symm
      have hord : ∃ k : ℕ, orderOf x = 3 ^ k := by
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hRtop.2.1) ⟨x, hx⟩
        exact ⟨k, by rw [← hk, Subgroup.orderOf_mk]⟩
      exact mem_of_mul_self_mem hord hsq
    have hRsyl : IsSylowIn 3 N₀ R :=
      ⟨hRN₀, hRtop.2.1, fun R' _ hR'3 hRR' => hRtop.2.2 R' le_top hR'3 hRR'⟩
    have hN₀M : N₀ ≤ M :=
      le_of_normalizes_component lemma104_v_holds h.toCex117Base.toSec11 hA3 hE4 hR
        (le_sup_left.trans hER) hRsyl (le_inf hJ.1 Subgroup.le_normalizer) inf_le_right hJSL
        (hcompM J hJ hJSL)
    have hNR : Subgroup.normalizer (R : Set G) ≤ M :=
      (le_sSup ⟨R, le_refl R, hR4, rfl⟩ : Subgroup.normalizer (R : Set G) ≤ GLBCore 3 4 R).trans
        hcore
    exact le_of_frattini hN₀n hRsyl hN₀M hNR

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1111b

end
