module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bQ8
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21bRed

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open KFactsSmall
open scoped Pointwise commutatorElement

namespace K21dRedProof

theorem isK21dGroup_of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : IsK21dGroup S) : IsK21dGroup S' := by
  rcases h with ⟨d, Q, hcase, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩
  · exact Or.inl ⟨d, Q, hcase, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨n, hn, ⟨e.symm.trans f⟩⟩))

theorem primePower_p_eq_two_of_card {q : TauCeti.PrimePower} {n : ℕ} (hn : n = 2 ∨ n = 4)
    (hq : q.card = n) : q.p = 2 := by
  have h1 : q.card = q.p ^ q.exponent := TauCeti.PrimePower.card_def q
  have hp : q.p.Prime := q.prime_p
  have h2 : q.p ∣ n := by
    rw [← hq, h1]
    exact dvd_pow_self _ (by have := q.exponent_pos; omega)
  rcases hn with rfl | rfl
  · exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2
  · have h4 : q.p ∣ 2 ^ 2 := by simpa using h2
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4)

theorem isClassicalTwoOrG2_of_isK21dGroup {S : Type} [Group S] (h : IsK21dGroup S) :
    CFSG.AGLEmbedding.IsClassicalTwoOrG2 S := by
  rcases h with ⟨d, Q, hcase, he⟩ | h5 | hU | ⟨n, hn, he⟩
  · rcases hcase with ⟨hQ, hd4⟩ | ⟨hc4, hd⟩
    · refine Or.inl ⟨d, ?_, he⟩
      rcases hd4 with hd | hd | hd | hd <;> (rw [hd]; exact hQ)
    · refine Or.inl ⟨d, ?_, he⟩
      rw [hd]
      exact primePower_p_eq_two_of_card (Or.inr rfl) hc4
  · obtain ⟨d, ⟨q, hq, hd⟩, e⟩ := h5
    refine Or.inl ⟨d, ?_, e⟩
    rw [hd]
    exact primePower_p_eq_two_of_card (Or.inl rfl) hq
  · obtain ⟨d, ⟨q, hq, hd⟩, e⟩ := hU
    exact Or.inr (Or.inr ⟨d, Or.inr ⟨q, hq, hd⟩, e⟩)
  · rcases hn with rfl | rfl
    · exact Or.inr (Or.inl ⟨6, Or.inr (Or.inl rfl), he⟩)
    · exact Or.inr (Or.inl ⟨8, Or.inr (Or.inr rfl), he⟩)

theorem isClassicalTwoOrG2_of_mulEquiv {Y Y' : Type} [Group Y] [Group Y'] (e : Y ≃* Y')
    (h : CFSG.AGLEmbedding.IsClassicalTwoOrG2 Y') : CFSG.AGLEmbedding.IsClassicalTwoOrG2 Y := by
  rcases h with ⟨d, hd, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨d, hd, ⟨e'⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.trans e'⟩⟩)

noncomputable def mulEquivInnAut (S : Type) [Group S] (hZ : Subgroup.center S = ⊥) :
    S ≃* ↥(innAut S) :=
  (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans
    ((QuotientGroup.quotientMulEquivOfEq (K21bRedProof.ker_conj_eq_center S).symm).trans
      (QuotientGroup.quotientKerEquivRange (MulAut.conj : S →* MulAut S)))

theorem isK21dGroup_innAut {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (h : IsK21dGroup S) : IsK21dGroup ↥(innAut S) :=
  isK21dGroup_of_mulEquiv (mulEquivInnAut S hZ) h

theorem center_eq_bot_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have ha : a ∈ Subgroup.center S := by rw [h]; exact Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem isQuasisimple_of_simple {S : Type} [Group S] [IsSimpleGroup S]
    (hnc : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  have hZ := center_eq_bot_of_simple hnc
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnc
      have h1 : ⁅a, b⁆ ∈ commutator S := Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
        (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact hab (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h1))
    · exact h
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem q8_cases (g : QuaternionGroup 2) :
    g = 1 ∨ g = QuaternionGroup.a 2 ∨ g * g = QuaternionGroup.a 2 := by
  revert g
  decide

theorem q8_central (g : QuaternionGroup 2) :
    QuaternionGroup.a 2 * g = g * QuaternionGroup.a 2 := by
  revert g
  decide

theorem q8_comm (g h : QuaternionGroup 2) (hgh : g * h ≠ h * g) :
    g * h * g⁻¹ * h⁻¹ = QuaternionGroup.a 2 := by
  revert g h
  decide

theorem q8_a2_sq : QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) := by
  decide

theorem q8_a2_ne_one : QuaternionGroup.a 2 ≠ (1 : QuaternionGroup 2) := by
  decide

theorem exists_central_inversion {E : Type} [Group E] [Finite E] (hV : ∀ x y : E, x * y = y * x)
    (hp : ∀ x : E, x ^ 3 = 1) (hc : Nat.card E = 9) {Q : Subgroup (MulAut E)}
    (e : ↥Q ≃* QuaternionGroup 2) :
    ∃ z : MulAut E, z ∈ Q ∧ z ≠ 1 ∧ z * z = 1 ∧ (∀ q ∈ Q, z * q = q * z) ∧
      (∀ q ∈ Q, q ≠ 1 → q = z ∨ q * q = z) ∧ (∀ x : E, z x = x⁻¹) ∧
      (∀ a ∈ Q, ∀ b ∈ Q, a * b ≠ b * a → a * b * a⁻¹ * b⁻¹ = z) := by
  set z : ↥Q := e.symm (QuaternionGroup.a 2) with hz
  have hz1 : z ≠ 1 := by
    intro h
    apply q8_a2_ne_one
    have h1 := congrArg e h
    rw [hz, MulEquiv.apply_symm_apply, map_one] at h1
    exact h1
  have hzz : z * z = 1 := by rw [hz, ← map_mul, q8_a2_sq, map_one]
  have hzc : ∀ q : ↥Q, z * q = q * z := by
    intro q
    apply e.injective
    rw [map_mul, map_mul, hz, MulEquiv.apply_symm_apply]
    exact q8_central _
  have hzq : ∀ q : ↥Q, q ≠ 1 → q = z ∨ q * q = z := by
    intro q hq
    rcases q8_cases (e q) with h | h | h
    · exact absurd (e.injective (by rw [h, map_one])) hq
    · exact Or.inl (e.injective (by rw [h, hz, MulEquiv.apply_symm_apply]))
    · refine Or.inr (e.injective ?_)
      rw [map_mul, h, hz, MulEquiv.apply_symm_apply]
  have hcomm : ∀ a b : ↥Q, a * b ≠ b * a → a * b * a⁻¹ * b⁻¹ = z := by
    intro a b hab
    apply e.injective
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hz, MulEquiv.apply_symm_apply]
    exact q8_comm _ _ (fun h => hab (e.injective (by rw [map_mul, map_mul, h])))
  have hzz' : ∀ x : E, (z : MulAut E) ((z : MulAut E) x) = x := by
    intro x
    have h := congrArg (fun σ : ↥Q => ((σ : MulAut E) x)) hzz
    simpa [MulAut.mul_apply] using h
  let F : Subgroup E :=
    { carrier := {x | (z : MulAut E) x = x}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_inv, ha] }
  have hF : ∀ a ∈ Q, ∀ x ∈ F, a x ∈ F := by
    intro a ha x hx
    have h1 := congrArg (fun σ : ↥Q => ((σ : MulAut E) x)) (hzc ⟨a, ha⟩)
    have hx' : (z : MulAut E) x = x := hx
    show (z : MulAut E) (a x) = a x
    simp only [Subgroup.coe_mul, MulAut.mul_apply] at h1
    rw [h1, hx']
  have hdich := eq_bot_or_eq_top_of_hasQ8 hV hp hc (A := Q) ⟨Q, le_rfl, ⟨e⟩⟩ F hF
  have hbot : ∀ x : E, (z : MulAut E) x = x → x = 1 := by
    intro x hx
    rcases hdich with h | h
    · exact Subgroup.mem_bot.mp (h ▸ (show x ∈ F from hx))
    · exfalso
      apply hz1
      apply Subtype.ext
      ext y
      have hy : y ∈ F := h ▸ Subgroup.mem_top y
      exact hy
  have hinv : ∀ x : E, (z : MulAut E) x = x⁻¹ := by
    intro x
    have hw : (z : MulAut E) (x * (z : MulAut E) x) = x * (z : MulAut E) x := by
      rw [map_mul, hzz', hV]
    exact eq_inv_of_mul_eq_one_right (hbot _ hw)
  refine ⟨(z : MulAut E), z.2, fun h => hz1 (Subtype.ext h),
    by simpa using congrArg Subtype.val hzz, fun q hq => congrArg Subtype.val (hzc ⟨q, hq⟩),
    fun q hq hq1 => ?_, hinv, fun a ha b hb hab => ?_⟩
  · rcases hzq ⟨q, hq⟩ (fun h => hq1 (congrArg Subtype.val h)) with h | h
    · exact Or.inl (congrArg Subtype.val h)
    · exact Or.inr (congrArg Subtype.val h)
  · exact congrArg Subtype.val (hcomm ⟨a, ha⟩ ⟨b, hb⟩ (fun h => hab (congrArg Subtype.val h)))

theorem q8_transitive {E : Type} [Group E] [Finite E] (hV : ∀ x y : E, x * y = y * x)
    (hp : ∀ x : E, x ^ 3 = 1) (hc : Nat.card E = 9) {Q : Subgroup (MulAut E)}
    (e : ↥Q ≃* QuaternionGroup 2) {x y : E} (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ q ∈ Q, q x = y := by
  obtain ⟨z, hzQ, hz1, hzz, hzc, hzq, hinv, -⟩ := exists_central_inversion hV hp hc e
  have hfree : ∀ q ∈ Q, ∀ x : E, x ≠ 1 → q x = x → q = 1 := by
    intro q hq x hx hqx
    by_contra hq1
    apply hx
    have hzx : z x = x := by
      rcases hzq q hq hq1 with h | h
      · rw [← h]
        exact hqx
      · rw [← h, MulAut.mul_apply, hqx, hqx]
    have h1 : x⁻¹ = x := by rw [← hinv x]; exact hzx
    have h2 : x * x = 1 := by
      calc x * x = x * x⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel x
    calc x = x * (x * x) := by rw [h2, mul_one]
      _ = x ^ 3 := (pow_three x).symm
      _ = 1 := hp x
  let f : ↥Q → E := fun q => (q : MulAut E) x
  have hinj : Function.Injective f := by
    intro q q' h
    have h1 : ((q⁻¹ * q' : ↥Q) : MulAut E) x = x := by
      have h2 : (q' : MulAut E) x = (q : MulAut E) x := h.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply, h2, MulAut.inv_apply_self]
    have h3 := hfree _ (q⁻¹ * q').2 x hx h1
    exact inv_mul_eq_one.mp (Subtype.ext h3)
  have hQ8 : Nat.card ↥Q = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hsub : Set.range f ⊆ {y : E | y ≠ 1} := by
    rintro _ ⟨q, rfl⟩ h
    exact hx ((MulEquiv.map_eq_one_iff (q : MulAut E)).mp h)
  have hcard : ({y : E | y ≠ 1} : Set E).ncard = 8 := by
    have h1 : ({y : E | y ≠ 1} : Set E) = Set.univ \ {1} := by ext y; simp
    rw [h1, Set.ncard_diff_singleton_of_mem (Set.mem_univ 1), Set.ncard_univ, hc]
  have hrange : (Set.range f).ncard = 8 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj, hQ8]
  have heq : Set.range f = {y : E | y ≠ 1} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, hrange]) (Set.toFinite _)
  have hy' : y ∈ Set.range f := by rw [heq]; exact hy
  obtain ⟨q, hq⟩ := hy'
  exact ⟨q, q.2, hq⟩

theorem conj_mem_stab {G : Type} [Group G] (T Inn E : Subgroup G) [Inn.Normal] {w x g : G}
    (hwT : w ∈ T) (hwE : w ∈ Subgroup.normalizer (E : Set G))
    (hg : g ∈ T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) :
    w * g * w⁻¹ ∈ T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({w * x * w⁻¹} : Set G) := by
  refine ⟨⟨⟨T.mul_mem (T.mul_mem hwT hg.1.1.1) (T.inv_mem hwT), ?_⟩,
    (Subgroup.normalizer (E : Set G)).mul_mem
      ((Subgroup.normalizer (E : Set G)).mul_mem hwE hg.1.2)
      ((Subgroup.normalizer (E : Set G)).inv_mem hwE)⟩, ?_⟩
  · exact Subgroup.Normal.conj_mem inferInstance g hg.1.1.2 w
  · refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hxg : x * g = g * x := Subgroup.mem_centralizer_iff.mp hg.2 x rfl
    calc w * x * w⁻¹ * (w * g * w⁻¹) = w * (x * g) * w⁻¹ := by group
      _ = w * (g * x) * w⁻¹ := by rw [hxg]
      _ = w * g * w⁻¹ * (w * x * w⁻¹) := by group

theorem card_stab_eq {G : Type} [Group G] (T Inn E : Subgroup G) [Inn.Normal] {w x : G}
    (hwT : w ∈ T) (hwE : w ∈ Subgroup.normalizer (E : Set G)) :
    Nat.card ↥(T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({w * x * w⁻¹} : Set G)) := by
  refine Nat.card_congr ⟨fun g => ⟨w * g.1 * w⁻¹, conj_mem_stab T Inn E hwT hwE g.2⟩,
    fun g => ⟨w⁻¹ * g.1 * w⁻¹⁻¹, ?_⟩, fun g => Subtype.ext (by group),
    fun g => Subtype.ext (by group)⟩
  have h := conj_mem_stab T Inn E (w := w⁻¹) (x := w * x * w⁻¹) (g := g.1) (T.inv_mem hwT)
    ((Subgroup.normalizer (E : Set G)).inv_mem hwE) g.2
  rwa [show w⁻¹ * (w * x * w⁻¹) * w⁻¹⁻¹ = x by group] at h

theorem card_stab_eq_of_hasQ8 {G : Type} [Group G] (T Inn E : Subgroup G) [Inn.Normal]
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hQ8 : HasQ8 (autInduced T E))
    {x y : G} (hx : x ∈ E) (hy : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) :
    Nat.card ↥(T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) =
      Nat.card ↥(T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) := by
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  obtain ⟨Q, hQA, ⟨e⟩⟩ := hQ8
  obtain ⟨q, hqQ, hqxy⟩ := q8_transitive (fun a b => hE.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hE.2 a.1 a.2)) hE9 e (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)
    (fun h => hx1 (congrArg Subtype.val h)) (fun h => hy1 (congrArg Subtype.val h))
  obtain ⟨n, hnT, hnq⟩ := hQA hqQ
  have hw : (n : G) * x * (n : G)⁻¹ = y := by
    have h := congrArg Subtype.val hqxy
    rw [← hnq, K21bRedProof.normalizerMonoidHom_coe] at h
    exact h
  rw [← hw]
  exact card_stab_eq T Inn E hnT n.2

theorem exists_inverting {G : Type} [Group G] (T Inn E : Subgroup G)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hQ8 : HasQ8 (autInduced T E))
    (hcomm : ∀ s ∈ T, ∀ t ∈ T, ⁅s, t⁆ ∈ Inn) :
    ∃ u ∈ T ⊓ Inn ⊓ Subgroup.normalizer (E : Set G), ∀ e ∈ E, u * e * u⁻¹ = e⁻¹ := by
  haveI : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE9]; norm_num)
  obtain ⟨Q, hQA, ⟨e⟩⟩ := hQ8
  obtain ⟨z, hzQ, hz1, hzz, hzc, hzq, hinv, hcommz⟩ :=
    exists_central_inversion (fun a b => hE.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hE.2 a.1 a.2)) hE9 e
  obtain ⟨a, ha, b, hb, hab⟩ := K21bQ8Proof.exists_noncomm_of_equiv e
  obtain ⟨na, hnaT, hna⟩ := hQA ha
  obtain ⟨nb, hnbT, hnb⟩ := hQA hb
  have hz : a * b * a⁻¹ * b⁻¹ = z := hcommz a ha b hb hab
  refine ⟨(na : G) * nb * (na : G)⁻¹ * (nb : G)⁻¹, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact T.mul_mem (T.mul_mem (T.mul_mem hnaT hnbT) (T.inv_mem hnaT)) (T.inv_mem hnbT)
  · exact hcomm _ hnaT _ hnbT
  · exact (na * nb * na⁻¹ * nb⁻¹ : ↥(Subgroup.normalizer (E : Set G))).2
  · intro x hx
    have h1 : E.normalizerMonoidHom (na * nb * na⁻¹ * nb⁻¹) = a * b * a⁻¹ * b⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hna, hnb]
    have h2 := congrArg (fun σ : MulAut ↥E => ((σ ⟨x, hx⟩ : ↥E) : G)) (h1.trans hz)
    simp only [K21bRedProof.normalizerMonoidHom_coe, hinv] at h2
    simpa using h2

theorem mem_normalizer_subgroupOf_iff {G : Type} [Group G] {K E : Subgroup G} (hEK : E ≤ K)
    (g : ↥K) : g ∈ Subgroup.normalizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) ↔
      (g : G) ∈ Subgroup.normalizer (E : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hg h
    constructor
    · intro hh
      have h1 := (hg ⟨h, hEK hh⟩).mp hh
      exact h1
    · intro hh
      have hK : h ∈ K := by
        have h2 : (g : G)⁻¹ * ((g : G) * h * (g : G)⁻¹) * (g : G) ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem g.2) (hEK hh)) g.2
        simpa [mul_assoc] using h2
      exact (hg ⟨h, hK⟩).mpr hh
  · intro hg h
    exact hg h.1

theorem card_transport {G : Type} [Group G] {K T E : Subgroup G} (hEK : E ≤ K) (x : ↥K) :
    Nat.card ↥((T ⊓ K).subgroupOf K ⊓
        Subgroup.normalizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊓
        Subgroup.centralizer ({x} : Set ↥K)) =
      Nat.card ↥(T ⊓ K ⊓ Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({(x : G)} : Set G)) := by
  have h : (T ⊓ K).subgroupOf K ⊓ Subgroup.normalizer ((E.subgroupOf K : Subgroup ↥K) : Set ↥K) ⊓
      Subgroup.centralizer ({x} : Set ↥K) =
      (T ⊓ K ⊓ Subgroup.normalizer (E : Set G) ⊓
        Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf K := by
    ext g
    constructor
    · rintro ⟨⟨hU, hN⟩, hC⟩
      refine ⟨⟨hU, (mem_normalizer_subgroupOf_iff hEK g).mp hN⟩, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hC x rfl)
    · rintro ⟨⟨hU, hN⟩, hC⟩
      refine ⟨⟨hU, (mem_normalizer_subgroupOf_iff hEK g).mpr hN⟩, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hC (x : G) rfl)
  rw [h]
  have hle : (T ⊓ K ⊓ Subgroup.normalizer (E : Set G) ⊓
      Subgroup.centralizer ({(x : G)} : Set G)) ≤ K :=
    inf_le_left.trans (inf_le_left.trans inf_le_right)
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv

end K21dRedProof

theorem K21d_of_K420 (hK420 : K420) (hRes : K21dRes) : K21d := by
  obtain ⟨hSimple, hGeom⟩ := hRes
  intro S _ _ hS N T' R E hInnN hT'N hT'p hSyl hRT' hT'R hRcore hsolv hEN hE hE9 hQ8
  haveI := K21bRedProof.finite_mulAut S
  haveI := K21bRedProof.innAut_normal S
  obtain ⟨hsimp, hnc⟩ := hSimple S hS
  haveI : IsSimpleGroup S := hsimp
  have hZ : Subgroup.center S = ⊥ := K21dRedProof.center_eq_bot_of_simple hnc
  have hq : CFSG.Open.IsQuasisimple S := K21dRedProof.isQuasisimple_of_simple hnc
  have hcl : CFSG.AGLEmbedding.IsClassicalTwoOrG2 (S ⧸ Subgroup.center S) :=
    K21dRedProof.isClassicalTwoOrG2_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
      (K21dRedProof.isClassicalTwoOrG2_of_isK21dGroup hS)
  have hcommInn : ∀ s ∈ T', ∀ t ∈ T', ⁅s, t⁆ ∈ innAut S :=
    fun s hs t ht => hK420 S hq hcl T' hT'p s hs t ht
  have hdich : (E ⊓ innAut S).subgroupOf E = ⊥ ∨ (E ⊓ innAut S).subgroupOf E = ⊤ := by
    refine eq_bot_or_eq_top_of_hasQ8 (V := ↥E) (fun x y => hE.1.is_comm.comm x y)
      (fun x => Subtype.ext (by simpa using hE.2 x.1 x.2)) hE9 hQ8 _ ?_
    rintro a ⟨n, hn, rfl⟩ x hx
    show ((E.normalizerMonoidHom n x : ↥E) : MulAut S) ∈ E ⊓ innAut S
    rw [K21bRedProof.normalizerMonoidHom_coe]
    exact ⟨((Subgroup.mem_normalizer_iff.mp n.2) x).mp x.2,
      (K21bRedProof.innAut_normal S).conj_mem x hx.2 n⟩
  rcases hdich with h | h
  · have hbot : E ⊓ innAut S = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx.1⟩ : ↥E) ∈ (E ⊓ innAut S).subgroupOf E := hx
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
    obtain ⟨a, ha, b, hb, hab⟩ := hasQ8_exists_noncomm hQ8
    refine hab (K21bRedProof.autInduced_comm T' E ?_ a ha b hb)
    intro s hs t ht hsN htN e he
    exact K21bRedProof.commute_of_inf_eq_bot (innAut S) E hbot (hcommInn s hs t ht)
      ((Subgroup.normalizer (E : Set (MulAut S))).mul_mem
        ((Subgroup.normalizer (E : Set (MulAut S))).mul_mem
          ((Subgroup.normalizer (E : Set (MulAut S))).mul_mem hsN htN)
          ((Subgroup.normalizer (E : Set (MulAut S))).inv_mem hsN))
        ((Subgroup.normalizer (E : Set (MulAut S))).inv_mem htN)) he
  · have hEI : E ≤ innAut S := fun x hx => by
      have h1 : (⟨x, hx⟩ : ↥E) ∈ (E ⊓ innAut S).subgroupOf E := by rw [h]; trivial
      exact h1.2
    obtain ⟨u, hu, huinv⟩ := K21dRedProof.exists_inverting T' (innAut S) E hE hE9 hQ8 hcommInn
    have hu' := Subgroup.mem_inf.mp hu
    have hu'' := Subgroup.mem_inf.mp hu'.1
    have hSinn : IsK21dGroup ↥(innAut S) := K21dRedProof.isK21dGroup_innAut hZ hS
    have hSylU : CFSG.ABGLocalTools.IsSylowOf 2 ((T' ⊓ innAut S).subgroupOf (innAut S)) ⊤ :=
      K21bRedProof.isSylowOf_subgroupOf_top hSyl
    have hUD : (T' ⊓ innAut S).subgroupOf (innAut S) ≤
        (N ⊓ Subgroup.normalizer (R : Set (MulAut S))).subgroupOf (innAut S) := by
      intro g hg
      have hg' := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hg)
      exact Subgroup.mem_inf.mpr ⟨hT'N hg'.1, hT'R hg'.1⟩
    have hEE : E.subgroupOf (innAut S) ≤
        (N ⊓ Subgroup.normalizer (R : Set (MulAut S))).subgroupOf (innAut S) :=
      fun g hg => hEN (Subgroup.mem_subgroupOf.mp hg)
    haveI := hsolv
    have hDsolv : Group.IsSolvable
        ↥((N ⊓ Subgroup.normalizer (R : Set (MulAut S))).subgroupOf (innAut S)) := by
      refine solvable_of_solvable_injective
        (f := MonoidHom.codRestrict
          ((innAut S).subtype.comp
            ((N ⊓ Subgroup.normalizer (R : Set (MulAut S))).subgroupOf (innAut S)).subtype)
          (N ⊓ Subgroup.normalizer (R : Set (MulAut S))) fun g => g.2) ?_
      intro a b hab
      have h2 := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h2)
    have hE'9 : Nat.card (E.subgroupOf (innAut S)) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv]
      exact hE9
    have hinvK : ∃ u' ∈ (T' ⊓ innAut S).subgroupOf (innAut S) ⊓
        Subgroup.normalizer ((E.subgroupOf (innAut S) : Subgroup ↥(innAut S)) : Set ↥(innAut S)),
        ∀ e ∈ E.subgroupOf (innAut S), u' * e * u'⁻¹ = e⁻¹ := by
      refine ⟨⟨u, hu''.2⟩, Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hu''.1, hu''.2⟩)
      · exact (K21dRedProof.mem_normalizer_subgroupOf_iff hEI ⟨u, hu''.2⟩).mpr hu'.2
      · intro e he
        exact Subtype.ext (huinv e.1 he)
    obtain ⟨x, hx, y, hy, hx1, hy1, hne⟩ := hGeom ↥(innAut S) hSinn _ _ _ hSylU hUD hDsolv hEE
      (K21bRedProof.isElemAbelian_subgroupOf hEI hE) hE'9 hinvK
    rw [K21dRedProof.card_transport hEI x, K21dRedProof.card_transport hEI y] at hne
    exact hne (K21dRedProof.card_stab_eq_of_hasQ8 T' (innAut S) E hE hE9 hQ8
      (x := (x : MulAut S)) (y := (y : MulAut S)) (Subgroup.mem_subgroupOf.mp hx)
      (Subgroup.mem_subgroupOf.mp hy) (fun h => hx1 (Subtype.ext h))
      (fun h => hy1 (Subtype.ext h)))

theorem K21dGeom_of_families (hT : K21dGeomTits) (h42 : K21dGeomU42) (h5 : K21dGeomL5)
    (h8 : K21dGeomA8) (h6 : K21dGeomA6) (h3 : K21dGeomU3) : K21dGeom := by
  intro S _ _ hS
  rcases hS with ⟨d, Q, hcase, he⟩ | h5' | hU | ⟨n, hn, he⟩
  · rcases hcase with ⟨hQ, hd⟩ | ⟨hc4, hd⟩
    · rcases hd with hd | hd | hd | hd
      · exact hT S (Or.inl ⟨d, Q, hQ, Or.inl hd, he⟩)
      · exact hT S (Or.inl ⟨d, Q, hQ, Or.inr (Or.inl hd), he⟩)
      · exact hT S (Or.inl ⟨d, Q, hQ, Or.inr (Or.inr (Or.inl hd)), he⟩)
      · by_cases hc : Q.card = 2
        · exact h42 S ⟨d, Q, hc, hd, he⟩
        · exact hT S (Or.inl ⟨d, Q, hQ, Or.inr (Or.inr (Or.inr ⟨hd, hc⟩)), he⟩)
    · exact hT S (Or.inr ⟨d, Q, hc4, hd, he⟩)
  · exact h5 S h5'
  · exact h3 S hU
  · rcases hn with rfl | rfl
    · exact h6 S he
    · exact h8 S he

end CFSG.LocalAnalysis.RankThreeUC.S15
