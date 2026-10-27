module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.ShapeCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.CheckSpec

public section

namespace CFSG.EvenSporadicStandard.HNRecog

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

theorem commute_of_closure {M : Type*} [Group M] {S T : Set M}
    (h : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) : ∀ x ∈ closure S, ∀ y ∈ closure T, x * y = y * x := by
  intro x hx y hy
  have h1 : ∀ s ∈ S, y * s = s * y := by
    intro s hs
    have hle : closure T ≤ centralizer ({s} : Set M) := by
      rw [closure_le]
      intro t ht
      rw [SetLike.mem_coe, mem_centralizer_iff]
      intro u hu
      rw [Set.mem_singleton_iff] at hu
      rw [hu]
      exact h s hs t ht
    exact (mem_centralizer_iff.1 (hle hy) s (Set.mem_singleton s)).symm
  have hle : closure S ≤ centralizer ({y} : Set M) := by
    rw [closure_le]
    intro s hs
    rw [SetLike.mem_coe, mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    rw [hu]
    exact h1 s hs
  exact (mem_centralizer_iff.1 (hle hx) y (Set.mem_singleton y)).symm

theorem conj_mem_closure_of_gens {M : Type*} [Group M] {S : Set M} {c : M}
    (h : ∀ s ∈ S, c * s * c⁻¹ ∈ closure S) : ∀ n ∈ closure S, c * n * c⁻¹ ∈ closure S := by
  intro n hn
  induction hn using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : c * (x * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem eq_one_of_mem_zpowers_of_not_mem {M : Type*} [Group M] {p : ℕ} [Fact p.Prime] {r : M}
    (hr : orderOf r = p) {Y : Subgroup M} (hrY : r ∉ Y) :
    ∀ l ∈ zpowers r, l ∈ Y → l = 1 := by
  intro l hl hlY
  by_contra hne
  haveI : Finite ↥(zpowers r) :=
    finite_zpowers.2 (orderOf_pos_iff.1 (hr ▸ (Fact.out : p.Prime).pos))
  have hdvd : orderOf l ∣ p := by
    have h1 := Subgroup.orderOf_dvd_natCard (zpowers r) hl
    rwa [Nat.card_zpowers, hr] at h1
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · exact hne (orderOf_eq_one_iff.1 h1)
  · have hle : zpowers l ≤ zpowers r := (Subgroup.zpowers_le).2 hl
    have hcard : Nat.card ↥(zpowers r) ≤ Nat.card ↥(zpowers l) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, h1, hr]
    have heq : zpowers l = zpowers r := Subgroup.eq_of_le_of_card_ge hle hcard
    apply hrY
    have : r ∈ zpowers l := by rw [heq]; exact Subgroup.mem_zpowers r
    exact (Subgroup.zpowers_le).2 hlY this

theorem mul_self_eq_one_of_orderOf_eq_two {M : Type*} [Group M] {x : M} (h : orderOf x = 2) :
    x * x = 1 := by
  have := pow_orderOf_eq_one x
  rwa [h, pow_two] at this

theorem ne_one_of_orderOf_eq_two {M : Type*} [Group M] {x : M} (h : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at h
  exact absurd h (by norm_num)

theorem zpowers_le_inf_centralizer {M : Type*} [Group M] {P : Subgroup M} {r : M} (hr : r ∈ P) :
    zpowers r ≤ P ⊓ centralizer ({r} : Set M) := by
  rw [Subgroup.zpowers_le]
  refine Subgroup.mem_inf.2 ⟨hr, mem_centralizer_iff.2 fun h hh => ?_⟩
  rw [Set.mem_singleton_iff] at hh
  rw [hh]

theorem mul_comm_of_mem_zpowers {M : Type*} [Group M] {P : Subgroup M} {r x : M}
    (hx : x ∈ P ⊓ centralizer ({r} : Set M)) : ∀ l ∈ zpowers r, x * l = l * x := by
  intro l hl
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
  have hc : Commute x r :=
    (mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx).2 r (Set.mem_singleton r)).symm
  exact (hc.zpow_right k).eq

theorem orderOf_eq_of_primeOrderOK {p : ℕ} [Fact p.Prime] {t : Table}
    {r : Equiv.Perm (Fin 1408)} (hr : Rep 1408 t r) (h : primeOrderOK p t = true) :
    orderOf r = p := by
  simp only [primeOrderOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine orderOf_eq_prime
    ((tblEq_iff_eq (Rep.powT (by norm_num) hr p) (Rep.idT (by norm_num))).1 h.1) ?_
  intro h1
  have h2 := (tblEq_iff_eq hr (Rep.idT (by norm_num))).2 h1
  exact Bool.false_ne_true (h.2.symm.trans h2)

theorem closure_words_le_inf_centralizer (hg : gensOK = true) {ws : List (List ℕ)}
    (hw : ws.all wordOK = true) {r : Equiv.Perm (Fin 1408)} {tr : Table} (hr : Rep 1408 tr r)
    (h : commWordsOK ws tr = true) :
    closure (elemW '' {w | w ∈ ws}) ≤ P1408 ⊓ centralizer ({r} : Set (Equiv.Perm (Fin 1408))) := by
  rw [closure_le]
  rintro _ ⟨w, hw', rfl⟩
  refine Subgroup.mem_inf.2 ⟨elemW_mem w, mem_centralizer_iff.2 ?_⟩
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact ((commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hw')) hr).1
    (List.all_eq_true.1 h w hw')).symm

theorem commPairsOK_spec (hg : gensOK = true) {us vs : List (List ℕ)}
    (hu : us.all wordOK = true) (hv : vs.all wordOK = true) (h : commPairsOK us vs = true) :
    ∀ x ∈ closure (elemW '' {w | w ∈ us}), ∀ y ∈ closure (elemW '' {w | w ∈ vs}),
      x * y = y * x := by
  apply commute_of_closure
  rintro _ ⟨u, hu', rfl⟩ _ ⟨v, hv', rfl⟩
  exact (commTT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hu u hu'))
    (rep_elemW_of_gensOK hg (List.all_eq_true.1 hv v hv'))).1
    (List.all_eq_true.1 (List.all_eq_true.1 h u hu') v hv')

theorem closure_words_le_of_wordsInOK (hg : gensOK = true) {ws : List (List ℕ)}
    (hw : ws.all wordOK = true) {K : Subgroup (Equiv.Perm (Fin 1408))} {L : Array Table}
    (hL : IsEnumSet 1408 L (K : Set (Equiv.Perm (Fin 1408)))) (h : wordsInOK L ws = true) :
    closure (elemW '' {w | w ∈ ws}) ≤ K := by
  rw [closure_le]
  rintro _ ⟨w, hw', rfl⟩
  exact (hL.memT_iff (rep_elemW_of_gensOK hg (List.all_eq_true.1 hw w hw'))).1
    (List.all_eq_true.1 h w hw')

theorem trivInterOK_iff {LV LA : Array Table} {SV SA : Set (Equiv.Perm (Fin 1408))}
    (hV : IsEnumSet 1408 LV SV) (hA : IsEnumSet 1408 LA SA) :
    trivInterOK (idT 1408) LV LA = true ↔ ∀ v ∈ SV, v ∈ SA → v = 1 := by
  refine hV.forall_iff _ (fun v => v ∈ SA → v = 1) ?_
  intro x g hx
  simp only [Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h hgA
    rcases h with h | h
    · exact (tblEq_iff_eq hx (Rep.idT (by norm_num))).1 h
    · have := (hA.memT_iff hx).2 hgA
      rw [this] at h
      exact absurd h (by simp)
  · intro H
    by_cases hm : memT 1408 LA x = true
    · exact Or.inl ((tblEq_iff_eq hx (Rep.idT (by norm_num))).2 (H ((hA.memT_iff hx).1 hm)))
    · exact Or.inr (by simpa using hm)

theorem powOneOK_iff {L : Array Table} {S : Set (Equiv.Perm (Fin 1408))}
    (hL : IsEnumSet 1408 L S) (e : ℕ) :
    powOneOK e (idT 1408) L = true ↔ ∀ g ∈ S, g ^ e = 1 := by
  refine hL.forall_iff _ (fun g => g ^ e = 1) ?_
  intro x g hx
  exact tblEq_iff_eq (Rep.powT (by norm_num) hx e) (Rep.idT (by norm_num))

theorem normGensOK_spec (hg : gensOK = true) {cs ns : List (List ℕ)}
    (hcs : cs.all wordOK = true) (hns : ns.all wordOK = true) {LN : Array Table}
    (hL : IsEnumSet 1408 LN (closure (elemW '' {w | w ∈ ns}) : Set (Equiv.Perm (Fin 1408))))
    (h : normGensOK LN cs ns = true) :
    ∀ x ∈ closure (elemW '' {w | w ∈ cs}), ∀ n ∈ closure (elemW '' {w | w ∈ ns}),
      x * n * x⁻¹ ∈ closure (elemW '' {w | w ∈ ns}) := by
  set N := closure (elemW '' {w | w ∈ ns}) with hN
  have hgen : ∀ c ∈ cs, ∀ n ∈ elemW '' {w | w ∈ ns},
      elemW c * n * (elemW c)⁻¹ ∈ N ∧ (elemW c)⁻¹ * n * ((elemW c)⁻¹)⁻¹ ∈ N := by
    intro c hc n hn
    obtain ⟨w, hw, rfl⟩ := hn
    have h1 := List.all_eq_true.1 h c hc
    simp only [normGensOK, Bool.and_eq_true] at h1
    obtain ⟨hinv, hall⟩ := h1
    have h2 := List.all_eq_true.1 hall w hw
    rw [Bool.and_eq_true] at h2
    have hrc := rep_elemW_of_gensOK hg (List.all_eq_true.1 hcs c hc)
    have hrn := rep_elemW_of_gensOK hg (List.all_eq_true.1 hns w hw)
    have hrci := Rep.inv_of_invOK hrc hinv
    have hrc' : Rep 1408 (tabW c) ((elemW c)⁻¹)⁻¹ := by rw [inv_inv]; exact hrc
    exact ⟨(hL.memT_iff (rep_conjT hrc hrci hrn)).1 h2.1,
      (hL.memT_iff (rep_conjT hrci hrc' hrn)).1 h2.2⟩
  have hnormal : closure (elemW '' {w | w ∈ cs}) ≤ Subgroup.normalizer N := by
    rw [closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact conj_mem_closure_of_gens (fun s hs => (hgen c hc s hs).1) n
    · intro hn
      have := conj_mem_closure_of_gens (c := (elemW c)⁻¹) (S := elemW '' {w | w ∈ ns})
        (fun s hs => (hgen c hc s hs).2) _ hn
      have e : (elemW c)⁻¹ * (elemW c * n * (elemW c)⁻¹) * ((elemW c)⁻¹)⁻¹ = n := by group
      rwa [e] at this
  intro x hx n hn
  exact (Subgroup.mem_normalizer_iff.1 (hnormal hx) n).1 hn

theorem commutatorEqOK_spec {tu tv ta : Table} {u v a : Equiv.Perm (Fin 1408)}
    (hu : Rep 1408 tu u) (hv : Rep 1408 tv v) (ha : Rep 1408 ta a)
    (h : commutatorEqOK tu tv ta = true) : u * v * u⁻¹ * v⁻¹ = a := by
  simp only [commutatorEqOK, Bool.and_eq_true] at h
  obtain ⟨⟨hui, hvi⟩, h⟩ := h
  exact (tblEq_iff_eq (Rep.compT (Rep.compT (Rep.compT hu hv) (Rep.inv_of_invOK hu hui))
    (Rep.inv_of_invOK hv hvi)) ha).1 h

theorem enumW_gens_words {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    gensOK = true ∧ ws.all wordOK = true := by
  simp only [enumW, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2⟩

theorem enumW_size {cap m : ℕ} {ws : List (List ℕ)} (h : enumW cap m ws = true) :
    (subgroupList cap ws).size = m := by
  simp only [enumW, enumOKH, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2.2

end CFSG.EvenSporadicStandard.HNRecog
