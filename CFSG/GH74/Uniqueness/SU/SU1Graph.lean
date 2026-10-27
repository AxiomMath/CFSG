module

public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {G : Type*} [Group G]

abbrev Ep2Vertex (p : ℕ) (H : Subgroup G) : Type _ :=
  {E : Subgroup G // E ≤ H ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ 2}

@[expose] def Ep2Graph (p : ℕ) (H : Subgroup G) : SimpleGraph (Ep2Vertex p H) where
  Adj A B := A ≠ B ∧ ∀ a ∈ A.1, ∀ b ∈ B.1, a * b = b * a
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun b hb a ha => (h.2 a ha b hb).symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

@[expose] def IsIsolated (p : ℕ) {H : Subgroup G} (A : Ep2Vertex p H) : Prop :=
  ∀ B : Ep2Vertex p H, ¬ (Ep2Graph p H).Adj A B

@[expose] def IsNormalEp2 (p : ℕ) (P U : Subgroup G) : Prop :=
  U ≤ P ∧ P ≤ normalizer (U : Set G) ∧ Open.IsElemAbelian p U ∧ Nat.card U = p ^ 2

@[expose] def IsHalfCentral (p : ℕ) (P : Subgroup G) (x : G) : Prop :=
  x ∈ P ∧ orderOf x = p ∧ (centralizer ({x} : Set G)).relIndex P ≤ p

section Finite

variable [Finite G] {p : ℕ}

omit [Finite G] in
theorem conj_mem_of_le_normalizer {P U : Subgroup G} (h : P ≤ normalizer (U : Set G)) :
    ∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ ∈ U := fun _ hg u hu =>
  (mem_normalizer_iff.mp (h hg) u).mp hu

theorem ig10_20_i (hp : p.Prime) {P : Subgroup G} {x : G} (hx : IsHalfCentral p P x) :
    Open.pRank p (centralizer ({x} : Set G) ⊓ P) = Open.pRank p P := by
  obtain ⟨hxP, hxo, hxi⟩ := hx
  set Q := centralizer ({x} : Set G) ⊓ P with hQ
  refine le_antisymm (pRank_mono hp.one_lt inf_le_right) ?_
  obtain ⟨A, hAP, hA, hAcard⟩ := exists_pRank hp.one_lt P
  set r := Open.pRank p P with hr
  by_cases hAQ : A ≤ Q
  · exact le_pRank hp.one_lt hAQ hA hAcard
  have hAcomm := (isElemAbelian_iff.mp hA).1
  have hxA : x ∉ A := by
    intro hx'
    apply hAQ
    intro a ha
    exact ⟨Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm a ha x hx'), hAP ha⟩
  have hxQ : x ∈ Q := ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxP⟩
  have hQP : Q.relIndex P = (centralizer ({x} : Set G)).relIndex P := by
    rw [hQ, Subgroup.inf_relIndex_right]
  have hne0 : Q.relIndex P ≠ 0 := relIndex_ne_zero_of_finite Q P
  have hrel : Q.relIndex A ≤ p := by
    calc Q.relIndex A ≤ Q.relIndex P := Subgroup.relIndex_le_of_le_right hAP hne0
      _ = (centralizer ({x} : Set G)).relIndex P := hQP
      _ ≤ p := hxi
  have hrel1 : Q.relIndex A ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    exact hAQ
  have hApg : IsPGroup p A := IsPGroup.of_card hAcard
  obtain ⟨n, hn⟩ := relIndex_pow hp hApg Q
  have hn1 : n = 1 := by
    have hle : p ^ n ≤ p := hn ▸ hrel
    have hne : p ^ n ≠ 1 := hn ▸ hrel1
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.eq_zero_or_pos n with h0 | h0
      · exact absurd (by rw [h0, pow_zero]) hne
      · omega
    · have : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos h2
      have h3 : p < p ^ 2 := by
        have := hp.one_lt
        nlinarith
      omega
  have hrelp : Q.relIndex A = p := by rw [hn, hn1, pow_one]
  have hmulc := Subgroup.relIndex_mul_card (H := Q) (K := A)
  rw [hrelp, hAcard] at hmulc
  obtain ⟨r', hr'⟩ : ∃ r', r = r' + 1 := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hmulc
      have := Nat.eq_one_of_mul_eq_one_right hmulc
      exact hp.one_lt.ne' this
    · exact ⟨r - 1, by omega⟩
  have hc : Nat.card ↥(Q ⊓ A) = p ^ r' := by
    rw [hr', pow_succ'] at hmulc
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmulc
  have hel : Open.IsElemAbelian p ((Q ⊓ A) ⊔ zpowers x) := by
    refine IsElemAbelian.sup (IsElemAbelian.mono inf_le_right hA)
      (isElemAbelian_zpowers (by rw [← hxo]; exact pow_orderOf_eq_one x)) ?_
    rintro b hb s ⟨m, rfl⟩
    have hbx : b * x = x * b := Subgroup.mem_centralizer_singleton_iff.mp hb.1.1
    exact (Commute.zpow_right (show Commute b x from hbx) m).eq
  have hlt : (Q ⊓ A) < (Q ⊓ A) ⊔ zpowers x := by
    refine lt_of_le_of_ne le_sup_left (fun h => hxA ?_)
    have hxm : x ∈ (Q ⊓ A) ⊔ zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [← h] at hxm
    exact hxm.2
  have hcl := card_lt_of_lt hlt
  obtain ⟨t, ht⟩ := IsElemAbelian.exists_card hp hel
  rw [hc, ht] at hcl
  have hrt : r' < t := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcl
  have hBQ : (Q ⊓ A) ⊔ zpowers x ≤ Q :=
    sup_le inf_le_left (Subgroup.zpowers_le.mpr hxQ)
  have := le_pRank hp.one_lt hBQ hel ht
  omega

theorem ig10_20_ii (hp : p.Prime) {P U : Subgroup G} (hP : IsPGroup p P) (hU : IsNormalEp2 p P U) :
    (∀ u ∈ U, u ≠ 1 → IsHalfCentral p P u) ∧ (centralizer (U : Set G)).relIndex P ≤ p ∧
      Open.pRank p (centralizer (U : Set G) ⊓ P) = Open.pRank p P := by
  obtain ⟨hUP, hUn, hUel, hUcard⟩ := hU
  have hconj := conj_mem_of_le_normalizer hUn
  have hUel' := isElemAbelian_iff.mp hUel
  have hhalf : ∀ u ∈ U, u ≠ 1 → IsHalfCentral p P u := by
    intro u hu hu1
    have := Fact.mk hp
    exact ⟨hUP hu, orderOf_eq_prime (hUel'.2 u hu) hu1,
      relIndex_centralizer_le hp hP hconj hUcard.le hu hu1⟩
  have hUbot : U ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hUcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨z, hzU, hz1, hzc⟩ := exists_central_of_normal hp hP hUP hconj hUbot
  have hzo : orderOf z = p := by
    have := Fact.mk hp
    exact orderOf_eq_prime (hUel'.2 z hzU) hz1
  have hexx : ∃ x ∈ U, x ∉ zpowers z := by
    by_contra hcon
    have hle : U ≤ zpowers z := fun y hy => by_contra (fun hy' => hcon ⟨y, hy, hy'⟩)
    have := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hzo, hUcard] at this
    have h2 : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega
  obtain ⟨x, hxU, hxz⟩ := hexx
  have hx1 : x ≠ 1 := fun h => hxz (h ▸ one_mem _)
  obtain ⟨-, hsupcard⟩ := isElemAbelian_card_sup_zpowers hp (hUel'.2 z hzU) (hUel'.2 x hxU) hz1 hxz
    (hUel'.1 z hzU x hxU)
  have hUeq : zpowers z ⊔ zpowers x = U :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr hzU)
      (Subgroup.zpowers_le.mpr hxU)) (by rw [hUcard, hsupcard])
  have hcent : centralizer (U : Set G) ⊓ P = centralizer ({x} : Set G) ⊓ P := by
    ext g
    simp only [Subgroup.mem_inf]
    refine and_congr_left (fun hgP => ?_)
    constructor
    · intro hg
      exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxU) hg
    · intro hg
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hzg : z ∈ centralizer ({g} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (hzc g hgP).symm
      have hxg : x ∈ centralizer ({g} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
      have hle : zpowers z ⊔ zpowers x ≤ centralizer ({g} : Set G) :=
        sup_le (Subgroup.zpowers_le.mpr hzg) (Subgroup.zpowers_le.mpr hxg)
      have hmem : h ∈ centralizer ({g} : Set G) := hle (by rw [hUeq]; exact hh)
      exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  have hrel : (centralizer (U : Set G)).relIndex P ≤ p := by
    have h1 : (centralizer (U : Set G)).relIndex P = (centralizer ({x} : Set G)).relIndex P := by
      rw [← Subgroup.inf_relIndex_right (centralizer (U : Set G)) P, hcent,
        Subgroup.inf_relIndex_right]
    rw [h1]
    exact (hhalf x hxU hx1).2.2
  refine ⟨hhalf, hrel, ?_⟩
  rw [hcent]
  exact ig10_20_i hp (hhalf x hxU hx1)

theorem ig10_21_i (hp : p.Prime) {P : Subgroup G} (hrk : Open.pRank p P ≤ 2) :
    ∀ A B : Ep2Vertex p P, ¬ (Ep2Graph p P).Adj A B := by
  rintro A B ⟨hne, hcomm⟩
  have hne' : A.1 ≠ B.1 := fun h => hne (Subtype.ext h)
  obtain ⟨hel, h3⟩ := sup_isElemAbelian_card hp A.2.2.1 A.2.2.2 B.2.2.1 B.2.2.2 hne' hcomm
  obtain ⟨k, hk⟩ := IsElemAbelian.exists_card hp hel
  have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp (hk ▸ h3)
  have := le_pRank hp.one_lt (sup_le A.2.1 B.2.1) hel hk
  omega

theorem ig10_21_i_reachable (hp : p.Prime) {P : Subgroup G} (hrk : Open.pRank p P ≤ 2)
    {A B : Ep2Vertex p P} (h : (Ep2Graph p P).Reachable A B) : A = B := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (ig10_21_i hp hrk _ _)

omit [Finite G] in
theorem reachable_of_commute {P : Subgroup G} {A B : Ep2Vertex p P}
    (h : ∀ a ∈ A.1, ∀ b ∈ B.1, a * b = b * a) : (Ep2Graph p P).Reachable A B := by
  by_cases hAB : A = B
  · rw [hAB]
  · exact SimpleGraph.Adj.reachable ⟨hAB, h⟩

omit [Finite G] in
theorem eq_of_reachable_of_isIsolated {P : Subgroup G} {A B : Ep2Vertex p P}
    (hA : IsIsolated p A) (h : (Ep2Graph p P).Reachable A B) : A = B := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj _ => exact absurd hadj (hA _)

theorem not_isIsolated_of_isNormalEp2 (hp : p.Prime) {P U : Subgroup G} (hP : IsPGroup p P)
    (hrk : 3 ≤ Open.pRank p P) (hU : IsNormalEp2 p P U) (A : Ep2Vertex p P) (hAU : A.1 = U) :
    ¬ IsIsolated p A := by
  intro hiso
  obtain ⟨-, -, hrank⟩ := ig10_20_ii hp hP hU
  have h3 : 3 ≤ Open.pRank p (centralizer (U : Set G) ⊓ P) := by rw [hrank]; exact hrk
  obtain ⟨F, hFle, hF, hFcard⟩ := exists_isElemAbelian_of_le_pRank hp h3
  obtain ⟨W, hWF, hW, hWcard, hWU⟩ := exists_other_vertex hp hU.2.2.2 hF (by rw [hFcard])
  refine hiso ⟨W, (hWF.trans hFle).trans inf_le_right, hW, hWcard⟩ ⟨?_, ?_⟩
  · intro h
    exact hWU ((congrArg Subtype.val h).symm.trans hAU)
  · intro a ha b hb
    rw [hAU] at ha
    exact Subgroup.mem_centralizer_iff.mp (hFle (hWF hb)).1 a ha

theorem isIsolated_of_not_reachable (hp : p.Prime) {P U : Subgroup G} (hP : IsPGroup p P)
    (hU : IsNormalEp2 p P U) (Uv : Ep2Vertex p P) (hUv : Uv.1 = U) (A : Ep2Vertex p P)
    (hA : ¬ (Ep2Graph p P).Reachable Uv A) : IsIsolated p A := by
  obtain ⟨-, hrel, -⟩ := ig10_20_ii hp hP hU
  rintro B ⟨hne, hcomm⟩
  have hne' : A.1 ≠ B.1 := fun h => hne (Subtype.ext h)
  obtain ⟨hel, h3⟩ := sup_isElemAbelian_card hp A.2.2.1 A.2.2.2 B.2.2.1 B.2.2.2 hne' hcomm
  have hCP : A.1 ⊔ B.1 ≤ P := sup_le A.2.1 B.2.1
  have hrelC : (centralizer (U : Set G)).relIndex (A.1 ⊔ B.1) ≤ p :=
    (Subgroup.relIndex_le_of_le_right hCP (relIndex_ne_zero_of_finite _ _)).trans hrel
  have hmul := Subgroup.relIndex_mul_card (H := centralizer (U : Set G)) (K := A.1 ⊔ B.1)
  have hD : p ^ 2 ≤ Nat.card ↥(centralizer (U : Set G) ⊓ (A.1 ⊔ B.1)) := by
    by_contra hcon
    have h1 := not_le.mp hcon
    have h2 : (centralizer (U : Set G)).relIndex (A.1 ⊔ B.1) *
        Nat.card ↥(centralizer (U : Set G) ⊓ (A.1 ⊔ B.1)) ≤
        p * Nat.card ↥(centralizer (U : Set G) ⊓ (A.1 ⊔ B.1)) := Nat.mul_le_mul_right _ hrelC
    have h4 : p * Nat.card ↥(centralizer (U : Set G) ⊓ (A.1 ⊔ B.1)) < p * p ^ 2 :=
      Nat.mul_lt_mul_of_pos_left h1 hp.pos
    have h5 : p * p ^ 2 = p ^ 3 := by ring
    omega
  obtain ⟨W, hWle, hW, hWcard⟩ := exists_vertex_le hp (IsElemAbelian.mono inf_le_right hel) hD
  have hWC : W ≤ A.1 ⊔ B.1 := hWle.trans inf_le_right
  have hWU : W ≤ centralizer (U : Set G) := hWle.trans inf_le_left
  let Wv : Ep2Vertex p P := ⟨W, hWC.trans hCP, hW, hWcard⟩
  apply hA
  refine (reachable_of_commute (A := Uv) (B := Wv) ?_).trans
    (reachable_of_commute (A := Wv) (B := A) ?_)
  · intro a ha b hb
    rw [hUv] at ha
    exact Subgroup.mem_centralizer_iff.mp (hWU hb) a ha
  · intro w hw a ha
    exact (isElemAbelian_iff.mp hel).1 w (hWC hw) a (Subgroup.mem_sup_left ha)

theorem ig10_21_ii (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P) (hrk : 3 ≤ Open.pRank p P)
    (hU : ∃ U, IsNormalEp2 p P U) :
    (∃ A : Ep2Vertex p P, ¬ IsIsolated p A) ∧ ∀ A B : Ep2Vertex p P, ¬ IsIsolated p A →
      ¬ IsIsolated p B → (Ep2Graph p P).Reachable A B := by
  obtain ⟨U, hU⟩ := hU
  let Uv : Ep2Vertex p P := ⟨U, hU.1, hU.2.2⟩
  have hnot : ¬ IsIsolated p Uv := not_isIsolated_of_isNormalEp2 hp hP hrk hU Uv rfl
  have hreach : ∀ A : Ep2Vertex p P, ¬ IsIsolated p A → (Ep2Graph p P).Reachable Uv A := by
    intro A hA
    by_contra hcon
    exact hA (isIsolated_of_not_reachable hp hP hU Uv rfl A hcon)
  exact ⟨⟨Uv, hnot⟩, fun A B hA hB => (hreach A hA).symm.trans (hreach B hB)⟩

theorem ig10_21_ii_component (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P)
    (hrk : 3 ≤ Open.pRank p P) (hU : ∃ U, IsNormalEp2 p P U) :
    ∃ C : (Ep2Graph p P).ConnectedComponent, (∃ A, (Ep2Graph p P).connectedComponentMk A = C) ∧
      ∀ A : Ep2Vertex p P, (Ep2Graph p P).connectedComponentMk A = C ↔ ¬ IsIsolated p A := by
  obtain ⟨⟨A0, hA0⟩, hall⟩ := ig10_21_ii hp hP hrk hU
  refine ⟨(Ep2Graph p P).connectedComponentMk A0, ⟨A0, rfl⟩, fun A => ?_⟩
  constructor
  · intro h hiso
    have hr : (Ep2Graph p P).Reachable A A0 := SimpleGraph.ConnectedComponent.exact h
    exact hA0 (eq_of_reachable_of_isIsolated hiso hr ▸ hiso)
  · intro hA
    exact SimpleGraph.ConnectedComponent.sound (hall A A0 hA hA0)

end Finite

end CFSG.GH74.Uniqueness.SU.SU1
