module

import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GH74.Uniqueness.SU.SU1

open Subgroup

variable {G : Type*} [Group G]

theorem isElemAbelian_iff {p : ℕ} {E : Subgroup G} :
    Open.IsElemAbelian p E ↔ (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) ∧ ∀ a ∈ E, a ^ p = 1 := by
  constructor
  · rintro ⟨hc, hp⟩
    refine ⟨fun a ha b hb => ?_, hp⟩
    have := hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  · rintro ⟨hc, hp⟩
    exact ⟨⟨⟨fun a b => Subtype.ext (hc a.1 a.2 b.1 b.2)⟩⟩, hp⟩

theorem IsElemAbelian.mono {p : ℕ} {E F : Subgroup G} (h : E ≤ F) (hF : Open.IsElemAbelian p F) :
    Open.IsElemAbelian p E := CFSG.Open.IsElemAbelian.mono hF h

theorem mem_sup_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {g : G}
    (hg : g ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = g := by
  have key : ∀ a ∈ A, ∀ h ∈ B, a * h * a⁻¹ ∈ B := by
    intro a ha h hh
    rw [hAB a ha h hh, mul_assoc, mul_inv_cancel, mul_one]
    exact hh
  have hle : A ≤ normalizer (B : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key a ha h hh, fun hh => ?_⟩
    have h2 := key a⁻¹ (A.inv_mem ha) _ hh
    have e : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [e] at h2
  have := Subgroup.coe_mul_of_left_le_normalizer_right A B hle
  have hg' : g ∈ ((A ⊔ B : Subgroup G) : Set G) := hg
  rw [this] at hg'
  obtain ⟨a, ha, b, hb, rfl⟩ := hg'
  exact ⟨a, ha, b, hb, rfl⟩

theorem IsElemAbelian.sup {p : ℕ} {A B : Subgroup G} (hA : Open.IsElemAbelian p A)
    (hB : Open.IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Open.IsElemAbelian p (A ⊔ B) := CFSG.Open.IsElemAbelian.sup_of_commute hA hB hAB

theorem isElemAbelian_zpowers {p : ℕ} {x : G} (hx : x ^ p = 1) :
    Open.IsElemAbelian p (zpowers x) := CFSG.Open.isElemAbelian_zpowers hx

theorem isElemAbelian_bot (p : ℕ) : Open.IsElemAbelian p (⊥ : Subgroup G) := by
  rw [isElemAbelian_iff]
  refine ⟨?_, ?_⟩
  · intro a ha b hb
    rw [Subgroup.mem_bot.mp ha]
    simp
  · intro a ha
    rw [Subgroup.mem_bot.mp ha]
    simp

section Finite

variable [Finite G] {p : ℕ}

theorem IsElemAbelian.exists_card (hp : p.Prime) {E : Subgroup G} (hE : Open.IsElemAbelian p E) :
    ∃ k, Nat.card E = p ^ k := by
  have := Fact.mk hp
  have hP : IsPGroup p E := fun g => ⟨1, by
    have h := (isElemAbelian_iff.mp hE).2 g.1 g.2
    apply Subtype.ext
    simpa using h⟩
  exact IsPGroup.iff_card.mp hP

theorem card_lt_of_lt {H K : Subgroup G} (h : H < K) : Nat.card H < Nat.card K := by
  by_contra hcon
  exact h.ne (Subgroup.eq_of_le_of_card_ge h.le (not_lt.mp hcon))

theorem bddAbove_rank (hp : 1 < p) (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hk⟩
  have h1 : p ^ k ≤ Nat.card G := hk ▸ Subgroup.card_le_card_group E
  exact (Nat.lt_pow_self hp).le.trans h1

theorem le_pRank (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H) (hE : Open.IsElemAbelian p E)
    {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ Open.pRank p H := CFSG.SectionRank.le_pRank hp hEH hE hk

omit [Finite G] in
theorem rank_set_nonempty (p : ℕ) (H : Subgroup G) :
    {k | ∃ E : Subgroup G, E ≤ H ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ k}.Nonempty :=
  ⟨0, ⊥, bot_le, isElemAbelian_bot p, by simp⟩

theorem exists_pRank (hp : 1 < p) (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ Open.pRank p H :=
  CFSG.SectionRank.exists_pRank hp H

theorem pRank_le_of {H : Subgroup G} {m : ℕ}
    (h : ∀ E : Subgroup G, E ≤ H → Open.IsElemAbelian p E → ∀ k, Nat.card E = p ^ k → k ≤ m) :
    Open.pRank p H ≤ m := by
  unfold Open.pRank
  refine csSup_le (rank_set_nonempty p H) ?_
  rintro k ⟨E, hEH, hE, hk⟩
  exact h E hEH hE k hk

theorem pRank_mono (hp : 1 < p) {H K : Subgroup G} (h : H ≤ K) :
    Open.pRank p H ≤ Open.pRank p K := CFSG.SectionRank.pRank_mono hp h

omit [Finite G] in
theorem exists_subgroup_card (hp : p.Prime) {E : Subgroup G} (hE : Open.IsElemAbelian p E)
    {j k : ℕ} (hjk : j ≤ k) (hk : Nat.card E = p ^ k) :
    ∃ F : Subgroup G, F ≤ E ∧ Open.IsElemAbelian p F ∧ Nat.card F = p ^ j := by
  have := Fact.mk hp
  have hP : IsPGroup p E := fun g => ⟨1, by
    have h := (isElemAbelian_iff.mp hE).2 g.1 g.2
    apply Subtype.ext
    simpa using h⟩
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card hp hP
    (n := j) (by rw [hk]; exact Nat.pow_le_pow_right hp.pos hjk)
  refine ⟨H.map E.subtype, Subgroup.map_subtype_le H, ?_, ?_⟩
  · exact IsElemAbelian.mono (Subgroup.map_subtype_le H) hE
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hH]

theorem exists_isElemAbelian_of_le_pRank (hp : p.Prime) {H : Subgroup G} {k : ℕ}
    (hk : k ≤ Open.pRank p H) :
    ∃ E : Subgroup G, E ≤ H ∧ Open.IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp.one_lt H
  obtain ⟨F, hFE, hF, hFcard⟩ := exists_subgroup_card hp hE hk hcard
  exact ⟨F, hFE.trans hEH, hF, hFcard⟩

theorem relIndex_ne_zero_of_finite (H K : Subgroup G) : H.relIndex K ≠ 0 :=
  Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf K)

theorem card_sup_le_of_commute {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Nat.card (A ⊔ B : Subgroup G) ≤ Nat.card A * Nat.card B := by
  have hsurj : Function.Surjective (fun x : A × B =>
      (⟨(x.1 : G) * x.2, (A ⊔ B).mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩ :
        ↥(A ⊔ B))) := by
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute hAB hg
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod] at this

end Finite

section PGroup

variable [Finite G] {p : ℕ}

theorem exists_central_of_normal (hp : p.Prime) {P U : Subgroup G} (hP : IsPGroup p P)
    (hUP : U ≤ P) (hnorm : ∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hne : U ≠ ⊥) :
    ∃ z ∈ U, z ≠ 1 ∧ ∀ g ∈ P, g * z = z * g := by
  have := Fact.mk hp
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hN : (U.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff hUP).mpr (fun h k hh hk => hnorm k hk h hh)
  have hne' : U.subgroupOf P ≠ ⊥ := by
    intro h
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.mpr hUP] at h
    exact hne h
  have h2 := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := U.subgroupOf P) hne'
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h2
  obtain ⟨haU, haC⟩ := Subgroup.mem_inf.mp ha
  refine ⟨(a : G), haU, ?_, fun g hg => ?_⟩
  · intro h
    apply ha1
    apply Subtype.ext
    apply Subtype.ext
    simpa using h
  · have := Subgroup.mem_center_iff.mp haC ⟨g, hg⟩
    exact congrArg Subtype.val this

theorem relIndex_centralizer_le (hp : p.Prime) {P U : Subgroup G} (hP : IsPGroup p P)
    (hnorm : ∀ g ∈ P, ∀ u ∈ U, g * u * g⁻¹ ∈ U) (hcard : Nat.card U ≤ p ^ 2) {x : G}
    (hxU : x ∈ U) (hx1 : x ≠ 1) : (centralizer ({x} : Set G)).relIndex P ≤ p := by
  have := Fact.mk hp
  let _ : MulAction P G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp P.subtype)
  have hsmul : ∀ (g : P) (y : G), g • y = (g : G) * y * (g : G)⁻¹ := fun g y =>
    ConjAct.smul_def (g : G) y
  have hstab : MulAction.stabilizer P x = (centralizer ({x} : Set G)).subgroupOf P := by
    ext g
    rw [MulAction.mem_stabilizer_iff, hsmul, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have := congrArg (fun t => t * (g : G)) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]
      simp
  have hindex : (centralizer ({x} : Set G)).relIndex P = (MulAction.orbit P x).ncard := by
    rw [Subgroup.relIndex, ← hstab, MulAction.index_stabilizer]
  have horbit : MulAction.orbit P x ⊆ (U : Set G) \ {1} := by
    rintro _ ⟨g, rfl⟩
    dsimp only
    refine ⟨?_, ?_⟩
    · rw [hsmul]
      exact hnorm g g.2 x hxU
    · intro h
      rw [Set.mem_singleton_iff, hsmul] at h
      apply hx1
      have := congrArg (fun t => (g : G)⁻¹ * t * (g : G)) h
      simpa [mul_assoc] using this
  have hfin : ((U : Set G) \ {1}).Finite := Set.toFinite _
  have hUcard : (U : Set G).ncard = Nat.card U := (Nat.card_coe_set_eq (U : Set G)).symm
  have hle : (MulAction.orbit P x).ncard ≤ p ^ 2 - 1 := by
    refine (Set.ncard_le_ncard horbit hfin).trans ?_
    rw [Set.ncard_sdiff_singleton_of_mem (by exact U.one_mem), hUcard]
    omega
  obtain ⟨n, hn⟩ := hP.index ((centralizer ({x} : Set G)).subgroupOf P)
  have hn' : (MulAction.orbit P x).ncard = p ^ n := by
    rw [← hindex]
    exact hn
  have hlt : p ^ n < p ^ 2 := by
    have : p ^ 2 - 1 < p ^ 2 := Nat.sub_lt (pow_pos hp.pos 2) one_pos
    omega
  have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
  calc (centralizer ({x} : Set G)).relIndex P = p ^ n := hn
    _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    _ = p := pow_one p

end PGroup

section Vertices

variable [Finite G] {p : ℕ}

theorem relIndex_pow (hp : p.Prime) {P : Subgroup G} (hP : IsPGroup p P) (Q : Subgroup G) :
    ∃ n, Q.relIndex P = p ^ n := by
  have := Fact.mk hp
  exact hP.index (Q.subgroupOf P)

omit [Finite G] in
theorem pow_eq_self_of_le (hp : p.Prime) {n : ℕ} (hle : p ^ n ≤ p) (hne : p ^ n ≠ 1) :
    p ^ n = p := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · rcases Nat.eq_zero_or_pos n with h0 | h0
    · exact absurd (by rw [h0, pow_zero]) hne
    · have : n = 1 := by omega
      rw [this, pow_one]
  · have h1 : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right hp.pos h2
    have h3 : p < p ^ 2 := by
      have := hp.one_lt
      nlinarith
    omega

theorem isElemAbelian_card_sup_zpowers (hp : p.Prime) {a y : G} (ha : a ^ p = 1) (hy : y ^ p = 1)
    (ha1 : a ≠ 1) (hya : y ∉ zpowers a) (hcomm : a * y = y * a) :
    Open.IsElemAbelian p (zpowers a ⊔ zpowers y) ∧
      Nat.card (zpowers a ⊔ zpowers y : Subgroup G) = p ^ 2 := by
  have := Fact.mk hp
  have hcomm' : ∀ s ∈ zpowers a, ∀ t ∈ zpowers y, s * t = t * s := by
    rintro s ⟨m, rfl⟩ t ⟨n, rfl⟩
    exact ((Commute.zpow_zpow (show Commute a y from hcomm) m n)).eq
  have hel : Open.IsElemAbelian p (zpowers a ⊔ zpowers y) :=
    IsElemAbelian.sup (isElemAbelian_zpowers ha) (isElemAbelian_zpowers hy) hcomm'
  refine ⟨hel, ?_⟩
  have hy1 : y ≠ 1 := fun h => hya (h ▸ one_mem _)
  have hoa : orderOf a = p := orderOf_eq_prime ha ha1
  have hoy : orderOf y = p := orderOf_eq_prime hy hy1
  have hup : Nat.card (zpowers a ⊔ zpowers y : Subgroup G) ≤ p ^ 2 := by
    refine (card_sup_le_of_commute hcomm').trans ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hoy, sq]
  have hlt : zpowers a < zpowers a ⊔ zpowers y :=
    lt_of_le_of_ne le_sup_left (fun h => hya (h ▸ Subgroup.mem_sup_right (mem_zpowers y)))
  have hcl := card_lt_of_lt hlt
  rw [Nat.card_zpowers, hoa] at hcl
  obtain ⟨k, hk⟩ := IsElemAbelian.exists_card hp hel
  rw [hk] at hcl hup ⊢
  have hk2 : 2 ≤ k := by
    by_contra hcon
    have : k ≤ 1 := by omega
    have : p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos this
    rw [pow_one] at this
    omega
  exact le_antisymm hup (Nat.pow_le_pow_right hp.pos hk2)

theorem exists_vertex_le (hp : p.Prime) {F : Subgroup G} (hF : Open.IsElemAbelian p F)
    (hcard : p ^ 2 ≤ Nat.card F) :
    ∃ W : Subgroup G, W ≤ F ∧ Open.IsElemAbelian p W ∧ Nat.card W = p ^ 2 := by
  obtain ⟨k, hk⟩ := IsElemAbelian.exists_card hp hF
  have hk2 : 2 ≤ k := by
    rw [hk] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  exact exists_subgroup_card hp hF hk2 hk

theorem exists_other_vertex (hp : p.Prime) {U F : Subgroup G} (hU : Nat.card U = p ^ 2)
    (hF : Open.IsElemAbelian p F) (hcard : p ^ 3 ≤ Nat.card F) :
    ∃ W : Subgroup G, W ≤ F ∧ Open.IsElemAbelian p W ∧ Nat.card W = p ^ 2 ∧ W ≠ U := by
  have hp3 : p ^ 2 ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
  obtain ⟨W₀, hW₀F, hW₀, hW₀card⟩ := exists_vertex_le hp hF (hp3.trans hcard)
  by_cases hWU : W₀ = U
  swap
  · exact ⟨W₀, hW₀F, hW₀, hW₀card, hWU⟩
  subst hWU
  have hexy : ∃ y ∈ F, y ∉ W₀ := by
    by_contra hcon
    have hle : F ≤ W₀ := fun y hy => by_contra (fun hy' => hcon ⟨y, hy, hy'⟩)
    have := Subgroup.card_le_of_le hle
    have h3 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  obtain ⟨y, hyF, hyW⟩ := hexy
  have hbot : W₀ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW₀card
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  obtain ⟨⟨a, haW⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haF : a ∈ F := hW₀F haW
  have hF' := isElemAbelian_iff.mp hF
  have hyz : y ∉ zpowers a := fun h => hyW (Subgroup.zpowers_le.mpr haW h)
  obtain ⟨hel, hcardW⟩ := isElemAbelian_card_sup_zpowers hp (hF'.2 a haF) (hF'.2 y hyF) ha1' hyz
    (hF'.1 a haF y hyF)
  refine ⟨zpowers a ⊔ zpowers y, sup_le (Subgroup.zpowers_le.mpr haF)
    (Subgroup.zpowers_le.mpr hyF), hel, hcardW, ?_⟩
  intro h
  exact hyW (h ▸ Subgroup.mem_sup_right (mem_zpowers y))

theorem sup_isElemAbelian_card (hp : p.Prime) {A B : Subgroup G} (hA : Open.IsElemAbelian p A)
    (hAcard : Nat.card A = p ^ 2) (hB : Open.IsElemAbelian p B) (hBcard : Nat.card B = p ^ 2)
    (hne : A ≠ B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    Open.IsElemAbelian p (A ⊔ B) ∧ p ^ 3 ≤ Nat.card (A ⊔ B : Subgroup G) := by
  have hel := IsElemAbelian.sup hA hB hAB
  refine ⟨hel, ?_⟩
  have hlt : A < A ⊔ B := by
    refine lt_of_le_of_ne le_sup_left (fun h => hne ?_)
    have hBA : B ≤ A := h ▸ le_sup_right
    exact (Subgroup.eq_of_le_of_card_ge hBA (by rw [hAcard, hBcard])).symm
  have hcl := card_lt_of_lt hlt
  obtain ⟨k, hk⟩ := IsElemAbelian.exists_card hp hel
  rw [hAcard, hk] at hcl
  have hk3 : 3 ≤ k := by
    by_contra hcon
    have : k ≤ 2 := by omega
    have : p ^ k ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos this
    omega
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk3

end Vertices

end CFSG.GH74.Uniqueness.SU.SU1
