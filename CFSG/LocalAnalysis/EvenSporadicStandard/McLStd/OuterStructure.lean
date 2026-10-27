module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup
open scoped commutatorElement

structure OuterSetup (G : Type) [Group G] (L : Subgroup G) (t : G) : Prop where
  t_sq : t * t = 1
  t_ne : t ≠ 1
  t_comm : ∀ l ∈ L, t * l = l * t
  norm : ∀ m : G, m * t = t * m → m ∈ normalizer (L : Set G)
  idx : (L ⊔ zpowers t).relIndex (centralizer ({t} : Set G)) ∣ 2
  centerless : ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z = 1
  card_L : Nat.card L = 898128000
  one_class : ∀ x ∈ L, ∀ y ∈ L, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 →
    ∃ c ∈ L, y = c * x * c⁻¹
  perfect : ∀ l ∈ L, l * l = 1 → l ≠ 1 →
    ∃ B : Subgroup G, B ≤ centralizer ({l} : Set G) ∧ l ∈ B ∧ ⁅B, B⁆ = B
  fix_card : ∀ v : G, v * t = t * v → v * v = 1 → v ∉ L ⊔ zpowers t →
    Nat.card {x : G // x ∈ L ∧ x * v = v * x} = 7920

variable {G : Type} [Group G] {L : Subgroup G} {t : G}

namespace OuterSetup

variable (S : OuterSetup G L t)

include S

theorem t_mem_centralizer : t ∈ centralizer (L : Set G) := by
  rw [mem_centralizer_iff]
  intro l hl
  exact (S.t_comm l hl).symm

theorem t_not_mem : t ∉ L := fun htL =>
  S.t_ne (S.centerless t htL fun l hl => S.t_comm l hl)

theorem le_centralizer : L ≤ centralizer ({t} : Set G) := fun l hl =>
  mem_centralizer_singleton_iff.2 (S.t_comm l hl).symm

theorem orderOf_t : orderOf t = 2 :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  orderOf_eq_prime (by rw [sq]; exact S.t_sq) S.t_ne

theorem mem_zpowers_cases {b : G} (hb : b ∈ zpowers t) : b = 1 ∨ b = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  rw [← zpow_mod_orderOf, S.orderOf_t]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · left; simp [h0]
  · right; simp [h0]

theorem mem_sup_cases {x : G} (hx : x ∈ L ⊔ zpowers t) : x ∈ L ∨ x * t ∈ L := by
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
    (A := L) (B := zpowers t) (zpowers_le.2 S.t_mem_centralizer) hx
  rcases S.mem_zpowers_cases hb with hb1 | hb1
  · left; rw [hb1, mul_one]; exact ha
  · right
    have : a * b * t = a := by rw [hb1, mul_assoc, S.t_sq, mul_one]
    rw [this]; exact ha

theorem sup_le_centralizer : L ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
  sup_le S.le_centralizer (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))

theorem comm_mem {a b : G} (ha : a * t = t * a) (hb : b * t = t * b) : ⁅a, b⁆ ∈ L := by
  have claim1 : ∀ m : G, m * t = t * m → ∀ n ∈ L ⊔ zpowers t, ⁅m, n⁆ ∈ L := by
    intro m hm n hn
    obtain ⟨l, hl, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer
      (A := L) (B := zpowers t) (zpowers_le.2 S.t_mem_centralizer) hn
    have hmz : m * z = z * m := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
      exact ((Commute.zpow_right (show Commute m t from hm) k)).eq
    have hml : m * l * m⁻¹ ∈ L := (mem_normalizer_iff.1 (S.norm m hm) l).1 hl
    have hz' : m * z * m⁻¹ = z := by rw [hmz]; group
    rw [commutatorElement_def]
    have : m * (l * z) * m⁻¹ * (l * z)⁻¹ = (m * l * m⁻¹) * l⁻¹ := by
      calc m * (l * z) * m⁻¹ * (l * z)⁻¹ = (m * l * m⁻¹) * (m * z * m⁻¹) * z⁻¹ * l⁻¹ := by group
        _ = (m * l * m⁻¹) * z * z⁻¹ * l⁻¹ := by rw [hz']
        _ = (m * l * m⁻¹) * l⁻¹ := by group
    rw [this]
    exact L.mul_mem hml (L.inv_mem hl)
  set N : Subgroup G := L ⊔ zpowers t with hN
  by_cases haN : a ∈ N
  · have := claim1 b hb a haN
    have h2 : ⁅a, b⁆ = ⁅b, a⁆⁻¹ := (commutatorElement_inv b a).symm
    rw [h2]
    exact L.inv_mem this
  by_cases hbN : b ∈ N
  · exact claim1 a ha b hbN
  have haM : a ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 ha
  have hbM : b ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hb
  have hidx2 : (N.subgroupOf (centralizer ({t} : Set G))).index = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 S.idx with h1 | h2
    · exfalso
      apply haN
      have h1' : N.subgroupOf (centralizer ({t} : Set G)) = ⊤ :=
        Subgroup.index_eq_one.1 (by rw [Subgroup.relIndex] at h1; exact h1)
      have : (⟨a, haM⟩ : centralizer ({t} : Set G)) ∈
          N.subgroupOf (centralizer ({t} : Set G)) := by rw [h1']; exact mem_top _
      exact this
    · rw [Subgroup.relIndex] at h2; exact h2
  have hmem : a * b⁻¹ ∈ N := by
    have hx' : (⟨a, haM⟩ : centralizer ({t} : Set G)) ∉
        N.subgroupOf (centralizer ({t} : Set G)) := haN
    have hy' : (⟨b⁻¹, (centralizer ({t} : Set G)).inv_mem hbM⟩ : centralizer ({t} : Set G)) ∉
        N.subgroupOf (centralizer ({t} : Set G)) := fun h => hbN (by simpa using N.inv_mem h)
    exact (Subgroup.mul_mem_iff_of_index_two hidx2
      (a := ⟨a, haM⟩) (b := ⟨b⁻¹, (centralizer ({t} : Set G)).inv_mem hbM⟩)).2
        (iff_of_false hx' hy')
  have h3 := claim1 b hb (a * b⁻¹) hmem
  have h4 : ⁅a, b⁆ = ⁅b, a * b⁻¹⁆⁻¹ := by
    rw [← commutatorElement_inv]
    simp only [commutatorElement_def]
    group
  rw [h4]
  exact L.inv_mem h3

theorem not_isConj {l : G} (hl : l ∈ L) (hl2 : l * l = 1) (hl1 : l ≠ 1) : ¬ IsConj t l := by
  rintro hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨B, hBc, hlB, hB⟩ := S.perfect l hl hl2 hl1
  let B' : Subgroup G := B.map (MulAut.conj c⁻¹).toMonoidHom
  have hB'M : ∀ x ∈ B', x * t = t * x := by
    rintro _ ⟨b, hb, rfl⟩
    have hbl : b * l = l * b := mem_centralizer_singleton_iff.1 (hBc hb)
    have ht' : t = c⁻¹ * l * c := by rw [← hc]; group
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc c⁻¹ * b * c⁻¹⁻¹ * t = c⁻¹ * (b * l) * c := by rw [ht']; group
      _ = c⁻¹ * (l * b) * c := by rw [hbl]
      _ = t * (c⁻¹ * b * c⁻¹⁻¹) := by rw [ht']; group
  have hB'perf : ⁅B', B'⁆ = B' := by
    show ⁅B.map (MulAut.conj c⁻¹).toMonoidHom, B.map (MulAut.conj c⁻¹).toMonoidHom⁆ =
      B.map (MulAut.conj c⁻¹).toMonoidHom
    rw [← Subgroup.map_commutator, hB]
  have htB' : t ∈ B' := by
    refine ⟨l, hlB, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]; group
  have hle : ⁅B', B'⁆ ≤ L := by
    rw [commutator_le]
    intro x hx y hy
    exact S.comm_mem (hB'M x hx) (hB'M y hy)
  have htB'' : t ∈ ⁅B', B'⁆ := by rw [hB'perf]; exact htB'
  exact S.t_not_mem (hle htB'')

theorem exists_sylow [Finite G] : ∃ P : Subgroup G, P ≤ centralizer ({t} : Set G) ∧
    IsPGroup 2 P ∧ t ∈ P ∧ ¬ 2 ∣ P.relIndex (centralizer ({t} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := centralizer ({t} : Set G) with hM
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  let t' : M := ⟨t, htM⟩
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact S.orderOf_t
  have hZ : IsPGroup 2 (zpowers t') :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, ht'2, pow_one])
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  refine ⟨(Q : Subgroup M).map M.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, -, rfl⟩
    exact y.2
  · exact (Q.isPGroup').of_equiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)
  · exact ⟨t', hQ (mem_zpowers t'), rfl⟩
  · have : ((Q : Subgroup M).map M.subtype).relIndex M = (Q : Subgroup M).index := by
      rw [Subgroup.relIndex, show ((Q : Subgroup M).map M.subtype).subgroupOf M = Q from
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective _]
    rw [this]
    exact Q.not_dvd_index

theorem false_of_centralizes_outer [Finite G] {P : Subgroup G}
    (hPM : P ≤ centralizer ({t} : Set G)) (hP : IsPGroup 2 P)
    (hodd : ¬ 2 ∣ P.relIndex (centralizer ({t} : Set G))) {v : G} (hvt : v * t = t * v)
    (hv2 : v * v = 1) (hvN : v ∉ L ⊔ zpowers t) (hvP : ∀ p ∈ P, p * v = v * p) : False := by
  classical
  set M : Subgroup G := centralizer ({t} : Set G) with hM
  set N : Subgroup G := L ⊔ zpowers t with hN
  have htM : t ∈ M := mem_centralizer_singleton_iff.2 rfl
  have hLM : L ≤ M := S.le_centralizer
  have hNM : N ≤ M := S.sup_le_centralizer
  have hLN : L ≤ N := le_sup_left
  have htN : t ∈ N := mem_sup_right (mem_zpowers t)
  have hNidx : N.relIndex M = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 S.idx with h1 | h2
    · exfalso
      exact hvN ((Subgroup.relIndex_eq_one.1 h1) (mem_centralizer_singleton_iff.2 hvt))
    · exact h2
  have hLNidx : L.relIndex N = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htN⟩, fun b => ?_⟩
    have hb := S.mem_sup_cases b.2
    have hnot : ¬ ((b : G) ∈ L ∧ (b : G) * t ∈ L) := by
      rintro ⟨h1, h2⟩
      apply S.t_not_mem
      have := L.mul_mem (L.inv_mem h1) h2
      simpa [mul_assoc] using this
    show Xor ((b : G) * t ∈ L) ((b : G) ∈ L)
    rcases hb with hb | hb
    · exact Or.inr ⟨hb, fun h => hnot ⟨hb, h⟩⟩
    · exact Or.inl ⟨hb, fun h => hnot ⟨h, hb⟩⟩
  have hLM4 : L.relIndex M = 4 := by
    rw [← Subgroup.relIndex_mul_relIndex L N M hLN hNM, hLNidx, hNidx]
  have hMcard : Nat.card M = 4 * 898128000 := by
    have h := Subgroup.relIndex_mul_card L M
    rw [inf_eq_left.2 hLM, S.card_L, hLM4] at h
    exact h.symm
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hPcard : Nat.card P = 2 ^ 9 := by
    have h := Subgroup.relIndex_mul_card P M
    rw [inf_eq_left.2 hPM, hMcard, hj] at h
    have hcop : Nat.Coprime 2 (P.relIndex M) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
    have h1 : 2 ^ j ∣ 2 ^ 9 * 7016625 :=
      Dvd.intro_left (P.relIndex M) (by rw [h]; norm_num)
    have h2 : 2 ^ 9 ∣ 2 ^ j * P.relIndex M :=
      Dvd.intro 7016625 (by rw [mul_comm (2 ^ j), h]; norm_num)
    have hj1 : j ≤ 9 := by
      have hc : Nat.Coprime (2 ^ j) 7016625 :=
        Nat.Coprime.pow_left j (by norm_num)
      have := hc.dvd_of_dvd_mul_right h1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    have hj2 : 9 ≤ j := by
      have hc : Nat.Coprime (2 ^ 9) (P.relIndex M) := Nat.Coprime.pow_left 9 hcop
      have := hc.dvd_of_dvd_mul_right h2
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
    rw [hj, show j = 9 by omega]
  set Q : Subgroup G := L ⊓ P with hQ
  have hQP : Q ≤ P := inf_le_right
  have hQ2 : IsPGroup 2 Q := hP.to_le hQP
  obtain ⟨k, hk⟩ := hQ2.exists_card_eq
  have hQc : Q ≤ L ⊓ centralizer ({v} : Set G) := fun x hx =>
    ⟨hx.1, mem_centralizer_singleton_iff.2 (hvP x hx.2)⟩
  have hfix := S.fix_card v hvt hv2 hvN
  have hcardC : Nat.card ↥(L ⊓ centralizer ({v} : Set G)) = 7920 := by
    rw [← hfix]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by
      simp [mem_inf, mem_centralizer_singleton_iff])
  have hdvd : Nat.card Q ∣ 7920 := hcardC ▸ Subgroup.card_dvd_of_le hQc
  have hk4 : 2 ^ k ≤ 16 := by
    rw [hk] at hdvd
    have hc : Nat.Coprime (2 ^ k) 495 := Nat.Coprime.pow_left k (by norm_num)
    have : 2 ^ k ∣ 16 := hc.dvd_of_dvd_mul_right (by simpa using hdvd)
    exact Nat.le_of_dvd (by norm_num) this
  have hrel : L.relIndex P ≤ 4 := by
    have := Subgroup.relIndex_le_of_le_right (H := L) hPM (by rw [hLM4]; norm_num)
    rwa [hLM4] at this
  have hmul := Subgroup.relIndex_mul_card L P
  rw [hPcard] at hmul
  have hle : L.relIndex P * Nat.card Q ≤ 4 * 16 := by
    rw [hk]
    exact Nat.mul_le_mul hrel hk4
  have hmul' : L.relIndex P * Nat.card Q = 2 ^ 9 := hmul
  omega

theorem mem_or_mul_mem [Finite G] {P : Subgroup G} (hPM : P ≤ centralizer ({t} : Set G))
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.relIndex (centralizer ({t} : Set G))) (htP : t ∈ P)
    {v : G} (hvP : ∀ p ∈ P, p * v = v * p) (hv2 : v * v = 1) : v ∈ L ∨ v * t ∈ L := by
  have hvt : v * t = t * v := (hvP t htP).symm
  by_cases hvN : v ∈ L ⊔ zpowers t
  · exact S.mem_sup_cases hvN
  · exact (S.false_of_centralizes_outer hPM hP hodd hvt hv2 hvN hvP).elim

end OuterSetup



end CFSG.EvenSporadicStandard.McLStd
