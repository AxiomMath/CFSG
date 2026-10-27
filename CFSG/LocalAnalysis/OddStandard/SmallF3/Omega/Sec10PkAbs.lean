module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs
public import CFSG.Walter.AStar.Subnormal
public import CFSG.Blueprint.OddStandardExact
public import CFSG.Blueprint.RecognitionDefs

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

local notation "SL23" => Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

section Subnormal

variable {G : Type*} [Group G]

theorem le_of_subnormal_of_commutators {K Q : Subgroup G} (hK : K.IsSubnormal) {t x : G}
    (ht : t ∈ K) (hx : x ∈ K)
    (hQ : ∀ q ∈ Q, ∃ q' ∈ Q, q = x * q' * x⁻¹ * q'⁻¹ ∨ q = t * (x * q' * x⁻¹ * q'⁻¹)) :
    Q ≤ K := by
  by_contra hQK
  have hKM : K ≤ K ⊔ Q := le_sup_left
  have hQM : Q ≤ K ⊔ Q := le_sup_right
  have hsn : (K.subgroupOf (K ⊔ Q)).IsSubnormal := hK.subgroupOf
  rcases hsn.lt_normal with htop | ⟨N, hNn, hKN, hNlt⟩
  · exact hQK (hQM.trans (Subgroup.subgroupOf_eq_top.1 htop))
  · refine hNlt.ne ?_
    have hxN : (⟨x, hKM hx⟩ : ↥(K ⊔ Q)) ∈ N := hKN (Subgroup.mem_subgroupOf.2 hx)
    have htN : (⟨t, hKM ht⟩ : ↥(K ⊔ Q)) ∈ N := hKN (Subgroup.mem_subgroupOf.2 ht)
    have hQN : ∀ q ∈ Q, q ∈ N.map (K ⊔ Q).subtype := by
      intro q hq
      obtain ⟨q', hq'Q, hq'⟩ := hQ q hq
      have hc : (⟨x, hKM hx⟩ : ↥(K ⊔ Q)) * ⟨q', hQM hq'Q⟩ * (⟨x, hKM hx⟩ : ↥(K ⊔ Q))⁻¹ *
          (⟨q', hQM hq'Q⟩ : ↥(K ⊔ Q))⁻¹ ∈ N := by
        rw [show ∀ a b : ↥(K ⊔ Q), a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) from
          fun a b => by group]
        exact N.mul_mem hxN (hNn.conj_mem _ (N.inv_mem hxN) _)
      refine ⟨⟨q, hQM hq⟩, ?_, rfl⟩
      rcases hq' with h | h
      · have : (⟨q, hQM hq⟩ : ↥(K ⊔ Q)) = ⟨x, hKM hx⟩ * ⟨q', hQM hq'Q⟩ * ⟨x, hKM hx⟩⁻¹ *
            ⟨q', hQM hq'Q⟩⁻¹ := Subtype.ext h
        rw [this]
        exact hc
      · have : (⟨q, hQM hq⟩ : ↥(K ⊔ Q)) = ⟨t, hKM ht⟩ * (⟨x, hKM hx⟩ * ⟨q', hQM hq'Q⟩ *
            ⟨x, hKM hx⟩⁻¹ * ⟨q', hQM hq'Q⟩⁻¹) := Subtype.ext h
        rw [this]
        exact N.mul_mem htN hc
    have hle : K ⊔ Q ≤ N.map (K ⊔ Q).subtype := by
      refine sup_le (fun k hk => ?_) hQN
      exact ⟨⟨k, hKM hk⟩, hKN (Subgroup.mem_subgroupOf.2 hk), rfl⟩
    rw [eq_top_iff]
    intro m _
    obtain ⟨n, hn, hnm⟩ := hle m.2
    have : n = m := Subtype.ext hnm
    rw [← this]
    exact hn

theorem le_of_subnormal_of_commutators' {C K Q : Subgroup G} (hKC : K ≤ C) (hQC : Q ≤ C)
    (hK : (K.subgroupOf C).IsSubnormal) {t x : G} (ht : t ∈ K) (hx : x ∈ K)
    (hQ : ∀ q ∈ Q, ∃ q' ∈ Q, q = x * q' * x⁻¹ * q'⁻¹ ∨ q = t * (x * q' * x⁻¹ * q'⁻¹)) :
    Q ≤ K := by
  have h := le_of_subnormal_of_commutators (K := K.subgroupOf C) (Q := Q.subgroupOf C) hK
    (t := ⟨t, hKC ht⟩) (x := ⟨x, hKC hx⟩) (Subgroup.mem_subgroupOf.2 ht)
    (Subgroup.mem_subgroupOf.2 hx) ?_
  · intro q hq
    exact Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_subgroupOf.2 hq : (⟨q, hQC hq⟩ : ↥C) ∈
      Q.subgroupOf C))
  · rintro ⟨q, hqC⟩ hq
    obtain ⟨q', hq', h'⟩ := hQ q (Subgroup.mem_subgroupOf.1 hq)
    refine ⟨⟨q', hQC hq'⟩, Subgroup.mem_subgroupOf.2 hq', ?_⟩
    rcases h' with h' | h'
    · exact Or.inl (Subtype.ext h')
    · exact Or.inr (Subtype.ext h')

end Subnormal

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCore_eq_bot_of_subnormal {C K : Subgroup G} (hKC : K ≤ C)
    (hC : ∀ N : Subgroup C, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hK : (K.subgroupOf C).IsSubnormal) : oddCore K = ⊥ := by
  have hC' : CFSG.pPrimeCore 2 C = ⊥ := by
    rw [CFSG.pPrimeCore_eq_bot_iff]
    exact fun N hN hcop => hC N hN (Nat.coprime_two_left.1 hcop)
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hK
  rw [hC', le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h1
  have h2 := CFSG.pPrimeCore_map_iso 2 (Subgroup.subgroupOfEquivOfLe hKC)
  rw [h1, Subgroup.map_bot] at h2
  refine le_antisymm ?_ bot_le
  rw [h2]
  exact sSup_le_sSup fun N ⟨hN, hodd⟩ => ⟨hN, Nat.coprime_two_left.2 hodd⟩

theorem noOdd_of_tests {C : Subgroup G} {Cl : List G} (hCl : ∀ x, x ∈ Cl ↔ x ∈ C) {k m : ℕ}
    (hm : m ∣ 9) (hcard : Nat.card C = 2 ^ k * m)
    (h1 : ∀ o ∈ Cl, o ≠ 1 → o ^ 3 = 1 → ∃ c ∈ Cl, (o * (c * o * c⁻¹)) ^ 3 ≠ 1)
    (h2 : ∀ x ∈ Cl, x ^ 9 = 1 → x ^ 3 = 1) :
    ∀ N : Subgroup ↥C, N.Normal → Odd (Nat.card N) → N = ⊥ := by
  intro N hN hodd
  have hdvd : Nat.card N ∣ 2 ^ k * m := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hcop : Nat.Coprime (Nat.card N) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 hodd)
  have h9 : Nat.card N ∣ 9 := (hcop.dvd_of_dvd_mul_left hdvd).trans hm
  have key : ∀ y : ↥C, y ∈ N → (y : G) ^ 3 = 1 := by
    intro y hy
    have hy1 : (⟨y, hy⟩ : ↥N) ^ Nat.card N = 1 := pow_card_eq_one'
    obtain ⟨j, hj⟩ := h9
    have hy9 : (y : G) ^ 9 = 1 := by
      have h' : y ^ Nat.card N = 1 := congrArg (fun z : ↥N => ((z : ↥C))) hy1
      have h'' : ((y ^ Nat.card N : ↥C) : G) = 1 := by rw [h']; rfl
      rw [hj, pow_mul]
      have : ((y : G)) ^ Nat.card N = 1 := by rw [← Subgroup.coe_pow]; exact h''
      rw [this, one_pow]
    exact h2 _ ((hCl _).2 y.2) hy9
  by_contra hne
  obtain ⟨o, ho⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hoC : ((o : ↥C) : G) ∈ Cl := (hCl _).2 (o : ↥C).2
  have ho1 : ((o : ↥C) : G) ≠ 1 := fun h => ho (Subtype.ext (Subtype.ext h))
  obtain ⟨c, hc, hc3⟩ := h1 _ hoC ho1 (key _ o.2)
  have hcC : (⟨c, (hCl c).1 hc⟩ : ↥C) * (o : ↥C) * (⟨c, (hCl c).1 hc⟩ : ↥C)⁻¹ ∈ N :=
    hN.conj_mem _ o.2 _
  exact hc3 (key _ (N.mul_mem o.2 hcC))

end OddCore

section ListSub

variable {G : Type*} [Group G]

def listSub (l : List G) : Subgroup G := Subgroup.closure {x | x ∈ l}

theorem mem_listSub_iff {l : List G} (h1 : (1 : G) ∈ l) (hmul : ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l)
    (hinv : ∀ a ∈ l, a⁻¹ ∈ l) {x : G} : x ∈ listSub l ↔ x ∈ l := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  let H : Subgroup G :=
    { carrier := {x | x ∈ l}
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := h1
      inv_mem' := fun {a} ha => hinv a ha }
  exact (Subgroup.closure_le H).2 (fun y hy => hy) h

theorem card_listSub_le [DecidableEq G] {l : List G} (h1 : (1 : G) ∈ l)
    (hmul : ∀ a ∈ l, ∀ b ∈ l, a * b ∈ l) (hinv : ∀ a ∈ l, a⁻¹ ∈ l) :
    Nat.card (listSub l) ≤ l.length := by
  have hset : ((listSub l : Subgroup G) : Set G) = ↑l.toFinset := by
    ext x
    simp only [SetLike.mem_coe, Finset.mem_coe, List.mem_toFinset]
    exact mem_listSub_iff h1 hmul hinv
  rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  exact List.toFinset_card_le l

theorem list_le_of_noncentral {C K : Subgroup G} {Qb : List G} {t x : G} (hKC : K ≤ C)
    (hsub : (K.subgroupOf C).IsSubnormal) (ht : t ∈ K) (hx : x ∈ K) (hQC : ∀ q ∈ Qb, q ∈ C)
    (h1 : (1 : G) ∈ Qb) (hmul : ∀ a ∈ Qb, ∀ b ∈ Qb, a * b ∈ Qb) (hinv : ∀ a ∈ Qb, a⁻¹ ∈ Qb)
    (hns : ∀ q ∈ Qb, ∃ q' ∈ Qb, q = x * q' * x⁻¹ * q'⁻¹ ∨ q = t * (x * q' * x⁻¹ * q'⁻¹)) :
    ∀ q ∈ Qb, q ∈ K := by
  have hQC' : listSub Qb ≤ C := (Subgroup.closure_le C).2 fun q hq => hQC q hq
  have h := le_of_subnormal_of_commutators' hKC hQC' hsub ht hx (fun q hq => by
    obtain ⟨q', hq', h'⟩ := hns q ((mem_listSub_iff h1 hmul hinv).1 hq)
    exact ⟨q', (mem_listSub_iff h1 hmul hinv).2 hq', h'⟩)
  exact fun q hq => h ((mem_listSub_iff h1 hmul hinv).2 hq)

end ListSub

section Counting

variable {G : Type*} [Group G] [Finite G]

theorem card_finset_le_card {K : Subgroup G} {s : Finset G} (h : ∀ p ∈ s, p ∈ K) :
    s.card ≤ Nat.card K := by
  have hinj : Function.Injective (fun p : ↥s => (⟨p.1, h p.1 p.2⟩ : K)) := fun a b hab =>
    Subtype.ext (Subtype.mk.inj hab)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

end Counting

section SL23Facts

def slT : SL23 := ⟨!![1, 1; 0, 1], by decide⟩

def slU : SL23 := ⟨!![1, 0; 1, 1], by decide⟩

def evalSL (w : List Bool) : SL23 := w.foldl (fun r b => r * if b then slU else slT) 1

def wordsSL : List (List Bool) :=
  [[], [false], [true], [false, false], [false, true], [true, false], [true, true],
    [false, false, true], [false, true, false], [false, true, true], [true, false, false],
    [true, false, true], [true, true, false], [false, false, true, false],
    [false, false, true, true], [false, true, false, false], [false, true, false, true],
    [false, true, true, false], [true, false, false, true], [true, false, true, true],
    [true, true, false, false], [true, true, false, true], [false, false, true, false, true],
    [false, true, false, true, true]]

theorem exists_word_sl23 : ∀ A : SL23, ∃ w ∈ wordsSL, evalSL w = A := by decide +kernel

theorem card_sl23 : Nat.card SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem closure_cube_sl23 : Subgroup.closure {x : SL23 | x ^ 3 = 1} = ⊤ := by
  have hT : slT ∈ Subgroup.closure {x : SL23 | x ^ 3 = 1} :=
    Subgroup.subset_closure (by decide +kernel : slT ^ 3 = 1)
  have hU : slU ∈ Subgroup.closure {x : SL23 | x ^ 3 = 1} :=
    Subgroup.subset_closure (by decide +kernel : slU ^ 3 = 1)
  have key : ∀ (w : List Bool) (r : SL23), r ∈ Subgroup.closure {x : SL23 | x ^ 3 = 1} →
      w.foldl (fun r b => r * if b then slU else slT) r ∈
        Subgroup.closure {x : SL23 | x ^ 3 = 1} := by
    intro w
    induction w with
    | nil => exact fun r hr => hr
    | cons b w ih =>
      intro r hr
      refine ih _ (Subgroup.mul_mem _ hr ?_)
      cases b
      · exact hT
      · exact hU
  rw [eq_top_iff]
  intro A _
  obtain ⟨w, -, rfl⟩ := exists_word_sl23 A
  exact key w 1 (Subgroup.one_mem _)

theorem sl23_facts {P : Type} [Group P] {K : Subgroup P} (hK : IsSL23Mod K)
    (hodd : oddCore K = ⊥) :
    Nat.card K = 24 ∧ ∀ H : Subgroup P, (∀ x ∈ K, x ^ 3 = 1 → x ∈ H) → K ≤ H := by
  obtain ⟨f⟩ := hK
  let e : K ≃* SL23 :=
    ((QuotientGroup.quotientMulEquivOfEq hodd).trans QuotientGroup.quotientBot).symm.trans f
  refine ⟨by rw [Nat.card_congr e.toEquiv]; exact card_sl23, fun H hH k hk => ?_⟩
  let H₂ : Subgroup SL23 := (H.comap K.subtype).comap e.symm.toMonoidHom
  have hle : Subgroup.closure {x : SL23 | x ^ 3 = 1} ≤ H₂ := by
    refine (Subgroup.closure_le H₂).2 fun y hy => ?_
    have h3 : ((e.symm y : K) : P) ^ 3 = 1 := by
      rw [← Subgroup.coe_pow, ← map_pow]
      have : y ^ 3 = 1 := hy
      rw [this, map_one, Subgroup.coe_one]
    exact hH _ (e.symm y).2 h3
  rw [closure_cube_sl23] at hle
  have h1 : (⟨k, hk⟩ : K) ∈ H.comap K.subtype := by
    have := hle (Subgroup.mem_top (e ⟨k, hk⟩))
    simpa [H₂] using this
  exact h1

end SL23Facts

end CFSG.OddStandard.SmallF3.Omega
