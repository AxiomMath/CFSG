module

public import Mathlib.Data.ZMod.QuotientGroup
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.LieType.SeitzGeneration

variable {G : Type*} [Group G] {p : ℕ}

theorem mul_rearrange {A B C A' B' C' : G} (hCA : Commute C A') (hBA : Commute B A')
    (hCB : Commute C B') : A * B * C * (A' * B' * C') = A * A' * (B * B') * (C * C') := by
  simp only [mul_assoc]
  rw [hCA.left_comm, hBA.left_comm, hCB.left_comm]

theorem closure_triple_form (hp : 0 < p) {a b c : G} (hab : Commute a b) (hac : Commute a c)
    (hbc : Commute b c) (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b, c} : Set G)) : ∃ i j k : ℕ, x = a ^ i * b ^ j * c ^ k := by
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | one => exact ⟨0, 0, 0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨i, j, k, rfl⟩ := hx
    obtain ⟨i', j', k', rfl⟩ := hy
    refine ⟨i + i', j + j', k + k', ?_⟩
    rw [mul_rearrange ((hac.symm).pow_pow k i') ((hab.symm).pow_pow j i') ((hbc.symm).pow_pow k j'),
      pow_add, pow_add, pow_add]
  | inv x _ hx =>
    obtain ⟨i, j, k, rfl⟩ := hx
    refine ⟨(p - 1) * i, (p - 1) * j, (p - 1) * k, ?_⟩
    have h1 : a ^ i * b ^ j * c ^ k * (a ^ ((p - 1) * i) * b ^ ((p - 1) * j) *
        c ^ ((p - 1) * k)) = 1 := by
      rw [mul_rearrange ((hac.symm).pow_pow k ((p - 1) * i)) ((hab.symm).pow_pow j ((p - 1) * i))
        ((hbc.symm).pow_pow k ((p - 1) * j)), ← pow_add, ← pow_add, ← pow_add]
      have key : ∀ m : ℕ, m + (p - 1) * m = p * m := fun m => by
        rw [Nat.sub_one_mul]
        have : m ≤ p * m := Nat.le_mul_of_pos_left m hp
        omega
      have h2 := key i
      have h3 := key j
      have h4 := key k
      rw [h2, h3, h4, pow_mul, pow_mul, pow_mul, ha, hb, hc]
      simp
    exact inv_eq_of_mul_eq_one_right h1

theorem closure_pair_le {E : Subgroup G} {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    Subgroup.closure ({a, b} : Set G) ≤ E :=
  (Subgroup.closure_le E).2 (by
    rintro y (rfl | rfl)
    exacts [ha, hb])

theorem mem_closure_pair_left (a b : G) : a ∈ Subgroup.closure ({a, b} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem mem_closure_pair_right (a b : G) : b ∈ Subgroup.closure ({a, b} : Set G) :=
  Subgroup.subset_closure (by simp)

theorem card_closure_pair_le (hp : 0 < p) {a b : G} (hab : Commute a b) (ha : a ^ p = 1)
    (hb : b ^ p = 1) : Nat.card (Subgroup.closure ({a, b} : Set G)) ≤ p ^ 2 := by
  have hsurj : Function.Surjective (fun ij : Fin p × Fin p =>
      (⟨a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ), Subgroup.mul_mem _
        (Subgroup.pow_mem _ (mem_closure_pair_left a b) _)
        (Subgroup.pow_mem _ (mem_closure_pair_right a b) _)⟩ :
        Subgroup.closure ({a, b} : Set G))) := by
    rintro ⟨x, hx⟩
    have hx' : x ∈ Subgroup.closure ({a, b, 1} : Set G) :=
      Subgroup.closure_mono (by intro y hy; simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hy ⊢; tauto) hx
    obtain ⟨i, j, k, rfl⟩ := closure_triple_form hp hab (Commute.one_right a)
      (Commute.one_right b) ha hb (one_pow p) hx'
    refine ⟨(⟨i % p, Nat.mod_lt _ hp⟩, ⟨j % p, Nat.mod_lt _ hp⟩), Subtype.ext ?_⟩
    simp only [one_pow, mul_one]
    rw [pow_eq_pow_mod i ha, pow_eq_pow_mod j hb]
  have h := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at h
  rw [sq]
  exact h

theorem card_le_card_pair_mul [Finite G] (hp : 0 < p) {E : Subgroup G} {a b c : G} (haE : a ∈ E)
    (hbE : b ∈ E) (hcE : c ∈ E) (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (hgen : E ≤ Subgroup.closure ({a, b, c} : Set G)) :
    Nat.card E ≤ Nat.card (Subgroup.closure ({a, b} : Set G)) * p := by
  have hle := closure_pair_le haE hbE
  have hsurj : Function.Surjective (fun hk : Subgroup.closure ({a, b} : Set G) × Fin p =>
      (⟨(hk.1 : G) * c ^ (hk.2 : ℕ), E.mul_mem (hle hk.1.2) (E.pow_mem hcE _)⟩ : E)) := by
    rintro ⟨e, he⟩
    obtain ⟨i, j, k, rfl⟩ := closure_triple_form hp hab hac hbc ha hb hc (hgen he)
    refine ⟨(⟨a ^ i * b ^ j, Subgroup.mul_mem _ (Subgroup.pow_mem _ (mem_closure_pair_left a b) _)
      (Subgroup.pow_mem _ (mem_closure_pair_right a b) _)⟩, ⟨k % p, Nat.mod_lt _ hp⟩),
      Subtype.ext ?_⟩
    simp only
    rw [pow_eq_pow_mod k hc]
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin p), Fintype.card_fin] at h

theorem card_closure_pair_eq [Finite G] (hp : 0 < p) {E : Subgroup G} {a b c : G} (haE : a ∈ E)
    (hbE : b ∈ E) (hcE : c ∈ E) (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (hgen : E ≤ Subgroup.closure ({a, b, c} : Set G)) (hcard : Nat.card E = p ^ 3) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = p ^ 2 := by
  have h1 := card_closure_pair_le hp hab ha hb
  have h2 := card_le_card_pair_mul hp haE hbE hcE hab hac hbc ha hb hc hgen
  rw [hcard] at h2
  have h3 : p ^ 2 * p ≤ Nat.card (Subgroup.closure ({a, b} : Set G)) * p := by
    rw [← pow_succ]; exact h2
  have h4 := Nat.le_of_mul_le_mul_right h3 hp
  omega

theorem relIndex_closure_pair [Finite G] (hp : 0 < p) {E : Subgroup G} {a b c : G} (haE : a ∈ E)
    (hbE : b ∈ E) (hcE : c ∈ E) (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (hgen : E ≤ Subgroup.closure ({a, b, c} : Set G)) (hcard : Nat.card E = p ^ 3) :
    (Subgroup.closure ({a, b} : Set G)).relIndex E = p := by
  have hle := closure_pair_le haE hbE
  have h := Subgroup.relIndex_mul_card (Subgroup.closure ({a, b} : Set G)) E
  rw [inf_eq_left.2 hle, card_closure_pair_eq hp haE hbE hcE hab hac hbc ha hb hc hgen hcard,
    hcard] at h
  have h' : p ^ 2 * (Subgroup.closure ({a, b} : Set G)).relIndex E = p ^ 2 * p := by
    rw [← pow_succ, mul_comm]; exact h
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hp 2) h'

theorem relIndex_three_pairs [Finite G] (hp : 0 < p) {E : Subgroup G} {a b c : G} (haE : a ∈ E)
    (hbE : b ∈ E) (hcE : c ∈ E) (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1)
    (hgen : E ≤ Subgroup.closure ({a, b, c} : Set G)) (hcard : Nat.card E = p ^ 3) :
    (Subgroup.closure ({a, b} : Set G)).relIndex E = p ∧
      (Subgroup.closure ({a, c} : Set G)).relIndex E = p ∧
      (Subgroup.closure ({b, c} : Set G)).relIndex E = p := by
  refine ⟨relIndex_closure_pair hp haE hbE hcE hab hac hbc ha hb hc hgen hcard, ?_, ?_⟩
  · refine relIndex_closure_pair hp haE hcE hbE hac hab hbc.symm ha hc hb ?_ hcard
    rwa [Set.pair_comm c b]
  · refine relIndex_closure_pair hp hbE hcE haE hbc hab.symm hac.symm hb hc ha ?_ hcard
    have : ({b, c, a} : Set G) = {a, b, c} := by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
    rwa [this]

theorem commute_of_mem_closure_pair {a b k : G} (ha : a * k = k * a) (hb : b * k = k * b) {f : G}
    (hf : f ∈ Subgroup.closure ({a, b} : Set G)) : f * k = k * f := by
  have hle : Subgroup.closure ({a, b} : Set G) ≤ Subgroup.centralizer ({k} : Set G) := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      intro h hh <;> rw [Set.mem_singleton_iff] at hh <;> subst hh
    exacts [ha.symm, hb.symm]
  have := Subgroup.mem_centralizer_iff.1 (hle hf) k (Set.mem_singleton k)
  exact this.symm

theorem mul_card_le_of_lt [Finite G] (hp : p.Prime) {E : Subgroup G} (hcard : Nat.card E = p ^ 3)
    {K H : Subgroup G} (hKH : K < H) (hHE : H ≤ E) : p * Nat.card K ≤ Nat.card H := by
  have hH : Nat.card H ∣ p ^ 3 := hcard ▸ Subgroup.card_dvd_of_le hHE
  have hK : Nat.card K ∣ p ^ 3 := hcard ▸ Subgroup.card_dvd_of_le (hKH.le.trans hHE)
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow hp).1 hH
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow hp).1 hK
  have hlt : Nat.card K < Nat.card H := by
    by_contra h
    push Not at h
    exact hKH.ne (Subgroup.eq_of_le_of_card_ge hKH.le h)
  rw [ha, hb] at hlt ⊢
  have hab : a < b := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
  calc p * p ^ a = p ^ (a + 1) := (pow_succ' p a).symm
    _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos hab

theorem le_closure_triple_of_independent [Finite G] (hp : p.Prime) {E : Subgroup G}
    (hcard : Nat.card E = p ^ 3) {a b c : G} (haE : a ∈ E) (hbE : b ∈ E) (hcE : c ∈ E)
    (ha : a ^ p = 1) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a)
    (hcab : c ∉ Subgroup.closure ({a, b} : Set G)) :
    E ≤ Subgroup.closure ({a, b, c} : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have hK₁ : Nat.card (Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, hord]
  have hKH : Subgroup.zpowers a < Subgroup.closure ({a, b} : Set G) := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.2 (mem_closure_pair_left a b)) ?_
    intro h
    exact hba (h ▸ mem_closure_pair_right a b)
  have hH₂E := closure_pair_le haE hbE
  have hH₃E : Subgroup.closure ({a, b, c} : Set G) ≤ E := by
    rw [Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    exacts [haE, hbE, hcE]
  have hH₂H₃ : Subgroup.closure ({a, b} : Set G) < Subgroup.closure ({a, b, c} : Set G) := by
    refine lt_of_le_of_ne (Subgroup.closure_mono (by
      intro y hy; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢; tauto)) ?_
    intro h
    exact hcab (h ▸ Subgroup.subset_closure (by simp))
  have h1 := mul_card_le_of_lt hp hcard hKH hH₂E
  have h2 := mul_card_le_of_lt hp hcard hH₂H₃ hH₃E
  rw [hK₁] at h1
  have h3 : Nat.card E ≤ Nat.card (Subgroup.closure ({a, b, c} : Set G)) := by
    rw [hcard]
    calc p ^ 3 = p * (p * p) := by ring
      _ ≤ p * Nat.card (Subgroup.closure ({a, b} : Set G)) := Nat.mul_le_mul_left p h1
      _ ≤ _ := h2
  exact (Subgroup.eq_of_le_of_card_ge hH₃E h3).ge

end CFSG.LieType.SeitzGeneration
