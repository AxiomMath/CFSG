
module

public import CFSG.Certificates.Kernel.SporSch.ThirdChainHBase
public import CFSG.Sporadic.Co2Schreier.ThirdOrderBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert

def TestX (j : ℕ) (g : Equiv.Perm (Fin 2300)) : Prop :=
  ∀ i, j ≤ i → i < 12 → locU (g (bpt i)) = g (bpt i)

open scoped Classical in
@[irreducible] def cosetX (j : ℕ) (p : Equiv.Perm (Fin 2300)) :
    Finset (Equiv.Perm (Fin 2300)) :=
  Finset.univ.filter fun g => p⁻¹ * g ∈ stabB j ∧ TestX j g

theorem mem_cosetX {j : ℕ} {p g : Equiv.Perm (Fin 2300)} :
    g ∈ cosetX j p ↔ p⁻¹ * g ∈ stabB j ∧ TestX j g := by
  classical
  unfold cosetX
  simp

theorem card_coset_sub (H : Subgroup (Equiv.Perm (Fin 2300))) (p : Equiv.Perm (Fin 2300)) :
    Nat.card {g // p⁻¹ * g ∈ H} = Nat.card H :=
  Nat.card_congr
    { toFun := fun g => ⟨p⁻¹ * g.1, g.2⟩
      invFun := fun s => ⟨p * s.1, by rw [inv_mul_cancel_left]; exact s.2⟩
      left_inv := fun g => Subtype.ext (mul_inv_cancel_left p g.1)
      right_inv := fun s => Subtype.ext (inv_mul_cancel_left p s.1) }

theorem eq_mul_inv_mul {G : Type*} [Group G] (a g : G) : g = a * (a⁻¹ * g) := by group

theorem inv_mul_eq_mul {G : Type*} [Group G] (p t g : G) : p⁻¹ * g = t * ((p * t)⁻¹ * g) := by
  group

theorem conj_conj {G : Type*} [Group G] (g u : G) : g * (g⁻¹ * u * g) * g⁻¹ = u := by group

theorem mul_conj {G : Type*} [Group G] (g u : G) : u * g = g * (g⁻¹ * u * g) := by group

theorem conj_fix {α : Type*} (g u : Equiv.Perm α) (x : α) (h : u (g x) = g x) :
    (g⁻¹ * u * g) x = x := by
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h]
  simp

theorem fix_of_comm' {α : Type*} (u g : Equiv.Perm α) (x : α) (hc : u * g = g * u)
    (hx : u x = x) : u (g x) = g x := by
  have := congrArg (fun y : Equiv.Perm α => y x) hc
  simp only [Equiv.Perm.mul_apply, hx] at this
  exact this

section Count

private theorem prod_Ico_succ_self (f : ℕ → ℕ) (n : ℕ) : ∏ i ∈ Finset.Ico n (n + 1), f i = f n := by
  rw [Nat.Ico_succ_singleton, Finset.prod_singleton]

variable (h : ThirdFactsH)
include h

theorem rep_apply_mul {pA : Array ℕ} {p : Equiv.Perm (Fin 2300)} (hp : Rep 2300 pA p) {j k : ℕ}
    (hj : j < 13) (hk : k < tsz j) :
    pA[(thL[j]!.tr[k]!)[thB[j]!]!]! = ((p * thT j k) (bpt j) : ℕ) := by
  rw [Equiv.Perm.mul_apply, ← rep_apply hp, ← rep_apply_bptH h (rep_thTH h hj hk) hj]

omit h in
theorem apply_of_mem {j k : ℕ} (hj : j < 13) {p g : Equiv.Perm (Fin 2300)}
    (hg : (p * thT j k)⁻¹ * g ∈ stabB (j + 1)) : g (bpt j) = (p * thT j k) (bpt j) := by
  have he : g = p * thT j k * ((p * thT j k)⁻¹ * g) := eq_mul_inv_mul _ g
  have hb : ((p * thT j k)⁻¹ * g) (bpt j) = bpt j := hg.2 j (by omega)
  conv_lhs => rw [he]
  rw [Equiv.Perm.mul_apply, hb]

omit h in
theorem testX_succ {j : ℕ} {g : Equiv.Perm (Fin 2300)} (ht : TestX j g) : TestX (j + 1) g :=
  fun i hi hi' => ht i (by omega) hi'

omit h in
theorem testX_of_succ {j : ℕ} {g : Equiv.Perm (Fin 2300)} (ht : TestX (j + 1) g)
    (hj : j < 12 → locU (g (bpt j)) = g (bpt j)) : TestX j g := by
  intro i hi hi'
  rcases eq_or_lt_of_le hi with rfl | hlt
  · exact hj hi'
  · exact ht i hlt hi'

theorem cover_cosetX {j : ℕ} (hj : j < 13) (p : Equiv.Perm (Fin 2300)) :
    cosetX j p = (Finset.range (tsz j)).biUnion fun k =>
      if j < 12 ∧ locU ((p * thT j k) (bpt j)) ≠ (p * thT j k) (bpt j) then ∅
      else cosetX (j + 1) (p * thT j k) := by
  ext g
  rw [Finset.mem_biUnion]
  constructor
  · intro hg
    rw [mem_cosetX] at hg
    obtain ⟨k, hk, hs⟩ := exists_thT_inv_mul_memH h hj hg.1
    have hs' : (p * thT j k)⁻¹ * g ∈ stabB (j + 1) := by rwa [mul_inv_rev, mul_assoc]
    refine ⟨k, Finset.mem_range.2 hk, ?_⟩
    rw [if_neg]
    · exact mem_cosetX.2 ⟨hs', testX_succ hg.2⟩
    · rintro ⟨hj12, hne⟩
      apply hne
      rw [← apply_of_mem hj hs']
      exact hg.2 j le_rfl hj12
  · rintro ⟨k, hk, hg⟩
    split_ifs at hg with htest
    · simp at hg
    · rw [mem_cosetX] at hg ⊢
      have hk' := Finset.mem_range.1 hk
      refine ⟨?_, testX_of_succ hg.2 fun hj12 => ?_⟩
      · have e : p⁻¹ * g = thT j k * ((p * thT j k)⁻¹ * g) := inv_mul_eq_mul p _ g
        rw [e]
        exact (stabB j).mul_mem (thT_mem_stabBH h hj hk') (stabB_succ_le j hg.1)
      · rw [apply_of_mem hj hg.1]
        by_contra hne
        exact htest ⟨hj12, hne⟩

theorem disj_cosetX {j : ℕ} (hj : j < 13) (p : Equiv.Perm (Fin 2300)) :
    (↑(Finset.range (tsz j)) : Set ℕ).PairwiseDisjoint fun k =>
      if j < 12 ∧ locU ((p * thT j k) (bpt j)) ≠ (p * thT j k) (bpt j) then ∅
      else cosetX (j + 1) (p * thT j k) := by
  intro k hk k' hk' hne
  refine Finset.disjoint_left.2 fun g hg hg' => hne ?_
  dsimp only at hg hg'
  split_ifs at hg hg' <;> try simp at hg hg'
  rw [mem_cosetX] at hg hg'
  have e1 := apply_of_mem hj hg.1
  have e2 := apply_of_mem hj hg'.1
  rw [e1] at e2
  simp only [Equiv.Perm.mul_apply, EmbeddingLike.apply_eq_iff_eq] at e2
  exact thT_injH h hj (Finset.mem_coe.1 hk |> Finset.mem_range.1)
    (Finset.mem_coe.1 hk' |> Finset.mem_range.1) e2

theorem card_cosetX_twelve (p : Equiv.Perm (Fin 2300)) : (cosetX 12 p).card = tsz 12 := by
  calc (cosetX 12 p).card = Nat.card {g // g ∈ cosetX 12 p} := (Nat.card_eq_finsetCard _).symm
    _ = Nat.card {g // p⁻¹ * g ∈ stabB 12} := Nat.card_congr (Equiv.subtypeEquivRight fun g => by
        rw [mem_cosetX]
        exact ⟨fun hg => hg.1, fun hg => ⟨hg, fun i hi hi' => absurd hi' (by omega)⟩⟩)
    _ = tsz 12 := by
        rw [card_coset_sub, card_stabBH h (by norm_num : 12 ≤ 13), prod_Ico_succ_self]

theorem card_cosetX_thirteen (p : Equiv.Perm (Fin 2300)) : (cosetX 13 p).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨p, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, fun g hg => ?_⟩⟩
  · rw [mem_cosetX, inv_mul_cancel]
    exact ⟨(stabB 13).one_mem, fun i hi hi' => absurd hi' (by omega)⟩
  · rw [mem_cosetX, stabB_thirteenH h, Subgroup.mem_bot] at hg
    rw [← mul_right_inj p⁻¹, hg.1, inv_mul_cancel]

omit h in
theorem conj_mem_twelve {g : Equiv.Perm (Fin 2300)} (hg : g ∈ co2P) (ht : TestX 0 g) :
    g⁻¹ * locU * g ∈ stabB 12 := by
  refine ⟨co2P.mul_mem (co2P.mul_mem (co2P.inv_mem hg) locU_mem) hg, fun i hi => ?_⟩
  exact conj_fix g locU (bpt i) (ht i (Nat.zero_le i) hi)

omit h in
theorem comm_of_conj {g : Equiv.Perm (Fin 2300)} (e : g⁻¹ * locU * g = locU) :
    locU * g = g * locU := by
  rw [mul_conj g locU, e]

omit h in
theorem one_of_conj {g : Equiv.Perm (Fin 2300)} (e : g⁻¹ * locU * g = 1) : locU = 1 := by
  rw [← conj_conj g locU, e, mul_one, mul_inv_cancel]

end Count

end CFSG.Sporadic.Co2Schreier
