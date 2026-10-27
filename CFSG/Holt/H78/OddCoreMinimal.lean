module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Holt.H78.Count

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General
open scoped Pointwise

section Lemma23iii

variable {G : Type*} [Group G] {Ω : Type*} [MulAction G Ω]

theorem smul_smul_eq_inv_smul_of_mem_longInvAt {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {t : G} {α : Ω} (ht : t ∈ longInvAt G Ω α)
    (htP : t ∈ Subgroup.normalizer (P : Set G)) {p : G} (hp : p ∈ P) :
    t • p • α = p⁻¹ • α := by
  have hp' : t * p * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp htP p).mp hp
  have h := hP _ hp' _ hp
  rw [inv_eq_self_of_mem_longInv ht.1] at hp' h
  have hX : t * (t * p * t * p) = t * p * t * p * t :=
    calc t * (t * p * t * p) = t * (p * (t * p * t)) := by rw [h]
      _ = t * p * t * p * t := by simp only [mul_assoc]
  have hfix : t • (t * p * t * p) • α = (t * p * t * p) • α := by
    rw [smul_smul, hX, mul_smul, ht.2]
  have hqα := (smul_eq_iff_of_mem_longInvAt ht _).mp hfix
  calc t • p • α = (t * p * t) • α := by rw [mul_smul, mul_smul, ht.2]
    _ = p⁻¹ • (t * p * t * p) • α := by rw [smul_smul, h, inv_mul_cancel_left]
    _ = p⁻¹ • α := by rw [hqα]

theorem smul_eq_self_of_mem_orbit {P : Subgroup G} (hP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p)
    {q : G} (hq : q ∈ P) {η ω γ : Ω} (hη : η ∈ orbit P γ) (hω : ω ∈ orbit P γ)
    (h : q • η = η) : q • ω = ω := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := hη
  obtain ⟨⟨y, hy⟩, rfl⟩ := hω
  have h' : q • x • γ = x • γ := h
  have hqγ : q • γ = γ := by
    refine smul_left_cancel x ?_
    rw [smul_smul, ← hP q hq x hx, mul_smul]
    exact h'
  show q • y • γ = y • γ
  rw [smul_smul, hP q hq y hy, mul_smul, hqγ]

theorem smul_eq_mul_smul_of_mem_longInvAt {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {s s' c : G} {γ : Ω} (hs : s ∈ longInvAt G Ω γ)
    (hs' : s' ∈ longInvAt G Ω (c • γ)) (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hs'P : s' ∈ Subgroup.normalizer (P : Set G)) (hc : c ∈ P) {ω : Ω}
    (hω : ω ∈ orbit P γ) : s' • ω = (c * c) • s • ω := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := hω
  show s' • x • γ = (c * c) • s • x • γ
  have e : x • γ = (x * c⁻¹) • c • γ := by rw [smul_smul, inv_mul_cancel_right]
  rw [smul_smul_eq_inv_smul_of_mem_longInvAt hP hs hsP hx, e,
    smul_smul_eq_inv_smul_of_mem_longInvAt hP hs' hs'P (mul_mem hx (inv_mem hc)), smul_smul,
    smul_smul, mul_inv_rev, inv_inv, mul_assoc, hP _ (inv_mem hx) _ hc, ← mul_assoc]

theorem smul_eq_smul_of_mem_orbit_of_smul_eq {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {s s' : G} {γ γ' : Ω} (hs : s ∈ longInvAt G Ω γ)
    (hs' : s' ∈ longInvAt G Ω γ') (hsP : s ∈ Subgroup.normalizer (P : Set G))
    (hs'P : s' ∈ Subgroup.normalizer (P : Set G)) (hγ' : γ' ∈ orbit P γ) {δ : Ω}
    (hδ : δ ∈ orbit P γ) (h : s • δ = s' • δ) {ω : Ω} (hω : ω ∈ orbit P γ) :
    s • ω = s' • ω := by
  obtain ⟨⟨c, hc⟩, rfl⟩ := hγ'
  have hs'' : s' ∈ longInvAt G Ω (c • γ) := hs'
  have hmaps : ∀ {η : Ω}, η ∈ orbit P γ → s • η ∈ orbit P γ := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    exact ⟨⟨x⁻¹, inv_mem hx⟩, (smul_smul_eq_inv_smul_of_mem_longInvAt hP hs hsP hx).symm⟩
  have hcc : (c * c) • s • δ = s • δ := by
    rw [← smul_eq_mul_smul_of_mem_longInvAt hP hs hs'' hsP hs'P hc hδ, ← h]
  rw [smul_eq_mul_smul_of_mem_longInvAt hP hs hs'' hsP hs'P hc hω,
    smul_eq_self_of_mem_orbit hP (mul_mem hc hc) (hmaps hδ) (hmaps hω) hcc]

theorem smul_mem_orbit_of_mem_normalizer {P : Subgroup G} {s : G}
    (hsP : s ∈ Subgroup.normalizer (P : Set G)) {α : Ω} (hsα : s • α ∈ orbit P α) {ω : Ω}
    (hω : ω ∈ orbit P α) : s • ω ∈ orbit P α := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := hω
  obtain ⟨⟨b, hb⟩, hbα⟩ := hsα
  have hbα' : b • α = s • α := hbα
  refine ⟨⟨s * x * s⁻¹ * b, mul_mem ((Subgroup.mem_normalizer_iff.mp hsP x).mp hx) hb⟩, ?_⟩
  show (s * x * s⁻¹ * b) • α = s • x • α
  rw [mul_smul, hbα', mul_smul, mul_smul, inv_smul_smul]

theorem mem_stabilizer_pair_of_mem_longInvSwap {t : G} {α β : Ω}
    (ht : t ∈ longInvSwap G Ω α β) : t ∈ stabilizer G ({α, β} : Set Ω) := by
  rw [mem_stabilizer_iff, Set.smul_set_insert, Set.smul_set_singleton, ht.2,
    smul_eq_of_mem_longInvSwap ht, Set.pair_comm]

variable [Finite G]

theorem mem_orbit_of_mem_longInvAt {P : Subgroup G} {t s : G} {α γ : Ω}
    (ht : t ∈ longInvAt G Ω α) (hs : s ∈ longInvAt G Ω γ)
    (htΛ : ∀ ω ∈ orbit P α, t • ω ∈ orbit P α) (hsΛ : ∀ ω ∈ orbit P α, s • ω ∈ orbit P α) :
    γ ∈ orbit P α := by
  have key : ∀ n : ℕ, (t * s) ^ n • α ∈ orbit P α := by
    intro n
    induction n with
    | zero => rw [pow_zero, one_smul]; exact mem_orbit_self α
    | succ n ih => rw [pow_succ', mul_smul, mul_smul]; exact htΛ _ (hsΛ _ ih)
  rw [← pow_period_div_two_mul_smul_eq ht hs]
  exact key _

theorem mem_orbit_of_mem_longInvSwap {P : Subgroup G} (hPn : P.Normal) {t s : G} {α β γ : Ω}
    (ht : t ∈ longInvAt G Ω α) (hβ : β ∈ orbit P α) (hs : s ∈ longInvSwap G Ω α β)
    (hsγ : s • γ = γ) : γ ∈ orbit P α := by
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) := fun g =>
    (Subgroup.normalizer_eq_top P).symm ▸ Subgroup.mem_top g
  refine mem_orbit_of_mem_longInvAt ht ⟨hs.1, hsγ⟩
    (fun ω hω => smul_mem_orbit_of_mem_normalizer (hN t) ?_ hω)
    (fun ω hω => smul_mem_orbit_of_mem_normalizer (hN s) ?_ hω)
  · rw [ht.2]
    exact mem_orbit_self α
  · rw [hs.2]
    exact hβ

theorem smul_eq_smul_of_mem_longInvSwap_of_mem_orbit {P : Subgroup G} (hPn : P.Normal)
    (hP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {α β : Ω} (hα : (longInvAt G Ω α).Nonempty)
    (hβ : β ∈ orbit P α) {s s' : G} (hs : s ∈ longInvSwap G Ω α β)
    (hs' : s' ∈ longInvSwap G Ω α β) {ω : Ω} (hω : ω ∈ orbit P α) : s • ω = s' • ω := by
  have hN : ∀ g : G, g ∈ Subgroup.normalizer (P : Set G) := fun g =>
    (Subgroup.normalizer_eq_top P).symm ▸ Subgroup.mem_top g
  obtain ⟨t, ht⟩ := hα
  obtain ⟨γ, hγ⟩ := exists_mem_longInvAt hs.1
  obtain ⟨γ', hγ'⟩ := exists_mem_longInvAt hs'.1
  have horb : orbit P γ = orbit P α :=
    orbit_eq_iff.mpr (mem_orbit_of_mem_longInvSwap hPn ht hβ hs hγ.2)
  have hγ'Λ : γ' ∈ orbit P γ := by
    rw [horb]
    exact mem_orbit_of_mem_longInvSwap hPn ht hβ hs' hγ'.2
  have hαΛ : α ∈ orbit P γ := by
    rw [horb]
    exact mem_orbit_self α
  exact smul_eq_smul_of_mem_orbit_of_smul_eq hP hγ hγ' (hN s) (hN s') hγ'Λ hαΛ
    (hs.2.trans hs'.2.symm) (horb ▸ hω)

theorem holtDelta_eq_singleton_of_mem_orbit {P : Subgroup G} (hPn : P.Normal)
    (hP : ∀ p ∈ P, ∀ q ∈ P, p * q = q * p) {α β : Ω} (hα : (longInvAt G Ω α).Nonempty)
    (hβ : β ∈ orbit P α) :
    ∃ γ ∈ orbit P α, holtDelta G Ω α β = {γ} ∧
      fixSet Ω (stabilizer G ({α, β} : Set Ω)) = {γ} := by
  obtain ⟨t, ht⟩ := hα
  obtain ⟨⟨b, hb⟩, hbα⟩ := hβ
  have hbα' : b • α = β := hbα
  have hu : b * t * b⁻¹ ∈ longInvAt G Ω β := hbα' ▸ conj_mem_longInvAt ht b
  obtain ⟨x, -, hs⟩ := exists_conj_mem_longInvSwap ht hu
  obtain ⟨γ, hγ⟩ := exists_mem_longInvAt hs.1
  have hβΛ : β ∈ orbit P α := ⟨⟨b, hb⟩, hbα⟩
  have hγΛ : γ ∈ orbit P α := mem_orbit_of_mem_longInvSwap hPn ht hβΛ hs hγ.2
  have hΔ : holtDelta G Ω α β = {γ} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨_, hs, hγ.2⟩, fun δ ⟨s', hs', hs'δ⟩ => ?_⟩
    have h := smul_eq_smul_of_mem_longInvSwap_of_mem_orbit hPn hP ⟨t, ht⟩ hβΛ hs' hs hγΛ
    rw [hγ.2] at h
    exact ((smul_eq_iff_of_mem_longInvAt ⟨hs'.1, hs'δ⟩ γ).mp h).symm
  refine ⟨γ, hγΛ, hΔ, Set.eq_singleton_iff_unique_mem.mpr ⟨fun g hg => ?_, fun ω hω => ?_⟩⟩
  · have h := mem_stabilizer_iff.mp (stabilizer_pair_le α β hg)
    rw [hΔ, Set.smul_set_singleton, Set.singleton_eq_singleton_iff] at h
    exact h
  · exact (smul_eq_iff_of_mem_longInvAt hγ ω).mp (hω _ (mem_stabilizer_pair_of_mem_longInvSwap hs))

end Lemma23iii

section Minimal

variable {G : Type*} [Group G] [Finite G] {Ω : Type*} [MulAction G Ω]

theorem commute_of_minimal_normal_of_odd {P : Subgroup G} (hPn : P.Normal)
    (hPmin : ∀ Q ≤ P, Q.Normal → Q = ⊥ ∨ Q = P) (hodd : Odd (Nat.card P)) :
    ∀ p ∈ P, ∀ q ∈ P, p * q = q * p := by
  have := hPn
  have hsolv : Group.IsSolvable P := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hbot : ⁅P, P⁆ = ⊥ := by
    rcases hPmin ⁅P, P⁆ (Subgroup.commutator_le_left P P) (Subgroup.commutator_normal P P)
      with h | h
    · exact h
    have htop : commutator P = ⊤ := Subgroup.map_injective P.subtype_injective (by
      rw [Subgroup.map_subtype_commutator, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype])
    rcases subsingleton_or_nontrivial P with hs | hn
    · rw [h]
      exact Subgroup.eq_bot_of_subsingleton P
    · exact absurd htop (Group.IsSolvable.commutator_lt_top_of_nontrivial P).ne
  intro p hp q hq
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot hp) q hq).symm

end Minimal

end CFSG.Holt.H78
