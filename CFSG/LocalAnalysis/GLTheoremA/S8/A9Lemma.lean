module

public import CFSG.LocalAnalysis.GLTheoremA.S8.A9Check
public import Mathlib.GroupTheory.SpecificGroups.Alternating

namespace CFSG.LocalAnalysis.GLTheoremA.S8.A9

open Equiv Equiv.Perm

def f0 : Perm (Fin 9) := swap 0 4 * swap 0 3 * swap 0 2 * swap 0 1

theorem f0_ne_iff : ∀ x : Fin 9, f0 x ≠ x ↔ x.val < 5 := by decide

theorem f0_lt : ∀ x : Fin 9, x.val < 5 → (f0 x).val < 5 := by decide

theorem f0_zero : f0 0 = 1 := by decide

theorem f0_pow_zero : ∀ j : Fin 9, j.val < 5 → (f0 ^ j.val) 0 = j := by decide

theorem f0_pow_inv : ∀ j : Fin 9, j.val < 5 → (f0 ^ (5 - j.val))⁻¹ 0 = j := by decide

theorem inv_mod5 : ∀ y : Fin 9, y.val < 5 → y ≠ 0 → y.val * (y.val ^ 3 % 5) % 5 = 1 := by
  decide

theorem orderOf_f0 : orderOf f0 = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact orderOf_eq_prime (by unfold f0; decide) (by unfold f0; decide)

theorem f0_pow_pow {y : Fin 9} (hy : y.val < 5) (hy0 : y ≠ 0) :
    ((f0 ^ y.val) ^ (y.val ^ 3 % 5)) 0 = 1 := by
  rw [← pow_mul, ← pow_mod_orderOf, orderOf_f0, inv_mod5 y hy hy0, pow_one, f0_zero]

theorem card_lt5 : (Finset.univ.filter fun j : Fin 9 => j.val < 5).card = 5 := by decide

theorem pow2_cases {n k : ℕ} (h : n = 2 ^ k) (h9 : n ≤ 9) : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
  subst h
  have hk : k < 4 := by
    by_contra hc
    have : 16 ≤ 2 ^ k := by
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp

open Classical in
noncomputable def orb (S : Subgroup (Perm (Fin 9))) (x : Fin 9) : Finset (Fin 9) :=
  Finset.univ.filter fun y => ∃ s ∈ S, s x = y

variable {S : Subgroup (Perm (Fin 9))}

theorem mem_orb {x y : Fin 9} : y ∈ orb S x ↔ ∃ s ∈ S, s x = y := by
  simp [orb]

theorem orb_self (x : Fin 9) : x ∈ orb S x := mem_orb.2 ⟨1, S.one_mem, rfl⟩

theorem orb_trans {x y z : Fin 9} (h1 : y ∈ orb S x) (h2 : z ∈ orb S y) : z ∈ orb S x := by
  obtain ⟨s, hs, rfl⟩ := mem_orb.1 h1
  obtain ⟨t, ht, rfl⟩ := mem_orb.1 h2
  exact mem_orb.2 ⟨t * s, S.mul_mem ht hs, rfl⟩

theorem orb_symm {x y : Fin 9} (h : y ∈ orb S x) : x ∈ orb S y := by
  obtain ⟨s, hs, rfl⟩ := mem_orb.1 h
  exact mem_orb.2 ⟨s⁻¹, S.inv_mem hs, by simp⟩

theorem orb_eq {x y : Fin 9} (h : y ∈ orb S x) : orb S y = orb S x := by
  ext z
  exact ⟨fun hz => orb_trans h hz, fun hz => orb_trans (orb_symm h) hz⟩

theorem orb_card_le (x : Fin 9) : (orb S x).card ≤ 9 := by
  simpa using Finset.card_le_univ (orb S x)

theorem orb_card_pow (hS : IsPGroup 2 S) (x : Fin 9) : ∃ k, (orb S x).card = 2 ^ k := by
  obtain ⟨k, hk⟩ := hS.card_orbit x
  refine ⟨k, ?_⟩
  have he : MulAction.orbit S x = ((orb S x : Finset (Fin 9)) : Set (Fin 9)) := by
    ext y
    simp [MulAction.mem_orbit_iff, mem_orb, Subgroup.smul_def, Perm.smul_def]
  rw [← hk, he, Nat.card_coe_set_eq, Set.ncard_coe_finset]

theorem orb_cases (hS : IsPGroup 2 S) (x : Fin 9) :
    (orb S x).card = 1 ∨ (orb S x).card = 2 ∨ (orb S x).card = 4 ∨ (orb S x).card = 8 := by
  obtain ⟨k, hk⟩ := orb_card_pow hS x
  exact pow2_cases hk (orb_card_le x)

section Normal

variable (hN : ∀ s ∈ S, f0 * s * f0⁻¹ ∈ S)
include hN

theorem conj_pow_mem (n : ℕ) : ∀ s ∈ S, f0 ^ n * s * (f0 ^ n)⁻¹ ∈ S := by
  induction n with
  | zero => intro s hs; simpa using hs
  | succ n ih =>
    intro s hs
    have e : f0 ^ (n + 1) * s * (f0 ^ (n + 1))⁻¹ = f0 * (f0 ^ n * s * (f0 ^ n)⁻¹) * f0⁻¹ := by
      rw [pow_succ', mul_inv_rev]
      simp only [mul_assoc]
    rw [e]
    exact hN _ (ih s hs)

theorem orb_f0 {x z : Fin 9} (h : z ∈ orb S x) : f0 z ∈ orb S (f0 x) := by
  obtain ⟨s, hs, rfl⟩ := mem_orb.1 h
  exact mem_orb.2 ⟨f0 * s * f0⁻¹, hN s hs, by simp [Perm.mul_apply]⟩

theorem orb_f0_pow (n : ℕ) {x z : Fin 9} (h : z ∈ orb S x) :
    (f0 ^ n) z ∈ orb S ((f0 ^ n) x) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ', Perm.mul_apply, Perm.mul_apply]
    exact orb_f0 hN ih

theorem one_mem_of {y : Fin 9} (hy : y ∈ orb S 0) (hy0 : y ≠ 0) : (1 : Fin 9) ∈ orb S 0 := by
  by_cases hf : f0 y = y
  · have h1 := orb_f0 hN hy
    rw [hf, f0_zero] at h1
    exact orb_trans hy (orb_symm h1)
  · have hlt : y.val < 5 := (f0_ne_iff y).1 hf
    have hcl : ∀ z ∈ orb S 0, (f0 ^ y.val) z ∈ orb S 0 := by
      intro z hz
      have h := orb_f0_pow hN y.val hz
      rw [f0_pow_zero y hlt] at h
      exact orb_trans hy h
    have hall : ∀ m : ℕ, ((f0 ^ y.val) ^ m) 0 ∈ orb S 0 := by
      intro m
      induction m with
      | zero => exact orb_self 0
      | succ m ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hcl _ ih
    rw [← f0_pow_pow hlt hy0]
    exact hall _

theorem dich (hS : IsPGroup 2 S) :
    (∀ s ∈ S, s 0 = 0) ∨ ((∀ j : Fin 9, j.val < 5 → j ∈ orb S 0) ∧ (orb S 0).card = 8) := by
  by_cases h1 : (1 : Fin 9) ∈ orb S 0
  · right
    have hcl : ∀ z ∈ orb S 0, f0 z ∈ orb S 0 := by
      intro z hz
      have h := orb_f0 hN hz
      rwa [f0_zero, orb_eq h1] at h
    have hall : ∀ n : ℕ, (f0 ^ n) 0 ∈ orb S 0 := by
      intro n
      induction n with
      | zero => exact orb_self 0
      | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hcl _ ih
    have hj : ∀ j : Fin 9, j.val < 5 → j ∈ orb S 0 := by
      intro j hj
      rw [← f0_pow_zero j hj]
      exact hall _
    refine ⟨hj, ?_⟩
    have h5 : 5 ≤ (orb S 0).card := by
      have hsub : (Finset.univ.filter fun j : Fin 9 => j.val < 5) ⊆ orb S 0 := by
        intro j hj'
        exact hj j (by simpa using hj')
      have := Finset.card_le_card hsub
      rw [card_lt5] at this
      exact this
    rcases orb_cases hS 0 with h | h | h | h <;> omega
  · left
    intro s hs
    by_contra h0
    exact h1 (one_mem_of hN (mem_orb.2 ⟨s, hs, rfl⟩) h0)

theorem fix_lt_of_fix0 (h0 : ∀ s ∈ S, s 0 = 0) : ∀ s ∈ S, ∀ j : Fin 9, j.val < 5 → s j = j := by
  intro s hs j hj
  have hv := h0 _ (conj_pow_mem hN (5 - j.val) s hs)
  rw [Perm.mul_apply, Perm.mul_apply, f0_pow_inv j hj] at hv
  have := (Perm.inv_eq_iff_eq.2 hv.symm)
  rw [f0_pow_inv j hj] at this
  exact this.symm

end Normal

section CaseB

variable (hS : IsPGroup 2 S) (hN : ∀ s ∈ S, f0 * s * f0⁻¹ ∈ S)
  (hj : ∀ j : Fin 9, j.val < 5 → j ∈ orb S 0) (h8 : (orb S 0).card = 8)

include h8 in
theorem B_out : ∀ s ∈ S, ∀ w, w ∉ orb S 0 → s w = w := by
  have hcomp : (orb S 0)ᶜ.card ≤ 1 := by
    rw [Finset.card_compl, h8]
    simp
  intro s hs w hw
  by_cases hsw : s w ∈ orb S 0
  · exact absurd (orb_trans hsw (mem_orb.2 ⟨s⁻¹, S.inv_mem hs, by simp⟩)) hw
  · exact Finset.card_le_one.1 hcomp _ (Finset.mem_compl.2 hsw) _ (Finset.mem_compl.2 hw)

include hj h8 in
theorem B_Fx3 : ((orb S 0).filter fun y => f0 y = y).card = 3 := by
  have hne : ((orb S 0).filter fun y => ¬ f0 y = y) =
      Finset.univ.filter fun j : Fin 9 => j.val < 5 := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => (f0_ne_iff y).1 h.2
    · exact fun h => ⟨hj y h, (f0_ne_iff y).2 h⟩
  have := Finset.card_filter_add_card_filter_not (s := orb S 0) (fun y => f0 y = y)
  rw [hne, card_lt5, h8] at this
  omega

include hS hN h8 in
theorem B_Sp {p : Fin 9} (hpA : p ∈ orb S 0) (hfp : f0 p = p) :
    ∀ u ∈ S, u p = p → ∀ j : Fin 9, j.val < 5 → u j = j := by
    have hp0 : p ≠ 0 := by
      rintro rfl
      rw [f0_zero] at hfp
      exact absurd hfp (by decide)
    let Sp : Subgroup (Perm (Fin 9)) := S ⊓ MulAction.stabilizer (Perm (Fin 9)) p
    have hmem : ∀ u, u ∈ Sp ↔ u ∈ S ∧ u p = p := by
      intro u
      simp [Sp, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Perm.smul_def]
    have hSp2 : IsPGroup 2 Sp := hS.to_le inf_le_left
    have hfi : f0⁻¹ p = p := Perm.inv_eq_iff_eq.2 hfp.symm
    have hNp : ∀ s ∈ Sp, f0 * s * f0⁻¹ ∈ Sp := by
      intro s hs
      obtain ⟨hs1, hs2⟩ := (hmem s).1 hs
      refine (hmem _).2 ⟨hN s hs1, ?_⟩
      simp [Perm.mul_apply, hfi, hs2, hfp]
    have hfix0 : ∀ s ∈ Sp, s 0 = 0 := by
      rcases dich hNp hSp2 with h | ⟨_, h8'⟩
      · exact h
      · exfalso
        have hsub : orb Sp 0 ⊆ (orb S 0).erase p := by
          intro y hy
          obtain ⟨s, hs, rfl⟩ := mem_orb.1 hy
          obtain ⟨hs1, hs2⟩ := (hmem s).1 hs
          refine Finset.mem_erase.2 ⟨?_, mem_orb.2 ⟨s, hs1, rfl⟩⟩
          intro he
          rw [← hs2] at he
          exact hp0 (s.injective he).symm
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hpA, h8, h8'] at this
        omega
    intro u hu hup j hjl
    exact fix_lt_of_fix0 hNp hfix0 u ((hmem u).2 ⟨hu, hup⟩) j hjl
include hS hN h8 in
theorem B_S0p {p : Fin 9} (hpA : p ∈ orb S 0) (hfp : f0 p = p) :
    ∀ u ∈ S, u 0 = 0 → u p = p := by
    intro u hu hu0
    obtain ⟨s, hs, hs0⟩ := mem_orb.1 hpA
    have hsi : s⁻¹ p = 0 := Perm.inv_eq_iff_eq.2 hs0.symm
    have step : ∀ w ∈ S, w 0 = 0 → (s * w * s⁻¹) 0 = 0 := by
      intro w hw hw0
      have hm : s * w * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs hw) (S.inv_mem hs)
      have hfp' : (s * w * s⁻¹) p = p := by simp [Perm.mul_apply, hsi, hw0, hs0]
      exact B_Sp hS hN h8 hpA hfp _ hm hfp' 0 (by decide)
    have hit : ∀ n : ℕ, (s ^ n * u * (s ^ n)⁻¹) 0 = 0 := by
      intro n
      induction n with
      | zero => simpa using hu0
      | succ n ih =>
        have e : s ^ (n + 1) * u * (s ^ (n + 1))⁻¹ = s * (s ^ n * u * (s ^ n)⁻¹) * s⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          simp only [mul_assoc]
        rw [e]
        exact step _ (S.mul_mem (S.mul_mem (S.pow_mem hs n) hu) (S.inv_mem (S.pow_mem hs n))) ih
    have hinv : s ^ (orderOf s - 1) = s⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos s), pow_orderOf_eq_one]
    have h := hit (orderOf s - 1)
    rw [hinv, inv_inv, Perm.mul_apply, Perm.mul_apply, hs0] at h
    have := Perm.inv_eq_iff_eq.1 h
    rw [hs0] at this
    exact this

include hS hN hj h8 in
theorem B_S0 : ∀ u ∈ S, u 0 = 0 → u = 1 := by
  obtain ⟨p₀, hp₀⟩ : ((orb S 0).filter fun y => f0 y = y).Nonempty :=
    Finset.card_pos.1 (by rw [B_Fx3 hj h8]; omega)
  obtain ⟨hp₀A, hfp₀⟩ := Finset.mem_filter.1 hp₀
  intro u hu hu0
  refine Equiv.Perm.ext fun x => ?_
  rw [Perm.one_apply]
  by_cases hx : x ∈ orb S 0
  · by_cases hfx : f0 x = x
    · exact B_S0p hS hN h8 hx hfx u hu hu0
    · exact B_Sp hS hN h8 hp₀A hfp₀ u hu (B_S0p hS hN h8 hp₀A hfp₀ u hu hu0) x
        ((f0_ne_iff x).1 hfx)
  · exact B_out h8 u hu x hx

include hS hN hj h8 in
theorem not_caseB : False := by
  obtain ⟨p₀, hp₀⟩ : ((orb S 0).filter fun y => f0 y = y).Nonempty :=
    Finset.card_pos.1 (by rw [B_Fx3 hj h8]; omega)
  obtain ⟨hp₀A, hfp₀⟩ := Finset.mem_filter.1 hp₀
  have hreg : ∀ s ∈ S, ∀ t ∈ S, s p₀ = t p₀ → s = t := by
    intro s hs t ht hst
    have hm : t⁻¹ * s ∈ S := S.mul_mem (S.inv_mem ht) hs
    have hfix : (t⁻¹ * s) p₀ = p₀ := by
      rw [Perm.mul_apply, hst]
      simp
    have h1 := B_S0 hS hN hj h8 _ hm (B_Sp hS hN h8 hp₀A hfp₀ _ hm hfix 0 (by decide))
    exact (inv_mul_eq_one.1 h1).symm
  have hAp : orb S p₀ = orb S 0 := orb_eq hp₀A
  let C : Subgroup (Perm (Fin 9)) := S ⊓ Subgroup.centralizer ({f0} : Set (Perm (Fin 9)))
  have hCmem : ∀ c, c ∈ C ↔ c ∈ S ∧ f0 * c = c * f0 := by
    intro c
    simp only [C, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq]
  have hC2 : IsPGroup 2 C := hS.to_le inf_le_left
  have hCorb : orb C p₀ = (orb S 0).filter fun y => f0 y = y := by
    ext y
    constructor
    · intro hy
      obtain ⟨c, hc, rfl⟩ := mem_orb.1 hy
      obtain ⟨hc1, hc2⟩ := (hCmem c).1 hc
      refine Finset.mem_filter.2 ⟨?_, ?_⟩
      · rw [← hAp]
        exact mem_orb.2 ⟨c, hc1, rfl⟩
      · rw [← Perm.mul_apply, hc2, Perm.mul_apply, hfp₀]
    · intro hy
      obtain ⟨hyA, hfy⟩ := Finset.mem_filter.1 hy
      rw [← hAp] at hyA
      obtain ⟨s, hs, rfl⟩ := mem_orb.1 hyA
      have hfi : f0⁻¹ p₀ = p₀ := Perm.inv_eq_iff_eq.2 hfp₀.symm
      have ht : (f0 * s * f0⁻¹) p₀ = s p₀ := by simp [Perm.mul_apply, hfi, hfy]
      have he := hreg _ (hN s hs) s hs ht
      have hcomm : f0 * s = s * f0 := by
        calc f0 * s = f0 * s * f0⁻¹ * f0 := by group
          _ = s * f0 := by rw [he]
      exact mem_orb.2 ⟨s, (hCmem s).2 ⟨hs, hcomm⟩, rfl⟩
  have h3 := orb_cases hC2 p₀
  rw [hCorb, B_Fx3 hj h8] at h3
  omega

end CaseB

theorem comm_f0 (hS : IsPGroup 2 S) (hN : ∀ s ∈ S, f0 * s * f0⁻¹ ∈ S) :
    ∀ s ∈ S, f0 * s = s * f0 := by
  have hfix : ∀ s ∈ S, ∀ j : Fin 9, j.val < 5 → s j = j := by
    rcases dich hN hS with h | ⟨hj, h8⟩
    · exact fix_lt_of_fix0 hN h
    · exact (not_caseB hS hN hj h8).elim
  intro s hs
  ext x
  simp only [Perm.mul_apply]
  by_cases hx : x.val < 5
  · rw [hfix s hs x hx, hfix s hs _ (f0_lt x hx)]
  · have hfx : f0 x = x := by
      by_contra h
      exact hx ((f0_ne_iff x).1 h)
    have hsx : ¬ (s x).val < 5 := by
      intro h
      have := hfix s hs _ h
      exact hx (s.injective this ▸ h)
    have hfsx : f0 (s x) = s x := by
      by_contra h
      exact hsx ((f0_ne_iff _).1 h)
    rw [hfsx, hfx]

theorem cycleType_of_orderOf_five {f : Perm (Fin 9)} (hf : orderOf f = 5) : f.cycleType = {5} := by
  have : Fact (orderOf f).Prime := ⟨by rw [hf]; exact Nat.prime_five⟩
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (σ := f) this.out
  have hsum := Equiv.Perm.sum_cycleType_le f
  rw [hn, hf, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hn0 : n = 0 := by omega
  rw [hn, hf, hn0]
  rfl

public section

theorem a9_fact : A9Fact := by
  intro f hf T hT hfT
  have hconj : IsConj f f0 := by
    rw [Equiv.Perm.isConj_iff_cycleType_eq, cycleType_of_orderOf_five hf,
      cycleType_of_orderOf_five orderOf_f0]
  obtain ⟨g, hg⟩ := isConj_iff.1 hconj
  set T' : Subgroup (Perm (Fin 9)) := T.map (MulAut.conj g).toMonoidHom with hT'
  have hT'p : IsPGroup 2 T' := hT.map _
  have hf0N : f0 ∈ Subgroup.normalizer (T' : Set (Perm (Fin 9))) := by
    rw [← hg]
    exact Subgroup.le_normalizer_map _ ⟨f, hfT, rfl⟩
  have hN : ∀ s ∈ T', f0 * s * f0⁻¹ ∈ T' := fun s hs =>
    (Subgroup.mem_normalizer_iff.1 hf0N s).1 hs
  have hcomm := comm_f0 hT'p hN
  intro t ht
  have h := hcomm (g * t * g⁻¹) ⟨t, ht, rfl⟩
  rw [← hg] at h
  have : g * (f * t) * g⁻¹ = g * (t * f) * g⁻¹ := by
    calc g * (f * t) * g⁻¹ = (g * f * g⁻¹) * (g * t * g⁻¹) := by group
      _ = (g * t * g⁻¹) * (g * f * g⁻¹) := h
      _ = g * (t * f) * g⁻¹ := by group
  simpa using this

theorem a9_lemma (hc : A9Fact) {f : Perm (Fin 9)} (hf : orderOf f = 5)
    {T : Subgroup (Perm (Fin 9))} (_hTA : T ≤ alternatingGroup (Fin 9)) (hT : IsPGroup 2 T)
    (hfT : f ∈ Subgroup.normalizer (T : Set (Perm (Fin 9)))) : ∀ t ∈ T, f * t = t * f :=
  hc f hf T hT hfT

end

end CFSG.LocalAnalysis.GLTheoremA.S8.A9
