module

public import CFSG.Certificates.Kernel.CosetBoundsLemmas
public import CFSG.Certificates.Kernel.Bounds.CoreE
public import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.Certificates.KB.Sound

open CFSG.Certificates.KB

theorem fwd_inv_closed {G : Type*} [Group G] {H : Subgroup G} {rp : ℕ → G} {N : ℕ} {g : G}
    (hcl : ∀ x < N, ∃ y < N, rel H (rp x * g) (rp y)) :
    ∀ x < N, ∃ y < N, rel H (rp x * g⁻¹) (rp y) := by
  obtain ⟨σ, hσ⟩ : ∃ σ : ℕ → ℕ, ∀ x < N, σ x < N ∧ rel H (rp x * g) (rp (σ x)) :=
    ⟨fun x => if h : x < N then Classical.choose (hcl x h) else 0, fun x hx => by
      simp only [dif_pos hx]
      exact Classical.choose_spec (hcl x hx)⟩
  intro x hx
  have hit : ∀ k, σ^[k] x < N ∧ rel H (rp x * g ^ k) (rp (σ^[k] x)) := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, mul_one]
      exact ⟨hx, rel_refl H _⟩
    | succ k ih =>
      rw [Function.iterate_succ_apply', pow_succ, ← mul_assoc]
      obtain ⟨h1, h2⟩ := hσ _ ih.1
      exact ⟨h1, rel_trans (rel_mul_right g ih.2) h2⟩
  let f : Fin (N + 1) → Fin N := fun k => ⟨σ^[k] x, (hit k).1⟩
  obtain ⟨a, b, hab, hfab⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  have key : ∀ i j, i < j → σ^[i] x = σ^[j] x → ∃ y < N, rel H (rp x * g⁻¹) (rp y) := by
    intro i j hij he
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
    have hj := (hit (i + d + 1)).2
    rw [← he] at hj
    have h := rel_mul_right ((g ^ i)⁻¹ * g⁻¹) (rel_trans hj (rel_symm (hit i).2))
    have hk : i + d + 1 = (d + 1) + i := by omega
    have e1 : rp x * g ^ (i + d + 1) * ((g ^ i)⁻¹ * g⁻¹) = rp x * g ^ d := by
      rw [hk, pow_add, pow_succ]
      group
    have e2 : rp x * g ^ i * ((g ^ i)⁻¹ * g⁻¹) = rp x * g⁻¹ := by group
    rw [e1, e2] at h
    exact ⟨_, (hit d).1, rel_trans (rel_symm h) (hit d).2⟩
  have hv : σ^[a] x = σ^[b] x := congrArg Fin.val hfab
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · exact key _ _ h hv
  · exact key _ _ h hv.symm

theorem index_le_even {G : Type*} [Group G] {H A : Subgroup G} (val rp : ℕ → G) {L N : ℕ}
    (hA : A ≤ Subgroup.closure (val '' {c | c < L})) (hrpA : ∀ x, rp x ∈ A)
    (hrp0 : rp 0 = 1) (hN : 1 ≤ N)
    (hxor : ∀ c < L, Nat.xor c 1 < L ∧ val (Nat.xor c 1) = (val c)⁻¹)
    (hcl : ∀ x < N, ∀ c < L, c % 2 = 0 → ∃ y < N, rel H (rp x * val c) (rp y)) :
    H.relIndex A ≠ 0 ∧ H.relIndex A ≤ N := by
  refine index_le val rp hA hrpA hrp0 hN (fun c hc => ⟨_, (hxor c hc).1, (hxor c hc).2⟩) ?_
  intro x hx c hc
  rcases Nat.mod_two_eq_zero_or_one c with h0 | h1
  · exact hcl x hx c hc h0
  · obtain ⟨hlt, hval⟩ := hxor c hc
    have h0 : (c ^^^ 1) % 2 = 0 := by
      rw [Nat.xor_mod_two_eq]
      omega
    have hv : val c = (val (Nat.xor c 1))⁻¹ := by rw [hval, inv_inv]
    rw [hv]
    exact fwd_inv_closed (fun x hx => hcl x hx _ hlt h0) x hx

def CovPE (F : ℕ → ℕ) (RW RM N Lh nF : ℕ) (x : ℕ) : Prop :=
  ∃ rest, Nat.rec (motive := fun _ => Bool) true
    (fun c acc => Bool.rec false acc
      (wCovEntry F N nF x (Nat.shiftLeft c (nat_lit 1))
        (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) Lh = true

theorem wCovStepE_spec (F : ℕ → ℕ) (RW RM N Lh nF : ℕ) (st : ℕ × ℕ) :
    (wCovStepE F RW RM N Lh nF st).2 = bad ∨
      ((wCovStepE F RW RM N Lh nF st).2 = st.2 + 1 ∧ CovPE F RW RM N Lh nF st.2) := by
  obtain ⟨rest, x⟩ := st
  unfold wCovStepE
  dsimp only
  cases hc : Nat.rec (motive := fun _ => Bool) true
    (fun c acc => Bool.rec false acc
      (wCovEntry F N nF x (Nat.shiftLeft c (nat_lit 1))
        (Nat.land (Nat.shiftRight rest (Nat.mul RW c)) RM))) Lh
  · exact Or.inl rfl
  · exact Or.inr ⟨rfl, rest, hc⟩

theorem wCovListE_run (F : ℕ → ℕ) (RW RM N Lh nF : ℕ) (l : List ℕ) (x : ℕ) :
    RunOk (CovPE F RW RM N Lh nF) x (wCovListE F RW RM N Lh nF l x) := by
  unfold wCovListE
  refine list_run _ (fun E x => ?_) l x
  unfold wCovElemE
  exact iter_run _ (wCovStepE_spec F RW RM N Lh nF) _ (Prod.mk (Nat.shiftRight E (nat_lit 8)) x)

theorem cover_closedE {G : Type*} [Group G] (H : Subgroup G) (val : ℕ → G)
    {inv L Lh nLab nT N RW RM nW nF : ℕ} {F D Wd Wd2 : ℕ → ℕ} {walk cov : List ℕ}
    (hLh : 2 * Lh = L)
    (hNl : N ≤ nLab) (hlab : nLab = nT + 1) (hlabbad : nLab + 1 ≤ bad) (hFbad : nF + 1 ≤ bad)
    (hxor : ∀ c < L, val (Nat.xor c 1) = (val c)⁻¹)
    (hinvv : ∀ c ≤ L, val (byte inv c) = (val c)⁻¹)
    (hW : ∀ j < nW, (∀ q < wN (Wd j), letter (Wd j) q ≤ L) ∧
      (wKind (Wd j) = 0 → lv val (wbytes (Wd j)) = 1) ∧
      (wKind (Wd j) = 1 → lv val (wbytes (Wd j)) ∈ H))
    (h2 : words2Ok Wd Wd2 inv nW = true)
    (htree : treeRange F D L nLab (nat_lit 0) nT = true)
    (hwalk : wWalkList F Wd2 RW RM nLab nW walk nT = nF)
    (hcov : wCovListE F RW RM N Lh nF cov (nat_lit 0) = N) :
    ∀ x < N, ∀ c < L, c % 2 = 0 → ∃ y < N, rel H (rep val F D nT x * val c) (rep val F D nT y) := by
  have hbad : bad = 4611686018427387904 := rfl
  have hfacts := facts_hold H val hlab hlabbad hFbad hinvv hW h2 htree hwalk
  have hgood := (wCovListE_run F RW RM N Lh nF cov 0).good (by rw [hcov]; omega)
  rw [hcov] at hgood
  intro x hx c hc hc2
  obtain ⟨rest, hrest⟩ := hgood x (Nat.zero_le _) hx
  have he := natrec_all _ Lh hrest (c / 2) (by omega)
  have hs : Nat.shiftLeft (c / 2) (nat_lit 1) = c := by
    change (c / 2) <<< 1 = c
    rw [Nat.shiftLeft_eq]
    omega
  rw [hs] at he
  obtain ⟨hg, hcases⟩ := wCovEntry_spec he
  obtain ⟨hH, -⟩ := hfacts _ hg
  rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact ⟨_, h3, rel_of_bwd hH rfl (by rw [h2, hxor c hc]) h1⟩
  · exact ⟨_, h3, rel_of_fwd hH h1 h2 rfl⟩

end CFSG.Certificates.KB.Sound

end
