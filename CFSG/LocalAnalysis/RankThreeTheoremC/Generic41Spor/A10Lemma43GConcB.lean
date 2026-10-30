module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcDefs
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GConcDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

namespace A10Perm

open Equiv Equiv.Perm Subgroup

def a10t1_cb_blk (i : Fin 10) : Bool := decide (5 ≤ (i : ℕ))

def a10t1_cb_Stab : Subgroup A10 where
  carrier := {σ | ∃ t : Bool, ∀ i : Fin 10,
    a10t1_cb_blk ((σ : Perm (Fin 10)) i) = xor (a10t1_cb_blk i) t}
  mul_mem' := by
    rintro σ τ ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨xor t s, fun i => ?_⟩
    show a10t1_cb_blk ((σ : Perm (Fin 10)) ((τ : Perm (Fin 10)) i)) = _
    rw [hs, ht, Bool.xor_assoc]
  one_mem' := ⟨false, fun i => by simp⟩
  inv_mem' := by
    rintro σ ⟨s, hs⟩
    refine ⟨s, fun i => ?_⟩
    have h := hs (((σ⁻¹ : A10) : Perm (Fin 10)) i)
    have h2 : (σ : Perm (Fin 10)) (((σ⁻¹ : A10) : Perm (Fin 10)) i) = i := by
      show (σ : Perm (Fin 10)) (((σ : Perm (Fin 10))⁻¹) i) = i
      simp
    rw [h2] at h
    rw [h, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

theorem a10t1_cb_exp_form {b : A10} (hb : b ∈ S₀) :
    ∃ u v : Fin 5, b = a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) := by
  obtain ⟨i, j, rfl⟩ := hb
  refine ⟨⟨i % 5, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 5, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  simp only
  rw [← pow_eq_pow_mod i a₁_pow, ← pow_eq_pow_mod j a₂_pow]

theorem a10t1_cb_fix_check : ∀ u v : Fin 5, (u ≠ 0 ∨ v ≠ 0) →
    (∃ p : Fin 10, ((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) : Perm (Fin 10)) p = p) →
    ∃ s : Bool, ∀ p : Fin 10,
      (((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) : Perm (Fin 10)) p = p ↔ a10t1_cb_blk p = s) := by
  decide +kernel

theorem a10t1_cb_diag_check : ∀ u v : Fin 5,
    (∀ p : Fin 10, ((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) : Perm (Fin 10)) p ≠ p) →
    ∀ x y : Fin 10, ((∃ k : Fin 5,
      (((a₁ ^ (u : ℕ) * a₂ ^ (v : ℕ) : A10) ^ (k : ℕ) : A10) : Perm (Fin 10)) x = y) ↔
        a10t1_cb_blk x = a10t1_cb_blk y) := by
  decide +kernel

theorem a10t1_cb_fix_of_mem {b : A10} (hb : b ∈ S₀) (hb1 : b ≠ 1)
    (hf : ∃ p : Fin 10, (b : Perm (Fin 10)) p = p) :
    ∃ s : Bool, ∀ p : Fin 10, ((b : Perm (Fin 10)) p = p ↔ a10t1_cb_blk p = s) := by
  obtain ⟨u, v, rfl⟩ := a10t1_cb_exp_form hb
  refine a10t1_cb_fix_check u v ?_ hf
  by_contra h
  push Not at h
  apply hb1
  rw [h.1, h.2]
  simp

theorem a10t1_cb_orb_of_mem {b : A10} (hb : b ∈ S₀)
    (hf : ∀ p : Fin 10, (b : Perm (Fin 10)) p ≠ p) (x y : Fin 10) :
    (∃ k : Fin 5, ((b ^ (k : ℕ) : A10) : Perm (Fin 10)) x = y) ↔ a10t1_cb_blk x = a10t1_cb_blk y := by
  obtain ⟨u, v, rfl⟩ := a10t1_cb_exp_form hb
  exact a10t1_cb_diag_check u v hf x y

theorem a10t1_cb_bool_aux : ∀ bx bn s s' : Bool, (bx = s ↔ bn = s') → bn = xor bx (xor s s') := by
  decide

theorem a10t1_cb_stab_aux {n : A10} {s s' : Bool}
    (h : ∀ x : Fin 10, (a10t1_cb_blk x = s ↔ a10t1_cb_blk ((n : Perm (Fin 10)) x) = s')) :
    n ∈ a10t1_cb_Stab :=
  ⟨xor s s', fun x => a10t1_cb_bool_aux _ _ _ _ (h x)⟩

theorem a10t1_cb_stab_of_conj {b n : A10} (hb : b ∈ S₀) (hb1 : b ≠ 1) (hb' : n * b * n⁻¹ ∈ S₀) :
    n ∈ a10t1_cb_Stab := by
  have hconj : ∀ x : Fin 10, ((n * b * n⁻¹ : A10) : Perm (Fin 10)) ((n : Perm (Fin 10)) x) =
      (n : Perm (Fin 10)) ((b : Perm (Fin 10)) x) := by
    intro x
    show ((n : Perm (Fin 10)) * (b : Perm (Fin 10)) * (n : Perm (Fin 10))⁻¹) ((n : Perm (Fin 10)) x) = _
    simp [Perm.mul_apply]
  have hb1' : n * b * n⁻¹ ≠ 1 := by
    intro h
    apply hb1
    have := congrArg (fun y => n⁻¹ * y * n) h
    simpa [mul_assoc] using this
  by_cases hfix : ∃ p : Fin 10, (b : Perm (Fin 10)) p = p
  · obtain ⟨s, hs⟩ := a10t1_cb_fix_of_mem hb hb1 hfix
    have hfix' : ∃ p : Fin 10, ((n * b * n⁻¹ : A10) : Perm (Fin 10)) p = p := by
      obtain ⟨p, hp⟩ := hfix
      exact ⟨(n : Perm (Fin 10)) p, by rw [hconj, hp]⟩
    obtain ⟨s', hs'⟩ := a10t1_cb_fix_of_mem hb' hb1' hfix'
    refine a10t1_cb_stab_aux (s := s) (s' := s') fun x => ?_
    rw [← hs x, ← hs' ((n : Perm (Fin 10)) x), hconj]
    exact ((n : Perm (Fin 10)).injective.eq_iff).symm
  · push Not at hfix
    have hfix' : ∀ p : Fin 10, ((n * b * n⁻¹ : A10) : Perm (Fin 10)) p ≠ p := by
      intro p hp
      have h1 := hconj (((n : Perm (Fin 10))⁻¹) p)
      rw [show (n : Perm (Fin 10)) (((n : Perm (Fin 10))⁻¹) p) = p by simp, hp] at h1
      apply hfix (((n : Perm (Fin 10))⁻¹) p)
      apply (n : Perm (Fin 10)).injective
      rw [← h1]
      simp
    refine a10t1_cb_stab_aux (s := a10t1_cb_blk 0) (s' := a10t1_cb_blk ((n : Perm (Fin 10)) 0)) fun x => ?_
    rw [← a10t1_cb_orb_of_mem hb hfix x 0, ← a10t1_cb_orb_of_mem hb' hfix' ((n : Perm (Fin 10)) x)
      ((n : Perm (Fin 10)) 0)]
    refine exists_congr fun k => ?_
    rw [conj_pow]
    show _ ↔ ((n : Perm (Fin 10)) * ((b ^ (k : ℕ) : A10) : Perm (Fin 10)) *
      (n : Perm (Fin 10))⁻¹) ((n : Perm (Fin 10)) x) = _
    simp [Perm.mul_apply]

theorem a10t1_cb_gamma_le : A10Gamma A10 S₀ ≤ a10t1_cb_Stab := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨B, hBS, hB1, hg⟩
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hB1
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have h2 : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.1 hg b).1 hbB
  exact a10t1_cb_stab_of_conj (hBS hbB) hb1' (hBS h2)

theorem a10t1_cb_a₁_fix : ∀ i : Fin 10, 5 ≤ (i : ℕ) → ((a₁ : A10) : Perm (Fin 10)) i = i := by
  decide +kernel

theorem a10t1_cb_a₂_fix : ∀ i : Fin 10, (i : ℕ) < 5 → ((a₂ : A10) : Perm (Fin 10)) i = i := by
  decide +kernel

theorem a10t1_cb_comm {a b : A10} (ha : a ∈ L1) (hb : b ∈ L2) : a * b = b * a := by
  have ha' : ∀ i : Fin 10, 5 ≤ (i : ℕ) → (a : Perm (Fin 10)) i = i := ha
  have hb' : ∀ i : Fin 10, (i : ℕ) < 5 → (b : Perm (Fin 10)) i = i := hb
  apply Subtype.ext
  apply Equiv.ext
  intro i
  show (a : Perm (Fin 10)) ((b : Perm (Fin 10)) i) = (b : Perm (Fin 10)) ((a : Perm (Fin 10)) i)
  by_cases hi : (i : ℕ) < 5
  · have hai : ((a : Perm (Fin 10)) i : ℕ) < 5 := by
      by_contra h
      push Not at h
      have h2 := (a : Perm (Fin 10)).injective (ha' _ h)
      rw [h2] at h
      omega
    rw [hb' i hi, hb' _ hai]
  · push Not at hi
    have hbi : 5 ≤ ((b : Perm (Fin 10)) i : ℕ) := by
      by_contra h
      push Not at h
      have h2 := (b : Perm (Fin 10)).injective (hb' _ h)
      rw [h2] at h
      omega
    rw [ha' i hi, ha' _ hbi]

theorem a10t1_cb_a₁_mem : a₁ ∈ L1 := a10t1_cb_a₁_fix

theorem a10t1_cb_a₂_mem : a₂ ∈ L2 := a10t1_cb_a₂_fix

theorem a10t1_cb_line₁_ne : line₁ ≠ ⊥ := by
  intro h
  apply a₁_ne
  have hm : a₁ ∈ line₁ := Subgroup.mem_zpowers a₁
  rw [h] at hm
  exact Subgroup.mem_bot.1 hm

theorem a10t1_cb_line₂_ne : line₂ ≠ ⊥ := by
  intro h
  apply a₂_ne
  have hm : a₂ ∈ line₂ := Subgroup.mem_zpowers a₂
  rw [h] at hm
  exact Subgroup.mem_bot.1 hm

theorem a10t1_cb_normalizer_zpowers {σ a : A10} (h : σ * a = a * σ) :
    σ ∈ normalizer ((zpowers a : Subgroup A10) : Set A10) := by
  apply Subgroup.mem_normalizer_fintype
  intro x hx
  have hx' : x ∈ zpowers a := hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx'
  have hc : Commute σ (a ^ k) := Commute.zpow_right h k
  show σ * a ^ k * σ⁻¹ ∈ zpowers a
  rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers a) k

theorem L1_le_gamma : L1 ≤ A10Gamma A10 S₀ := by
  intro σ hσ
  exact Subgroup.subset_closure ⟨line₂, line₂_le, a10t1_cb_line₂_ne,
    a10t1_cb_normalizer_zpowers (a10t1_cb_comm hσ a10t1_cb_a₂_mem)⟩

theorem L2_le_gamma : L2 ≤ A10Gamma A10 S₀ := by
  intro σ hσ
  exact Subgroup.subset_closure ⟨line₁, line₁_le, a10t1_cb_line₁_ne,
    a10t1_cb_normalizer_zpowers (a10t1_cb_comm a10t1_cb_a₁_mem hσ).symm⟩

theorem a10t1_cb_pres_of_stab {σ : A10} (hσ : σ ∈ a10t1_cb_Stab) {k : ℕ} (hk : σ ^ 5 ^ k = 1) :
    ∀ i : Fin 10, a10t1_cb_blk ((σ : Perm (Fin 10)) i) = a10t1_cb_blk i := by
  obtain ⟨t, ht⟩ := hσ
  have hpow : ∀ (m : ℕ) (i : Fin 10), a10t1_cb_blk (((σ ^ m : A10) : Perm (Fin 10)) i) =
      xor (a10t1_cb_blk i) (t && decide (m % 2 = 1)) := by
    intro m
    induction m with
    | zero => intro i; simp
    | succ m ih =>
      intro i
      have h1 : ((σ ^ (m + 1) : A10) : Perm (Fin 10)) i =
          ((σ ^ m : A10) : Perm (Fin 10)) ((σ : Perm (Fin 10)) i) := by
        rw [pow_succ]; rfl
      rw [h1, ih, ht]
      by_cases hm : m % 2 = 1
      · have h3 : ¬ (m + 1) % 2 = 1 := by omega
        simp only [hm, h3, decide_true, decide_false, Bool.and_true, Bool.and_false]
        cases t <;> cases a10t1_cb_blk i <;> rfl
      · have h3 : (m + 1) % 2 = 1 := by omega
        simp only [hm, h3, decide_true, decide_false, Bool.and_true, Bool.and_false]
        cases t <;> cases a10t1_cb_blk i <;> rfl
  have hodd : 5 ^ k % 2 = 1 := by simp [Nat.pow_mod]
  have h0 := hpow (5 ^ k) 0
  rw [hk, hodd] at h0
  have hb0 : a10t1_cb_blk 0 = false := by decide
  have h00 : a10t1_cb_blk (((1 : A10) : Perm (Fin 10)) 0) = false := hb0
  rw [h00, hb0] at h0
  have ht0 : t = false := by simpa using h0.symm
  intro i
  rw [ht i, ht0]
  simp

theorem a10t1_cb_sign_eq_one {α : Type*} [Fintype α] [DecidableEq α] {τ : Perm α} {k : ℕ}
    (h : τ ^ 5 ^ k = 1) : sign τ = 1 := by
  have h1 : sign τ ^ 5 ^ k = 1 := by rw [← map_pow, h, map_one]
  rwa [Int.units_pow_eq_pow_mod_two, show 5 ^ k % 2 = 1 by simp [Nat.pow_mod], pow_one] at h1

theorem a10t1_cb_subtypePerm_pow_one {α : Type*} {p : α → Prop} {σ : Perm α}
    (h : ∀ x, p (σ x) ↔ p x) {m : ℕ} (hm : σ ^ m = 1) :
    (σ.subtypePerm h : Perm {x // p x}) ^ m = 1 := by
  rw [subtypePerm_pow]
  ext x
  simp [hm]

theorem a10t1_cb_split_perm {σ : Perm (Fin 10)} (hp : ∀ i : Fin 10, a10t1_cb_blk (σ i) = a10t1_cb_blk i)
    {k : ℕ} (hk : σ ^ 5 ^ k = 1) :
    ∃ σ₁ σ₂ : Perm (Fin 10), σ = σ₁ * σ₂ ∧ sign σ₁ = 1 ∧ sign σ₂ = 1 ∧
      (∀ i : Fin 10, 5 ≤ (i : ℕ) → σ₁ i = i) ∧ (∀ i : Fin 10, (i : ℕ) < 5 → σ₂ i = i) := by
  have h1 : ∀ x : Fin 10, ((σ x : Fin 10) : ℕ) < 5 ↔ (x : ℕ) < 5 := by
    intro x
    have := hp x
    simp only [a10t1_cb_blk, decide_eq_decide] at this
    rw [← not_le, ← not_le]
    exact not_congr this
  have h2 : ∀ x : Fin 10, ¬ (((σ x : Fin 10) : ℕ) < 5) ↔ ¬ ((x : ℕ) < 5) :=
    fun x => not_congr (h1 x)
  let ep : Perm {a : Fin 10 // (a : ℕ) < 5} := σ.subtypePerm h1
  let en : Perm {a : Fin 10 // ¬ ((a : ℕ) < 5)} := σ.subtypePerm h2
  have e1 : ∀ (i : Fin 10) (hi : (i : ℕ) < 5), (ep.subtypeCongr 1) i = σ i := fun i hi => by
    rw [Perm.subtypeCongr.left_apply (a := i) ep 1 hi]; rfl
  have e2 : ∀ (i : Fin 10) (hi : ¬ ((i : ℕ) < 5)), (ep.subtypeCongr 1) i = i := fun i hi => by
    rw [Perm.subtypeCongr.right_apply (a := i) ep 1 hi]; rfl
  have e3 : ∀ (i : Fin 10) (hi : (i : ℕ) < 5),
      ((1 : Perm {a : Fin 10 // (a : ℕ) < 5}).subtypeCongr en) i = i := fun i hi => by
    rw [Perm.subtypeCongr.left_apply (a := i) 1 en hi]; rfl
  have e4 : ∀ (i : Fin 10) (hi : ¬ ((i : ℕ) < 5)),
      ((1 : Perm {a : Fin 10 // (a : ℕ) < 5}).subtypeCongr en) i = σ i := fun i hi => by
    rw [Perm.subtypeCongr.right_apply (a := i) 1 en hi]; rfl
  refine ⟨ep.subtypeCongr 1, (1 : Perm {a : Fin 10 // (a : ℕ) < 5}).subtypeCongr en,
    ?_, ?_, ?_, ?_, ?_⟩
  · ext i
    by_cases hi : (i : ℕ) < 5
    · rw [Perm.mul_apply, e3 i hi, e1 i hi]
    · rw [Perm.mul_apply, e4 i hi, e2 _ ((h2 i).2 hi)]
  · rw [sign_subtypeCongr, map_one, mul_one]
    exact a10t1_cb_sign_eq_one (a10t1_cb_subtypePerm_pow_one h1 hk)
  · rw [sign_subtypeCongr, map_one, one_mul]
    exact a10t1_cb_sign_eq_one (a10t1_cb_subtypePerm_pow_one h2 hk)
  · intro i hi
    exact e2 i (by omega)
  · intro i hi
    exact e3 i hi

theorem a10t1_cb_mem_sup {σ : A10}
    (hp : ∀ i : Fin 10, a10t1_cb_blk ((σ : Perm (Fin 10)) i) = a10t1_cb_blk i)
    {k : ℕ} (hk : σ ^ 5 ^ k = 1) : σ ∈ L1 ⊔ L2 := by
  have hk' : (σ : Perm (Fin 10)) ^ 5 ^ k = 1 := by
    have := congrArg (fun x : A10 => (x : Perm (Fin 10))) hk
    simpa using this
  obtain ⟨σ₁, σ₂, hσ, hs₁, hs₂, hf₁, hf₂⟩ := a10t1_cb_split_perm hp hk'
  have m1 : σ₁ ∈ alternatingGroup (Fin 10) := mem_alternatingGroup.2 hs₁
  have m2 : σ₂ ∈ alternatingGroup (Fin 10) := mem_alternatingGroup.2 hs₂
  have h : σ = (⟨σ₁, m1⟩ : A10) * ⟨σ₂, m2⟩ := Subtype.ext hσ
  rw [h]
  exact Subgroup.mul_mem_sup (show (⟨σ₁, m1⟩ : A10) ∈ L1 from hf₁)
    (show (⟨σ₂, m2⟩ : A10) ∈ L2 from hf₂)

theorem gamma_five : ∀ g ∈ A10Gamma A10 S₀, (∃ k : ℕ, g ^ 5 ^ k = 1) → g ∈ L1 ⊔ L2 := by
  rintro g hg ⟨k, hk⟩
  exact a10t1_cb_mem_sup (a10t1_cb_pres_of_stab (a10t1_cb_gamma_le hg) hk) hk

end A10Perm

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
