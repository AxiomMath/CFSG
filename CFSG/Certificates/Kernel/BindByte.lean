module

public import CFSG.Certificates.Kernel.HOrbSound
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Certificates.BindL

open CFSG.KC CFSG.KC.LceS CFSG.KC.Bind CFSG.Certificates.LCE

theorem andB_iff (a b : Bool) : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem orB_iff (a b : Bool) : orB a b = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem letB_eq (v : ℕ) (k : ℕ → Bool) : letB v k = k v := by
  cases v <;> rfl

theorem brec_eq {α : Sort*} (a b : α) (c : Bool) :
    Bool.rec (motive := fun _ => α) a b c = if c = true then b else a := by
  cases c <;> rfl

theorem allRec_iff (f : ℕ → Bool) : ∀ n,
    Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (f q)) n = true ↔
      ∀ q < n, f q = true
  | 0 => ⟨fun _ q hq => absurd hq (Nat.not_lt_zero q), fun _ => rfl⟩
  | n + 1 => by
    change andB (Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (f q)) n) (f n) =
      true ↔ _
    rw [andB_iff, allRec_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ q hq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hq with h | rfl
      · exact h1 q h
      · exact h2
    · intro h
      exact ⟨fun q hq => h q (by omega), h n (by omega)⟩

theorem shr1 (x : ℕ) : Nat.shiftRight x 1 = x / 2 := by
  change x >>> 1 = x / 2
  rw [Nat.shiftRight_eq_div_pow, pow_one]

theorem land1 (x : ℕ) : Nat.land x 1 = x % 2 := Nat.and_one_is_mod x

theorem fold_spec (f : ℕ → ℕ) : ∀ k, (∀ j < k, f j < 256) →
    HO.byteFold f k < 256 ^ k ∧ ∀ i < k, HO.byteFold f k / 256 ^ i % 256 = f i
  | 0, _ => ⟨by simp [HO.byteFold], fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | k + 1, hf => by
    obtain ⟨hlt, hb⟩ := fold_spec f k (fun j hj => hf j (by omega))
    have hlt2 : HO.byteFold f k < 2 ^ (8 * k) := by rw [HO.two_pow_eight_mul]; exact hlt
    have e : HO.byteFold f (k + 1) = HO.byteFold f k + f k * 256 ^ k := by
      change HO.byteFold f k ||| (f k <<< (8 * k)) = _
      rw [Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt2, Nat.shiftLeft_eq,
        HO.two_pow_eight_mul, Nat.add_comm]
    rw [e]
    have hk := hf k (by omega)
    refine ⟨?_, fun i hi => ?_⟩
    · calc HO.byteFold f k + f k * 256 ^ k < 256 ^ k + f k * 256 ^ k := by omega
        _ = (f k + 1) * 256 ^ k := by ring
        _ ≤ 256 * 256 ^ k := Nat.mul_le_mul_right _ (by omega)
        _ = 256 ^ (k + 1) := by ring
    · rw [HO.byte_concat hlt]
      split_ifs with h
      · exact hb i h
      · have : i = k := by omega
        subst this
        simp [Nat.mod_eq_of_lt hk]

theorem fold_byte (f : ℕ → ℕ) {k : ℕ} (hf : ∀ j < k, f j < 256) {i : ℕ} (hi : i < k) :
    wLet (HO.byteFold f k) i = f i := by
  rw [HO.wLet_eq]
  exact (fold_spec f k hf).2 i hi

@[expose] def sbE (SB s : ℕ) : ℕ := Nat.land (Nat.shiftRight SB (24 * s)) 16777215

theorem findSub_spec (SB g : ℕ) : ∀ ns, findSub SB ns g = 0 ∨
    ∃ s < ns, Nat.land (sbE SB s) 255 = g ∧ findSub SB ns g = Nat.shiftRight (sbE SB s) 8 + 1
  | 0 => Or.inl rfl
  | ns + 1 => by
    have e : findSub SB (ns + 1) g = Bool.rec (motive := fun _ => ℕ) (findSub SB ns g)
        (Nat.succ (Nat.shiftRight (sbE SB ns) 8)) (Nat.beq (Nat.land (sbE SB ns) 255) g) := rfl
    rw [e, brec_eq]
    split_ifs with hb
    · rw [Nat.beq_eq] at hb
      exact Or.inr ⟨ns, by omega, hb, rfl⟩
    · rcases findSub_spec SB g ns with h | ⟨s, hs, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨s, by omega, h1, h2⟩

theorem subsOK_spec {PRT : ℕ → ℕ} {SB ns : ℕ} (h : subsOK PRT SB ns true = true) :
    ∀ s < ns, 0 < wLen (PRT (Nat.shiftRight (sbE SB s) 8)) ∧
      wLet (wWord (PRT (Nat.shiftRight (sbE SB s) 8))) 0 = 2 * Nat.land (sbE SB s) 255 + 1 := by
  intro s hs
  have h1 := (allRec_iff _ ns).1 h s hs
  simp only [andB_iff, Nat.blt_eq, Nat.beq_eq] at h1
  exact h1

theorem findSub_rel {PRT : ℕ → ℕ} {SB ns PR g : ℕ} (hsub : subsOK PRT SB ns true = true)
    (hSB : ∀ s < ns, Nat.shiftRight (Nat.land (Nat.shiftRight SB (24 * s)) 16777215) 8 < PR)
    (h0 : 0 < findSub SB ns g) :
    findSub SB ns g - 1 < PR ∧ 0 < wLen (PRT (findSub SB ns g - 1)) ∧
      wLet (wWord (PRT (findSub SB ns g - 1))) 0 = 2 * g + 1 := by
  rcases findSub_spec SB g ns with h | ⟨s, hs, h1, h2⟩
  · omega
  · rw [h2, Nat.add_sub_cancel]
    obtain ⟨a, b⟩ := subsOK_spec hsub s hs
    exact ⟨hSB s hs, a, by rw [b, h1]⟩

theorem letV_ren {G : Type*} [Group G] (pg cg : ℕ → G) {l m : ℕ} (hl : l < 254) (hm : m < 127)
    (hc : cg m = pg (l / 2)) : letV cg (2 * m + l % 2) = letV pg l := by
  unfold letV
  have h1 : 2 * m + l % 2 ≠ 255 := by omega
  have h2 : l ≠ 255 := by omega
  have h3 : (2 * m + l % 2) % 2 = l % 2 := by omega
  have h4 : (2 * m + l % 2) / 2 = m := by omega
  rw [ite_eq_right h1, ite_eq_right h2, h3, h4, hc]

theorem letV_odd {G : Type*} [Group G] (pg : ℕ → G) {g : ℕ} (hg : 2 * g + 1 ≠ 255) :
    letV pg (2 * g + 1) = (pg g)⁻¹ := by
  unfold letV
  have h3 : (2 * g + 1) % 2 = 1 := by omega
  have h4 : (2 * g + 1) / 2 = g := by omega
  rw [ite_eq_right hg, h3, h4]
  rfl

theorem letV_even {G : Type*} [Group G] (pg : ℕ → G) {g : ℕ} (hg : 2 * g < 255) :
    letV pg (2 * g) = pg g := by
  unfold letV
  have h3 : (2 * g) % 2 = 0 := by omega
  have h4 : (2 * g) / 2 = g := by omega
  have h5 : 2 * g ≠ 255 := Nat.ne_of_lt hg
  rw [ite_eq_right h5, h3, h4]
  rfl

theorem letV_inv {G : Type*} [Group G] (pg : ℕ → G) (hinv : ∀ g, pg g * pg g = 1) {l : ℕ}
    (hl : l ≠ 255) : letV pg l = pg (l / 2) := by
  unfold letV
  rw [ite_eq_right hl]
  split_ifs
  · rfl
  · exact inv_eq_of_mul_eq_one_right (hinv _)

theorem bval_cons {G : Type*} [Group G] (pg : ℕ → G) (W m : ℕ) :
    bval pg W (m + 1) = letV pg (wLet W 0) *
      ((List.range m).map fun j => letV pg (wLet W (j + 1))).prod := by
  unfold bval
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  rfl

theorem mapW_eq (M W n : ℕ) : mapW M W n =
    HO.byteFold (fun q => 2 * mget M (Nat.shiftRight (wLet W q) 1) + Nat.land (wLet W q) 1) n :=
  rfl

theorem relsSub_sound' {G : Type*} [Group G] (pg cg : ℕ → G) {CRT PRT : ℕ → ℕ} {M R PR Hs : ℕ}
    (h : relsSub CRT PRT M R PR Hs = true)
    (hM : ∀ g < 128, mget M g < 255 → mget M g < 127 ∧ cg (mget M g) = pg g)
    (hP : ∀ r < PR, bval pg (wWord (PRT r)) (wLen (PRT r)) = 1)
    (hPL : ∀ r < PR, ∀ q < wLen (PRT r), wLet (wWord (PRT r)) q < 254) :
    ∀ r < R, bval cg (wWord (CRT r)) (wLen (CRT r)) = 1 := by
  intro r hr
  have hall := (allRec_iff (fun r => andB (Nat.blt (hget Hs r) PR)
    (subRel M (PRT (hget Hs r)) (CRT r))) R).1 h r hr
  simp only [andB_iff, Nat.blt_eq] at hall
  obtain ⟨hlt, hsub⟩ := hall
  unfold subRel at hsub
  simp only [andB_iff, Nat.beq_eq] at hsub
  obtain ⟨hok, hlen, hw⟩ := hsub
  have hok' := (allRec_iff _ _).1 hok
  simp only [Nat.blt_eq, shr1] at hok'
  rw [hlen, hw, mapW_eq, ← hP _ hlt]
  have hL := hPL _ hlt
  have hf : ∀ q < wLen (PRT (hget Hs r)),
      (fun q => 2 * mget M (Nat.shiftRight (wLet (wWord (PRT (hget Hs r))) q) 1) +
        Nat.land (wLet (wWord (PRT (hget Hs r))) q) 1) q < 256 := by
    intro q hq
    have h1 := hL q hq
    have h2 := hok' q hq
    simp only [shr1, land1]
    have h3 := (hM _ (by omega) h2).1
    omega
  unfold bval
  congr 1
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  rw [fold_byte _ hf hq]
  have h1 := hL q hq
  have h2 := hok' q hq
  simp only [shr1, land1]
  obtain ⟨h3, h4⟩ := hM _ (by omega) h2
  exact letV_ren pg cg h1 h3 h4

end CFSG.Certificates.BindL

end
