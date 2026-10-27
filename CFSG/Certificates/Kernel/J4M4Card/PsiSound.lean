module

public import Certificates.Data.Kernel.J4M4Card.PsiDefs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.SetTheory.Cardinal.Finite
public import CFSG.Certificates.Kernel.Spor.RawOrbEval
import Mathlib.Tactic.IntervalCases

public section

namespace CFSG.KS.J4M4Card

open CFSG.KC.Enum CFSG.KS CFSG.KD.J4M4Card CFSG.Quasithin.J4M4Card

theorem lt_of_blt7256 {a b : Nat} (h : Nat.blt a b = true) : a < b := Eq.mp Nat.blt_eq h

theorem ite_xor7256 (c1 c2 : Bool) (x y m : Nat) :
    (if (c1 ^^ c2) = true then x ^^^ y ^^^ m else x ^^^ y) =
      (if c1 = true then x ^^^ m else x) ^^^ (if c2 = true then y ^^^ m else y) := by
  cases c1 <;> cases c2
  · rfl
  · exact Nat.xor_assoc x y m
  · change x ^^^ y ^^^ m = x ^^^ m ^^^ y
    rw [Nat.xor_assoc, Nat.xor_comm y m, ← Nat.xor_assoc]
  · change x ^^^ y = x ^^^ m ^^^ (y ^^^ m)
    rw [Nat.xor_assoc, Nat.xor_comm m (y ^^^ m), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem xorMasks_xor (ms : List Nat) (a b : Nat) :
    xorMasks ms (a ^^^ b) = xorMasks ms a ^^^ xorMasks ms b := by
  unfold xorMasks
  suffices h : ∀ (L : List Nat) (x y : Nat),
      L.foldl (fun acc k => if (a ^^^ b).testBit k then acc ^^^ ms.getD k 0 else acc) (x ^^^ y) =
        L.foldl (fun acc k => if a.testBit k then acc ^^^ ms.getD k 0 else acc) x ^^^
          L.foldl (fun acc k => if b.testBit k then acc ^^^ ms.getD k 0 else acc) y by
    have := h (List.range 11) 0 0
    rwa [Nat.xor_self] at this
  intro L
  induction L with
  | nil => intro x y; rfl
  | cons k L ih =>
    intro x y
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    rw [Nat.testBit_xor]
    exact ite_xor7256 _ _ _ _ _

theorem two_pow_add_xor {k c : Nat} (hc : c < 2 ^ k) : 2 ^ k + c = 2 ^ k ^^^ c := by
  have e := Nat.two_pow_add_eq_or_of_lt hc 1
  rw [Nat.mul_one] at e
  rw [e]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : k = j
  · subst h
    rw [Nat.testBit_lt_two_pow hc]
    simp
  · simp [h]

theorem eq_of_dbl {f g : Nat → Nat} (h0 : f 0 = g 0) : ∀ m : Nat,
    (∀ k < m, f (2 ^ k) = g (2 ^ k)) →
    (∀ k < m, ∀ c < 2 ^ k, f (2 ^ k + c) = f c ^^^ f (2 ^ k)) →
    (∀ k < m, ∀ c < 2 ^ k, g (2 ^ k + c) = g c ^^^ g (2 ^ k)) → ∀ c < 2 ^ m, f c = g c
  | 0, _, _, _, c, hc => by
    have : c = 0 := by simpa using hc
    rw [this, h0]
  | m + 1, hk, hf, hg, c, hc => by
    have ih := eq_of_dbl h0 m (fun k h => hk k (by omega)) (fun k h => hf k (by omega))
      (fun k h => hg k (by omega))
    by_cases h : c < 2 ^ m
    · exact ih c h
    · have hp : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [Nat.pow_succ]; omega
      have e : c = 2 ^ m + (c - 2 ^ m) := by omega
      rw [e, hf m (by omega) _ (by omega), hg m (by omega) _ (by omega), ih _ (by omega),
        hk m (by omega)]

theorem shl_one7256 (k : Nat) : Nat.shiftLeft 1 k = 2 ^ k := by
  change 1 <<< k = 2 ^ k
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem strictB_eq7256' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem laneK_spec {P : Nat → Nat} {lo n : Nat} (h : laneK P lo n = true) {i : Nat} (h1 : lo ≤ i)
    (h2 : i < lo + n) : ∀ c < 2048, pg 12 (mask 12) (P i) c = xorMasks (maskTab.getD i []) c := by
  have hi := Raw.Orb.allN_iff.1 h (i - lo) (by omega)
  have e : Nat.add lo (i - lo) = i := by change lo + (i - lo) = i; omega
  rw [e, strictB_eq7256', Raw.Orb.bAnd_eq, Raw.Orb.bAnd_eq, Bool.and_eq_true, Bool.and_eq_true]
    at hi
  obtain ⟨hd, h0, hk⟩ := hi
  have hk' := Raw.Orb.allN_iff.1 hk
  have hd' := Raw.Orb.allN_iff.1 hd
  intro c hc
  refine eq_of_dbl (Nat.eq_of_beq_eq_true h0) 11 (fun k hk1 => ?_) (fun k hk1 c hc => ?_)
    (fun k _ c hc => ?_) c hc
  · have := Nat.eq_of_beq_eq_true (hk' k hk1)
    rwa [shl_one7256] at this
  · have := Nat.eq_of_beq_eq_true (Raw.Orb.allN_iff.1 (hd' k hk1) c (by rwa [shl_one7256]))
    rwa [shl_one7256] at this
  · rw [two_pow_add_xor hc, xorMasks_xor, Nat.xor_comm]

@[expose] def Lin (σ : Equiv.Perm (Fin 2048)) : Prop :=
  ∀ a b c : Fin 2048, c.val = a.val ^^^ b.val → (σ c).val = (σ a).val ^^^ (σ b).val

theorem xor_lt2048 (a b : Fin 2048) : a.val ^^^ b.val < 2048 :=
  Nat.xor_lt_two_pow (n := 11) a.isLt b.isLt

theorem lin_one : Lin 1 := fun _ _ _ h => h

theorem lin_mul {σ τ : Equiv.Perm (Fin 2048)} (hσ : Lin σ) (hτ : Lin τ) : Lin (σ * τ) :=
  fun a b c h => hσ (τ a) (τ b) (τ c) (hτ a b c h)

theorem lin_inv {σ : Equiv.Perm (Fin 2048)} (hσ : Lin σ) : Lin σ⁻¹ := by
  intro a b c h
  obtain ⟨a', rfl⟩ := σ.surjective a
  obtain ⟨b', rfl⟩ := σ.surjective b
  have hd := hσ a' b' ⟨_, xor_lt2048 a' b'⟩ rfl
  have e : σ ⟨_, xor_lt2048 a' b'⟩ = c := Fin.ext (by rw [hd, h])
  rw [← e]
  simp

theorem lin_zero {σ : Equiv.Perm (Fin 2048)} (hσ : Lin σ) : σ 0 = 0 := by
  have h := hσ 0 0 0 (by simp)
  rw [Nat.xor_self] at h
  exact Fin.ext h

theorem eq_one_of_pow {σ : Equiv.Perm (Fin 2048)} (hσ : Lin σ)
    (hfix : ∀ k < 11, ∀ c : Fin 2048, c.val = 2 ^ k → σ c = c) : σ = 1 := by
  let f : Nat → Nat := fun c => if h : c < 2048 then (σ ⟨c, h⟩).val else c
  have hf : ∀ c (h : c < 2048), f c = (σ ⟨c, h⟩).val := fun c h => by simp [f, h]
  have hp : ∀ k < 11, 2 ^ k < 2048 := fun k hk => by interval_cases k <;> norm_num
  have hz : (σ ⟨0, by norm_num⟩).val = 0 := congrArg Fin.val (lin_zero hσ)
  have key := eq_of_dbl (f := f) (g := id) (by rw [hf 0 (by norm_num), hz]; rfl) 11
    (fun k hk => by rw [hf _ (hp k hk), hfix k hk ⟨_, hp k hk⟩ rfl]; rfl)
    (fun k hk c hc => by
      have h1 : 2 ^ k + c < 2048 := by
        interval_cases k <;> norm_num at hc ⊢ <;> omega
      have h2 : c < 2048 := by omega
      rw [hf _ h1, hf _ h2, hf _ (hp k hk), Nat.xor_comm]
      exact hσ ⟨_, hp k hk⟩ ⟨c, h2⟩ ⟨_, h1⟩ (two_pow_add_xor hc))
    (fun k _ c hc => by simp only [id]; rw [two_pow_add_xor hc, Nat.xor_comm])
  ext x
  have := key x.val x.isLt
  rw [hf _ x.isLt] at this
  simpa using this

@[expose] noncomputable def oFin (hO : ovK = true) (k : Fin 128) : Fin 2048 :=
  ⟨psiOv k.val, lt_of_blt7256 (Raw.Orb.allN_iff.1 hO k.val k.isLt)⟩

theorem xorL_lt (hO : ovK = true) : ∀ l : List Nat, ltL l = true → xorL l < 2048
  | [], _ => by decide
  | p :: l, hl => by
    change bAnd(Nat.blt p 128, ltL l) = true at hl
    rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hl
    have hp := lt_of_blt7256 hl.1
    have hx : xorL (p :: l) = psiOv p ^^^ xorL l := rfl
    rw [hx]
    exact xor_lt2048 (oFin hO ⟨p, hp⟩) ⟨_, xorL_lt hO l hl.2⟩

theorem fix_xorL {σ : Equiv.Perm (Fin 2048)} (hσ : Lin σ) (hO : ovK = true)
    (hfix : ∀ k, σ (oFin hO k) = oFin hO k) :
    ∀ l : List Nat, (hl : ltL l = true) → σ ⟨xorL l, xorL_lt hO l hl⟩ = ⟨xorL l, xorL_lt hO l hl⟩
  | [], _ => lin_zero hσ
  | p :: l, hl => by
    have hl' : Nat.blt p 128 = true ∧ ltL l = true := by
      change bAnd(Nat.blt p 128, ltL l) = true at hl
      rwa [Raw.Orb.bAnd_eq, Bool.and_eq_true] at hl
    have hp : p < 128 := lt_of_blt7256 hl'.1
    have hx := fix_xorL hσ hO hfix l hl'.2
    have hv : xorL (p :: l) = psiOv p ^^^ xorL l := rfl
    refine Fin.ext ?_
    have e := hσ (oFin hO ⟨p, hp⟩) ⟨_, xorL_lt hO l hl'.2⟩ ⟨_, xorL_lt hO (p :: l) hl⟩ hv
    rw [e, hfix, hx]
    exact hv.symm

theorem eq_one_of_fix (hO : ovK = true) (hs : spanK = true) {σ : Equiv.Perm (Fin 2048)}
    (hσ : Lin σ) (hfix : ∀ k, σ (oFin hO k) = oFin hO k) : σ = 1 := by
  refine eq_one_of_pow hσ fun k hk c hc => ?_
  have h := Raw.Orb.allN_iff.1 hs k hk
  rw [Raw.Orb.bAnd_eq, Bool.and_eq_true] at h
  have e := fix_xorL hσ hO hfix _ h.1
  have he : xorL (getLL psiSpan k) = 2 ^ k := by
    have := Nat.eq_of_beq_eq_true h.2
    rwa [shl_one7256] at this
  have hc' : c = ⟨xorL (getLL psiSpan k), xorL_lt hO _ h.1⟩ := Fin.ext (by rw [hc]; exact he.symm)
  rw [hc']
  exact e

theorem card_le_of_pairs {m : Nat} {σ : Fin m → Equiv.Perm (Fin 2048)}
    {τ : Fin m → Equiv.Perm (Fin 128)} (O : Fin 128 → Fin 2048) (hlin : ∀ j, Lin (σ j))
    (hc : ∀ j k, σ j (O k) = O (τ j k))
    (hfaith : ∀ ρ : Equiv.Perm (Fin 2048), Lin ρ → (∀ k, ρ (O k) = O k) → ρ = 1) :
    Nat.card (Subgroup.closure (Set.range σ)) ≤ Nat.card (Subgroup.closure (Set.range τ)) := by
  let f : Fin m → Equiv.Perm (Fin 2048) × Equiv.Perm (Fin 128) := fun j => (σ j, τ j)
  let H := Subgroup.closure (Set.range f)
  have hQ : ∀ p ∈ H, Lin p.1 ∧ ∀ k, p.1 (O k) = O (p.2 k) := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact ⟨hlin j, hc j⟩
    | one => exact ⟨lin_one, fun k => rfl⟩
    | mul x y _ _ hx hy =>
      refine ⟨lin_mul hx.1 hy.1, fun k => ?_⟩
      change x.1 (y.1 (O k)) = O (x.2 (y.2 k))
      rw [hy.2, hx.2]
    | inv x _ hx =>
      refine ⟨lin_inv hx.1, fun k => ?_⟩
      change x.1⁻¹ (O k) = O (x.2⁻¹ k)
      rw [Equiv.Perm.inv_eq_iff_eq, hx.2]
      simp
  have h1 : (H.map (MonoidHom.fst _ _)) = Subgroup.closure (Set.range σ) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have h2 : (H.map (MonoidHom.snd _ _)) = Subgroup.closure (Set.range τ) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  rw [← h1, ← h2]
  refine le_trans (Nat.card_le_card_of_surjective _ ((MonoidHom.fst _ _).subgroupMap_surjective H))
    (Nat.card_le_card_of_injective ((MonoidHom.snd _ _).subgroupMap H) ?_)
  intro p q hpq
  have h2 : p.val.2 = q.val.2 := congrArg Subtype.val hpq
  have hr := hQ (p.val * q.val⁻¹) (H.mul_mem p.2 (H.inv_mem q.2))
  have hr1 : (p.val * q.val⁻¹).1 = 1 := by
    refine hfaith _ hr.1 fun k => ?_
    rw [hr.2 k]
    change O ((p.val.2 * q.val.2⁻¹) k) = O k
    rw [h2, mul_inv_cancel]
    rfl
  have h1 : p.val.1 = q.val.1 := by
    have : p.val.1 * q.val.1⁻¹ = 1 := hr1
    exact mul_inv_eq_one.1 this
  exact Subtype.ext (Prod.ext h1 h2)

end CFSG.KS.J4M4Card

end
