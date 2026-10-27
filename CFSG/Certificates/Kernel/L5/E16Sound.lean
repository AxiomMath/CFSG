module

public import Certificates.Data.Kernel.L5E16.Defs
public import CFSG.Certificates.Kernel.L5.Fast
public import CFSG.GH74.GLS.C3.Layer2.L5C3Inputs
public import Mathlib.Algebra.Order.Ring.Star
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Certificates.Kernel.L5E16S

open CFSG.KC.L5E16 CFSG.Certificates.Kernel.PkCV CFSG.Certificates CFSG.KC.Enum CFSG.KS
  CFSG.KS.PF CFSG.KS.PinvS CFSG.Certificates.Kernel.PkEnum
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.Model

theorem bAnd_eq (a b : Bool) : Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

theorem bIf_eq (c t e : Bool) : Bool.rec (motive := fun _ => Bool) e t c = (if c then t else e) := by
  cases c <;> rfl

theorem memK_iff (x : Nat) : ∀ L : List Nat, memK x L = true ↔ x ∈ L
  | [] => by simp [memK]
  | a :: L => by
    have ih := memK_iff x L
    change Bool.rec (motive := fun _ => Bool) (memK x L) true (Nat.beq a x) = true ↔ _
    rw [bIf_eq, List.mem_cons]
    cases h : Nat.beq a x
    · have hne : a ≠ x := Nat.ne_of_beq_eq_false h
      simp only [Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · exact Or.inr
      · rintro (e | e)
        · exact absurd e.symm hne
        · exact e
    · simp only [↓reduceIte, true_iff]
      exact Or.inl (Nat.eq_of_beq_eq_true h).symm

theorem allL_iff (f : Nat → Bool) : ∀ L : List Nat, allL L f = true ↔ ∀ a ∈ L, f a = true
  | [] => by simp [allL]
  | a :: L => by
    have ih := allL_iff f L
    change Bool.rec (motive := fun _ => Bool) false (allL L f) (f a) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem cntK_eq (one t : Nat) : ∀ S : List Nat, cntK one S t = (S.filter (cmI one t)).length
  | [] => rfl
  | u :: S => by
    change Bool.rec (motive := fun _ => Nat) (cntK one S t) (Nat.succ (cntK one S t))
      (cmI one t u) = _
    rw [List.filter_cons, cntK_eq one t S]
    cases cmI one t u <;> rfl

@[expose] noncomputable def code (x : Equiv.Perm (Fin 16)) : Nat := (cOf x).1

theorem code_injective : Function.Injective code := fun x y h => by
  have e : cOf x = cOf y := Subtype.ext h
  rw [← ev_cOf x, ← ev_cOf y, e]

theorem wC16 : wC 16 = 5 := by
  unfold wC
  rw [(Nat.log2_eq_iff (n := 17) (k := 4) (by norm_num)).2 ⟨by norm_num, by norm_num⟩]

theorem cOf_mul (x y : Equiv.Perm (Fin 16)) : cOf (x * y) = cOf x * cOf y :=
  ev_injective (by rw [ev_mul, ev_cOf, ev_cOf, ev_cOf])

theorem code_mul (x y : Equiv.Perm (Fin 16)) : code (x * y) = mul16 (code x) (code y) := by
  unfold code
  rw [cOf_mul]
  change pcomp 16 (wC 16) (mask (wC 16)) (cOf x).1 (cOf y).1 = _
  rw [wC16]
  rfl

theorem cmI_code (one : Nat) (hone : code 1 = one) (t u : Equiv.Perm (Fin 16)) :
    cmI one (code t) (code u) = decide (u ≠ 1 ∧ u * u = 1 ∧ t * u = u * t) := by
  unfold cmI invB
  rw [bAnd_eq, bAnd_eq, ← hone, ← code_mul, ← code_mul, ← code_mul]
  have e : ∀ a b : Equiv.Perm (Fin 16), Nat.beq (code a) (code b) = decide (a = b) := by
    intro a b
    cases h : decide (a = b)
    · exact Bool.eq_false_iff.2 fun h' =>
        (decide_eq_false_iff_not.1 h) (code_injective (Nat.eq_of_beq_eq_true h'))
    · rw [decide_eq_true_iff.1 h]
      exact Nat.beq_refl _
  rw [e, e, e]
  by_cases a : u = 1 <;> by_cases b : u * u = 1 <;> by_cases c : t * u = u * t <;> simp [a, b, c]

theorem closureList_nodup (gens : List (Equiv.Perm (Fin 16))) (k : Nat) :
    (closureList gens (k + 1)).Nodup := by
  unfold closureList
  rw [Function.iterate_succ_apply']
  exact List.nodup_dedup _

theorem code_mem_of_closedK {S G : List Nat} {one : Nat} (gens : List (Equiv.Perm (Fin 16)))
    (k : Nat) (hone : code 1 = one) (hG : gens.map code = G) (h : closedK one S G = true) :
    ∀ x ∈ closureList gens k, code x ∈ S := by
  unfold closedK at h
  rw [bAnd_eq, Bool.and_eq_true, memK_iff, allL_iff] at h
  obtain ⟨h1, hc⟩ := h
  have step : ∀ a, code a ∈ S → ∀ g ∈ gens, code (a * g) ∈ S := by
    intro a ha g hg
    have h2 := (allL_iff _ G).1 (hc _ ha) (code g) (hG ▸ List.mem_map_of_mem hg)
    rw [memK_iff] at h2
    rw [code_mul]
    exact h2
  intro x hx
  unfold closureList at hx
  induction k generalizing x with
  | zero =>
    rw [Function.iterate_zero, id, List.mem_singleton] at hx
    rw [hx, hone]
    exact h1
  | succ k ih =>
    rw [Function.iterate_succ_apply'] at hx
    unfold closureStep at hx
    rw [List.mem_dedup, List.mem_append, List.mem_flatMap] at hx
    rcases hx with hx | ⟨a, ha, hx⟩
    · exact ih x hx
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hx
      exact step a (ih a ha) g hg

theorem e16Chk_of_sub {S RC : List Nat} {one : Nat} {L R : List (Equiv.Perm (Fin 16))}
    (hone : code 1 = one) (hnd : L.Nodup) (hsub : ∀ x ∈ L, code x ∈ S)
    (hR : R.map code = RC) (he : e16K one S RC = true) : e16Chk L R = true := by
  have hsp : (L.map code).Subperm S :=
    List.subperm_of_subset (hnd.map code_injective) fun c hc => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      exact hsub x hx
  unfold e16K at he
  rw [allL_iff] at he
  unfold e16Chk
  simp only [map_nrm, List.all_eq_true]
  intro t ht
  by_cases hc : t ≠ 1 ∧ t * t = 1 ∧ t ∉ R
  · rw [decide_eq_true hc]
    change decide ((L.filter fun u => decide (u ≠ 1 ∧ u * u = 1 ∧ t * u = u * t)).length < 15)
      = true
    obtain ⟨h1, h2, h3⟩ := hc
    have hinv : invB one (code t) = true := by
      have := cmI_code one hone t t
      unfold cmI at this
      rw [bAnd_eq, decide_eq_true ⟨h1, h2, rfl⟩, Bool.and_eq_true] at this
      exact this.1
    have hR' : memK (code t) RC = false := by
      cases e : memK (code t) RC
      · rfl
      · rw [memK_iff, ← hR] at e
        obtain ⟨r, hr, er⟩ := List.mem_map.1 e
        exact absurd (code_injective er ▸ hr) h3
    have hb := he (code t) (hsub t ht)
    rw [hinv, hR'] at hb
    change Nat.blt (cntK one S (code t)) 15 = true at hb
    rw [Nat.blt_eq, cntK_eq] at hb
    have hf : L.filter (fun u => decide (u ≠ 1 ∧ u * u = 1 ∧ t * u = u * t)) =
        L.filter (cmI one (code t) ∘ code) :=
      List.filter_congr fun u _ => by rw [Function.comp_apply, cmI_code one hone]
    have hl : (L.filter (cmI one (code t) ∘ code)).length ≤
        (S.filter (cmI one (code t))).length := by
      rw [← List.length_map (f := code), ← List.filter_map]
      exact (hsp.filter _).length_le
    rw [hf, decide_eq_true_iff]
    omega
  · rw [decide_eq_false hc]
    rfl

theorem e16Chk_of {S G R : List Nat} {one : Nat} (hone : code 1 = one)
    (hG : sh1Gens.map code = G) (hR : RhatL1.map code = R) (hcl : closedK one S G = true)
    (he : e16K one S R = true) : e16Chk Sh1L RhatL1 = true := by
  have e : Sh1L = closureList sh1Gens (11 + 1) := rfl
  rw [e]
  exact e16Chk_of_sub hone (closureList_nodup sh1Gens 11)
    (code_mem_of_closedK sh1Gens _ hone hG hcl) hR he

end CFSG.Certificates.Kernel.L5E16S

end
