module

public import CFSG.Certificates.Kernel.BalanceSC.SylowEq
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.BalanceSC.TableSound

open CFSG.KC.BalanceSC CFSG.KC.BalanceSC.SylowEq
open CFSG.KC.Enum (pg pcomp pidn)
open CFSG.KS.Raw (unpack szOK)
open CFSG.KC.BfsPin (PP)
open CFSG.KC.Misc.ArrEnum (headK pointK pointsK keysK keyK permB allNP_iff pp_of_permB)
open CFSG.OddStandard.Solomon75.AhatData
open Equiv Equiv.Perm

theorem zipAll_nil_cons {α β : Type} (f : α → β → Bool) (b : β) (bs : List β) :
    zipAll f [] (b :: bs) = false := rfl

theorem zipAll_cons_nil {α β : Type} (f : α → β → Bool) (a : α) (as : List α) :
    zipAll f (a :: as) [] = false := rfl

theorem zipAll_cons_cons {α β : Type} (f : α → β → Bool) (a : α) (as : List α) (b : β)
    (bs : List β) : zipAll f (a :: as) (b :: bs) = (f a b && zipAll f as bs) := by
  change bAnd(f a b, zipAll f as bs) = _
  rw [bAnd_eq]

theorem zipAll_mem {α β : Type} {f : α → β → Bool} :
    ∀ {as : List α} {bs : List β}, zipAll f as bs = true → ∀ a ∈ as, ∃ b ∈ bs, f a b = true
  | [], _, _, a, ha => absurd ha (List.not_mem_nil)
  | _ :: _, [], h, _, _ => by rw [zipAll_cons_nil] at h; exact absurd h (by simp)
  | x :: as, y :: bs, h, a, ha => by
    rw [zipAll_cons_cons, Bool.and_eq_true] at h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨y, List.mem_cons_self, h.1⟩
    · obtain ⟨b, hb, hab⟩ := zipAll_mem h.2 a ha
      exact ⟨b, List.mem_cons_of_mem _ hb, hab⟩

theorem eqL_eq : ∀ {a b : List ℕ}, eqL a b = true → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => absurd h (by rw [eqL, zipAll_nil_cons]; simp)
  | _ :: _, [], h => absurd h (by rw [eqL, zipAll_cons_nil]; simp)
  | x :: a, y :: b, h => by
    rw [eqL, zipAll_cons_cons, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, eqL_eq h.2]

variable {n N : ℕ} {G PT : ℕ → ℕ} {E : ℕ → ℕ → ℕ} {PAR LAB : ℕ → ℕ} {PS : List ℕ}

@[expose] noncomputable def tabOf (n N : ℕ) (PT : ℕ → ℕ) : Array (Array ℕ) :=
  Array.ofFn (n := N) fun i => unpack n 4 (PT i.val)

theorem size_tabOf : (tabOf n N PT).size = N := by simp [tabOf]

theorem tabOf_getElem {i : ℕ} (hi : i < (tabOf n N PT).size) :
    (tabOf n N PT)[i] = unpack n 4 (PT i) := by
  simp [tabOf]

theorem tabOf_get {i : ℕ} (hi : i < N) : (tabOf n N PT)[i]! = unpack n 4 (PT i) := by
  rw [getElem!_pos (tabOf n N PT) i (by rw [size_tabOf]; exact hi), tabOf_getElem]

structure Checks (n N : ℕ) (G PT : ℕ → ℕ) (E : ℕ → ℕ → ℕ) (PAR LAB : ℕ → ℕ) (PS : List ℕ) :
    Prop where
  sz : szOK n 4 = true
  gsize : (gensA n).size = 3
  gen : ((List.range 3).all fun k => (List.range n).all fun i =>
    Nat.beq (((gensA n)[k]!)[i]!) (pg 4 15 (G k) i)) = true
  sq : ∀ k < 3, pcomp n 4 15 (G k) (G k) = pidn n 4
  head : headK n 4 3 N G PT = true
  points : pointsK n 4 3 N G PT E PAR LAB 0 N = true
  keys : keysK n 4 PS PT 0 N = true

variable (C : Checks n N G PT E PAR LAB PS)
include C

theorem head_facts : (∀ k < 3, PP n 4 (G k)) ∧ 0 < N ∧ PT 0 = pidn n 4 := by
  have hh := C.head
  unfold headK at hh
  simp only [Bool.and_eq_true, Nat.blt_eq] at hh
  obtain ⟨⟨hGp, hN0⟩, hT0⟩ := hh
  exact ⟨fun k hk => pp_of_permB C.sz (allNP_iff.1 hGp k hk), hN0, Nat.eq_of_beq_eq_true hT0⟩

theorem point_facts {i : ℕ} (hi : i < N) : PP n 4 (PT i) ∧
    (∀ k < 3, E i k < N ∧ PT (E i k) = pcomp n 4 15 (G k) (PT i)) ∧
    (i = 0 ∨ (PAR i < i ∧ LAB i < 3 ∧ PT i = pcomp n 4 15 (G (LAB i)) (PT (PAR i)))) := by
  have h := allNP_iff.1 C.points i hi
  simp only [Nat.add_eq, Nat.zero_add] at h
  unfold pointK at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨pp_of_permB C.sz h1, fun k hk => ?_, h3.imp id fun h => ⟨h.1.1, h.1.2, h.2⟩⟩
  have := allNP_iff.1 h2 k hk
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at this
  exact this

theorem gen_eqA {k : ℕ} (hk : k < 3) : eqA n (gensA n)[k]! (unpack n 4 (G k)) = true := by
  have h := C.gen
  rw [List.all_eq_true] at h
  have h1 := h k (List.mem_range.2 hk)
  rw [List.all_eq_true] at h1
  rw [eqA, nat_all_iff]
  intro i hi
  rw [CFSG.KS.Raw.Orb.unpack_get hi, beq_iff_eq]
  exact Nat.eq_of_beq_eq_true (h1 i (List.mem_range.2 hi))

variable [NeZero n] (hn : 8 ≤ n) (hn' : n ≤ 11)
include hn hn'

theorem gen_rep {k : ℕ} (hk : k < 3) : ∃ σ ∈ genPerms n, Rep n (unpack n 4 (G k)) σ := by
  have hmem : (gensA n)[k]! ∈ gensA n := by
    rw [getElem!_pos (gensA n) k (by rw [C.gsize]; exact hk)]
    exact Array.getElem_mem _
  obtain ⟨σ, hσ, hrep⟩ := (mem_gensA hn hn').1 _ hmem
  exact ⟨σ, hσ, rep_of_eqA_left hrep (gen_eqA C hk)⟩

theorem rep_gen {σ : Perm (Fin n)} (hσ : σ ∈ genPerms n) :
    ∃ k < 3, Rep n (unpack n 4 (G k)) σ := by
  obtain ⟨x, hx, hrep⟩ := (mem_gensA hn hn').2 σ hσ
  obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
  have hk3 : k < 3 := by rw [← C.gsize]; exact hk
  refine ⟨k, hk3, rep_of_eqA_left ?_ (gen_eqA C hk3)⟩
  rw [getElem!_pos (gensA n) k hk]
  exact hrep

theorem gen_sq {σ : Perm (Fin n)} (hσ : σ ∈ genPerms n) : σ * σ = 1 := by
  obtain ⟨k, hk, hrep⟩ := rep_gen C hn hn' hσ
  have hG := (head_facts C).1 k hk
  have h1 := rep_mulA hrep hrep
  rw [mulA_u hG hG, C.sq k hk, ← idA_u C.sz] at h1
  exact Rep.unique h1 rep_idA

theorem pt_mem {i : ℕ} (hi : i < N) : ∃ σ ∈ P0 n, Rep n (unpack n 4 (PT i)) σ := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain ⟨-, -, hpar⟩ := point_facts C hi
    rcases hpar with rfl | ⟨hp, hl, he⟩
    · refine ⟨1, one_mem _, ?_⟩
      rw [(head_facts C).2.2, ← idA_u C.sz]
      exact rep_idA
    · obtain ⟨σ, hσ, hrep⟩ := ih (PAR i) hp (by omega)
      obtain ⟨τ, hτ, hτrep⟩ := gen_rep C hn hn' hl
      have h1 := rep_mulA hτrep hrep
      rw [mulA_u ((head_facts C).1 _ hl) (point_facts C (by omega : PAR i < N)).1, ← he] at h1
      exact ⟨τ * σ, mul_mem (Subgroup.subset_closure hτ) hσ, h1⟩

theorem pt_surj {σ : Perm (Fin n)} (hσ : σ ∈ P0 n) :
    ∃ i < N, Rep n (unpack n 4 (PT i)) σ := by
  have step : ∀ x y : Perm (Fin n), x ∈ genPerms n → (∃ i < N, Rep n (unpack n 4 (PT i)) y) →
      ∃ i < N, Rep n (unpack n 4 (PT i)) (x * y) := by
    rintro x y hx ⟨i, hi, hy⟩
    obtain ⟨k, hk, hxr⟩ := rep_gen C hn hn' hx
    obtain ⟨hpp, hed, -⟩ := point_facts C hi
    have h1 := rep_mulA hxr hy
    rw [mulA_u ((head_facts C).1 k hk) hpp, ← (hed k hk).2] at h1
    exact ⟨E i k, (hed k hk).1, h1⟩
  refine Subgroup.closure_induction_left
    (p := fun x _ => ∃ i < N, Rep n (unpack n 4 (PT i)) x) ?_ ?_ ?_ hσ
  · refine ⟨0, (head_facts C).2.1, ?_⟩
    rw [(head_facts C).2.2, ← idA_u C.sz]
    exact rep_idA
  · intro x hx y _ ih
    exact step x y hx ih
  · intro x hx y _ ih
    have : x⁻¹ = x := inv_eq_of_mul_eq_one_right (gen_sq C hn hn' hx)
    rw [this]
    exact step x y hx ih

theorem tableSpec_of_checks : TableSpec n (tabOf n N PT) N := by
  refine ⟨size_tabOf, fun a ha => ?_, fun σ hσ => ?_, fun k l hk hl σ hkσ hlσ => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 ha
    rw [tabOf_getElem]
    exact pt_mem C hn hn' (by rw [size_tabOf] at hi; exact hi)
  · obtain ⟨i, hi, hrep⟩ := pt_surj C hn hn' hσ
    refine ⟨unpack n 4 (PT i), ?_, hrep⟩
    rw [← tabOf_get hi]
    rw [getElem!_pos (tabOf n N PT) i (by rw [size_tabOf]; exact hi)]
    exact Array.getElem_mem _
  · rw [tabOf_getElem] at hkσ hlσ
    rw [size_tabOf] at hk hl
    have heq : eqA n (unpack n 4 (PT k)) (unpack n 4 (PT l)) = true := (eqA_iff hkσ hlσ).2 rfl
    rw [eqA_u (point_facts C hk).1 (point_facts C hl).1] at heq
    have hPT := Nat.eq_of_beq_eq_true heq
    have hkeys := C.keys
    unfold keysK at hkeys
    by_contra hne
    have key : ∀ a b, a < N → b < a → PT a = PT b → False := by
      intro a b ha hb hab
      have h1 := allNP_iff.1 (allNP_iff.1 hkeys a ha) b (by simpa using hb)
      simp only [Nat.add_eq, Nat.zero_add, hab, Nat.beq_refl, Bool.not_true] at h1
      exact absurd h1 (by simp)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact key l k hl h hPT.symm
    · exact key k l hk h hPT

omit hn hn' [NeZero n] in
theorem bind_of_checks : Bind n N PT (tabOf n N PT) :=
  ⟨C.sz, (head_facts C).2.1, size_tabOf, fun _ hi => tabOf_get hi,
    fun _ hi => (point_facts C hi).1⟩

theorem sylow_of_checks {I ORD : List ℕ} (hI : eqL I (isoIdxK n N PT) = true)
    (h1 : nbrK n PT I = true) (h2 : connK n PT I ORD = true) (h3 : rankK n PT I = true)
    (h4 : eightK n PT I = true) (h5 : halfK n N PT I = true) :
    Nat.card (P0 n) = N ∧ SylowGood n (P0 n) := by
  have T := tableSpec_of_checks C hn hn'
  have B := bind_of_checks C
  have hI' : (isoIdx n (tabOf n N PT)).toList = I := (isoIdx_eq B).trans (eqL_eq hI).symm
  obtain ⟨h8a, h8b⟩ := eight_of_eightOK T (by rw [eightOK_eq B hI']; exact h4)
  exact ⟨T.card_eq, nbr_of_nbrOK T (by rw [nbrOK_eq B hI']; exact h1),
    conn_of_connOK T (ord := ORD.toArray) (by rw [connOK_eq B hI' ORD]; exact h2),
    rank_of_rankOK T (by rw [rankOK_eq B hI']; exact h3), h8a, h8b,
    half_of_halfOK T (by rw [halfOK_eq B hI']; exact h5)⟩

end CFSG.KC.BalanceSC.TableSound

end
