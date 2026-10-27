module

public import Mathlib.Data.List.GetD
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

structure CodeIso (H : Type*) [Group H] (N : ℕ) (mul : ℕ → ℕ → ℕ) where
  f : H → ℕ
  lt : ∀ h, f h < N
  inj : Function.Injective f
  surj : ∀ c, c < N → ∃ h, f h = c
  map_mul : ∀ x y, f (x * y) = mul (f x) (f y)

@[expose] def cconj (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (g h : ℕ) : ℕ := mul (mul g h) (inv g)

namespace CodeIso

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul)

@[expose] noncomputable def g (c : ℕ) : H := if h : c < N then (Φ.surj c h).choose else 1

theorem f_g {c : ℕ} (hc : c < N) : Φ.f (Φ.g c) = c := by
  unfold g
  split
  · exact (Φ.surj c ‹_›).choose_spec
  · exact absurd hc ‹_›

theorem g_f (h : H) : Φ.g (Φ.f h) = h := Φ.inj (Φ.f_g (Φ.lt h))

omit Φ in
theorem pos (Φ : CodeIso H N mul) : 0 < N := lt_of_le_of_lt (Nat.zero_le _) (Φ.lt 1)

theorem f_eq_iff {x y : H} : Φ.f x = Φ.f y ↔ x = y := Φ.inj.eq_iff

theorem f_one (h0 : mul 0 0 = 0) : Φ.f 1 = 0 := by
  obtain ⟨e, he⟩ := Φ.surj 0 Φ.pos
  have : e * e = e := Φ.inj (by rw [Φ.map_mul, he, h0])
  rw [← he, mul_eq_left.1 this]

theorem f_inv (h0 : mul 0 0 = 0) {x : H} {c : ℕ} (hc : c < N) (h : mul (Φ.f x) c = 0) :
    Φ.f x⁻¹ = c := by
  have : x * Φ.g c = 1 := Φ.inj (by rw [Φ.map_mul, Φ.f_g hc, h, Φ.f_one h0])
  rw [← eq_inv_of_mul_eq_one_right this, Φ.f_g hc]

theorem f_conj (h0 : mul 0 0 = 0) {inv : ℕ → ℕ} (hinv : ∀ c, c < N → inv c < N ∧ mul c (inv c) = 0)
    (x y : H) : Φ.f (x * y * x⁻¹) = cconj mul inv (Φ.f x) (Φ.f y) := by
  rw [Φ.map_mul, Φ.map_mul, Φ.f_inv h0 (hinv _ (Φ.lt x)).1 (hinv _ (Φ.lt x)).2, cconj]

theorem card_eq (P : ℕ → Bool) :
    Nat.card {h : H // P (Φ.f h) = true} = ((List.range N).filter P).length := by
  have e : {h : H // P (Φ.f h) = true} ≃ {c : ℕ // c ∈ (List.range N).filter P} :=
    { toFun := fun h => ⟨Φ.f h.1, List.mem_filter.2 ⟨List.mem_range.2 (Φ.lt _), h.2⟩⟩
      invFun := fun c => ⟨Φ.g c.1, by
        obtain ⟨h1, h2⟩ := List.mem_filter.1 c.2
        rw [Φ.f_g (List.mem_range.1 h1)]; exact h2⟩
      left_inv := fun h => Subtype.ext (Φ.g_f h.1)
      right_inv := fun c => Subtype.ext (Φ.f_g (List.mem_range.1 (List.mem_filter.1 c.2).1)) }
  rw [Nat.card_congr e, Nat.subtype_card ((List.range N).filter P).toFinset
    (fun c => List.mem_toFinset), List.toFinset_card_of_nodup ((List.nodup_range).filter _)]

omit Φ in
theorem card_univ (Φ : CodeIso H N mul) : Nat.card H = N := by
  have h := Φ.card_eq (fun _ => true)
  rw [List.filter_true, List.length_range] at h
  rw [← h]
  exact (Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => rfl)).symm

omit Φ in
theorem finite (Φ : CodeIso H N mul) : Finite H :=
  Nat.finite_of_card_ne_zero (by rw [Φ.card_univ]; exact Φ.pos.ne')

@[expose] def ofEquiv {H' : Type*} [Group H'] (e : H' ≃* H) : CodeIso H' N mul where
  f x := Φ.f (e x)
  lt x := Φ.lt _
  inj _ _ h := e.injective (Φ.inj h)
  surj c hc := by
    obtain ⟨h, hh⟩ := Φ.surj c hc
    exact ⟨e.symm h, by simp [hh]⟩
  map_mul x y := by simp [Φ.map_mul]

end CodeIso

inductive Reach (mul : ℕ → ℕ → ℕ) (gens : List ℕ) : ℕ → Prop
  | zero : Reach mul gens 0
  | step {c g : ℕ} : Reach mul gens c → g ∈ gens → Reach mul gens (mul c g)

@[expose] def Gen (mul : ℕ → ℕ → ℕ) (gens : List ℕ) (N : ℕ) : Prop := ∀ c, c < N → Reach mul gens c

namespace CodeIso

variable {H : Type*} [Group H] {N : ℕ} {mul : ℕ → ℕ → ℕ} (Φ : CodeIso H N mul)

theorem induction (h0 : mul 0 0 = 0) {gens : List ℕ} (hgens : ∀ g ∈ gens, g < N)
    (hG : Gen mul gens N) {P : H → Prop} (h1 : P 1) (hstep : ∀ h, P h → ∀ g ∈ gens, P (h * Φ.g g))
    (h : H) : P h := by
  have key : ∀ c, Reach mul gens c → ∃ x, Φ.f x = c ∧ P x := by
    intro c hc
    induction hc with
    | zero => exact ⟨1, Φ.f_one h0, h1⟩
    | step _ hg ih =>
      obtain ⟨x, rfl, hx⟩ := ih
      exact ⟨x * Φ.g _, by rw [Φ.map_mul, Φ.f_g (hgens _ hg)], hstep x hx _ hg⟩
  obtain ⟨x, hx, hP⟩ := key _ (hG _ (Φ.lt h))
  rwa [Φ.inj hx] at hP

end CodeIso

@[expose] def treeOK (mul : ℕ → ℕ → ℕ) (gens : List ℕ) (N : ℕ) (par pj dep : ℕ → ℕ) : Bool :=
  (List.range N).all fun c => c == 0 || (decide (pj c < gens.length) &&
    mul (par c) (gens.getD (pj c) 0) == c && decide (par c < N) && decide (dep (par c) < dep c))

theorem gen_of_treeOK {mul : ℕ → ℕ → ℕ} {gens : List ℕ} {N : ℕ} {par pj dep : ℕ → ℕ}
    (h : treeOK mul gens N par pj dep = true) : Gen mul gens N := by
  unfold treeOK at h
  have key : ∀ d c, dep c < d → c < N → Reach mul gens c := by
    intro d
    induction d with
    | zero => intro c hc; omega
    | succ d ih =>
      intro c hc hcN
      by_cases h0 : c = 0
      · rw [h0]; exact Reach.zero
      have hc' := List.all_eq_true.1 h c (List.mem_range.2 hcN)
      simp only [Bool.or_eq_true, beq_iff_eq, h0, false_or, Bool.and_eq_true,
        decide_eq_true_eq] at hc'
      obtain ⟨⟨⟨hpj, hmul⟩, hpar⟩, hdep⟩ := hc'
      rw [← hmul]
      exact Reach.step (ih _ (by omega) hpar)
        (by rw [List.getD_eq_getElem _ _ hpj]; exact List.getElem_mem hpj)
  exact fun c hc => key _ c (Nat.lt_succ_self _) hc

end CFSG.EvenSmallLie.OmegaEight.SpBranch
