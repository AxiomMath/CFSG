module

public import CFSG.Certificates.Kernel.SmithL6KWedge

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6
open CFSG.SmithE (tri applyCols)

theorem tvApply_eq_tvA (k x : Nat) : tvApply k x = tvA (tvPair k) x := by
  unfold tvApply tvA
  obtain ⟨v, φ⟩ := tvPair k
  rfl

theorem tvA_xor (p : Nat × Nat) (x y : Nat) : tvA p (x ^^^ y) = tvA p x ^^^ tvA p y := by
  unfold tvA
  rw [form_xor_right]
  cases form p.2 x <;> cases form p.2 y <;>
    simp only [Bool.true_xor, Bool.false_xor, Bool.not_true, Bool.not_false, Bool.false_eq_true,
      ↓reduceIte] <;>
    (apply Nat.eq_of_testBit_eq
     intro i
     simp only [Nat.testBit_xor]
     cases x.testBit i <;> cases y.testBit i <;> cases p.1.testBit i <;> rfl)

theorem tvA_tvA {p : Nat × Nat} (hp : TvP p) (x : Nat) : tvA p (tvA p x) = x := by
  obtain ⟨v, φ⟩ := p
  have hφv : form φ v = false := hp.2.2.2.2
  unfold tvA
  simp only
  cases hx : form φ x
  · simp [hx]
  · simp only [↓reduceIte]
    rw [form_xor_right, hx, hφv]
    simp [Nat.xor_assoc]

theorem tvA_conjP {p : Nat × Nat} (hp : TvP p) (q : Nat × Nat) (x : Nat) :
    tvA (conjP p q) x = tvA p (tvA q (tvA p x)) := by
  obtain ⟨w, ψ⟩ := p
  obtain ⟨v, φ⟩ := q
  have e1 : form (conjP (w, ψ) (v, φ)).2 x = form φ (tvA (w, ψ) x) := by
    unfold conjP tvA
    simp only
    cases hφw : form φ w <;> cases hψx : form ψ x <;>
      simp [form_xor_left, form_xor_right, hφw, hψx]
  have e2 : (conjP (w, ψ) (v, φ)).1 = tvA (w, ψ) v := rfl
  have lhs : tvA (conjP (w, ψ) (v, φ)) x =
      if form φ (tvA (w, ψ) x) then x ^^^ tvA (w, ψ) v else x := by
    rw [← e1, ← e2]
    rfl
  rw [lhs]
  generalize hy : tvA (w, ψ) x = y
  have hx : x = tvA (w, ψ) y := by rw [← hy, tvA_tvA hp]
  subst hx
  have hq : tvA (v, φ) y = if form φ y then y ^^^ v else y := rfl
  rw [hq]
  cases form φ y
  · simp only [Bool.false_eq_true, ↓reduceIte]
  · simp only [↓reduceIte]
    rw [tvA_xor]

theorem tvApply_tvImg {g u : Nat} (hg : g < 1953) (hu : u < 1953) (x : Nat) :
    tvApply (tvImg g u) x = tvApply g (tvApply u (tvApply g x)) := by
  rw [tvApply_eq_tvA, tvPair_tvImg hg hu, tvA_conjP (tvP_tvPair hg), tvApply_eq_tvA,
    tvApply_eq_tvA, tvApply_eq_tvA]

theorem tvCols_lt {k m : Nat} (hm : m < 20) : (tvCols k)[m]! < 2 ^ 20 := by
  rw [tvCols_get hm]
  exact wedge3_lt20 _ _ _

theorem applyCols_ltL {cols : Array Nat} {n : Nat} (h : ∀ m < cols.size, cols[m]! < 2 ^ n)
    (c : Nat) : applyCols cols c < 2 ^ n := by
  unfold applyCols
  have key : ∀ L : List Nat, (∀ m ∈ L, m < cols.size) → ∀ a < 2 ^ n,
      L.foldl (fun acc m => if c.testBit m then acc ^^^ cols[m]! else acc) a < 2 ^ n := by
    intro L
    induction L with
    | nil => intro _ a ha; simpa using ha
    | cons m L ih =>
      intro hL a ha
      simp only [List.foldl_cons]
      apply ih (fun x hx => hL x (List.mem_cons_of_mem _ hx))
      split_ifs
      · exact Nat.xor_lt_two_pow ha (h m (hL m List.mem_cons_self))
      · exact ha
  exact key _ (fun m hm => List.mem_range.mp hm) 0 (Nat.two_pow_pos n)

theorem applyCols_tvCols_lt (k c : Nat) : applyCols (tvCols k) c < 2 ^ 20 :=
  applyCols_ltL (fun m hm => tvCols_lt (by rw [tvCols_size] at hm; exact hm)) c

theorem tvCols_tvImg {g u : Nat} (hg : g < 1953) (hu : u < 1953) :
    ∀ x < 2 ^ 20, applyCols (tvCols (tvImg g u)) x =
      applyCols (tvCols g) (applyCols (tvCols u) (applyCols (tvCols g) x)) := by
  refine xorAdd_ext (applyCols_xorL _) (fun a b => by simp only [applyCols_xorL]) 20 ?_
  intro m hm
  obtain ⟨h0, h1, h2⟩ := tri_lt6 m hm
  have l := fun {k x : Nat} (hk : k < 1953) (hx : x < 64) => tvApply_lt hk hx
  rw [← wedge3_tri m hm, tvCols_wedge3 _ (pow_lt64 h0) (pow_lt64 h1) (pow_lt64 h2),
    tvCols_wedge3 _ (pow_lt64 h0) (pow_lt64 h1) (pow_lt64 h2),
    tvCols_wedge3 _ (l hg (pow_lt64 h0)) (l hg (pow_lt64 h1)) (l hg (pow_lt64 h2)),
    tvCols_wedge3 _ (l hu (l hg (pow_lt64 h0))) (l hu (l hg (pow_lt64 h1)))
      (l hu (l hg (pow_lt64 h2))),
    tvApply_tvImg hg hu, tvApply_tvImg hg hu, tvApply_tvImg hg hu]

theorem fB_xor_left (u u' v : Nat) : fB (u ^^^ u') v = (fB u v ^^ fB u' v) := by
  unfold fB
  have e : (fun b t => b ^^ ((u ^^^ u').testBit t && v.testBit (19 - t))) =
      fun b t => b ^^ ((u.testBit t && v.testBit (19 - t)) ^^
        (u'.testBit t && v.testBit (19 - t))) := by
    funext b t
    rw [Nat.testBit_xor]
    cases u.testBit t <;> cases u'.testBit t <;> cases v.testBit (19 - t) <;> rfl
  rw [e]
  exact foldl_xor_split _ _ _ false

theorem fB_xor_right (u v v' : Nat) : fB u (v ^^^ v') = (fB u v ^^ fB u v') := by
  unfold fB
  have e : (fun b t => b ^^ (u.testBit t && (v ^^^ v').testBit (19 - t))) =
      fun b t => b ^^ ((u.testBit t && v.testBit (19 - t)) ^^
        (u.testBit t && v'.testBit (19 - t))) := by
    funext b t
    rw [Nat.testBit_xor]
    cases u.testBit t <;> cases v.testBit (19 - t) <;> cases v'.testBit (19 - t) <;> rfl
  rw [e]
  exact foldl_xor_split _ _ _ false

theorem toNat_xorB (p q : Bool) : (p ^^ q).toNat = p.toNat ^^^ q.toNat := by
  cases p <;> cases q <;> rfl

theorem eq_of_toNatB {p q : Bool} (h : p.toNat = q.toNat) : p = q := by
  cases p <;> cases q <;> first | rfl | exact absurd h (by decide)

theorem fB_inv_of_basis {T : Nat → Nat} (hT : ∀ a b, T (a ^^^ b) = T a ^^^ T b)
    (h : ∀ a < 20, ∀ b < 20, fB (T (2 ^ a)) (T (2 ^ b)) = fB (2 ^ a) (2 ^ b)) :
    ∀ x < 2 ^ 20, ∀ y < 2 ^ 20, fB (T x) (T y) = fB x y := by
  have h1 : ∀ b < 20, ∀ x < 2 ^ 20, fB (T x) (T (2 ^ b)) = fB x (2 ^ b) := by
    intro b hb x hx
    refine eq_of_toNatB (xorAdd_ext (F := fun x => (fB (T x) (T (2 ^ b))).toNat)
      (G := fun x => (fB x (2 ^ b)).toNat) ?_ ?_ 20
      (fun a ha => by simp only [h a ha b hb]) x hx)
    · intro a a'
      simp only [hT, fB_xor_left, toNat_xorB]
    · intro a a'
      simp only [fB_xor_left, toNat_xorB]
  intro x hx y hy
  refine eq_of_toNatB (xorAdd_ext (F := fun y => (fB (T x) (T y)).toNat)
    (G := fun y => (fB x y).toNat) ?_ ?_ 20 (fun b hb => by simp only [h1 b hb x hx]) y hy)
  · intro a a'
    simp only [hT, fB_xor_right, toNat_xorB]
  · intro a a'
    simp only [fB_xor_right, toNat_xorB]

theorem reach_gens {G : List Nat} (hR : Reach 1953 G.length (· == 0)
    (fun s u v => tvImg (G.getD s 0) u == v)) (P : Nat → Prop) (h0 : P 0)
    (hstep : ∀ s < G.length, ∀ u < 1953, P u → P (tvImg (G.getD s 0) u)) :
    ∀ v < 1953, P v := by
  refine hR P (fun v _ hv => by rw [beq_iff_eq.mp hv]; exact h0) ?_
  intro s hs u hu v _ he hP
  rw [← beq_iff_eq.mp he]
  exact hstep s hs u hu hP

@[expose] def FormInv (k : Nat) : Prop :=
  ∀ x < 2 ^ 20, ∀ y < 2 ^ 20, fB (applyCols (tvCols k) x) (applyCols (tvCols k) y) = fB x y

theorem formInv_of_basis {k : Nat}
    (h : ∀ a < 20, ∀ b < 20, fB (tvCols k)[a]! (tvCols k)[b]! = fB (2 ^ a) (2 ^ b)) :
    FormInv k := by
  refine fB_inv_of_basis (applyCols_xorL _) fun a ha b hb => ?_
  rw [applyCols_powL _ (by rw [tvCols_size]; exact ha),
    applyCols_powL _ (by rw [tvCols_size]; exact hb)]
  exact h a ha b hb

theorem formInv_tvImg {g u : Nat} (hg : g < 1953) (hu : u < 1953) (hPg : FormInv g)
    (hPu : FormInv u) : FormInv (tvImg g u) := by
  intro x hx y hy
  rw [tvCols_tvImg hg hu x hx, tvCols_tvImg hg hu y hy,
    hPg _ (applyCols_tvCols_lt _ _) _ (applyCols_tvCols_lt _ _),
    hPu _ (applyCols_tvCols_lt _ _) _ (applyCols_tvCols_lt _ _), hPg x hx y hy]

theorem chkFormInv_of {G : List Nat} (hG : ∀ s < G.length, G.getD s 0 < 1953)
    (hG0 : G.getD 0 1 = 0) (hR : Reach 1953 G.length (· == 0)
      (fun s u v => tvImg (G.getD s 0) u == v))
    (hbase : ∀ s < G.length, ∀ a < 20, ∀ b < 20,
      fB (tvCols (G.getD s 0))[a]! (tvCols (G.getD s 0))[b]! = fB (2 ^ a) (2 ^ b)) :
    chkFormInv = true := by
  have hlen : 0 < G.length := by
    rcases G with _ | ⟨g, G⟩
    · simp at hG0
    · simp
  have hgd : G.getD 0 0 = 0 := by
    rcases G with _ | ⟨g, G⟩
    · simp at hlen
    · simpa using hG0
  have hall := reach_gens hR FormInv (hgd ▸ formInv_of_basis (hbase 0 hlen))
    fun s hs u hu hP => formInv_tvImg (hG s hs) hu (formInv_of_basis (hbase s hs)) hP
  unfold chkFormInv
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro k hk a ha b hb
  rw [tvArr_get hk, ← applyCols_powL _ (by rw [tvCols_size]; exact ha),
    ← applyCols_powL _ (by rw [tvCols_size]; exact hb)]
  exact hall k hk _ (Nat.pow_lt_pow_right (by decide) ha) _ (Nat.pow_lt_pow_right (by decide) hb)

end CFSG.SmithL6.K
