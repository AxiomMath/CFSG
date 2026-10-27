module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.OrthCentEntries

public section

namespace CFSG.HardMathSupport.Cooperstein.StructureLie

variable {n : ℕ} {F : Type} [Field F]

abbrev bar {n : ℕ} : Fin n ⊕ Fin n → Fin n ⊕ Fin n := Sum.swap

theorem bar_bar (x : Fin n ⊕ Fin n) : bar (bar x) = x := Sum.swap_swap x

theorem bar_ne (x : Fin n ⊕ Fin n) : bar x ≠ x := by
  rcases x with x | x <;> simp [bar]

theorem bar_inj {x y : Fin n ⊕ Fin n} : bar x = bar y ↔ x = y :=
  ⟨fun h => by simpa [bar_bar] using congrArg bar h, fun h => by rw [h]⟩

theorem bar_kap (m : Fin n) (r : Bool) : bar (kap m r) = kap m (!r) := by
  cases r <;> simp [bar, kap]

@[expose] def HM (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (p r : Fin n ⊕ Fin n) : Prop :=
  ∀ x y, G x p * (if y = bar r then 1 else 0) - G x r * (if y = bar p then 1 else 0) =
    (if x = p then 1 else 0) * G (bar r) y - (if x = r then 1 else 0) * G (bar p) y

variable {G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F} {p r : Fin n ⊕ Fin n}

theorem HM.col_p (h : HM G p r) (hpr : p ≠ r) (x : Fin n ⊕ Fin n) :
    G x p = (if x = p then G (bar r) (bar r) else 0) - (if x = r then G (bar p) (bar r) else 0) := by
  have := h x (bar r)
  have hne : bar r ≠ bar p := fun e => hpr (bar_inj.mp e).symm
  simpa [hne] using this

theorem HM.col_r (h : HM G p r) (hpr : p ≠ r) (x : Fin n ⊕ Fin n) :
    G x r = (if x = r then G (bar p) (bar p) else 0) - (if x = p then G (bar r) (bar p) else 0) := by
  have := h x (bar p)
  have hne : bar p ≠ bar r := fun e => hpr (bar_inj.mp e)
  have : - G x r = (if x = p then 1 else 0) * G (bar r) (bar p) -
      (if x = r then 1 else 0) * G (bar p) (bar p) := by simpa [hne] using this
  simp only [ite_mul, one_mul, zero_mul] at this
  linear_combination (-1 : F) * this

theorem HM.row_bar (h : HM G p r) (hpr : p ≠ r) {y : Fin n ⊕ Fin n} (hy1 : y ≠ bar r)
    (hy2 : y ≠ bar p) : G (bar r) y = 0 ∧ G (bar p) y = 0 := by
  constructor
  · have := h p y
    simpa [hy1, hy2, hpr] using this.symm
  · have := h r y
    simpa [hy1, hy2, hpr.symm] using this

structure Cfg (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (P : Set (Fin n ⊕ Fin n)) : Prop where
  disj : ∀ p ∈ P, bar p ∉ P
  hm : ∀ p ∈ P, ∀ r, bar r ∉ P → r ≠ p → HM G p r
  two : ∀ p ∈ P, ∃ r₁ r₂, r₁ ≠ r₂ ∧ (bar r₁ ∉ P ∧ r₁ ≠ p) ∧ (bar r₂ ∉ P ∧ r₂ ≠ p)

namespace Cfg

variable {P : Set (Fin n ⊕ Fin n)} (C : Cfg G P)
include C

theorem exists_ne (hp : p ∈ P) (x : Fin n ⊕ Fin n) :
    ∃ r, (bar r ∉ P ∧ r ≠ p) ∧ r ≠ x := by
  obtain ⟨r₁, r₂, h12, h1, h2⟩ := C.two p hp
  by_cases h : r₁ = x
  · exact ⟨r₂, h2, fun e => h12 (h.trans e.symm)⟩
  · exact ⟨r₁, h1, h⟩

theorem col_p_zero (hp : p ∈ P) {x : Fin n ⊕ Fin n} (hx : x ≠ p) : G x p = 0 := by
  obtain ⟨r, ⟨hr1, hr2⟩, hrx⟩ := C.exists_ne hp x
  rw [(C.hm p hp r hr1 hr2).col_p hr2.symm x]
  simp [hx, hrx.symm]

theorem diag_p (hp : p ∈ P) {r : Fin n ⊕ Fin n} (hr1 : bar r ∉ P) (hr2 : r ≠ p) :
    G p p = G (bar r) (bar r) := by
  rw [(C.hm p hp r hr1 hr2).col_p hr2.symm p]
  simp [hr2.symm]

theorem diag_r (hp : p ∈ P) {r : Fin n ⊕ Fin n} (hr1 : bar r ∉ P) (hr2 : r ≠ p) :
    G r r = G (bar p) (bar p) := by
  rw [(C.hm p hp r hr1 hr2).col_r hr2.symm r]
  simp [hr2]

theorem row_bar_zero (hp : p ∈ P) {y : Fin n ⊕ Fin n} (hy : y ≠ bar p) : G (bar p) y = 0 := by
  obtain ⟨r₁, r₂, h12, h1, h2⟩ := C.two p hp
  by_cases h : y = bar r₁
  · exact ((C.hm p hp r₂ h2.1 h2.2).row_bar h2.2.symm
      (by rw [h]; exact fun e => h12 (bar_inj.mp e)) hy).2
  · exact ((C.hm p hp r₁ h1.1 h1.2).row_bar h1.2.symm h hy).2

end Cfg

@[expose] def Qf (n : ℕ) (v : Fin n ⊕ Fin n → F) : F := ∑ i : Fin n, v (.inl i) * v (.inr i)

@[expose] def Bf (n : ℕ) (v w : Fin n ⊕ Fin n → F) : F := ∑ x, v x * w (bar x)

theorem Qf_add (v w : Fin n ⊕ Fin n → F) : Qf n (v + w) = Qf n v + Qf n w + Bf n v w := by
  simp only [Qf, Bf, Pi.add_apply, Fintype.sum_sum_type, bar, Sum.swap_inl, Sum.swap_inr]
  have h : ∀ i : Fin n, (v (.inl i) + w (.inl i)) * (v (.inr i) + w (.inr i)) =
      v (.inl i) * v (.inr i) + w (.inl i) * w (.inr i) +
        (v (.inl i) * w (.inr i) + v (.inr i) * w (.inl i)) := fun i => by ring
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp only [Finset.sum_add_distrib]

theorem Qf_single (q : Fin n ⊕ Fin n) : Qf n (Pi.single q (1 : F)) = 0 := by
  unfold Qf
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : Sum.inl i = q
  · subst h; simp
  · simp [Pi.single_apply, Ne.symm h]

theorem Bf_single (q q' : Fin n ⊕ Fin n) :
    Bf n (Pi.single q (1 : F)) (Pi.single q' 1) = if q' = bar q then 1 else 0 := by
  unfold Bf
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul]
  simp [eq_comm]

theorem orth_cols (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v) (q q' : Fin n ⊕ Fin n) :
    ∑ x, G x q * G (bar x) q' = if q' = bar q then 1 else 0 := by
  have h1 := hQ (Pi.single q 1 + Pi.single q' 1)
  have hq := hQ (Pi.single q 1)
  have hq' := hQ (Pi.single q' 1)
  rw [Matrix.mulVec_add, Qf_add, Qf_add, hq, hq', Qf_single, Qf_single] at h1
  have hc : ∀ q'' : Fin n ⊕ Fin n, G.mulVec (Pi.single q'' (1 : F)) = fun x => G x q'' := fun q'' => by
    ext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc, hc] at h1
  have := Bf_single (F := F) q q'
  unfold Bf at h1 this
  rw [← this]
  linear_combination h1

theorem sq_eq_one [CharP F 2] {a : F} (h : a * a = 1) : a = 1 := by
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have : (a - 1) * (a - 1) = 0 := by linear_combination h + (1 - a) * h2
  exact sub_eq_zero.mp (mul_self_eq_zero.mp this)

namespace Cfg

variable {P : Set (Fin n ⊕ Fin n)} (C : Cfg G P)
include C

theorem lam_mu (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v) (hp : p ∈ P) :
    G p p * G (bar p) (bar p) = 1 := by
  have h := orth_cols hQ p (bar p)
  rw [Finset.sum_eq_single p (fun x _ hx => by rw [C.col_p_zero hp hx, zero_mul])
    (fun h => absurd (Finset.mem_univ p) h)] at h
  simpa using h

theorem lam_one_free [CharP F 2] (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v) (hp : p ∈ P)
    {r : Fin n ⊕ Fin n} (h1 : bar r ∉ P) (h2 : r ≠ p) (h3 : r ∉ P) (h4 : bar r ≠ p) :
    G p p = 1 := by
  have e1 := C.diag_p hp h1 h2
  have e2 := C.diag_r hp (r := bar r) (by rwa [bar_bar]) h4
  have := C.lam_mu hQ hp
  rw [← e2, ← e1] at this
  exact sq_eq_one this

theorem lam_one_three [CharP F 2] (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v) {p p' p'' : Fin n ⊕ Fin n}
    (hp : p ∈ P) (hp' : p' ∈ P) (hp'' : p'' ∈ P) (h1 : p ≠ p') (h2 : p ≠ p'') (h3 : p' ≠ p'') :
    G p p = 1 := by
  have key : ∀ {a b : Fin n ⊕ Fin n}, a ∈ P → b ∈ P → a ≠ b → G a a * G b b = 1 := by
    intro a b ha hb hab
    have := C.lam_mu hQ ha
    rwa [← C.diag_r ha (r := b) (C.disj b hb) hab.symm] at this
  have k1 := key hp hp' h1
  have k2 := key hp hp'' h2
  have k3 := key hp' hp'' h3
  have hne : G p p ≠ 0 := fun h => by simp [h] at k1
  have heq : G p' p' = G p'' p'' := mul_left_cancel₀ hne (by rw [k1, k2])
  rw [← heq] at k3
  have h1' := sq_eq_one k3
  rw [h1', mul_one] at k1
  exact k1

theorem delta [CharP F 2] (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v) (hl : ∀ p ∈ P, G p p = 1)
    (hP2 : ∀ p ∈ P, ∃ p' ∈ P, p' ≠ p) (hne : P.Nonempty) (x y : Fin n ⊕ Fin n)
    (h : ¬ (x ∈ P ∧ bar y ∈ P)) : G x y = if x = y then 1 else 0 := by
  have hmu : ∀ p ∈ P, G (bar p) (bar p) = 1 := fun p hp => by
    have := C.lam_mu hQ hp
    rwa [hl p hp, one_mul] at this
  by_cases hyP : y ∈ P
  · by_cases hxy : x = y
    · subst hxy
      simp [hl x hyP]
    · rw [C.col_p_zero hyP hxy]
      simp [hxy]
  · by_cases hby : bar y ∈ P
    · obtain ⟨p, hp, rfl⟩ : ∃ p ∈ P, y = bar p := ⟨bar y, hby, (bar_bar y).symm⟩
      have hxP : x ∉ P := fun hx => h ⟨hx, hby⟩
      by_cases hxb : bar x ∈ P
      · obtain ⟨p', hp', rfl⟩ : ∃ p' ∈ P, x = bar p' := ⟨bar x, hxb, (bar_bar x).symm⟩
        by_cases hpp : p' = p
        · subst hpp
          simp [hmu p' hp']
        · rw [C.row_bar_zero hp' (fun e => hpp (bar_inj.mp e).symm)]
          have : bar p' ≠ bar p := fun e => hpp (bar_inj.mp e)
          simp [this]
      · obtain ⟨p', hp', hp'p⟩ := hP2 p hp
        have hr1 : bar (bar x) ∉ P := by rwa [bar_bar]
        have hr2 : bar x ≠ p' := fun e => hxb (e ▸ hp')
        have := ((C.hm p' hp' (bar x) hr1 hr2).row_bar hr2.symm
          (y := bar p) (by rw [bar_bar]; exact fun e => hxb (by rw [← e, bar_bar]; exact hp))
          (fun e => hp'p (bar_inj.mp e).symm)).1
        rw [bar_bar] at this
        rw [this]
        have hxy : x ≠ bar p := fun e => hxb (by rw [e, bar_bar]; exact hp)
        simp [hxy]
    · obtain ⟨p, hp⟩ := hne
      obtain ⟨p', hp', hp'p⟩ := hP2 p hp
      have hyp : y ≠ p := fun e => hyP (e ▸ hp)
      have hyp' : y ≠ p' := fun e => hyP (e ▸ hp')
      have hcol := (C.hm p hp y hby hyp).col_r hyp.symm x
      have hz := ((C.hm p' hp' y hby hyp').row_bar hyp'.symm
        (y := bar p) (fun e => hyp (bar_inj.mp e).symm) (fun e => hp'p (bar_inj.mp e).symm)).1
      rw [hcol, hz, hmu p hp]
      by_cases hxy : x = y <;> simp [hxy]

end Cfg

theorem Bf_single_left (q : Fin n ⊕ Fin n) (w : Fin n ⊕ Fin n → F) :
    Bf n (Pi.single q (1 : F)) w = w (bar q) := by
  unfold Bf
  simp [Pi.single_apply]

theorem Bf_single_right (q : Fin n ⊕ Fin n) (v : Fin n ⊕ Fin n → F) :
    Bf n v (Pi.single q (1 : F)) = v (bar q) := by
  unfold Bf
  rw [Finset.sum_eq_single (bar q)]
  · simp [bar_bar]
  · intro x _ hx
    have : ¬ (bar x = q) := fun e => hx (by rw [← e, bar_bar])
    simp [Pi.single_apply, this]
  · simp

theorem Bf_add_left (v v' w : Fin n ⊕ Fin n → F) : Bf n (v + v') w = Bf n v w + Bf n v' w := by
  unfold Bf
  simp [add_mul, Finset.sum_add_distrib]

theorem Bf_add_right (v w w' : Fin n ⊕ Fin n → F) : Bf n v (w + w') = Bf n v w + Bf n v w' := by
  unfold Bf
  simp [mul_add, Finset.sum_add_distrib]

@[expose] noncomputable def suppP (P : Set (Fin n ⊕ Fin n)) (v : Fin n ⊕ Fin n → F) : Fin n ⊕ Fin n → F :=
  fun x => open Classical in if x ∈ P then v x else 0

theorem Qf_suppP {P : Set (Fin n ⊕ Fin n)} (hd : ∀ p ∈ P, bar p ∉ P) (v : Fin n ⊕ Fin n → F) :
    Qf n (suppP P v) = 0 := by
  unfold Qf
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases h : (Sum.inl i : Fin n ⊕ Fin n) ∈ P
  · have : (Sum.inr i : Fin n ⊕ Fin n) ∉ P := hd _ h
    simp [suppP, this]
  · simp [suppP, h]

theorem Bf_suppP {P : Set (Fin n ⊕ Fin n)} (hd : ∀ p ∈ P, bar p ∉ P) (v w : Fin n ⊕ Fin n → F) :
    Bf n (suppP P v) (suppP P w) = 0 := by
  unfold Bf
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases h : x ∈ P
  · have : bar x ∉ P := hd _ h
    simp [suppP, this]
  · simp [suppP, h]

namespace Cfg

variable {P : Set (Fin n ⊕ Fin n)} {p' : Fin n ⊕ Fin n}

theorem col_bar_eq (hΔ : ∀ x y, ¬ (x ∈ P ∧ bar y ∈ P) → G x y = if x = y then 1 else 0)
    (hd : ∀ p ∈ P, bar p ∉ P) (hp : p ∈ P) :
    (fun x => G x (bar p)) = Pi.single (bar p) 1 + suppP P (fun x => G x (bar p)) := by
  classical
  ext x
  by_cases hx : x ∈ P
  · have : x ≠ bar p := fun e => hd p hp (e ▸ hx)
    simp [suppP, hx, this]
  · simp only [Pi.add_apply, suppP, hx, ite_false, add_zero, Pi.single_apply]
    rw [hΔ x (bar p) (fun h => hx h.1)]

theorem alt_diag (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v)
    (hΔ : ∀ x y, ¬ (x ∈ P ∧ bar y ∈ P) → G x y = if x = y then 1 else 0)
    (hd : ∀ p ∈ P, bar p ∉ P) (hp : p ∈ P) : G p (bar p) = 0 := by
  have hc : ∀ q : Fin n ⊕ Fin n, G.mulVec (Pi.single q (1 : F)) = fun x => G x q := fun q => by
    ext x; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have h := hQ (Pi.single (bar p) 1)
  rw [hc, Qf_single, col_bar_eq hΔ hd hp, Qf_add, Qf_single, Qf_suppP hd, Bf_single_left,
    bar_bar] at h
  simpa [suppP, hp] using h

theorem alt_symm [CharP F 2] (hQ : ∀ v, Qf n (G.mulVec v) = Qf n v)
    (hΔ : ∀ x y, ¬ (x ∈ P ∧ bar y ∈ P) → G x y = if x = y then 1 else 0)
    (hd : ∀ p ∈ P, bar p ∉ P) (hp : p ∈ P) (hp' : p' ∈ P) (hne : p ≠ p') :
    G p (bar p') = G p' (bar p) := by
  have h2 : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
  have := orth_cols hQ (bar p) (bar p')
  have hsum : ∑ x, G x (bar p) * G (bar x) (bar p') =
      Bf n (fun x => G x (bar p)) (fun x => G x (bar p')) := rfl
  rw [hsum, col_bar_eq hΔ hd hp, col_bar_eq hΔ hd hp'] at this
  rw [Bf_add_left, Bf_add_right, Bf_add_right, Bf_suppP hd] at this
  have e1 : ¬ (p = bar p') := fun e => hd p' hp' (e ▸ hp)
  have e2 : ¬ (bar p' = p) := fun e => hd p' hp' (e ▸ hp)
  have e3 : ¬ (p' = bar p) := fun e => hd p hp (e ▸ hp')
  simp only [Bf_single_left, Bf_single_right, suppP, bar_bar, hp, hp', ite_true, Pi.single_apply,
    e1, e2, e3, ite_false] at this
  linear_combination this - (G p' (bar p)) * h2

end Cfg

end CFSG.HardMathSupport.Cooperstein.StructureLie
