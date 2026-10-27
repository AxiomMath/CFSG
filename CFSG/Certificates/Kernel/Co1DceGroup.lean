module

public import CFSG.Certificates.Kernel.Co1DceLemmas
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

public section

namespace CFSG.Certificates.Co1D

open CFSG.KC CFSG.KC.DceS CFSG.KS.P16
open scoped Pointwise

section LiftRange

variable {F H G : Type*} [Group F] [Group H] [Group G]

theorem eq_of_ker_le {φ : F →* H} {ψ : F →* G} (hk : φ.ker ≤ ψ.ker) {a b : F} (h : φ a = φ b) :
    ψ a = ψ b := by
  have hm : a * b⁻¹ ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have h2 := hk hm
  rw [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

noncomputable def liftRange (φ : F →* H) (ψ : F →* G) (hk : φ.ker ≤ ψ.ker) : φ.range →* G where
  toFun h := ψ (Classical.choose (MonoidHom.mem_range.1 h.2))
  map_one' := by
    have e := Classical.choose_spec (MonoidHom.mem_range.1 (1 : φ.range).2)
    exact (eq_of_ker_le hk (e.trans φ.map_one.symm)).trans ψ.map_one
  map_mul' a b := by
    have ea := Classical.choose_spec (MonoidHom.mem_range.1 a.2)
    have eb := Classical.choose_spec (MonoidHom.mem_range.1 b.2)
    have eab := Classical.choose_spec (MonoidHom.mem_range.1 (a * b).2)
    rw [← map_mul ψ]
    apply eq_of_ker_le hk
    rw [map_mul, ea, eb]
    exact eab

theorem liftRange_apply {φ : F →* H} {ψ : F →* G} (hk : φ.ker ≤ ψ.ker) (y : φ.range) (u : F)
    (hy : (y : H) = φ u) : liftRange φ ψ hk y = ψ u :=
  eq_of_ker_le hk ((Classical.choose_spec (MonoidHom.mem_range.1 y.2)).trans hy)

end LiftRange

theorem lift_eq_word {α K : Type*} [DecidableEq α] [Group K] (f : α → K)
    (hf : ∀ a, f a * f a = 1) (u : FreeGroup α) :
    FreeGroup.lift f u = ((FreeGroup.toWord u).map fun p => f p.1).prod := by
  conv_lhs => rw [← FreeGroup.mk_toWord (x := u)]
  rw [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  rintro ⟨a, b⟩ -
  cases b
  · exact (eq_inv_of_mul_eq_one_left (hf a)).symm
  · rfl

theorem prod_map_filter {α K : Type*} [Monoid K] (p : α → Bool) (f : α → K)
    (hf : ∀ a, p a = false → f a = 1) : ∀ l : List α, (l.map f).prod = ((l.filter p).map f).prod
  | [] => rfl
  | a :: l => by
    cases ha : p a
    · rw [List.filter_cons_of_neg (by simp [ha]), List.map_cons, List.prod_cons, hf a ha, one_mul,
        prod_map_filter p f hf l]
    · rw [List.filter_cons_of_pos ha, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
        prod_map_filter p f hf l]

section Model

variable {G : Type*} [Group G]

@[expose] noncomputable def Lf (LT : ℕ → ℕ) (NL TL c : ℕ) : Equiv.Perm (Fin 16) :=
  if c < NL ∧ c ≠ TL then perm16 (Nat.land (LT c) m64) else 1

@[expose] noncomputable def Mg (LT : ℕ → ℕ) (NL TL : ℕ) : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure (Set.range (Lf LT NL TL))

@[expose] noncomputable def xf (x : ℕ → G) (NL TL c : ℕ) : G :=
  if c < NL ∧ c ≠ TL then x c else 1

@[expose] noncomputable def Nsub (x : ℕ → G) (NL TL : ℕ) : Subgroup G :=
  Subgroup.closure (x '' {c | c < NL ∧ c ≠ TL})

open Classical in
noncomputable def rhoM (LT : ℕ → ℕ) (NL TL : ℕ) (x : ℕ → G) : Mg LT NL TL →* G :=
  if hk : (FreeGroup.lift (Lf LT NL TL)).ker ≤ (FreeGroup.lift (xf x NL TL)).ker then
    (liftRange _ _ hk).comp
      (MulEquiv.subgroupCongr (FreeGroup.range_lift_eq_closure (f := Lf LT NL TL)).symm).toMonoidHom
  else 1

open Classical in
noncomputable def rc (LT : ℕ → ℕ) (NL TL : ℕ) (x : ℕ → G) (P : ℕ) : G :=
  if h : perm16 P ∈ Mg LT NL TL then rhoM LT NL TL x ⟨perm16 P, h⟩ else 1

variable {LT : ℕ → ℕ} {NL TL : ℕ} {x : ℕ → G}

theorem Lf_of_not {c : ℕ} (hc : ¬(c < NL ∧ c ≠ TL)) : Lf LT NL TL c = 1 := by
  rw [Lf, ite_eq_right hc]

theorem Lf_of {c : ℕ} (hc : c < NL ∧ c ≠ TL) : Lf LT NL TL c = perm16 (Nat.land (LT c) m64) := by
  rw [Lf, ite_eq_left hc]

theorem xf_of_not {c : ℕ} (hc : ¬(c < NL ∧ c ≠ TL)) : xf x NL TL c = 1 := by
  rw [xf, ite_eq_right hc]

theorem xf_of {c : ℕ} (hc : c < NL ∧ c ≠ TL) : xf x NL TL c = x c := by
  rw [xf, ite_eq_left hc]

section Hyps

variable (hL : ∀ c < NL, c ≠ TL → IsP (Nat.land (LT c) m64) ∧
  pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP)
include hL

theorem Lf_sq (c : ℕ) : Lf LT NL TL c * Lf LT NL TL c = 1 := by
  by_cases hc : c < NL ∧ c ≠ TL
  · obtain ⟨h1, h2⟩ := hL c hc.1 hc.2
    rw [Lf_of hc, ← perm16_pmul h1 h1, h2, perm16_idP]
  · rw [Lf_of_not hc, one_mul]

theorem Lf_inv (c : ℕ) : (Lf LT NL TL c)⁻¹ = Lf LT NL TL c :=
  inv_eq_of_mul_eq_one_right (Lf_sq hL c)

theorem perm16_wc {w : List ℕ} (hw : ∀ c ∈ w, c < NL ∧ c ≠ TL) :
    IsP (wc LT w) ∧ perm16 (wc LT w) = (w.map (Lf LT NL TL)).prod := by
  have hp : ∀ c ∈ w, IsP (Nat.land (LT c) m64) := fun c hc => (hL c (hw c hc).1 (hw c hc).2).1
  refine ⟨(wc_spec hp).1, ?_⟩
  rw [(wc_spec hp).2]
  congr 1
  apply List.map_congr_left
  intro c hc
  rw [Lf_of (hw c hc)]

theorem mem_wc {w : List ℕ} (hw : ∀ c ∈ w, c < NL ∧ c ≠ TL) :
    perm16 (wc LT w) ∈ Mg LT NL TL := by
  rw [(perm16_wc hL hw).2]
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨c, -, rfl⟩ := List.mem_map.1 hg
  exact Subgroup.subset_closure ⟨c, rfl⟩

theorem Mg_word {g : Equiv.Perm (Fin 16)} (hg : g ∈ Mg LT NL TL) :
    ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ perm16 (wc LT w) = g := by
  suffices h : ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ (w.map (Lf LT NL TL)).prod = g by
    obtain ⟨w, hw, e⟩ := h
    exact ⟨w, hw, (perm16_wc hL hw).2.trans e⟩
  have gen : ∀ c, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧
      (w.map (Lf LT NL TL)).prod = Lf LT NL TL c := fun c => by
    by_cases hc : c < NL ∧ c ≠ TL
    · exact ⟨[c], by simpa using hc, by simp⟩
    · exact ⟨[], by simp, (Lf_of_not hc).symm⟩
  rw [Mg] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    obtain ⟨c, rfl⟩ := hg
    exact gen c
  | inv_mem g hg =>
    obtain ⟨c, rfl⟩ := hg
    rw [Lf_inv hL]
    exact gen c
  | one => exact ⟨[], by simp, rfl⟩
  | mul g g' _ _ ih ih' =>
    obtain ⟨w, hw, e⟩ := ih
    obtain ⟨w', hw', e'⟩ := ih'
    refine ⟨w ++ w', fun c hc => ?_, by rw [List.map_append, List.prod_append, e, e']⟩
    rcases List.mem_append.1 hc with h | h
    · exact hw c h
    · exact hw' c h

variable (hx : ∀ c < NL, x c * x c = 1)
  (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
include hx

omit hL in
theorem xf_sq (c : ℕ) : xf x NL TL c * xf x NL TL c = 1 := by
  by_cases hc : c < NL ∧ c ≠ TL
  · rw [xf_of hc, hx c hc.1]
  · rw [xf_of_not hc, one_mul]

include hρ

theorem ker_le : (FreeGroup.lift (Lf LT NL TL)).ker ≤ (FreeGroup.lift (xf x NL TL)).ker := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu ⊢
  rw [lift_eq_word _ (Lf_sq hL)] at hu
  rw [lift_eq_word _ (xf_sq hx)]
  let l := (FreeGroup.toWord u).map Prod.fst
  let p : ℕ → Bool := fun c => decide (c < NL ∧ c ≠ TL)
  have e1 : ((FreeGroup.toWord u).map fun q => Lf LT NL TL q.1) = l.map (Lf LT NL TL) := by
    simp [l, Function.comp_def]
  have e2 : ((FreeGroup.toWord u).map fun q => xf x NL TL q.1) = l.map (xf x NL TL) := by
    simp [l, Function.comp_def]
  have hw : ∀ c ∈ l.filter p, c < NL ∧ c ≠ TL := fun c hc => by
    simpa [p] using (List.mem_filter.1 hc).2
  rw [e1, prod_map_filter p _ (fun c hc => Lf_of_not (by simpa [p] using hc)) l,
    ← (perm16_wc hL hw).2] at hu
  rw [e2, prod_map_filter p _ (fun c hc => xf_of_not (by simpa [p] using hc)) l]
  have hid : wc LT (l.filter p) = idP :=
    perm16_inj (perm16_wc hL hw).1 isP_idP (by rw [hu, perm16_idP])
  have e3 : ((l.filter p).map (xf x NL TL)).prod = ((l.filter p).map x).prod := by
    congr 1
    apply List.map_congr_left
    intro c hc
    exact xf_of (hw c hc)
  rw [e3]
  exact hρ _ hw hid

theorem rhoM_mk (y : Mg LT NL TL) (u : FreeGroup ℕ) (hy : (y : Equiv.Perm (Fin 16)) =
    FreeGroup.lift (Lf LT NL TL) u) : rhoM LT NL TL x y = FreeGroup.lift (xf x NL TL) u := by
  unfold rhoM
  rw [dite_eq_left (ker_le hL hx hρ)]
  exact liftRange_apply (φ := FreeGroup.lift (Lf LT NL TL)) (ψ := FreeGroup.lift (xf x NL TL))
    (ker_le hL hx hρ)
    ((MulEquiv.subgroupCongr (FreeGroup.range_lift_eq_closure (f := Lf LT NL TL)).symm) y) u hy

theorem rhoM_word {w : List ℕ} (hw : ∀ c ∈ w, c < NL ∧ c ≠ TL) (y : Mg LT NL TL)
    (hy : (y : Equiv.Perm (Fin 16)) = perm16 (wc LT w)) : rhoM LT NL TL x y = (w.map x).prod := by
  have e : (y : Equiv.Perm (Fin 16)) = FreeGroup.lift (Lf LT NL TL) (w.map FreeGroup.of).prod := by
    rw [hy, (perm16_wc hL hw).2, map_list_prod, List.map_map]
    congr 1
  rw [rhoM_mk hL hx hρ y _ e, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp [xf_of (hw c hc)]

theorem rhoM_range : (rhoM LT NL TL x).range = Nsub x NL TL := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    obtain ⟨w, hw, e⟩ := Mg_word hL y.2
    rw [rhoM_word hL hx hρ hw y e.symm]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hg
    exact Subgroup.subset_closure ⟨c, hw c hc, rfl⟩
  · rw [Nsub, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    have hw : ∀ d ∈ [c], d < NL ∧ d ≠ TL := by simpa using hc
    refine ⟨⟨_, mem_wc hL hw⟩, ?_⟩
    rw [rhoM_word hL hx hρ hw _ rfl]
    simp

theorem rc_word {w : List ℕ} (hw : ∀ c ∈ w, c < NL ∧ c ≠ TL) :
    rc LT NL TL x (wc LT w) = (w.map x).prod := by
  unfold rc
  rw [dite_eq_left (mem_wc hL hw)]
  exact rhoM_word hL hx hρ hw _ rfl

theorem rc_letter {c : ℕ} (hc : c < NL) (hcT : c ≠ TL) :
    perm16 (Nat.land (LT c) m64) ∈ Mg LT NL TL ∧ rc LT NL TL x (Nat.land (LT c) m64) = x c := by
  have hw : ∀ d ∈ [c], d < NL ∧ d ≠ TL := by simpa using ⟨hc, hcT⟩
  have e := wc_single (LT := LT) (hL c hc hcT).1
  refine ⟨e ▸ mem_wc hL hw, ?_⟩
  rw [← e, rc_word hL hx hρ hw]
  simp

end Hyps

theorem rc_eq {P : ℕ} (y : Mg LT NL TL) (hy : (y : Equiv.Perm (Fin 16)) = perm16 P) :
    rc LT NL TL x P = rhoM LT NL TL x y := by
  have hm : perm16 P ∈ Mg LT NL TL := hy ▸ y.2
  unfold rc
  rw [dite_eq_left hm]
  congr 1
  exact Subtype.ext hy.symm

theorem rc_mul {a b : ℕ} (ha : IsP a) (hb : IsP b) (hma : perm16 a ∈ Mg LT NL TL)
    (hmb : perm16 b ∈ Mg LT NL TL) :
    perm16 (pmul a b) ∈ Mg LT NL TL ∧
      rc LT NL TL x (pmul a b) = rc LT NL TL x a * rc LT NL TL x b := by
  have e : ((⟨_, hma⟩ * ⟨_, hmb⟩ : Mg LT NL TL) : Equiv.Perm (Fin 16)) = perm16 (pmul a b) := by
    rw [perm16_pmul ha hb]
    rfl
  refine ⟨e ▸ (Mg LT NL TL).mul_mem hma hmb, ?_⟩
  rw [rc_eq _ e, map_mul, rc_eq ⟨_, hma⟩ rfl, rc_eq ⟨_, hmb⟩ rfl]

theorem rc_inv {a : ℕ} (ha : IsP a) (hma : perm16 a ∈ Mg LT NL TL) :
    perm16 (pinv a) ∈ Mg LT NL TL ∧ rc LT NL TL x (pinv a) = (rc LT NL TL x a)⁻¹ := by
  have e : ((⟨_, hma⟩⁻¹ : Mg LT NL TL) : Equiv.Perm (Fin 16)) = perm16 (pinv a) := by
    rw [perm16_pinv ha]
    rfl
  refine ⟨e ▸ (Mg LT NL TL).inv_mem hma, ?_⟩
  rw [rc_eq _ e, map_inv, rc_eq ⟨_, hma⟩ rfl]

theorem rc_idP : perm16 idP ∈ Mg LT NL TL ∧ rc LT NL TL x idP = 1 := by
  have e : ((1 : Mg LT NL TL) : Equiv.Perm (Fin 16)) = perm16 idP := by
    rw [perm16_idP]
    rfl
  refine ⟨e ▸ (Mg LT NL TL).one_mem, ?_⟩
  rw [rc_eq _ e, map_one]

theorem rc_mem (hL : ∀ c < NL, c ≠ TL → IsP (Nat.land (LT c) m64) ∧
    pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP)
    (hx : ∀ c < NL, x c * x c = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    {P : ℕ} (hm : perm16 P ∈ Mg LT NL TL) : rc LT NL TL x P ∈ Nsub x NL TL := by
  rw [rc_eq ⟨_, hm⟩ rfl, ← rhoM_range hL hx hρ]
  exact ⟨_, rfl⟩

end Model

theorem testBit_packGens (f : ℕ → ℕ) : ∀ n i,
    (packGens f n).testBit i = (decide (i < 64 * n) && (f (i / 64)).testBit (i % 64))
  | 0, i => by
    change (0 : ℕ).testBit i = _
    simp
  | n + 1, i => by
    change (packGens f n ||| Nat.land (f n) m64 <<< (64 * n)).testBit i = _
    rw [Nat.testBit_or, testBit_packGens f n i, Nat.testBit_shiftLeft, land_lit (f n) 64 m64 rfl,
      Nat.testBit_mod_two_pow]
    by_cases h1 : i < 64 * n
    · rw [decide_eq_true h1, decide_eq_true (by omega : i < 64 * (n + 1)),
        decide_eq_false (by omega : ¬(i ≥ 64 * n))]
      simp
    · by_cases h2 : i < 64 * n + 64
      · have e1 : i / 64 = n := by omega
        have e2 : i % 64 = i - 64 * n := by omega
        rw [decide_eq_false h1, decide_eq_true (by omega : i < 64 * (n + 1)),
          decide_eq_true (by omega : i ≥ 64 * n), decide_eq_true (by omega : i - 64 * n < 64), e1,
          e2]
        simp
      · rw [decide_eq_false h1, decide_eq_false (by omega : ¬(i < 64 * (n + 1))),
          decide_eq_true (by omega : i ≥ 64 * n), decide_eq_false (by omega : ¬(i - 64 * n < 64))]
        simp

theorem gk_packGens (f : ℕ → ℕ) {n k : ℕ} (hk : k < n) :
    gk (packGens f n) k = Nat.land (f k) m64 := by
  apply Nat.eq_of_testBit_eq
  intro j
  unfold gk
  rw [land_lit _ 64 m64 rfl, land_lit _ 64 m64 rfl, Nat.testBit_mod_two_pow,
    Nat.testBit_mod_two_pow]
  change (decide (j < 64) && (packGens f n >>> (64 * k)).testBit j) = _
  rw [Nat.testBit_shiftRight, testBit_packGens]
  by_cases hj : j < 64
  · have h1 : 64 * k + j < 64 * n := by omega
    have e1 : (64 * k + j) / 64 = k := by omega
    have e2 : (64 * k + j) % 64 = j := by omega
    simp [hj, h1, e1, e2]
  · simp [hj]

theorem gk_nGens {LT : ℕ → ℕ} {NL TL k : ℕ} (hk : k < NL - 1) :
    ∃ c, c < NL ∧ c ≠ TL ∧ gk (nGens LT NL TL) k = Nat.land (LT c) m64 := by
  refine ⟨Bool.rec (motive := fun _ => ℕ) (Nat.succ k) k (Nat.blt k TL), ?_, ?_,
    gk_packGens _ hk⟩ <;> cases hb : Nat.blt k TL
  · change k + 1 < NL
    omega
  · change k < NL
    omega
  · have : ¬k < TL := fun h => by simp [Nat.blt_eq.mpr h] at hb
    change k + 1 ≠ TL
    omega
  · have := Nat.blt_eq.mp hb
    change k ≠ TL
    omega

theorem card_Mg {LT NE : ℕ → ℕ} {NL TL ngN nN : ℕ}
    (hL : ∀ c < NL, c ≠ TL → IsP (Nat.land (LT c) m64) ∧
      pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP)
    (hTL : TL < NL) (hng : ngN = NL - 1)
    (hE : Nat.beq (eCnt (enumRun NE (nGens LT NL TL) ngN nN 0 nN 1)) (Nat.succ nN) = true)
    (hN : 0 < nN) : Nat.card (Mg LT NL TL) = nN := by
  subst hng
  have hG : ∀ k < NL - 1, IsP (gk (nGens LT NL TL) k) := fun k hk => by
    obtain ⟨c, hc, hcT, e⟩ := gk_nGens (LT := LT) hk
    rw [e]
    exact (hL c hc hcT).1
  obtain ⟨hE1, hE2, hE3⟩ := enum_sound hE hG
  let E : Finset (Equiv.Perm (Fin 16)) := (Finset.range nN).image fun i => perm16 (eCode NE 0 i)
  have hEc : E.card = nN := by
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    exact hE2 i hi j hj (perm16_inj (hE1 i hi).1 (hE1 j hj).1 e)
  have hEM : ∀ g ∈ E, g ∈ Mg LT NL TL := by
    intro g hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hg
    have hcl := (hE1 i (Finset.mem_range.1 hi)).2
    refine (Submonoid.closure_le (S := (Mg LT NL TL).toSubmonoid)).2 ?_ hcl
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨c, hc, hcT, e⟩ := gk_nGens (LT := LT) hk
    rw [e, ← Lf_of ⟨hc, hcT⟩]
    exact Subgroup.subset_closure ⟨c, rfl⟩
  have gen : ∀ c, ∀ e ∈ E, e * Lf LT NL TL c ∈ E := by
    intro c e he
    by_cases hc : c < NL ∧ c ≠ TL
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he
      obtain ⟨k, hk, ek⟩ := nLetter_index hTL hc.1 hc.2
      have egk : gk (nGens LT NL TL) k = Nat.land (LT c) m64 := by
        rw [← ek]
        exact gk_packGens _ hk
      obtain ⟨j, hj, ej⟩ := hE3 i (Finset.mem_range.1 hi) k hk
      rw [egk] at ej
      refine Finset.mem_image.2 ⟨j, Finset.mem_range.2 hj, ?_⟩
      rw [Lf_of hc, ← ej, perm16_pmul (hE1 i (Finset.mem_range.1 hi)).1 (hL c hc.1 hc.2).1]
    · rw [Lf_of_not hc, mul_one]
      exact he
  have hEr : ∀ g ∈ Mg LT NL TL, ∀ e ∈ E, e * g ∈ E := by
    intro g hg
    rw [Mg] at hg
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨c, rfl⟩ := hg
      exact gen c
    | inv_mem g hg =>
      obtain ⟨c, rfl⟩ := hg
      rw [Lf_inv hL]
      exact gen c
    | one =>
      intro e he
      rw [mul_one]
      exact he
    | mul g g' _ _ ih ih' =>
      intro e he
      rw [← mul_assoc]
      exact ih' _ (ih e he)
  have he0 : perm16 (eCode NE 0 0) ∈ E := Finset.mem_image.2 ⟨0, Finset.mem_range.2 hN, rfl⟩
  have hset : ((Mg LT NL TL : Set (Equiv.Perm (Fin 16)))) = (E : Set (Equiv.Perm (Fin 16))) := by
    ext g
    constructor
    · intro hg
      have hm := (Mg LT NL TL).mul_mem ((Mg LT NL TL).inv_mem (hEM _ he0)) hg
      have := hEr _ hm _ he0
      rwa [mul_inv_cancel_left] at this
    · intro hg
      exact hEM g hg
  change Nat.card ((Mg LT NL TL : Set (Equiv.Perm (Fin 16)))) = nN
  rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset, hEc]

@[expose] noncomputable def Tg (TGs ngT : ℕ) : Subgroup (Equiv.Perm (Fin 16)) :=
  Subgroup.closure {g | ∃ k < ngT, g = perm16 (gk TGs k)}

@[expose] noncomputable def tj {G : Type*} [Group G] (LT HT GT : ℕ → ℕ) (NL TL : ℕ) (x : ℕ → G)
    (j : ℕ) : G :=
  (rc LT NL TL x (hP (HT (GT j))))⁻¹ * x TL * rc LT NL TL x (hP (HT (GT j)))

section DceOk

variable {blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE : ℕ → ℕ}
  {NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT
    hL hH hO hR hD P : ℕ} {Cs CCs : List ℕ} {S0 S1 X0 X1 : ℕ}

theorem dceOk_rhoHyps {G : Type*} [Group G] (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE
      NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO
      hR hD P Cs CCs S0 S1 X0 X1 = true) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1) :
    (∀ c < NL, c ≠ TL → IsP (Nat.land (LT c) m64) ∧
      pmul (Nat.land (LT c) m64) (Nat.land (LT c) m64) = idP) ∧ ∀ c < NL, x c * x c = 1 :=
  ⟨(dceOk_letters h).2.2.2, (dceOk_words h x hrels).1⟩

theorem dceOk_card (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) (hN : 0 < nN) : Nat.card (Mg LT NL TL) = nN := by
  have hs := dceOk_spec h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h25, h26, -⟩ := hs
  rw [Nat.beq_eq] at h25
  exact card_Mg (dceOk_letters h).2.2.2 (dceOk_letters h).1 h25 h26 hN

theorem dceOk_hdr_mem (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) : ∀ k < NH, IsP (hP (HT k)) ∧ perm16 (hP (HT k)) ∈ Mg LT NL TL := by
  intro k hk
  obtain ⟨w, hw, e⟩ := dceOk_hdr h k hk
  rw [← e]
  exact ⟨(perm16_wc (dceOk_letters h).2.2.2 hw).1, mem_wc (dceOk_letters h).2.2.2 hw⟩

theorem dceOk_g (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL ND
      ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) : ∀ j < NO, IsP (hP (HT (GT j))) ∧ perm16 (hP (HT (GT j))) ∈ Mg LT NL TL ∧
      (perm16 (hP (HT (GT j))))⁻¹ • sysOf NB (OMT I0) = sysOf NB (OMT j) := by
  intro j hj
  obtain ⟨hg, e⟩ := (dceOk_omega h).2.2.2.2.1 j hj
  exact ⟨(dceOk_hdr_mem h _ hg).1, (dceOk_hdr_mem h _ hg).2, e⟩

theorem dceOk_orbit (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) :
    MulAction.orbit (Mg LT NL TL) (sysOf NB (OMT I0)) =
      ↑((Finset.range NO).image fun j => sysOf NB (OMT j)) := by
  have hLv := (dceOk_letters h).2.2.2
  obtain ⟨hI0, -, -, -, -, hcl, -⟩ := dceOk_omega h
  have gen : ∀ c, ∀ j < NO, ∃ j' < NO, sysOf NB (OMT j') = Lf LT NL TL c • sysOf NB (OMT j) := by
    intro c j hj
    by_cases hc : c < NL ∧ c ≠ TL
    · obtain ⟨j', hj', e⟩ := hcl j hj c hc.1 hc.2
      refine ⟨j', hj', ?_⟩
      rw [← e, ← Lf_of hc, Lf_inv hLv]
    · exact ⟨j, hj, by rw [Lf_of_not hc, one_smul]⟩
  have key : ∀ g ∈ Mg LT NL TL, ∀ j < NO, ∃ j' < NO, sysOf NB (OMT j') = g • sysOf NB (OMT j) := by
    intro g hg
    rw [Mg] at hg
    induction hg using Subgroup.closure_induction'' with
    | mem g hg =>
      obtain ⟨c, rfl⟩ := hg
      exact gen c
    | inv_mem g hg =>
      obtain ⟨c, rfl⟩ := hg
      rw [Lf_inv hLv]
      exact gen c
    | one => exact fun j hj => ⟨j, hj, by rw [one_smul]⟩
    | mul g g' _ _ ih ih' =>
      intro j hj
      obtain ⟨j1, hj1, e1⟩ := ih' j hj
      obtain ⟨j2, hj2, e2⟩ := ih j1 hj1
      exact ⟨j2, hj2, by rw [e2, e1, mul_smul]⟩
  ext Ω
  simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨j', hj', e⟩ := key g g.2 I0 hI0
    exact ⟨j', hj', e⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨-, hm, e⟩ := dceOk_g h j hj
    exact ⟨⟨_, (Mg LT NL TL).inv_mem hm⟩, e⟩

theorem dceOk_stab_card (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL
      TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1
      X0 X1 = true) (hN : 0 < nN) :
    Nat.card (MulAction.stabilizer (Mg LT NL TL) (sysOf NB (OMT I0))) = nT := by
  have hs := dceOk_spec h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, h32, -⟩ := hs
  rw [Nat.beq_eq] at h32
  have hI0 := (dceOk_omega h).1
  have hinj := (dceOk_omega h).2.2.2.1
  have hidx := MulAction.index_stabilizer (Mg LT NL TL) (sysOf NB (OMT I0))
  rw [dceOk_orbit h, Set.ncard_coe_finset, Finset.card_image_of_injOn, Finset.card_range] at hidx
  · have hc := Subgroup.card_mul_index (MulAction.stabilizer (Mg LT NL TL) (sysOf NB (OMT I0)))
    rw [hidx, dceOk_card h hN] at hc
    have h32' : nT * NO = nN := h32
    exact Nat.eq_of_mul_eq_mul_right (by omega) (hc.trans h32'.symm)
  · intro i hi i' hi' e
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    exact hinj i hi i' hi' e

theorem dceOk_stab (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE NB NO I0 BB BASEM NL TL
      ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO hR hD P Cs CCs S0 S1 X0
      X1 = true) (hN : 0 < nN)
    (hTw : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k) :
    Tg TGs ngT ≤ Mg LT NL TL ∧
      (Tg TGs ngT).subgroupOf (Mg LT NL TL) =
        MulAction.stabilizer (Mg LT NL TL) (sysOf NB (OMT I0)) := by
  have hLv := (dceOk_letters h).2.2.2
  have hTgen := (dceOk_omega h).2.2.2.2.2.2
  have hs := dceOk_spec h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, h31, -⟩ := hs
  have hTM : Tg TGs ngT ≤ Mg LT NL TL := by
    rw [Tg, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨w, hw, e⟩ := hTw k hk
    rw [← e]
    exact mem_wc hLv hw
  have hTS : Tg TGs ngT ≤ MulAction.stabilizer (Equiv.Perm (Fin 16)) (sysOf NB (OMT I0)) := by
    rw [Tg, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (inv_smul_eq_iff.1 (hTgen k hk).2).symm
  refine ⟨hTM, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
  · intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact hTS hy
  · rw [dceOk_stab_card h hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTM).toEquiv]
    obtain ⟨hE1, hE2, -⟩ := enum_sound h31 fun k hk => (hTgen k hk).1
    let E : Finset (Equiv.Perm (Fin 16)) :=
      (Finset.range nT).image fun i => perm16 (eCode TTE 0 i)
    have hEc : E.card = nT := by
      rw [Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj e
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact hE2 i hi j hj (perm16_inj (hE1 i hi).1 (hE1 j hj).1 e)
    have hsub : (E : Set (Equiv.Perm (Fin 16))) ⊆ (Tg TGs ngT : Set (Equiv.Perm (Fin 16))) := by
      intro g hg
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hg
      exact (Submonoid.closure_le (S := (Tg TGs ngT).toSubmonoid)).2 Subgroup.subset_closure
        (hE1 i (Finset.mem_range.1 hi)).2
    change nT ≤ Nat.card ((Tg TGs ngT : Set (Equiv.Perm (Fin 16))))
    rw [Nat.card_coe_set_eq, ← hEc, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)

theorem dceOk_stab_comm {G : Type*} [Group G] (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT
      TTE NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH
      hO hR hD P Cs CCs S0 S1 X0 X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod)
    {Q : ℕ} (hQM : perm16 Q ∈ Mg LT NL TL)
    (hQ : (perm16 Q)⁻¹ • sysOf NB (OMT I0) = sysOf NB (OMT I0)) :
    rc LT NL TL x Q * x TL = x TL * rc LT NL TL x Q := by
  obtain ⟨hLv, hx⟩ := dceOk_rhoHyps h x hrels
  obtain ⟨hTM, hTS⟩ := dceOk_stab h hN fun k hk =>
    let ⟨w, hw, e, _⟩ := hT k hk
    ⟨w, hw, e⟩
  have hy : (⟨_, hQM⟩ : Mg LT NL TL) ∈ MulAction.stabilizer (Mg LT NL TL) (sysOf NB (OMT I0)) := by
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def]
    exact (inv_smul_eq_iff.1 hQ).symm
  rw [← hTS, Subgroup.mem_subgroupOf] at hy
  have key : ∀ g, g ∈ Subgroup.closure {g | ∃ k < ngT, g = perm16 (gk TGs k)} →
      ∀ hm : g ∈ Mg LT NL TL, Commute (rhoM LT NL TL x ⟨g, hm⟩) (x TL) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      obtain ⟨w, hw, e, hc⟩ := hT k hk
      intro hm
      rw [rhoM_word hLv hx hρ hw ⟨_, hm⟩ (by rw [e])]
      exact hc
    | one =>
      intro hm
      have e : (⟨1, hm⟩ : Mg LT NL TL) = 1 := rfl
      rw [e, map_one]
      exact Commute.one_left _
    | mul g g' hg hg' ih ih' =>
      intro hm
      have e : (⟨g * g', hm⟩ : Mg LT NL TL) = ⟨g, hTM hg⟩ * ⟨g', hTM hg'⟩ := rfl
      rw [e, map_mul]
      exact (ih (hTM hg)).mul_left (ih' (hTM hg'))
    | inv g hg ih =>
      intro hm
      have e : (⟨g⁻¹, hm⟩ : Mg LT NL TL) = (⟨g, hTM hg⟩)⁻¹ := rfl
      rw [e, map_inv]
      exact (ih (hTM hg)).inv_left
  rw [rc_eq ⟨_, hQM⟩ rfl]
  exact (key _ hy hQM).eq

theorem dceOk_tconj {G : Type*} [Group G] (h : dceOk blk LT HT PBT OMT GT WT RT NE SE STT OHT TTE
      NB NO I0 BB BASEM NL TL ND ALIVE INV INV8 NR IH NH NW HS nf nN ngN SUMIDX TGs ngT nT hL hH hO
      hR hD P Cs CCs S0 S1 X0 X1 = true) (hN : 0 < nN) (x : ℕ → G)
    (hrels : ∀ r < NR, bvF x (rW (RT r)) (rN (RT r)) = 1)
    (hρ : ∀ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) → wc LT w = idP → (w.map x).prod = 1)
    (hT : ∀ k < ngT, ∃ w : List ℕ, (∀ c ∈ w, c < NL ∧ c ≠ TL) ∧ wc LT w = gk TGs k ∧
      (w.map x).prod * x TL = x TL * (w.map x).prod)
    {j Q : ℕ} (hj : j < NO) (hQ : IsP Q) (hQM : perm16 Q ∈ Mg LT NL TL)
    (hΩ : (perm16 Q)⁻¹ • sysOf NB (OMT j) = sysOf NB (OMT I0)) :
    rc LT NL TL x Q * x TL * (rc LT NL TL x Q)⁻¹ = tj LT HT GT NL TL x j := by
  obtain ⟨hg, hgM, hgΩ⟩ := dceOk_g h j hj
  obtain ⟨hsM, hs⟩ := rc_mul (x := x) hg hQ hgM hQM
  have hsΩ : (perm16 (pmul (hP (HT (GT j))) Q))⁻¹ • sysOf NB (OMT I0) = sysOf NB (OMT I0) := by
    rw [perm16_pmul hg hQ, mul_inv_rev, mul_smul, hgΩ, hΩ]
  have hc := dceOk_stab_comm h hN x hrels hρ hT hsM hsΩ
  rw [hs] at hc
  unfold tj
  set a := rc LT NL TL x (hP (HT (GT j)))
  set b := rc LT NL TL x Q
  calc b * x TL * b⁻¹ = a⁻¹ * (a * b * x TL) * b⁻¹ := by group
    _ = a⁻¹ * (x TL * (a * b)) * b⁻¹ := by rw [hc]
    _ = a⁻¹ * x TL * a := by group

end DceOk

end CFSG.Certificates.Co1D

end
