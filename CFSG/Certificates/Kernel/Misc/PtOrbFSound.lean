module

public import Certificates.Data.Kernel.Misc.PtOrbF
public import CFSG.Certificates.Kernel.Spor.RawDefs
public import CFSG.Sporadic.HNOddCore.ChainUtil
public import CFSG.Sporadic.HNOddCore.OrbitCert
import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.PtOrb

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem strictB_eq' (y : Nat) (k : Nat → Bool) : strictB y k = k y := by
  cases y <;> rfl

theorem bitP_eq (s x : Nat) : bitP s x = s.testBit x := by
  change Nat.beq ((s >>> x) &&& 1) 1 = _
  rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, Nat.testBit_eq_decide_div_mod_eq, Bool.eq_iff_iff,
    Nat.beq_eq, decide_eq_true_iff]

theorem allF_iff (m : Nat) (f : Nat → Bool) : allF m f = true ↔ ∀ i < m, f i = true := by
  induction m with
  | zero => exact ⟨fun _ i hi => absurd hi (Nat.not_lt_zero i), fun _ => rfl⟩
  | succ m ih =>
    have e : allF (m + 1) f = (f m && allF m f) := by
      change Bool.rec (motive := fun _ => Bool) false (allF m f) (f m) = _
      cases f m <;> rfl
    rw [e, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
      exacts [h2 i h, h1]
    · intro h
      exact ⟨h m (Nat.lt_succ_self m), fun i hi => h i (Nat.lt_succ_of_lt hi)⟩

theorem imgF_succ (f : Nat → Nat) (s n : Nat) :
    imgF f s (n + 1) = if bitP s n then imgF f s n ||| (1 <<< f n) else imgF f s n := by
  change Bool.rec (motive := fun _ => Nat) (imgF f s n) (Nat.lor (imgF f s n) (Nat.shiftLeft 1 (f n)))
    (bitP s n) = _
  cases bitP s n <;> rfl

theorem testBit_imgF (f : Nat → Nat) (s n y : Nat) :
    (imgF f s n).testBit y = true ↔ ∃ z < n, s.testBit z = true ∧ f z = y := by
  induction n with
  | zero =>
    change (0 : Nat).testBit y = true ↔ _
    simp
  | succ n ih =>
    rw [imgF_succ]
    by_cases hb : bitP s n = true
    · rw [if_pos hb, Nat.testBit_or, Bool.or_eq_true, ih, Nat.one_shiftLeft, Nat.testBit_two_pow,
        decide_eq_true_iff]
      rw [bitP_eq] at hb
      constructor
      · rintro (⟨z, hz, h1, h2⟩ | h)
        · exact ⟨z, Nat.lt_succ_of_lt hz, h1, h2⟩
        · exact ⟨n, Nat.lt_succ_self n, hb, h⟩
      · rintro ⟨z, hz, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hz with h | rfl
        · exact Or.inl ⟨z, h, h1, h2⟩
        · exact Or.inr h2
    · rw [if_neg hb, ih]
      rw [bitP_eq] at hb
      constructor
      · rintro ⟨z, hz, h1, h2⟩
        exact ⟨z, Nat.lt_succ_of_lt hz, h1, h2⟩
      · rintro ⟨z, hz, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hz with h | rfl
        · exact ⟨z, h, h1, h2⟩
        · exact absurd h1 hb

theorem testBit_roundF (f : Nat → Nat → Nat) (k n s y : Nat) :
    (roundF f k n s).testBit y = true ↔
      s.testBit y = true ∨ ∃ j < k, ∃ z < n, s.testBit z = true ∧ f j z = y := by
  induction k with
  | zero =>
    change s.testBit y = true ↔ _
    simp
  | succ k ih =>
    have e : roundF f (k + 1) n s = roundF f k n s ||| imgF (f k) s n := rfl
    rw [e, Nat.testBit_or, Bool.or_eq_true, ih, testBit_imgF]
    constructor
    · rintro ((h | ⟨j, hj, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, h⟩
      · exact Or.inr ⟨k, Nat.lt_succ_self k, h⟩
    · rintro (h | ⟨j, hj, h⟩)
      · exact Or.inl (Or.inl h)
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact Or.inl (Or.inr ⟨j, hj, h⟩)
        · exact Or.inr h

theorem closeF_succ (f : Nat → Nat → Nat) (k n r s : Nat) :
    closeF f k n (r + 1) s = closeF f k n r (roundF f k n s) :=
  strictN_eq' _ _

theorem closeF_inv (f : Nat → Nat → Nat) (k n : Nat) (P : Nat → Prop)
    (hP : ∀ j < k, ∀ z < n, P z → P (f j z)) (r : Nat) :
    ∀ s, (∀ y, s.testBit y = true → P y) → ∀ y, (closeF f k n r s).testBit y = true → P y := by
  induction r with
  | zero => exact fun s hs => hs
  | succ r ih =>
    intro s hs
    rw [closeF_succ]
    refine ih _ fun y hy => ?_
    rcases (testBit_roundF f k n s y).1 hy with h | ⟨j, hj, z, hz, h1, rfl⟩
    · exact hs y h
    · exact hP j hj z hz (hs z h1)

theorem closeF_mono (f : Nat → Nat → Nat) (k n r : Nat) :
    ∀ s y, s.testBit y = true → (closeF f k n r s).testBit y = true := by
  induction r with
  | zero => exact fun s y h => h
  | succ r ih =>
    intro s y h
    rw [closeF_succ]
    exact ih _ _ ((testBit_roundF f k n s y).2 (Or.inl h))

theorem closedF_spec {f : Nat → Nat → Nat} {k n S : Nat} (h : closedF f k n S = true) :
    ∀ j < k, ∀ z < n, S.testBit z = true → S.testBit (f j z) = true := by
  intro j hj z hz hs
  have h1 := (allF_iff k _).1 h j hj
  rw [Nat.beq_eq] at h1
  have h2 : (imgF (f j) S n).testBit (f j z) = true :=
    (testBit_imgF (f j) S n _).2 ⟨z, hz, hs, rfl⟩
  have h3 : (imgF (f j) S n ||| S).testBit (f j z) = true := by
    rw [Nat.testBit_or, h2, Bool.true_or]
  have e : Nat.lor (imgF (f j) S n) S = imgF (f j) S n ||| S := rfl
  rw [← e, h1] at h3
  exact h3

theorem bitsIs_spec {S n : Nat} {t : Nat → Bool} (h : bitsIs S n t = true) :
    ∀ y < n, S.testBit y = t y := by
  intro y hy
  unfold bitsIs at h
  rw [strictB_eq', allF_iff] at h
  have h1 := h y hy
  rw [bitP_eq] at h1
  cases e1 : S.testBit y <;> cases e2 : t y <;> simp_all

theorem popF_succ (s n : Nat) : popF s (n + 1) = popF s n + if bitP s n then 1 else 0 := by
  change Nat.add (popF s n) (Bool.rec (motive := fun _ => Nat) 0 1 (bitP s n)) = _
  cases bitP s n <;> rfl

theorem card_bits (S n : Nat) : Nat.card {y : Fin n | S.testBit y = true} = popF S n := by
  rw [Nat.card_eq_fintype_card, Fintype.card_ofFinset, Finset.card_filter]
  simp only [Set.mem_setOf_eq]
  rw [Fin.sum_univ_eq_sum_range (fun i => if S.testBit i = true then 1 else 0) n]
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ih, popF_succ, bitP_eq]

theorem popIs_spec {S n c : Nat} (h : popIs S n c = true) : popF S n = c := by
  unfold popIs at h
  rw [strictB_eq', Nat.beq_eq] at h
  exact h

variable {n : Nat}

theorem mem_orbit_iff {k : Nat} {f : Nat → Nat → Nat} {G : Subgroup (Equiv.Perm (Fin n))}
    {g : Nat → Equiv.Perm (Fin n)} (hG : G = Subgroup.closure {h | ∃ j < k, g j = h})
    (hf : ∀ j < k, ∀ x : Fin n, f j x = g j x) {r x : Nat} (hx : x < n)
    (hc : orbClosed f k n r x = true) (y : Fin n) :
    y ∈ MulAction.orbit G (⟨x, hx⟩ : Fin n) ↔
      (closeF f k n r (Nat.shiftLeft 1 x)).testBit y = true := by
  unfold orbClosed at hc
  rw [strictB_eq'] at hc
  set S := closeF f k n r (Nat.shiftLeft 1 x) with hS
  have hx1 : (Nat.shiftLeft 1 x).testBit x = true := by
    change (1 <<< x).testBit x = true
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_self]
  constructor
  · rintro ⟨⟨h, hh⟩, rfl⟩
    have hpres : ∀ z : Fin n, S.testBit z = true → S.testBit (h z) = true := by
      rw [hG] at hh
      induction hh using Subgroup.closure_induction with
      | mem a ha =>
        obtain ⟨j, hj, rfl⟩ := ha
        intro z hz
        rw [← hf j hj z]
        exact closedF_spec hc j hj z z.2 hz
      | one => exact fun z hz => hz
      | mul a b _ _ ha hb => exact fun z hz => ha _ (hb z hz)
      | inv a _ ha =>
        exact CFSG.Sporadic.HNOddCore.perm_preimage_of_image (S := {z | S.testBit z = true}) ha
    exact hpres ⟨x, hx⟩ (closeF_mono f k n r _ x hx1)
  · intro hy
    obtain ⟨_, ho⟩ := closeF_inv f k n (fun z => ∃ hz : z < n, (⟨z, hz⟩ : Fin n) ∈
        MulAction.orbit G (⟨x, hx⟩ : Fin n))
      (fun j hj z hz ⟨_, ho⟩ => by
        have hgj : g j ∈ G := by
          rw [hG]
          exact Subgroup.subset_closure ⟨j, hj, rfl⟩
        have e : f j z = ((g j ⟨z, hz⟩ : Fin n) : Nat) := hf j hj ⟨z, hz⟩
        refine ⟨e ▸ (g j ⟨z, hz⟩).2, ?_⟩
        have hm : (⟨f j z, e ▸ (g j ⟨z, hz⟩).2⟩ : Fin n) = (⟨g j, hgj⟩ : G) • (⟨z, hz⟩ : Fin n) :=
          Fin.ext e
        rw [hm]
        exact MulAction.mem_orbit_of_mem_orbit _ ho)
      r _ (fun z hz => by
        change (1 <<< x).testBit z = true at hz
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow, decide_eq_true_iff] at hz
        subst hz
        exact ⟨hx, MulAction.mem_orbit_self _⟩) y hy
    exact ho

theorem card_orbit {k : Nat} {f : Nat → Nat → Nat} {G : Subgroup (Equiv.Perm (Fin n))}
    {g : Nat → Equiv.Perm (Fin n)} (hG : G = Subgroup.closure {h | ∃ j < k, g j = h})
    (hf : ∀ j < k, ∀ x : Fin n, f j x = g j x) {r x : Nat} (hx : x < n)
    (hc : orbClosed f k n r x = true) :
    Nat.card (MulAction.orbit G (⟨x, hx⟩ : Fin n)) =
      popF (closeF f k n r (Nat.shiftLeft 1 x)) n := by
  have e : MulAction.orbit G (⟨x, hx⟩ : Fin n) =
      {y : Fin n | (closeF f k n r (Nat.shiftLeft 1 x)).testBit y = true} :=
    Set.ext fun y => mem_orbit_iff hG hf hx hc y
  rw [e, card_bits]

theorem arrGen_gens {w k : Nat} {O : Array (Array Nat)} {Q QI : Nat → Nat} (hO : O.size = k)
    (hQ : ∀ j < k, O[j]! = unpack n w (Q j))
    (hp : ∀ j < k, permOK n w (mask w) (n * w) (Q j) (QI j) = true) :
    CFSG.Sporadic.HNOddCore.arrGen n O = Subgroup.closure
        {h | ∃ j < k, CFSG.Monster.B.Co2.permOfArr n O[j]! = h} ∧
      ∀ j < k, ∀ x : Fin n, pg w (mask w) (Q j) x = CFSG.Monster.B.Co2.permOfArr n O[j]! x := by
  refine ⟨by rw [CFSG.Sporadic.HNOddCore.arrGen, hO], fun j hj x => ?_⟩
  have hr := (CFSG.Monster.B.Co2.rep_permOfArr (Orb.isInvA_unpack (hp j hj))).1 x
  rw [hQ j hj, ← hr, Orb.unpack_get x.2]

theorem mem_orbit_arrGen_iff {w k : Nat} {O : Array (Array Nat)} {Q QI : Nat → Nat}
    (hO : O.size = k) (hQ : ∀ j < k, O[j]! = unpack n w (Q j))
    (hp : ∀ j < k, permOK n w (mask w) (n * w) (Q j) (QI j) = true) {r x : Nat} (hx : x < n)
    (hc : orbClosed (fun j => pg w (mask w) (Q j)) k n r x = true) (y : Fin n) :
    y ∈ MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen n O) (⟨x, hx⟩ : Fin n) ↔
      (closeF (fun j => pg w (mask w) (Q j)) k n r (Nat.shiftLeft 1 x)).testBit y = true :=
  mem_orbit_iff (arrGen_gens hO hQ hp).1 (arrGen_gens hO hQ hp).2 hx hc y

theorem card_orbit_arrGen {w k : Nat} {O : Array (Array Nat)} {Q QI : Nat → Nat}
    (hO : O.size = k) (hQ : ∀ j < k, O[j]! = unpack n w (Q j))
    (hp : ∀ j < k, permOK n w (mask w) (n * w) (Q j) (QI j) = true) {r x : Nat} (hx : x < n)
    (hc : orbClosed (fun j => pg w (mask w) (Q j)) k n r x = true) :
    Nat.card (MulAction.orbit (CFSG.Sporadic.HNOddCore.arrGen n O) (⟨x, hx⟩ : Fin n)) =
      popF (closeF (fun j => pg w (mask w) (Q j)) k n r (Nat.shiftLeft 1 x)) n :=
  card_orbit (arrGen_gens hO hQ hp).1 (arrGen_gens hO hQ hp).2 hx hc

end CFSG.KC.PtOrb

end
