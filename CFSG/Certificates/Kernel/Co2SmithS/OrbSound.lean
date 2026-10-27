module

public import Certificates.Data.Kernel.Co2SmithS.Orb
public import Certificates.Data.CFSGNative.Co2Smith.Check
import CFSG.Certificates.Kernel.Co2SmithS.BfsSound
import Mathlib.Data.Fintype.EquivFin

public section

namespace CFSG.KC.Co2SmithS

open CFSG.Sporadic.Co2Smith.Native

private structure OrbFacts (stepK : Nat → Nat → Nat) (ngen N start : Nat)
    (T PA LA M S : Nat → Nat) (TB : Nat → Nat → Nat) (i : Nat) : Prop where
  img : ∀ l < ngen, TB i l < N ∧ stepK l (T i) = T (TB i l)
  cnt : M (i + 1) = if i < M i then rowC PA LA TB ngen i (M i) else 0
  s : S i < N
  sort : i + 1 < N → T (S i) < T (S (i + 1))
  root : i = 0 → T 0 = start ∧ PA 0 = 0 ∧ LA 0 = 0 ∧ M 0 = 1
  tree : 0 < i → PA i < i ∧ LA i < ngen ∧ T i = stepK (LA i) (T (PA i))

private theorem orbFacts {stepK : Nat → Nat → Nat} {ngen N start : Nat}
    {T PA LA M S : Nat → Nat} {TB : Nat → Nat → Nat} {i : Nat}
    (h : orbRecK stepK ngen N start T PA LA M S TB i = true) :
    OrbFacts stepK ngen N start T PA LA M S TB i := by
  unfold orbRecK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun l hl => ?_, Nat.eq_of_beq_eq_true h2, of_decide_eq_true h3, fun hk => ?_,
    fun hk => ?_, fun hk => ?_⟩
  · rw [List.all_eq_true] at h1
    have := h1 l (List.mem_range.2 hl)
    simp only [Bool.and_eq_true] at this
    exact ⟨of_decide_eq_true this.1, Nat.eq_of_beq_eq_true this.2⟩
  · rw [Bool.or_eq_true] at h4
    rcases h4 with h4 | h4
    · rw [Bool.not_eq_true'] at h4
      exact absurd hk (of_decide_eq_false h4)
    · exact of_decide_eq_true h4
  · subst hk
    rw [if_pos rfl] at h5
    simp only [Bool.and_eq_true] at h5
    obtain ⟨⟨⟨a, b⟩, c⟩, d⟩ := h5
    exact ⟨Nat.eq_of_beq_eq_true a, Nat.eq_of_beq_eq_true b, Nat.eq_of_beq_eq_true c,
      Nat.eq_of_beq_eq_true d⟩
  · rw [if_neg (by omega)] at h5
    simp only [Bool.and_eq_true] at h5
    obtain ⟨⟨a, b⟩, c⟩ := h5
    exact ⟨of_decide_eq_true a, of_decide_eq_true b, Nat.eq_of_beq_eq_true c⟩

private theorem inj_of_sort {T S : Nat → Nat} {N : Nat} (hs : ∀ k < N, S k < N)
    (hsort : ∀ k, k + 1 < N → T (S k) < T (S (k + 1))) :
    ∀ i < N, ∀ j < N, T i = T j → i = j := by
  have hmono : ∀ a b, a < b → b < N → T (S a) < T (S b) := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h | h
      · exact Nat.lt_trans (ih h (by omega)) (hsort b hb)
      · subst h
        exact hsort a hb
  let f : Fin N → Fin N := fun t => ⟨S t.val, hs t.val t.isLt⟩
  have hf : Function.Injective f := by
    intro a b hab
    have e : S a.val = S b.val := congrArg Fin.val hab
    rcases Nat.lt_trichotomy a.val b.val with h | h | h
    · have := hmono _ _ h b.isLt
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
    · exact Fin.ext h
    · have := hmono _ _ h a.isLt
      rw [e] at this
      exact absurd this (Nat.lt_irrefl _)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.1 hf
  intro i hi j hj e
  obtain ⟨a, ha⟩ := hsurj ⟨i, hi⟩
  obtain ⟨b, hb⟩ := hsurj ⟨j, hj⟩
  have ea : S a.val = i := congrArg Fin.val ha
  have eb : S b.val = j := congrArg Fin.val hb
  rcases Nat.lt_trichotomy a.val b.val with h | h | h
  · have := hmono _ _ h b.isLt
    rw [ea, eb, e] at this
    exact absurd this (Nat.lt_irrefl _)
  · rw [← ea, ← eb, h]
  · have := hmono _ _ h a.isLt
    rw [ea, eb, e] at this
    exact absurd this (Nat.lt_irrefl _)

private theorem posMapN_eq (pts : Array Nat) :
    posMapN pts = (List.range pts.size).foldl (fun m i => m.insert pts[i]! i) ∅ := by
  unfold posMapN
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Id.run, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, List.forIn_pure_yield_eq_foldl, List.range_eq_range']
  rfl

theorem orbRec_sound {step stepK : Nat → Nat → Nat} {ngen N start cap : Nat}
    {T PA LA M S : Nat → Nat} {TB : Nat → Nat → Nat} (hN : 0 < N) (hcap : N ≤ cap)
    (hstep : ∀ l < ngen, ∀ x, step l x = stepK l x) (hlast : M N = N)
    (h : ∀ i < N, orbRecK stepK ngen N start T PA LA M S TB i = true) :
    orbitBFS step ngen start cap = (Array.ofFn (n := N) fun i => T i.val,
      Array.ofFn (n := N) fun i => PA i.val, Array.ofFn (n := N) fun i => LA i.val) ∧
    ∀ closed, treeOK step ngen start N closed (Array.ofFn (n := N) fun i => T i.val,
      Array.ofFn (n := N) fun i => PA i.val, Array.ofFn (n := N) fun i => LA i.val) = true := by
  have hF : ∀ i < N, OrbFacts stepK ngen N start T PA LA M S TB i := fun i hi => orbFacts (h i hi)
  have hinj : ∀ i < N, ∀ j < N, T i = T j → i = j :=
    inj_of_sort (fun k hk => (hF k hk).s) (fun k hk => (hF k (by omega)).sort hk)
  obtain ⟨hT0, hp0, hl0, hm0⟩ := (hF 0 hN).root rfl
  have hpt : ∀ i < N, ∀ l < ngen, TB i l < N ∧ step l (T i) = T (TB i l) := fun i hi l hl =>
    ⟨((hF i hi).img l hl).1, by rw [hstep l hl]; exact ((hF i hi).img l hl).2⟩
  have hbfs : orbitBFS step ngen start cap = (Array.ofFn (n := N) fun i => T i.val,
      Array.ofFn (n := N) fun i => PA i.val, Array.ofFn (n := N) fun i => LA i.val) := by
    rw [orbitBFS_eq, ← hT0]
    exact gbfs_of (key := id) hcap hinj hpt ⟨hN, hm0, fun k hk => (hF k hk).cnt, hlast⟩ hp0 hl0
  refine ⟨hbfs, fun closed => ?_⟩
  have hget : ∀ (f : Nat → Nat) i, i < N → (Array.ofFn (n := N) fun i => f i.val)[i]! = f i :=
    fun f i hi => by
      rw [getElem!_pos _ i (by simpa using hi)]
      simp
  have hpos : ∀ i < N, (posMapN (Array.ofFn (n := N) fun i => T i.val)).getD (T i) N = i := by
    intro i hi
    rw [posMapN_eq]
    have := CFSG.KS.VOR.vindex_get (pts := Array.ofFn (n := N) fun i => T i.val) (k := id)
      (fun a ha b hb e => by
        simp only [Array.size_ofFn] at ha hb
        simp only [id, hget T a ha, hget T b hb] at e
        exact hinj a ha b hb e) i (by simpa using hi)
    simp only [id, hget T i hi, Array.size_ofFn] at this
    rw [Std.HashMap.getD_eq_getD_getElem?, Array.size_ofFn, this]
    rfl
  unfold treeOK
  dsimp only
  simp only [Array.size_ofFn, beq_self_eq_true, Bool.true_and, Bool.and_eq_true, List.all_eq_true,
    List.mem_range]
  refine ⟨?_, fun x hx => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · rw [hget T 0 hN, hT0]
    exact beq_self_eq_true _
  · rw [hget T x hx, hpos x hx]
    exact beq_self_eq_true _
  · by_cases h0 : x = 0
    · subst h0
      rfl
    · obtain ⟨hp, hl, he⟩ := (hF x hx).tree (by omega)
      rw [hget PA x hx, hget LA x hx, hget T x hx, hget T (PA x) (by omega), hstep _ hl, ← he]
      simp [hp, hl]
  · cases closed
    · rfl
    · simp only [Bool.not_true, Bool.false_or, List.all_eq_true, List.mem_range, Bool.and_eq_true]
      intro l hl
      obtain ⟨ht, e⟩ := hpt x hx l hl
      rw [hget T x hx, e, hpos _ ht, hget T _ ht]
      simp [ht]

end CFSG.KC.Co2SmithS

end
