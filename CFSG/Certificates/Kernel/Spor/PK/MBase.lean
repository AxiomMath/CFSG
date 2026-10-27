module

public import CFSG.Certificates.Kernel.Spor.PK.M11Enum
public import CFSG.Certificates.Kernel.Spor.PK.SiftSim
public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Certificates.Kernel.Spor.PK.CertBridge
public import CFSG.Certificates.Kernel.Spor.PK.Words
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KS.PK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.KS.MEnum CFSG.Certificates
  CFSG.Sporadic.Schreier CFSG.Monster.B.Mathieu

@[expose] def MPK (n w g : Nat) (σ : Equiv.Perm (Fin n)) : Prop :=
  g < 2 ^ (w * n) ∧ IsPermN n (fd w g) ∧ permOf n (fd w g) = σ

private theorem mb_isPermN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ x < n, f x = g x)
    (hf : IsPermN n f) : IsPermN n g :=
  ⟨fun x hx => by rw [← h x hx]; exact hf.1 x hx,
    fun x hx y hy e => hf.2 x hx y hy (by rw [h x hx, h y hy]; exact e)⟩

theorem mpk_pack {n w : Nat} (hw : n < 2 ^ w) {t : List Nat} {σ : Equiv.Perm (Fin n)}
    (h : t = imageList σ) : MPK n w (packL w t) σ := by
  subst h
  have hmem : ∀ x ∈ imageList σ, x < 2 ^ w := by
    intro x hx
    simp only [imageList, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := (σ i).isLt
    omega
  have hlen : (imageList σ).length = n := imageList_length σ
  have hget : ∀ x, (imageList σ).getD x 0 < 2 ^ w := by
    intro x
    by_cases hx : x < (imageList σ).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]
      exact hmem _ (List.getElem_mem hx)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      exact Nat.two_pow_pos w
  have hpack : packL w (imageList σ) = enc w (fun i => (imageList σ).getD i 0) n := by
    rw [packL_eq hmem, hlen]
  have hfd : ∀ x (hx : x < n), fd w (packL w (imageList σ)) x = (σ ⟨x, hx⟩ : Nat) := by
    intro x hx
    rw [hpack, fd_enc (fun i _ => hget i) hx]
    have hx' : x < (imageList σ).length := by rw [hlen]; exact hx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx', Option.getD_some]
    simp only [imageList, List.getElem_ofFn]
  have hperm : IsPermN n (fd w (packL w (imageList σ))) :=
    mb_isPermN_congr (f := fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x)
      (fun x hx => by simp [hx, hfd x hx]) (isPermN_val σ)
  refine ⟨?_, hperm, ?_⟩
  · rw [hpack]
    exact enc_lt (fun i _ => hget i)
  · exact (permOf_congr (g := fun x => if h : x < n then (σ ⟨x, h⟩ : Nat) else x)
      (fun x hx => by simp [hx, hfd x hx])).trans (permOf_val σ)

private theorem mb_pinv_eq {n w g : Nat} {σ : Equiv.Perm (Fin n)} (hw : n < 2 ^ w)
    (h : MPK n w g σ) : pinvS n w (mask w) g = enc w (finv n (fd w g)) n :=
  pinvS_eq (n := n) (w := w) (by omega) (fun i hi => h.2.1.1 i hi)
    (fun j hj => finv_spec h.2.1 hj) (fun i hi => finv_apply h.2.1 hi)

theorem mpk_fd_pinv {n w g : Nat} {σ : Equiv.Perm (Fin n)} (hn0 : 0 < n) (hw : n < 2 ^ w)
    (h : MPK n w g σ) : ∀ x < n, fd w (pinvS n w (mask w) g) x = finv n (fd w g) x := by
  have hfv : ∀ i, finv n (fd w g) i < 2 ^ w := fun i => by
    have := finv_lt (n := n) hn0 (fd w g) i
    omega
  intro x hx
  rw [mb_pinv_eq hw h, fd_enc (fun i _ => hfv i) hx]

theorem mpk_inv {n w g : Nat} {σ : Equiv.Perm (Fin n)} (hn0 : 0 < n) (hw : n < 2 ^ w)
    (h : MPK n w g σ) : MPK n w (pinvS n w (mask w) g) σ⁻¹ := by
  have hfd := mpk_fd_pinv hn0 hw h
  have hpinv := mb_pinv_eq hw h
  obtain ⟨hlt, hperm, hσ⟩ := h
  have hfv : ∀ i, finv n (fd w g) i < 2 ^ w := fun i => by
    have := finv_lt (n := n) hn0 (fd w g) i
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hpinv]
    exact enc_lt (fun i _ => hfv i)
  · exact mb_isPermN_congr (fun x hx => (hfd x hx).symm) hperm.finv
  · rw [← hσ, permOf_inv hperm]
    exact permOf_congr hfd

@[expose] def mbGens (n : Nat) (fa fb : Nat → Nat) (z : Int) : Nat → Nat :=
  if z = 1 then fa else if z = -1 then finv n fa else if z = 2 then fb else finv n fb

private def mb_Rel (n : Nat) (L : List (Nat → Nat)) (S : List (Equiv.Perm (Fin n))) : Prop :=
  L.length = 2 * S.length ∧ (∀ l, IsPermN n (L.getD l id)) ∧
    ∀ j < S.length, permOf n (L.getD (2 * j) id) = S.getD j 1 ∧
      L.getD (2 * j + 1) id = finv n (L.getD (2 * j) id)

private theorem mb_getD_pair (L : List (Nat → Nat)) (a b : Nat → Nat) (l : Nat) :
    (L ++ [a, b]).getD l id = if l < L.length then L.getD l id
      else if l = L.length then a else if l = L.length + 1 then b else id := by
  by_cases h : l < L.length
  · rw [if_pos h, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h]
  · rw [if_neg h, List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.not_lt.1 h)]
    obtain ⟨k, rfl⟩ : ∃ k, l = L.length + k := ⟨l - L.length, by omega⟩
    rw [Nat.add_sub_cancel_left]
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [if_neg (by omega), if_neg (by omega)]
      simp

private theorem mb_word {n : Nat} {gens : Int → Nat → Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) {L : List (Nat → Nat)}
    {S : List (Equiv.Perm (Fin n))} (hR : mb_Rel n L S) :
    ∀ w : List Int, (∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length) →
      IsPermN n (wordFn gens L (w.map sh)) ∧
        permOf n (wordFn gens L (w.map sh)) = evalCodes S w := by
  obtain ⟨hlen, hperm, hrel⟩ := hR
  have hlet : ∀ z : Int, 1 ≤ z.natAbs → z.natAbs ≤ S.length →
      IsPermN n (letFn gens L (sh z)) ∧ permOf n (letFn gens L (sh z)) =
        (if 0 < z then S.getD (z.toNat - 1) 1 else (S.getD ((-z).toNat - 1) 1)⁻¹) := by
    intro z hz1 hz2
    by_cases hz : 0 < z
    · have hsz : sh z = z + 2 := by rw [hsh, if_pos hz]
      have e : (z + 2).natAbs - 3 = z.toNat - 1 := by omega
      have hl : letFn gens L (sh z) = L.getD (2 * (z.toNat - 1)) id := by
        rw [hsz]
        unfold letFn
        rw [if_neg (by omega), if_pos (by omega), e]
      rw [hl, if_pos hz]
      exact ⟨hperm _, (hrel (z.toNat - 1) (by omega)).1⟩
    · have hsz : sh z = z - 2 := by rw [hsh, if_neg hz]
      have e : (z - 2).natAbs - 3 = (-z).toNat - 1 := by omega
      have hl : letFn gens L (sh z) = L.getD (2 * ((-z).toNat - 1) + 1) id := by
        rw [hsz]
        unfold letFn
        rw [if_neg (by omega), if_neg (by omega), e]
      rw [hl, if_neg hz]
      obtain ⟨h1, h2⟩ := hrel ((-z).toNat - 1) (by omega)
      refine ⟨hperm _, ?_⟩
      rw [h2, ← permOf_inv (hperm _), h1]
  intro w
  induction w with
  | nil =>
    intro _
    refine ⟨isPermN_id n, ?_⟩
    exact (permOf_eq_one_iff (isPermN_id n)).2 (fun x _ => rfl)
  | cons z w ih =>
    intro hw
    obtain ⟨ih1, ih2⟩ := ih (fun y hy => hw y (List.mem_cons_of_mem _ hy))
    obtain ⟨hl1, hl2⟩ := hlet z (hw z List.mem_cons_self).1 (hw z List.mem_cons_self).2
    have hwf : wordFn gens L ((z :: w).map sh) =
        fun x => letFn gens L (sh z) (wordFn gens L (w.map sh) x) := rfl
    rw [hwf]
    refine ⟨hl1.comp ih1, ?_⟩
    rw [← permOf_mul hl1 ih1, hl2, ih2]
    rfl

private theorem mb_rel_step {n : Nat} {gens : Int → Nat → Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) {L : List (Nat → Nat)}
    {S : List (Equiv.Perm (Fin n))} (hR : mb_Rel n L S) {w : List Int}
    (hw : ∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length) :
    mb_Rel n (L ++ [wordFn gens L (w.map sh), finv n (wordFn gens L (w.map sh))])
      (S ++ [tab (evalCodes S w)]) := by
  obtain ⟨hP, hPσ⟩ := mb_word (gens := gens) hsh hR w hw
  generalize wordFn gens L (w.map sh) = P at hP hPσ ⊢
  obtain ⟨hlen, hperm, hrel⟩ := hR
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  · intro l
    rw [mb_getD_pair]
    split_ifs
    · exact hperm l
    · exact hP
    · exact hP.finv
    · exact isPermN_id n
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjS : j < S.length
    · have h1 : 2 * j < L.length := by omega
      have h2 : 2 * j + 1 < L.length := by omega
      have hSg : (S ++ [tab (evalCodes S w)]).getD j 1 = S.getD j 1 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hjS]
      rw [mb_getD_pair, if_pos h1, mb_getD_pair, if_pos h2, hSg]
      exact hrel j hjS
    · have hj' : j = S.length := by omega
      subst hj'
      have h1 : ¬ 2 * S.length < L.length := by omega
      have h2 : ¬ 2 * S.length + 1 < L.length := by omega
      rw [mb_getD_pair, if_neg h1, if_pos (by omega), mb_getD_pair, if_neg h2,
        if_neg (by omega), if_pos (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      refine ⟨?_, rfl⟩
      rw [hPσ, tab_eq]
      rfl

private theorem mb_rel_all {n : Nat} {gens : Int → Nat → Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) :
    ∀ (ws : List (List Int)) (L : List (Nat → Nat)) (S : List (Equiv.Perm (Fin n))),
      mb_Rel n L S →
      (∀ i < ws.length, ∀ z ∈ ws.getD i [], 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length + i) →
      mb_Rel n (lettersFrom n gens L (ws.map (List.map sh))) (buildStrong S ws) := by
  intro ws
  induction ws with
  | nil => intro L S hR _; exact hR
  | cons w ws ih =>
    intro L S hR hrange
    have hw : ∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length := fun z hz => by
      have := hrange 0 (by simp) z (by simpa using hz)
      simpa using this
    have e1 : lettersFrom n gens L ((w :: ws).map (List.map sh)) =
        lettersFrom n gens (L ++ [wordFn gens L (w.map sh), finv n (wordFn gens L (w.map sh))])
          (ws.map (List.map sh)) := rfl
    have e2 : buildStrong S (w :: ws) = buildStrong (S ++ [tab (evalCodes S w)]) ws := rfl
    rw [e1, e2]
    refine ih _ _ (mb_rel_step hsh hR hw) ?_
    intro i hi z hz
    have := hrange (i + 1) (by simpa using hi) z (by simpa using hz)
    simp only [List.length_append, List.length_singleton]
    omega

private theorem mb_rel_base {n : Nat} {fa fb : Nat → Nat} {gA gB : Equiv.Perm (Fin n)}
    (ha : IsPermN n fa) (hb : IsPermN n fb) (hpa : permOf n fa = gA)
    (hpb : permOf n fb = gB) : mb_Rel n [fa, finv n fa, fb, finv n fb] [gA, gB] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro l
    match l with
    | 0 => exact ha
    | 1 => exact ha.finv
    | 2 => exact hb
    | 3 => exact hb.finv
    | l + 4 =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
      exact isPermN_id n
  · intro j hj
    match j, hj with
    | 0, _ => exact ⟨hpa, rfl⟩
    | 1, _ => exact ⟨hpb, rfl⟩

private theorem mb_wordFn_one (n : Nat) (fa fb : Nat → Nat) (L : List (Nat → Nat)) :
    wordFn (mbGens n fa fb) L [1] = fa := by
  funext x
  change letFn (mbGens n fa fb) L 1 x = fa x
  unfold letFn
  rw [if_pos (by decide)]
  unfold mbGens
  rw [if_pos rfl]

private theorem mb_wordFn_two (n : Nat) (fa fb : Nat → Nat) (L : List (Nat → Nat)) :
    wordFn (mbGens n fa fb) L [2] = fb := by
  funext x
  change letFn (mbGens n fa fb) L 2 x = fb x
  unfold letFn
  rw [if_pos (by decide)]
  unfold mbGens
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

private theorem mb_lettersFn_W (n : Nat) (fa fb : Nat → Nat) (ws : List (List Int)) :
    lettersFn n (mbGens n fa fb) ([[1], [2]] ++ ws) =
      lettersFrom n (mbGens n fa fb) [fa, finv n fa, fb, finv n fb] ws := by
  have e : lettersFn n (mbGens n fa fb) ([[1], [2]] ++ ws) =
      lettersFrom n (mbGens n fa fb) ([] ++ [wordFn (mbGens n fa fb) [] [1],
        finv n (wordFn (mbGens n fa fb) [] [1])] ++
          [wordFn (mbGens n fa fb) ([] ++ [wordFn (mbGens n fa fb) [] [1],
            finv n (wordFn (mbGens n fa fb) [] [1])]) [2],
          finv n (wordFn (mbGens n fa fb) ([] ++ [wordFn (mbGens n fa fb) [] [1],
            finv n (wordFn (mbGens n fa fb) [] [1])]) [2])]) ws := rfl
  rw [e, mb_wordFn_one, mb_wordFn_two]
  rfl

private theorem mb_range {sh : Int → Int} (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2)
    {words : List (List Int)}
    (hws : CFSG.KS.Mathieu.wordsOK ([[1], [2]] ++ words.map (List.map sh)) 0 = true) :
    ∀ i < words.length, ∀ z ∈ words.getD i [], 1 ≤ z.natAbs ∧ z.natAbs ≤ 2 + i := by
  intro i hi z hz
  have hget : ([[1], [2]] ++ words.map (List.map sh)).getD (i + 2) [] =
      (words.getD i []).map sh := by
    have e : ([[1], [2]] ++ words.map (List.map sh)).getD (i + 2) [] =
        (words.map (List.map sh)).getD i [] := by
      change ([1] :: [2] :: words.map (List.map sh)).getD (i + 1 + 1) [] = _
      rw [List.getD_cons_succ, List.getD_cons_succ]
    rw [e]
    have hmapget : ∀ (l : List (List Int)) (i : Nat),
        (l.map (List.map sh)).getD i [] = (l.getD i []).map sh := by
      intro l
      induction l with
      | nil => intro i; simp
      | cons a l ih =>
        intro i
        cases i with
        | zero => simp
        | succ i =>
          simp only [List.map_cons, List.getD_cons_succ]
          exact ih i
    exact hmapget words i
  have hmem : sh z ∈ ([[1], [2]] ++ words.map (List.map sh)).getD (i + 2) [] := by
    rw [hget]
    exact List.mem_map_of_mem hz
  have hlen : i + 2 < ([[1], [2]] ++ words.map (List.map sh)).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]
    omega
  obtain ⟨h0, h1, h2⟩ := (wordsOK_iff _ 0).1 hws (i + 2) hlen (sh z) hmem
  rw [hsh z] at h0 h1 h2
  split_ifs at h0 h1 h2 <;> omega

private theorem mb_rel_letters {n : Nat} {fa fb : Nat → Nat} {gA gB : Equiv.Perm (Fin n)}
    {sh : Int → Int} (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) (ha : IsPermN n fa)
    (hb : IsPermN n fb) (hpa : permOf n fa = gA) (hpb : permOf n fb = gB)
    {words : List (List Int)}
    (hws : CFSG.KS.Mathieu.wordsOK ([[1], [2]] ++ words.map (List.map sh)) 0 = true) :
    mb_Rel n (lettersFn n (mbGens n fa fb) ([[1], [2]] ++ words.map (List.map sh)))
      (buildStrong [gA, gB] words) := by
  rw [mb_lettersFn_W]
  exact mb_rel_all hsh words _ [gA, gB] (mb_rel_base ha hb hpa hpb) (fun i hi z hz => by
    have := mb_range hsh hws i hi z hz
    simpa using this)

private theorem mb_LT_eq {n w A B : Nat} {gA gB : Equiv.Perm (Fin n)} (hn16 : n < 2 ^ 16)
    (hw : n + 1 < 2 ^ w) (hn0 : 0 < n) (hA : MPK n w A gA) (hB : MPK n w B gB)
    {W : List (List Int)} (hws : CFSG.KS.Mathieu.wordsOK W 0 = true) :
    lettersP n w (mask w) (n * w) (mask (n * w)) (pidn n w) A (pinvS n w (mask w) A) B
        (pinvS n w (mask w) B) W 0 0 =
      enc (n * w) (fun l => enc w ((lettersFn n (mbGens n (fd w A) (fd w B)) W).getD l id) n)
        (2 * W.length) := by
  have hwn : n < 2 ^ w := by omega
  exact lettersP_eq (n := n) (w := w) (A := A) (Ai := pinvS n w (mask w) A) (B := B)
    (Bi := pinvS n w (mask w) B) (gens := mbGens n (fd w A) (fd w B)) hn16 hw
    (fun x _ => by unfold mbGens; rw [if_pos rfl])
    (fun x hx => by
      unfold mbGens
      rw [if_neg (by decide), if_pos rfl]
      exact (mpk_fd_pinv hn0 hwn hA x hx).symm)
    (fun x _ => by
      unfold mbGens
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl])
    (fun x hx => by
      unfold mbGens
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      exact (mpk_fd_pinv hn0 hwn hB x hx).symm)
    (fun z hz0 hz2 => by
      unfold mbGens
      by_cases h1 : z = 1
      · rw [if_pos h1]; exact hA.2.1
      by_cases h2 : z = -1
      · rw [if_neg h1, if_pos h2]; exact hA.2.1.finv
      by_cases h3 : z = 2
      · rw [if_neg h1, if_neg h2, if_pos h3]; exact hB.2.1
      · rw [if_neg h1, if_neg h2, if_neg h3]; exact hB.2.1.finv) hws

private theorem mb_finv_finv {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) {x : Nat} (hx : x < n) :
    finv n (finv n f) x = f x := by
  have h := finv_apply hf.finv (hf.1 x hx)
  rwa [finv_apply hf hx] at h

private theorem mb_letF {n w NL : Nat} {Fa : Nat → Nat → Nat} (hw : n < 2 ^ w)
    (hF : ∀ l, IsPermN n (Fa l)) {LT : Nat} (hLT : LT = enc (n * w) (fun l => enc w (Fa l) n) NL) :
    ∀ l < NL, ∀ x < n, letF n w LT l x = Fa l x := by
  intro l hl x hx
  have h1 : ∀ i < NL, enc w (Fa i) n < 2 ^ (n * w) := fun i _ => by
    rw [Nat.mul_comm n w]
    exact enc_lt (fun j hj => by have := (hF i).1 j hj; omega)
  have h2 : ∀ j < n, Fa l j < 2 ^ w := fun j hj => by
    have := (hF l).1 j hj
    omega
  change fd w (fd (n * w) LT l) x = _
  rw [hLT, fd_enc h1 hl, fd_enc h2 hx]

private theorem mb_PairsOK {n NL m : Nat} {F : Nat → Nat → Nat} {L : List (Nat → Nat)}
    (hNL : NL = 2 * m) (hF : ∀ l < NL, ∀ x < n, F l x = L.getD l id x)
    (hL : ∀ l, IsPermN n (L.getD l id))
    (hodd : ∀ j < m, L.getD (2 * j + 1) id = finv n (L.getD (2 * j) id)) : PairsOK n F NL := by
  refine ⟨by omega, fun l hl => ⟨mb_isPermN_congr (fun x hx => (hF l hl x hx).symm) (hL l), ?_⟩⟩
  intro x hx
  unfold CFSG.Perm.Native.invL
  by_cases hev : l % 2 = 0
  · rw [if_pos hev]
    obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j := ⟨l / 2, by omega⟩
    rw [hF (2 * j + 1) (by omega) x hx, hodd j (by omega)]
    exact finv_congr (fun y hy => (hF (2 * j) hl y hy).symm) x
  · rw [if_neg hev]
    obtain ⟨j, rfl⟩ : ∃ j, l = 2 * j + 1 := ⟨l / 2, by omega⟩
    have e : 2 * j + 1 - 1 = 2 * j := by omega
    rw [e, hF (2 * j) (by omega) x hx, finv_congr (fun y hy => hF (2 * j + 1) hl y hy) x,
      hodd j (by omega), mb_finv_finv (hL (2 * j)) hx]

private theorem mb_absChain_iff {n NL : Nat} {F : Nat → Nat → Nat} (ps : List (BS × Nat)) :
    absChain n F NL ps = true ↔ ∀ i (h : i < ps.length),
      absSch n F (maskL NL ps[i].2) ps[i].1 ((ps.drop (i + 1)).map Prod.fst) = true := by
  induction ps with
  | nil => simp [absChain]
  | cons p ps ih =>
    rw [absChain, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ j => exact h1 j (Nat.lt_of_succ_lt_succ hi)
    · intro h
      exact ⟨h 0 (Nat.succ_pos _), fun j hj => h (j + 1) (Nat.succ_lt_succ hj)⟩

private theorem mb_levLast (n w LT NL : Nat) (bs : List Nat) :
    levLast n w LT NL bs (mask NL) = levMaskAt n w LT NL bs bs.length := by
  unfold levMaskAt
  rw [List.take_length]

theorem mb_chain {n w LT NL : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l < NL, IsPermN n (letF n w LT l)) {bs sz : List Nat} (hbs : ∀ b ∈ bs, b < n)
    (h : levels n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL bs (mask NL)
      (fun Ls LVt => (chainSch n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL Ls &&
        (maskId (n * w) (mask (n * w)) (pidn n w) LT NL LVt && sizesEq Ls sz))) = true) :
    (∀ i (hi : i < (natLevels n (letF n w LT) NL bs).length),
      absSch n (letF n w LT) (natLevels n (letF n w LT) NL bs)[i].1
        (natLevels n (letF n w LT) NL bs)[i].2.2
        (((natLevels n (letF n w LT) NL bs).drop (i + 1)).map fun e => e.2.2) = true) ∧
    (∀ l ∈ lvAt (letF n w LT) NL bs bs.length, ∀ x < n, letF n w LT l x = x) ∧
    (natLevels n (letF n w LT) NL bs).map (fun e => e.2.2.pts.length) = sz := by
  rw [levels_eq hn16 hw hL hbs] at h
  simp only [Bool.and_eq_true] at h
  rw [mb_levLast] at h
  generalize hps : levPairs n w LT NL bs (mask NL) = ps at h
  obtain ⟨hsch, hmid, hsz⟩ := h
  have hps' : ps = (List.range bs.length).map fun i =>
      (BS.run (letF n w LT) (lvAt (letF n w LT) NL bs i) n (bs.getD i 0),
        levMaskAt n w LT NL bs i) := by
    rw [← hps]
    exact levPairs_eq _
  have hlen : ps.length = bs.length := by
    rw [hps']
    simp
  have hget : ∀ i (hi : i < ps.length), ps[i] =
      (BS.run (letF n w LT) (lvAt (letF n w LT) NL bs i) n (bs.getD i 0),
        levMaskAt n w LT NL bs i) := by
    intro i hi
    subst hps'
    simp
  have hgood : ∀ p ∈ ps, GoodBS n (letF n w LT) p.1 := by
    intro p hp
    rw [hps'] at hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    have hmem : bs.getD i 0 ∈ bs := by
      rw [List.getD_eq_getElem _ _ (List.mem_range.1 hi)]
      exact List.getElem_mem _
    exact goodBS_run (hbs _ hmem) (fun l hl => hL l (lvAt_sub _ _ _ _ l hl))
  have hfst : ps.map Prod.fst =
      (natLevels n (letF n w LT) NL bs).map (fun e => e.2.2) := by
    rw [hps']
    simp [natLevels, List.map_map, Function.comp_def]
  have hnl : ∀ i (hi : i < (natLevels n (letF n w LT) NL bs).length),
      (natLevels n (letF n w LT) NL bs)[i] = (lvAt (letF n w LT) NL bs i, bs.getD i 0,
        BS.run (letF n w LT) (lvAt (letF n w LT) NL bs i) n (bs.getD i 0)) := by
    intro i hi
    simp [natLevels]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i < bs.length := by simpa [natLevels] using hi
    have hi' : i < ps.length := by rw [hlen]; exact hi0
    have habs : absChain n (letF n w LT) NL ps = true := by
      rw [← chainSch_eq hn16 hw hL hgood]
      exact hsch
    have h1 := (mb_absChain_iff ps).1 habs i hi'
    have e1 := hget i hi'
    have e2 : (ps[i]'hi').2 = levMaskAt n w LT NL bs i := by rw [e1]
    have e3 : (ps[i]'hi').1 =
        BS.run (letF n w LT) (lvAt (letF n w LT) NL bs i) n (bs.getD i 0) := by
      rw [e1]
    have hmask : maskL NL (levMaskAt n w LT NL bs i) = lvAt (letF n w LT) NL bs i := by
      rw [maskL_levMaskAt, Nat.min_eq_left (Nat.le_of_lt hi0)]
    have hdrop : (ps.drop (i + 1)).map Prod.fst =
        ((natLevels n (letF n w LT) NL bs).drop (i + 1)).map (fun e => e.2.2) := by
      rw [List.map_drop, hfst, List.map_drop]
    rw [e2, e3, hmask, hdrop] at h1
    rw [hnl i hi]
    exact h1
  · rw [maskId_iff hn16 hw, maskL_levMaskAt, Nat.min_self] at hmid
    exact hmid
  · have h1 := (sizesEq_iff _ _).1 hsz
    have h2 : List.map lcnt (List.map (fun p => recBS n w (letF n w LT) p.fst p.snd) ps) =
        ps.map (fun p => p.1.pts.length) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro p hp
      exact lcnt_recBS hn16 hw (hgood p hp) p.2
    rw [h2] at h1
    rw [← h1]
    have h3 : (natLevels n (letF n w LT) NL bs).map (fun e => e.2.2.pts.length) =
        ((natLevels n (letF n w LT) NL bs).map (fun e => e.2.2)).map
          (fun s => s.pts.length) := by
      rw [List.map_map]
      rfl
    have h4 : ps.map (fun p => p.1.pts.length) = (ps.map Prod.fst).map (fun s => s.pts.length) := by
      rw [List.map_map]
      rfl
    rw [h3, ← hfst, h4]

theorem levN_eq {n w LT NL : Nat} (hn16 : n < 2 ^ 16) (hw : n + 1 < 2 ^ w)
    (hL : ∀ l < NL, IsPermN n (letF n w LT l)) {bs : List Nat} (hbs : ∀ b ∈ bs, b < n) (LV : Nat)
    (k : List Nat → Nat → Nat) :
    levN n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL bs LV k =
      k ((levPairs n w LT NL bs LV).map fun p => recBS n w (letF n w LT) p.1 p.2)
        (levLast n w LT NL bs LV) := by
  induction bs generalizing LV k with
  | nil => rfl
  | cons b bs ih =>
    have hb : b < n := hbs b List.mem_cons_self
    have hbs' : ∀ c ∈ bs, c < n := fun c hc => hbs c (List.mem_cons_of_mem _ hc)
    have hLV : ∀ l ∈ maskL NL LV, IsPermN n (letF n w LT l) := fun l hl =>
      hL l (List.mem_range.mp (List.mem_filter.mp hl).1)
    change strictN (bfs n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL LV b) (fun S =>
      strictN (fixMask w (mask w) (n * w) (mask (n * w)) LT NL LV b) (fun LV' =>
        levN n w (mask w) (n * w) (mask (n * w)) (pidn n w) LT NL bs LV'
          (fun Ls LVt => k (S :: Ls) LVt))) = _
    rw [strictN_eq, bfs_eq hn16 hw hb hLV, strictN_eq, ih hbs']
    rfl

private theorem mb_map_idxOf {α β : Type*} [BEq α] [LawfulBEq α] {l : List α}
    (hl : l.Nodup) (g : Nat → β) :
    l.map (fun v => g (l.idxOf v)) = (List.range l.length).map g := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [hl.idxOf_getElem]

private theorem mb_levelTransversals {n : Nat} {hn : 1 ≤ n} {F : Nat → Nat → Nat} {NL k : Nat}
    {bs : Vector (Fin n) k} {hbs : bs.toList.Nodup} (hF : PairsOK n F NL) (i : Fin k) :
    levelTransversals (rawOf n hn F NL bs hbs) i =
      (List.range (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n
          (bs.get i).val).pts.length).map
        fun j => permOf n (BS.trans F (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n
          (bs.get i).val) j) := by
  have hkeys := rawOf_keys (hn := hn) (hbs := hbs) hF i
  have hok : RunOK n F (lvAt F NL (bs.toList.map Fin.val) i.val) (bs.get i).val
      (BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val) :=
    run_ok (fun l hl x hx => (hF.2 l (lvAt_sub _ _ _ _ l hl)).1.1 x hx) (bs.get i).isLt
  have hnd := hok.nodup
  have htr := rawOf_transversal (hn := hn) (hbs := hbs) hF i
  set s := BS.run F (lvAt F NL (bs.toList.map Fin.val) i.val) n (bs.get i).val with hs
  change ((rawOf n hn F NL bs hbs).orbitSearch i).keys.map
    (fun x => (((rawOf n hn F NL bs hbs).orbitSearch i).transversal? x).getD 1) = _
  rw [← mb_map_idxOf hnd]
  have e := congrArg (List.map fun v => permOf n (BS.trans F s (s.pts.idxOf v))) hkeys
  rw [List.map_map] at e
  rw [← e]
  refine List.map_congr_left fun x hx => ?_
  have hxmem : x.val ∈ s.pts := by
    rw [← hkeys]
    exact List.mem_map_of_mem hx
  change ((rawOf n hn F NL bs hbs).transversal? i x).getD 1 = _
  rw [htr x]
  dsimp only
  rw [if_pos hxmem]
  rfl

@[expose] noncomputable def mbF (n w : Nat) (tA tB : List Nat) (W : List (List Int)) :
    Nat → Nat → Nat :=
  letF n w (mLT n w tA tB W)

@[expose] def mbS (n : Nat) (F : Nat → Nat → Nat) (NL : Nat) (bs : List Nat) (i : Nat) : BS :=
  BS.run F (lvAt F NL bs i) n (bs.getD i 0)

private theorem mb_allLtN_iff (n : Nat) : ∀ l : List Nat, allLtN n l = true ↔ ∀ x ∈ l, x < n
  | [] => by simp [allLtN]
  | x :: l => by
    change bAnd(Nat.blt x n, allLtN n l) = true ↔ _
    rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, mb_allLtN_iff n l, List.forall_mem_cons]

theorem mBase_facts {n w : Nat} {bs sz : List Nat} {NW : Nat} {tA tB : List Nat}
    {W : List (List Int)} (hbase : mBase n w bs sz NW tA tB W = true) :
    n < 2 ^ 24 ∧ n + 1 < 2 ^ w ∧ (∀ b ∈ bs, b < n) := by
  simp only [mBase, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hbase
  obtain ⟨h1, -, h3, h4, -⟩ := hbase
  have hm := mask_eq w
  refine ⟨by simpa using h1, by omega, (mb_allLtN_iff n bs).1 h4⟩

theorem mBase_chain {n w k : Nat} {gA gB : Equiv.Perm (Fin n)} {words : List (List Int)}
    {hn : 1 ≤ n} {bv : Vector (Fin n) k} {hbs : bv.toList.Nodup}
    {tA tB : List Nat} {W : List (List Int)} {bs sz : List Nat} {NW : Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2)
    (hA : tA = imageList gA) (hB : tB = imageList gB)
    (hW : W = [[1], [2]] ++ words.map (List.map sh))
    (hbsv : bs = bv.toList.map Fin.val) (hNW : NW = words.length + 2) (hn16 : n < 2 ^ 16)
    (hbase : mBase n w bs sz NW tA tB W = true) :
    (certificate hn [gA, gB] words bv hbs).check = true ∧
      (enumeration (certificate hn [gA, gB] words bv hbs)).Perm
        (products ((List.range k).map fun i =>
          (List.range (mbS n (mbF n w tA tB W) (NW + NW) bs i).pts.length).map fun j =>
            permOf n (BS.trans (mbF n w tA tB W) (mbS n (mbF n w tA tB W) (NW + NW) bs i) j))) ∧
      (List.range k).map (fun i => (mbS n (mbF n w tA tB W) (NW + NW) bs i).pts.length) = sz ∧
      (∀ l < NW + NW, IsPermN n (mbF n w tA tB W l)) := by
  obtain ⟨-, hw, hbsl⟩ := mBase_facts hbase
  have hn0 : 0 < n := hn
  have hwn : n < 2 ^ w := by omega
  have hAPK : MPK n w (packL w tA) gA := mpk_pack hwn hA
  have hBPK : MPK n w (packL w tB) gB := mpk_pack hwn hB
  have hbase' := hbase
  simp only [mBase, strictB_eq, bAnd_eq, Bool.and_eq_true, Nat.mul_eq, Nat.add_eq] at hbase'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h11, h12, -, -, h15⟩ := hbase'
  have hlenW : W.length = NW := by
    rw [← lenW_eq]
    exact Nat.eq_of_beq_eq_true h12
  have hws : CFSG.KS.Mathieu.wordsOK ([[1], [2]] ++ words.map (List.map sh)) 0 = true :=
    hW ▸ h11
  have hRel0 := mb_rel_letters (n := n) (gA := gA) (gB := gB) hsh hAPK.2.1 hBPK.2.1 hAPK.2.2
    hBPK.2.2 hws
  rw [← hW] at hRel0
  have hLT0 : mLT n w tA tB W = lettersP n w (mask w) (n * w) (mask (n * w)) (pidn n w)
      (packL w tA) (pinvS n w (mask w) (packL w tA)) (packL w tB)
      (pinvS n w (mask w) (packL w tB)) W 0 0 := by
    unfold mLT
    simp only [strictN_eq]
    rfl
  have hLT := mb_LT_eq hn16 hw hn0 hAPK hBPK h11
  rw [← hLT0, hlenW] at hLT
  generalize lettersFn n (mbGens n (fd w (packL w tA)) (fd w (packL w tB))) W = L at hRel0 hLT
  have hS : (buildStrong [gA, gB] words).length = NW := by
    rw [length_buildStrong]
    simp only [List.length_cons, List.length_nil]
    omega
  have hNL : NW + NW = 2 * NW := by omega
  have hF : ∀ l < NW + NW, ∀ x < n, mbF n w tA tB W l x = L.getD l id x := by
    rw [hNL]
    exact mb_letF hwn hRel0.2.1 hLT
  have hLperm : ∀ l < NW + NW, IsPermN n (mbF n w tA tB W l) := fun l hl =>
    mb_isPermN_congr (fun x hx => (hF l hl x hx).symm) (hRel0.2.1 l)
  have h15' : levels n w (mask w) (n * w) (mask (n * w)) (pidn n w) (mLT n w tA tB W) (NW + NW) bs
      (mask (NW + NW)) (fun Ls LVt =>
        (chainSch n w (mask w) (n * w) (mask (n * w)) (pidn n w) (mLT n w tA tB W) (NW + NW) Ls &&
          (maskId (n * w) (mask (n * w)) (pidn n w) (mLT n w tA tB W) (NW + NW) LVt &&
            sizesEq Ls sz))) = true := by
    refine Eq.trans ?_ h15
    congr 1
  obtain ⟨hsch, hterm, hszs⟩ := mb_chain hn16 hw hLperm hbsl h15'
  have hPairs : PairsOK n (mbF n w tA tB W) (NW + NW) := by
    refine mb_PairsOK (m := NW) hNL hF hRel0.2.1 (fun j hj => ?_)
    exact (hRel0.2.2 j (by rw [hS]; exact hj)).2
  have hLetters : LettersOf n (mbF n w tA tB W) (buildStrong [gA, gB] words) := by
    intro j hj
    rw [hS] at hj
    have hj12 : 2 * j < NW + NW := by omega
    have hj12' : 2 * j + 1 < NW + NW := by omega
    obtain ⟨h1, h2⟩ := hRel0.2.2 j (by rw [hS]; exact hj)
    refine ⟨mb_isPermN_congr (fun x hx => (hF _ hj12 x hx).symm) (hRel0.2.1 _), ?_, ?_⟩
    · rw [← h1]
      exact permOf_congr (fun x hx => hF _ hj12 x hx)
    · intro x hx
      rw [hF _ hj12' x hx, h2]
      exact finv_congr (fun y hy => (hF _ hj12 y hy).symm) x
  have hbl : bs.length = k := by rw [hbsv]; simp
  have hNL' : NW + NW = 2 * ([gA, gB].length + words.length) := by
    simp only [List.length_cons, List.length_nil]
    omega
  have hterm' : ∀ l ∈ lvAt (mbF n w tA tB W) (NW + NW) (bv.toList.map Fin.val) k, ∀ x < n,
      mbF n w tA tB W l x = x := by
    rw [← hbsv, ← hbl]
    exact hterm
  have hsch' := hsch
  rw [hbsv] at hsch'
  rw [hNL'] at hPairs hsch' hterm'
  have hQ'chk := rawOf_check (hn := hn) (bs := bv) (hbs := hbs) hPairs hsch' hterm'
  have hQchk : (certificate hn [gA, gB] words bv hbs).check = true :=
    check_certificate hn [gA, gB] words bv hbs hLetters hQ'chk
  have hlev := levelSubgroup_certificate_eq hn [gA, gB] words bv hbs hLetters 0
  have hperm := perm_enumeration hQchk hQ'chk hlev
  have hget : ∀ i : Fin k, (bv.get i).val = bs.getD i.val 0 := by
    intro i
    rw [hbsv, List.getD_eq_getElem _ _ (by simp)]
    simp [Vector.get]
  have hfin : ∀ (g : Nat → List (Equiv.Perm (Fin n))),
      (List.finRange k).map (fun i => g i.val) = (List.range k).map g := by
    intro g
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  have henum : enumeration (rawOf n hn (mbF n w tA tB W) (2 * ([gA, gB].length + words.length))
      bv hbs) = products ((List.range k).map fun i =>
        (List.range (mbS n (mbF n w tA tB W) (NW + NW) bs i).pts.length).map fun j =>
          permOf n (BS.trans (mbF n w tA tB W) (mbS n (mbF n w tA tB W) (NW + NW) bs i) j)) := by
    change products ((List.finRange k).map (levelTransversals (rawOf n hn (mbF n w tA tB W)
      (2 * ([gA, gB].length + words.length)) bv hbs))) = _
    rw [← hfin]
    refine congrArg products (List.map_congr_left fun i _ =>
      (mb_levelTransversals (hn := hn) (bs := bv) (hbs := hbs) hPairs i).trans ?_)
    rw [hget i]
    simp only [mbS, ← hNL', ← hbsv]
  refine ⟨hQchk, henum ▸ hperm, ?_, hLperm⟩
  rw [← hszs, ← hbl]
  simp [natLevels, mbS, mbF, List.map_map, Function.comp_def]

end CFSG.KS.PK

end
