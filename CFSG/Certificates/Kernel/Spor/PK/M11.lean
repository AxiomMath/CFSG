module

public import CFSG.Certificates.Kernel.Spor.PK.M11Enum
public import CFSG.Certificates.Kernel.Spor.PK.SiftSim
public import CFSG.Monster.B.Mathieu.Order
public import CFSG.Certificates.Kernel.Spor.PK.CertBridge
public import CFSG.Certificates.Kernel.Spor.PK.Words
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
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

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.M11 CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Monster.B.Mathieu

private theorem m11_isPermN_congr {n : Nat} {f g : Nat → Nat} (h : ∀ x < n, f x = g x)
    (hf : IsPermN n f) : IsPermN n g :=
  ⟨fun x hx => by rw [← h x hx]; exact hf.1 x hx,
    fun x hx y hy e => hf.2 x hx y hy (by rw [h x hx, h y hy]; exact e)⟩

private def m11_PK (g : Nat) (σ : Equiv.Perm (Fin 11)) : Prop :=
  g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g) ∧ permOf 11 (fd 4 g) = σ

private theorem m11_PK_pack {t : List Nat} {σ : Equiv.Perm (Fin 11)} (h : t = imageList σ) :
    m11_PK (packL 4 t) σ := by
  subst h
  have hmem : ∀ x ∈ imageList σ, x < 2 ^ 4 := by
    intro x hx
    simp only [imageList, List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have := (σ i).isLt
    omega
  have hlen : (imageList σ).length = 11 := imageList_length σ
  have hget : ∀ x, (imageList σ).getD x 0 < 2 ^ 4 := by
    intro x
    by_cases hx : x < (imageList σ).length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx]
      exact hmem _ (List.getElem_mem hx)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      decide
  have hpack : packL 4 (imageList σ) = enc 4 (fun i => (imageList σ).getD i 0) 11 := by
    rw [packL_eq hmem, hlen]
  have hfd : ∀ x (hx : x < 11), fd 4 (packL 4 (imageList σ)) x = (σ ⟨x, hx⟩ : Nat) := by
    intro x hx
    rw [hpack, fd_enc (fun i _ => hget i) hx]
    have hx' : x < (imageList σ).length := by rw [hlen]; exact hx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hx', Option.getD_some]
    simp only [imageList, List.getElem_ofFn]
  have hperm : IsPermN 11 (fd 4 (packL 4 (imageList σ))) :=
    m11_isPermN_congr (f := fun x => if h : x < 11 then (σ ⟨x, h⟩ : Nat) else x) 
      (fun x hx => by simp [hx, hfd x hx]) (isPermN_val σ)
  refine ⟨?_, hperm, ?_⟩
  · rw [hpack]
    exact enc_lt (fun i _ => hget i)
  · exact (permOf_congr (g := fun x => if h : x < 11 then (σ ⟨x, h⟩ : Nat) else x)
      (fun x hx => by simp [hx, hfd x hx])).trans (permOf_val σ)

private theorem m11_fd_pinv {g : Nat} {σ : Equiv.Perm (Fin 11)} (h : m11_PK g σ) :
    ∀ x < 11, fd 4 (pinvS 11 4 15 g) x = finv 11 (fd 4 g) x := by
  obtain ⟨hlt, hperm, hσ⟩ := h
  have hpinv : pinvS 11 4 15 g = enc 4 (finv 11 (fd 4 g)) 11 :=
    pinvS_eq (n := 11) (w := 4) (by decide) (fun i hi => by have := hperm.1 i hi; omega)
      (fun j hj => finv_spec hperm hj) (fun i hi => finv_apply hperm hi)
  have hfv : ∀ i, finv 11 (fd 4 g) i < 2 ^ 4 := fun i => by
    have := finv_lt (n := 11) (by omega) (fd 4 g) i
    omega
  intro x hx
  rw [hpinv, fd_enc (fun i _ => hfv i) hx]

private theorem m11_PK_inv {g : Nat} {σ : Equiv.Perm (Fin 11)} (h : m11_PK g σ) :
    m11_PK (pinvS 11 4 15 g) σ⁻¹ := by
  have hfd := m11_fd_pinv h
  obtain ⟨hlt, hperm, hσ⟩ := h
  have hpinv : pinvS 11 4 15 g = enc 4 (finv 11 (fd 4 g)) 11 :=
    pinvS_eq (n := 11) (w := 4) (by decide) (fun i hi => by have := hperm.1 i hi; omega)
      (fun j hj => finv_spec hperm hj) (fun i hi => finv_apply hperm hi)
  have hfv : ∀ i, finv 11 (fd 4 g) i < 2 ^ 4 := fun i => by
    have := finv_lt (n := 11) (by omega) (fd 4 g) i
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [hpinv]
    exact enc_lt (fun i _ => hfv i)
  · exact m11_isPermN_congr (fun x hx => (hfd x hx).symm) hperm.finv
  · rw [← hσ, permOf_inv hperm]
    exact permOf_congr hfd

private theorem m11_PK_mul {p q : Nat} {σ τ : Equiv.Perm (Fin 11)} (hp : m11_PK p σ)
    (hq : m11_PK q τ) : m11_PK (pcomp 11 4 15 p q) (σ * τ) := by
  obtain ⟨-, hpp, hσ⟩ := hp
  obtain ⟨-, hqp, hτ⟩ := hq
  have hpc : pcomp 11 4 15 p q = enc 4 (fun i => fd 4 p (fd 4 q i)) 11 := pcomp11_eq p q
  have hfd : ∀ x < 11, fd 4 (pcomp 11 4 15 p q) x = fd 4 p (fd 4 q x) := fun x hx => by
    rw [hpc, fd_enc (fun i _ => fd_lt 4 p _) hx]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpc]
    exact enc_lt (fun i _ => fd_lt 4 p _)
  · exact m11_isPermN_congr (fun x hx => (hfd x hx).symm) (hpp.comp hqp)
  · rw [← hσ, ← hτ, permOf_mul hpp hqp]
    exact permOf_congr hfd

private theorem m11_orderIs_iff {g : Nat} {σ : Equiv.Perm (Fin 11)} {k : Nat} (h : m11_PK g σ) :
    ordIs 11 4 15 (pidn 11 4) g k = true ↔ orderIs σ (k + 1) = true := by
  obtain ⟨hlt, hperm, hσ⟩ := h
  rw [ordIs_iff hlt hperm, orderIs_iff σ (Nat.succ_pos k), hσ]

private def m11_gens (fa fb : Nat → Nat) (z : Int) : Nat → Nat :=
  if z = 1 then fa else if z = -1 then finv 11 fa else if z = 2 then fb else finv 11 fb

private def m11_Rel (L : List (Nat → Nat)) (S : List (Equiv.Perm (Fin 11))) : Prop :=
  L.length = 2 * S.length ∧ (∀ l, IsPermN 11 (L.getD l id)) ∧
    ∀ j < S.length, permOf 11 (L.getD (2 * j) id) = S.getD j 1 ∧
      L.getD (2 * j + 1) id = finv 11 (L.getD (2 * j) id)

private theorem m11_getD_pair (L : List (Nat → Nat)) (a b : Nat → Nat) (l : Nat) :
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

private theorem m11_word {gens : Int → Nat → Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) {L : List (Nat → Nat)}
    {S : List (Equiv.Perm (Fin 11))} (hR : m11_Rel L S) :
    ∀ w : List Int, (∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length) →
      IsPermN 11 (wordFn gens L (w.map sh)) ∧
        permOf 11 (wordFn gens L (w.map sh)) = evalCodes S w := by
  obtain ⟨hlen, hperm, hrel⟩ := hR
  have hlet : ∀ z : Int, 1 ≤ z.natAbs → z.natAbs ≤ S.length →
      IsPermN 11 (letFn gens L (sh z)) ∧ permOf 11 (letFn gens L (sh z)) =
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
    refine ⟨isPermN_id 11, ?_⟩
    exact (permOf_eq_one_iff (isPermN_id 11)).2 (fun x _ => rfl)
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

private theorem m11_rel_step {gens : Int → Nat → Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) {L : List (Nat → Nat)}
    {S : List (Equiv.Perm (Fin 11))} (hR : m11_Rel L S) {w : List Int}
    (hw : ∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length) :
    m11_Rel (L ++ [wordFn gens L (w.map sh), finv 11 (wordFn gens L (w.map sh))])
      (S ++ [tab (evalCodes S w)]) := by
  obtain ⟨hP, hPσ⟩ := m11_word (gens := gens) hsh hR w hw
  generalize wordFn gens L (w.map sh) = P at hP hPσ ⊢
  obtain ⟨hlen, hperm, hrel⟩ := hR
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil, hlen]
    omega
  · intro l
    rw [m11_getD_pair]
    split_ifs
    · exact hperm l
    · exact hP
    · exact hP.finv
    · exact isPermN_id 11
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjS : j < S.length
    · have h1 : 2 * j < L.length := by omega
      have h2 : 2 * j + 1 < L.length := by omega
      have hSg : (S ++ [tab (evalCodes S w)]).getD j 1 = S.getD j 1 := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hjS]
      rw [m11_getD_pair, if_pos h1, m11_getD_pair, if_pos h2, hSg]
      exact hrel j hjS
    · have hj' : j = S.length := by omega
      subst hj'
      have h1 : ¬ 2 * S.length < L.length := by omega
      have h2 : ¬ 2 * S.length + 1 < L.length := by omega
      rw [m11_getD_pair, if_neg h1, if_pos (by omega), m11_getD_pair, if_neg h2,
        if_neg (by omega), if_pos (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
      refine ⟨?_, rfl⟩
      rw [hPσ, tab_eq]
      rfl

private theorem m11_rel_all {gens : Int → Nat → Nat} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) :
    ∀ (ws : List (List Int)) (L : List (Nat → Nat)) (S : List (Equiv.Perm (Fin 11))),
      m11_Rel L S →
      (∀ i < ws.length, ∀ z ∈ ws.getD i [], 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length + i) →
      m11_Rel (lettersFrom 11 gens L (ws.map (List.map sh))) (buildStrong S ws) := by
  intro ws
  induction ws with
  | nil => intro L S hR _; exact hR
  | cons w ws ih =>
    intro L S hR hrange
    have hw : ∀ z ∈ w, 1 ≤ z.natAbs ∧ z.natAbs ≤ S.length := fun z hz => by
      have := hrange 0 (by simp) z (by simpa using hz)
      simpa using this
    have e1 : lettersFrom 11 gens L ((w :: ws).map (List.map sh)) =
        lettersFrom 11 gens (L ++ [wordFn gens L (w.map sh), finv 11 (wordFn gens L (w.map sh))])
          (ws.map (List.map sh)) := rfl
    have e2 : buildStrong S (w :: ws) = buildStrong (S ++ [tab (evalCodes S w)]) ws := rfl
    rw [e1, e2]
    refine ih _ _ (m11_rel_step hsh hR hw) ?_
    intro i hi z hz
    have := hrange (i + 1) (by simpa using hi) z (by simpa using hz)
    simp only [List.length_append, List.length_singleton]
    omega

private theorem m11_rel_base {fa fb : Nat → Nat} {gA gB : Equiv.Perm (Fin 11)}
    (ha : IsPermN 11 fa) (hb : IsPermN 11 fb) (hpa : permOf 11 fa = gA)
    (hpb : permOf 11 fb = gB) : m11_Rel [fa, finv 11 fa, fb, finv 11 fb] [gA, gB] := by
  refine ⟨rfl, ?_, ?_⟩
  · intro l
    match l with
    | 0 => exact ha
    | 1 => exact ha.finv
    | 2 => exact hb
    | 3 => exact hb.finv
    | l + 4 =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
      exact isPermN_id 11
  · intro j hj
    match j, hj with
    | 0, _ => exact ⟨hpa, rfl⟩
    | 1, _ => exact ⟨hpb, rfl⟩

private theorem m11_wordFn_one (fa fb : Nat → Nat) (L : List (Nat → Nat)) :
    wordFn (m11_gens fa fb) L [1] = fa := by
  funext x
  show letFn (m11_gens fa fb) L 1 x = fa x
  unfold letFn
  rw [if_pos (by decide)]
  unfold m11_gens
  rw [if_pos rfl]

private theorem m11_wordFn_two (fa fb : Nat → Nat) (L : List (Nat → Nat)) :
    wordFn (m11_gens fa fb) L [2] = fb := by
  funext x
  show letFn (m11_gens fa fb) L 2 x = fb x
  unfold letFn
  rw [if_pos (by decide)]
  unfold m11_gens
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

private theorem m11_lettersFn_W (fa fb : Nat → Nat) (ws : List (List Int)) :
    lettersFn 11 (m11_gens fa fb) ([[1], [2]] ++ ws) =
      lettersFrom 11 (m11_gens fa fb) [fa, finv 11 fa, fb, finv 11 fb] ws := by
  have e : lettersFn 11 (m11_gens fa fb) ([[1], [2]] ++ ws) =
      lettersFrom 11 (m11_gens fa fb) ([] ++ [wordFn (m11_gens fa fb) [] [1],
        finv 11 (wordFn (m11_gens fa fb) [] [1])] ++
          [wordFn (m11_gens fa fb) ([] ++ [wordFn (m11_gens fa fb) [] [1],
            finv 11 (wordFn (m11_gens fa fb) [] [1])]) [2],
          finv 11 (wordFn (m11_gens fa fb) ([] ++ [wordFn (m11_gens fa fb) [] [1],
            finv 11 (wordFn (m11_gens fa fb) [] [1])]) [2])]) ws := rfl
  rw [e, m11_wordFn_one, m11_wordFn_two]
  rfl

private theorem m11_range {sh : Int → Int} (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2)
    {words : List (List Int)}
    (hws : CFSG.KS.Mathieu.wordsOK ([[1], [2]] ++ words.map (List.map sh)) 0 = true) :
    ∀ i < words.length, ∀ z ∈ words.getD i [], 1 ≤ z.natAbs ∧ z.natAbs ≤ 2 + i := by
  intro i hi z hz
  have hget : ([[1], [2]] ++ words.map (List.map sh)).getD (i + 2) [] =
      (words.getD i []).map sh := by
    have e : ([[1], [2]] ++ words.map (List.map sh)).getD (i + 2) [] =
        (words.map (List.map sh)).getD i [] := by
      show ([1] :: [2] :: words.map (List.map sh)).getD (i + 1 + 1) [] = _
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

private theorem m11_rel_letters {fa fb : Nat → Nat} {gA gB : Equiv.Perm (Fin 11)}
    {sh : Int → Int} (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) (ha : IsPermN 11 fa)
    (hb : IsPermN 11 fb) (hpa : permOf 11 fa = gA) (hpb : permOf 11 fb = gB)
    {words : List (List Int)}
    (hws : CFSG.KS.Mathieu.wordsOK ([[1], [2]] ++ words.map (List.map sh)) 0 = true) :
    m11_Rel (lettersFn 11 (m11_gens fa fb) ([[1], [2]] ++ words.map (List.map sh)))
      (buildStrong [gA, gB] words) := by
  rw [m11_lettersFn_W]
  exact m11_rel_all hsh words _ [gA, gB] (m11_rel_base ha hb hpa hpb) (fun i hi z hz => by
    have := m11_range hsh hws i hi z hz
    simpa using this)

private theorem m11_LT_eq {A B : Nat} {gA gB : Equiv.Perm (Fin 11)} (hA : m11_PK A gA)
    (hB : m11_PK B gB) {W : List (List Int)} (hws : CFSG.KS.Mathieu.wordsOK W 0 = true) :
    lettersP 11 4 15 44 17592186044415 (pidn 11 4) A (pinvS 11 4 15 A) B (pinvS 11 4 15 B) W 0 0 =
      enc (11 * 4) (fun l => enc 4 ((lettersFn 11 (m11_gens (fd 4 A) (fd 4 B)) W).getD l id) 11)
        (2 * W.length) := by
  have h := lettersP_eq (n := 11) (w := 4) (A := A) (Ai := pinvS 11 4 15 A) (B := B)
    (Bi := pinvS 11 4 15 B) (gens := m11_gens (fd 4 A) (fd 4 B)) (by decide) (by decide)
    (fun x _ => by unfold m11_gens; rw [if_pos rfl])
    (fun x hx => by
      unfold m11_gens
      rw [if_neg (by decide), if_pos rfl]
      exact (m11_fd_pinv hA x hx).symm)
    (fun x _ => by
      unfold m11_gens
      rw [if_neg (by decide), if_neg (by decide), if_pos rfl])
    (fun x hx => by
      unfold m11_gens
      rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
      exact (m11_fd_pinv hB x hx).symm)
    (fun z hz0 hz2 => by
      unfold m11_gens
      by_cases h1 : z = 1
      · rw [if_pos h1]; exact hA.2.1
      by_cases h2 : z = -1
      · rw [if_neg h1, if_pos h2]; exact hA.2.1.finv
      by_cases h3 : z = 2
      · rw [if_neg h1, if_neg h2, if_pos h3]; exact hB.2.1
      · rw [if_neg h1, if_neg h2, if_neg h3]; exact hB.2.1.finv) hws
  exact h

private theorem m11_finv_finv {n : Nat} {f : Nat → Nat} (hf : IsPermN n f) {x : Nat} (hx : x < n) :
    finv n (finv n f) x = f x := by
  have h := finv_apply hf.finv (hf.1 x hx)
  rwa [finv_apply hf hx] at h

private theorem m11_letF {Fa : Nat → Nat → Nat} (hF : ∀ l, IsPermN 11 (Fa l)) {LT : Nat}
    (hLT : LT = enc (11 * 4) (fun l => enc 4 (Fa l) 11) 12) :
    ∀ l < 12, ∀ x < 11, letF 11 4 LT l x = Fa l x := by
  intro l hl x hx
  have h1 : ∀ i < 12, enc 4 (Fa i) 11 < 2 ^ (11 * 4) := fun i _ => by
    rw [Nat.mul_comm 11 4]
    exact enc_lt (fun j hj => by have := (hF i).1 j hj; omega)
  have h2 : ∀ j < 11, Fa l j < 2 ^ 4 := fun j hj => by
    have := (hF l).1 j hj
    omega
  show fd 4 (fd (11 * 4) LT l) x = _
  rw [hLT, fd_enc h1 hl, fd_enc h2 hx]

private theorem m11_PairsOK {F : Nat → Nat → Nat} {L : List (Nat → Nat)}
    (hF : ∀ l < 12, ∀ x < 11, F l x = L.getD l id x) (hL : ∀ l, IsPermN 11 (L.getD l id))
    (hodd : ∀ j < 6, L.getD (2 * j + 1) id = finv 11 (L.getD (2 * j) id)) : PairsOK 11 F 12 := by
  refine ⟨rfl, fun l hl => ⟨m11_isPermN_congr (fun x hx => (hF l hl x hx).symm) (hL l), ?_⟩⟩
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
      hodd j (by omega), m11_finv_finv (hL (2 * j)) hx]

private theorem m11_nIf_iff (c : Bool) :
    Bool.rec (motive := fun _ => Nat) 0 1 c = 1 ↔ c = true := by
  cases c <;> simp

private theorem m11_lev_pred {LT : Nat} (hL : ∀ l < 12, IsPermN 11 (letF 11 4 LT l))
    {k : Nat → Nat → Nat → Nat → Nat → Nat} {P : Nat → Nat → Nat → Nat → Nat → Prop}
    (hk : ∀ a b c d e, k a b c d e = 1 ↔ P a b c d e) (h : m11Lev LT k = 1) :
    P (recBS 11 4 (letF 11 4 LT) (m11Run LT 0) (levMaskAt 11 4 LT 12 m11Bs 0))
      (recBS 11 4 (letF 11 4 LT) (m11Run LT 1) (levMaskAt 11 4 LT 12 m11Bs 1))
      (recBS 11 4 (letF 11 4 LT) (m11Run LT 2) (levMaskAt 11 4 LT 12 m11Bs 2))
      (recBS 11 4 (letF 11 4 LT) (m11Run LT 3) (levMaskAt 11 4 LT 12 m11Bs 3))
      (levMaskAt 11 4 LT 12 m11Bs 4) := by
  rw [m11Lev_eq hL] at h
  exact (hk _ _ _ _ _).1 h

private theorem m11_natLevels_eq (LT : Nat) :
    natLevels 11 (letF 11 4 LT) 12 m11Bs =
      [(lvAt (letF 11 4 LT) 12 m11Bs 0, 0, m11Run LT 0),
        (lvAt (letF 11 4 LT) 12 m11Bs 1, 1, m11Run LT 1),
        (lvAt (letF 11 4 LT) 12 m11Bs 2, 2, m11Run LT 2),
        (lvAt (letF 11 4 LT) 12 m11Bs 3, 3, m11Run LT 3)] := rfl

private theorem m11_chain_core {LT : Nat} (hL : ∀ l < 12, IsPermN 11 (letF 11 4 LT l))
    (hch : chainSch 11 4 15 44 17592186044415 (pidn 11 4) LT 12
      [recBS 11 4 (letF 11 4 LT) (m11Run LT 0) (levMaskAt 11 4 LT 12 m11Bs 0),
        recBS 11 4 (letF 11 4 LT) (m11Run LT 1) (levMaskAt 11 4 LT 12 m11Bs 1),
        recBS 11 4 (letF 11 4 LT) (m11Run LT 2) (levMaskAt 11 4 LT 12 m11Bs 2),
        recBS 11 4 (letF 11 4 LT) (m11Run LT 3) (levMaskAt 11 4 LT 12 m11Bs 3)] = true)
    (hmask : maskId 44 17592186044415 (pidn 11 4) LT 12 (levMaskAt 11 4 LT 12 m11Bs 4) = true)
    (hsz : sizesEq [recBS 11 4 (letF 11 4 LT) (m11Run LT 0) (levMaskAt 11 4 LT 12 m11Bs 0),
        recBS 11 4 (letF 11 4 LT) (m11Run LT 1) (levMaskAt 11 4 LT 12 m11Bs 1),
        recBS 11 4 (letF 11 4 LT) (m11Run LT 2) (levMaskAt 11 4 LT 12 m11Bs 2),
        recBS 11 4 (letF 11 4 LT) (m11Run LT 3) (levMaskAt 11 4 LT 12 m11Bs 3)]
      [11, 10, 9, 8] = true) :
    (∀ i (hi : i < (natLevels 11 (letF 11 4 LT) 12 m11Bs).length),
      absSch 11 (letF 11 4 LT) (natLevels 11 (letF 11 4 LT) 12 m11Bs)[i].1
        (natLevels 11 (letF 11 4 LT) 12 m11Bs)[i].2.2
        (((natLevels 11 (letF 11 4 LT) 12 m11Bs).drop (i + 1)).map fun e => e.2.2) = true) ∧
    (∀ l ∈ lvAt (letF 11 4 LT) 12 m11Bs 4, ∀ x < 11, letF 11 4 LT l x = x) ∧
    (m11Run LT 0).pts.length = 11 ∧ (m11Run LT 1).pts.length = 10 ∧
      (m11Run LT 2).pts.length = 9 ∧ (m11Run LT 3).pts.length = 8 := by
  have hgood : ∀ i, i < 4 → GoodBS 11 (letF 11 4 LT) (m11Run LT i) := fun i hi =>
    goodBS_run (by omega) (fun l hl => hL l (lvAt_sub _ _ _ _ l hl))
  have hlv : ∀ i ≤ 4, maskL 12 (levMaskAt 11 4 LT 12 m11Bs i) =
      lvAt (letF 11 4 LT) 12 m11Bs i := by
    intro i hi
    rw [maskL_levMaskAt]
    congr 1
    simp only [m11Bs, List.length_cons, List.length_nil]
    omega
  have hab := chainSch_eq (n := 11) (w := 4) (LT := LT) (NL := 12) (by decide) (by decide) hL
    (ps := [(m11Run LT 0, levMaskAt 11 4 LT 12 m11Bs 0),
      (m11Run LT 1, levMaskAt 11 4 LT 12 m11Bs 1), (m11Run LT 2, levMaskAt 11 4 LT 12 m11Bs 2),
      (m11Run LT 3, levMaskAt 11 4 LT 12 m11Bs 3)])
    (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | hp | hp | hp
      · rw [hp]; dsimp only; exact hgood 0 (by decide)
      · rw [hp]; dsimp only; exact hgood 1 (by decide)
      · rw [hp]; dsimp only; exact hgood 2 (by decide)
      · rw [hp]; dsimp only; exact hgood 3 (by decide))
  simp only [List.map_cons, List.map_nil] at hab
  have hab' : absChain 11 (letF 11 4 LT) 12 [(m11Run LT 0, levMaskAt 11 4 LT 12 m11Bs 0),
      (m11Run LT 1, levMaskAt 11 4 LT 12 m11Bs 1), (m11Run LT 2, levMaskAt 11 4 LT 12 m11Bs 2),
      (m11Run LT 3, levMaskAt 11 4 LT 12 m11Bs 3)] = true := by
    rw [← hab]
    exact hch
  simp only [absChain, Bool.and_eq_true, List.map_cons, List.map_nil, Bool.and_true] at hab'
  rw [hlv 0 (by decide), hlv 1 (by decide), hlv 2 (by decide), hlv 3 (by decide)] at hab'
  refine ⟨?_, ?_, ?_⟩
  · rw [m11_natLevels_eq]
    intro i hi
    have hi4 : i < 4 := by simpa using hi
    interval_cases i
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.drop_succ_cons,
        List.drop_zero, List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd]
      exact hab'.1
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.drop_succ_cons,
        List.drop_zero, List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd]
      exact hab'.2.1
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.drop_succ_cons,
        List.drop_zero, List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd]
      exact hab'.2.2.1
    · simp only [List.getElem_cons_zero, List.getElem_cons_succ, List.drop_succ_cons,
        List.drop_zero, List.map_cons, List.map_nil, Nat.zero_add, Nat.reduceAdd]
      exact hab'.2.2.2
  · have hid := (maskId_iff (n := 11) (w := 4) (LT := LT) (NL := 12) (by decide) (by decide)
      (levMaskAt 11 4 LT 12 m11Bs 4)).1 hmask
    rw [hlv 4 (Nat.le_refl 4)] at hid
    exact hid
  · have hs := (sizesEq_iff _ _).1 hsz
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hs
    rw [lcnt_recBS (by decide) (by decide) (hgood 0 (by decide)),
      lcnt_recBS (by decide) (by decide) (hgood 1 (by decide)),
      lcnt_recBS (by decide) (by decide) (hgood 2 (by decide)),
      lcnt_recBS (by decide) (by decide) (hgood 3 (by decide))] at hs
    exact hs

private theorem m11_prodsA_mem {F : Nat → Nat → Nat} {s0 s1 s2 s3 : BS} (h0 : GoodBS 11 F s0)
    (h1 : GoodBS 11 F s1) (h2 : GoodBS 11 F s2) (h3 : GoodBS 11 F s3) :
    ∀ g ∈ prodsA F s0 s1 s2 s3, g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g) := by
  intro g hg
  simp only [prodsA, List.mem_flatMap, List.mem_map, List.mem_range] at hg
  obtain ⟨k0, hk0, k1, hk1, k2, hk2, k3, hk3, rfl⟩ := hg
  have hp : IsPermN 11 fun x => BS.trans F s0 k0 (BS.trans F s1 k1 (BS.trans F s2 k2
      (BS.trans F s3 k3 x))) :=
    (h0.2.2.2.2 k0 hk0).comp ((h1.2.2.2.2 k1 hk1).comp ((h2.2.2.2.2 k2 hk2).comp
      (h3.2.2.2.2 k3 hk3)))
  have hlt : ∀ i < 11, (fun x => BS.trans F s0 k0 (BS.trans F s1 k1 (BS.trans F s2 k2
      (BS.trans F s3 k3 x)))) i < 2 ^ 4 := fun i hi => by
    have := hp.1 i hi
    omega
  refine ⟨enc_lt hlt, m11_isPermN_congr (fun x hx => ?_) hp⟩
  rw [fd_enc hlt hx]

private theorem m11_filter_eq {P : List Nat} (hP : ∀ g ∈ P, g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g))
    (k : Nat) :
    (P.map fun g => permOf 11 (fd 4 g)).filter (fun σ => orderIs σ (k + 1)) =
      (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g k).map fun g => permOf 11 (fd 4 g) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro g hg
  obtain ⟨hlt, hperm⟩ := hP g hg
  simp only [Function.comp]
  exact Bool.eq_iff_iff.2 (by rw [ordIs_iff hlt hperm, orderIs_iff _ (Nat.succ_pos k)])

private theorem m11_lenRec {α : Type} (L : List α) :
    List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L = L.length := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    show Nat.succ _ = _
    rw [ih]
    rfl

private theorem m11_pairsBdd_iff (nw : Nat) (L : List (Nat × Nat)) :
    pairsBdd nw L = true ↔ L.length < 65536 ∧ ∀ p ∈ L, p.1 < 2 ^ nw ∧ p.2 < 2 ^ nw := by
  have hall : ∀ L : List (Nat × Nat),
      List.rec (motive := fun _ => Bool) true (fun p _ ih => Prod.rec (motive := fun _ => Bool)
        (fun g gi => bAnd(Nat.blt g (Nat.shiftLeft (nat_lit 1) nw),
          bAnd(Nat.blt gi (Nat.shiftLeft (nat_lit 1) nw), ih))) p) L = true ↔
        ∀ p ∈ L, p.1 < 2 ^ nw ∧ p.2 < 2 ^ nw := by
    intro L
    have he : Nat.shiftLeft 1 nw = 2 ^ nw := Nat.one_shiftLeft nw
    induction L with
    | nil => simp
    | cons p L ih =>
      obtain ⟨g, gi⟩ := p
      simp only [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, he, List.mem_cons, forall_eq_or_imp] at ih ⊢
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, ih.1 h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, ih.2 h3⟩
  unfold pairsBdd
  rw [bAnd_eq, Bool.and_eq_true, Nat.blt_eq, m11_lenRec, hall]

private theorem m11_pairsBdd {X : List Nat} (hlen : X.length < 65536)
    (hX : ∀ g ∈ X, g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g)) : pairsBdd 44 (pairsOf X) = true := by
  rw [m11_pairsBdd_iff]
  refine ⟨by simpa [pairsOf] using hlen, ?_⟩
  intro p hp
  simp only [pairsOf, List.mem_map] at hp
  obtain ⟨g, hg, rfl⟩ := hp
  obtain ⟨hlt, hperm⟩ := hX g hg
  exact ⟨hlt, (m11_PK_inv (σ := permOf 11 (fd 4 g)) ⟨hlt, hperm, rfl⟩).1⟩

private theorem m11_prodsA_length (F : Nat → Nat → Nat) (s0 s1 s2 s3 : BS) :
    (prodsA F s0 s1 s2 s3).length = s0.pts.length * s1.pts.length * s2.pts.length *
      s3.pts.length := by
  simp only [prodsA, List.length_flatMap, List.length_map, List.length_range, List.map_const',
    List.sum_replicate, smul_eq_mul]
  ring

private theorem m11_base_get {n : Nat} {Q Q' : RawSchreierDatum n}
    (hbase : Q.base.toList = Q'.base.toList) (i : Fin Q.baseCount) (i' : Fin Q'.baseCount)
    (h : i.val = i'.val) : Q.base.get i = Q'.base.get i' := by
  have h1 : Q.base.toList[i.val]'(by simp) = Q'.base.toList[i'.val]'(by simp) := by
    have := List.getElem_of_eq hbase (i := i.val) (by simp)
    rw [this]
    simp [h]
  simpa [Vector.getElem_toList, Vector.get] using h1

private theorem m11_orbitSize_eq {n : Nat} {Q Q' : RawSchreierDatum n}
    (hlev : ∀ i, Q.levelSubgroup i = Q'.levelSubgroup i)
    (hbase : Q.base.toList = Q'.base.toList) (i : Fin Q.baseCount) (i' : Fin Q'.baseCount)
    (h : i.val = i'.val) : Q.orbitSize i = Q'.orbitSize i' := by
  rw [RawSchreierDatum.orbitSize_eq_card, RawSchreierDatum.orbitSize_eq_card,
    RawSchreierDatum.orbitPoints_eq_orbit, RawSchreierDatum.orbitPoints_eq_orbit, hlev,
    m11_base_get hbase i i' h, h]

private theorem m11_count {Q : RawSchreierDatum 11} {P : List Nat}
    (hperm : (enumeration Q).Perm (P.map fun g => permOf 11 (fd 4 g)))
    (hP : ∀ g ∈ P, g < 2 ^ (4 * 11) ∧ IsPermN 11 (fd 4 g)) (hlen : P.length < 65536)
    {XL YL : List (Nat × Nat)} (hXb : pairsBdd 44 XL = true) (hYb : pairsBdd 44 YL = true)
    (hX : packPairs (pairsOf (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g 1)) = packPairs XL)
    (hY : packPairs (pairsOf (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g 3)) = packPairs YL) :
    ((((enumeration Q).map tab).filter (orderIs · 2)).length = XL.length ∧
      (((enumeration Q).map tab).filter (orderIs · 4)).length = YL.length ∧
      ((((enumeration Q).map tab).filter (orderIs · 2) ×ˢ
          ((enumeration Q).map tab).filter (orderIs · 4)).filter
        fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6).length =
        pairCntL XL YL) := by
  have hXL : XL = pairsOf (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g 1) :=
    packPairs_inj hXb (m11_pairsBdd (lt_of_le_of_lt (List.length_filter_le _ _) hlen)
      (fun g hg => hP g (List.mem_of_mem_filter hg))) hX.symm
  have hYL : YL = pairsOf (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g 3) :=
    packPairs_inj hYb (m11_pairsBdd (lt_of_le_of_lt (List.length_filter_le _ _) hlen)
      (fun g hg => hP g (List.mem_of_mem_filter hg))) hY.symm
  have hE : (enumeration Q).map tab = enumeration Q := by
    rw [List.map_congr_left (fun g _ => tab_eq g), List.map_id']
  rw [hE]
  have h2 : (P.map fun g => permOf 11 (fd 4 g)).filter (fun σ => orderIs σ 2) =
      (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g 1).map fun g => permOf 11 (fd 4 g) :=
    m11_filter_eq hP 1
  have h4 : (P.map fun g => permOf 11 (fd 4 g)).filter (fun σ => orderIs σ 4) =
      (P.filter fun g => ordIs 11 4 15 (pidn 11 4) g 3).map fun g => permOf 11 (fd 4 g) :=
    m11_filter_eq hP 3
  refine ⟨?_, ?_, ?_⟩
  · rw [length_filter_eq_of_perm hperm, h2, hXL]
    simp [pairsOf]
  · rw [length_filter_eq_of_perm hperm, h4, hYL]
    simp [pairsOf]
  · rw [length_filter_product_eq_of_perm hperm, h2, h4, hXL, hYL,
      pairCntL_pairsOf (fun g hg => hP g (List.mem_of_mem_filter hg))
        (fun g hg => hP g (List.mem_of_mem_filter hg))]

private theorem m11_cert {gA gB : Equiv.Perm (Fin 11)} {words : List (List Int)}
    {hbs : (#v[0, 1, 2, 3] : Vector (Fin 11) 4).toList.Nodup} {F : Nat → Nat → Nat}
    (hwl : words.length = 4) (hPairs : PairsOK 11 F 12)
    (hLetters : LettersOf 11 F (buildStrong [gA, gB] words))
    (hsch : ∀ i (h : i < (natLevels 11 F 12 m11Bs).length),
      absSch 11 F (natLevels 11 F 12 m11Bs)[i].1 (natLevels 11 F 12 m11Bs)[i].2.2
        (((natLevels 11 F 12 m11Bs).drop (i + 1)).map fun e => e.2.2) = true)
    (hterm : ∀ l ∈ lvAt F 12 m11Bs 4, ∀ x < 11, F l x = x) {s : Nat → BS}
    (hsd : ∀ i, s i = BS.run F (lvAt F 12 m11Bs i) 11 i)
    (hs0 : (s 0).pts.length = 11) (hs1 : (s 1).pts.length = 10) (hs2 : (s 2).pts.length = 9)
    (hs3 : (s 3).pts.length = 8) :
    (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).check = true ∧
    (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).orderCertificate = 7920 ∧
    (enumeration (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs)).Perm
      ((prodsA F (s 0) (s 1) (s 2) (s 3)).map fun g => permOf 11 (fd 4 g)) := by
  have hbsl : (#v[0, 1, 2, 3] : Vector (Fin 11) 4).toList.map Fin.val = m11Bs := rfl
  have hQ'chk : (rawOf 11 (by decide) F 12 #v[0, 1, 2, 3] hbs).check = true := by
    apply rawOf_check hPairs
    · rw [hbsl]
      exact hsch
    · rw [hbsl]
      exact hterm
  have hNL : 2 * ([gA, gB].length + words.length) = 12 := by
    simp [hwl]
  have hQchk : (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).check = true := by
    refine check_certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs hLetters ?_
    rw [hNL]
    exact hQ'chk
  have hlev : ∀ i, (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).levelSubgroup i =
      (rawOf 11 (by decide) F 12 #v[0, 1, 2, 3] hbs).levelSubgroup i := by
    intro i
    have h := levelSubgroup_certificate_eq (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs hLetters i
    rw [hNL] at h
    exact h
  refine ⟨hQchk, ?_, ?_⟩
  · have hsz4 : ∀ i : Fin 4, (rawOf 11 (by decide) F 12 #v[0, 1, 2, 3] hbs).orbitSize i =
        [11, 10, 9, 8].getD i 0 := by
      intro i
      rw [rawOf_orbitSize hPairs, hbsl]
      fin_cases i
      · show (BS.run F (lvAt F 12 m11Bs 0) 11 0).pts.length = 11
        rw [← hsd 0]
        exact hs0
      · show (BS.run F (lvAt F 12 m11Bs 1) 11 1).pts.length = 10
        rw [← hsd 1]
        exact hs1
      · show (BS.run F (lvAt F 12 m11Bs 2) 11 2).pts.length = 9
        rw [← hsd 2]
        exact hs2
      · show (BS.run F (lvAt F 12 m11Bs 3) 11 3).pts.length = 8
        rw [← hsd 3]
        exact hs3
    have hos : ∀ i : Fin 4,
        (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).orbitSize i =
          [11, 10, 9, 8].getD i 0 := fun i =>
      (m11_orbitSize_eq hlev rfl i i rfl).trans (hsz4 i)
    unfold RawSchreierDatum.orderCertificate
    have h1 : (List.finRange
          (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).baseCount).map
        (certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs).orbitSize =
        (List.finRange 4).map fun i : Fin 4 => [11, 10, 9, 8].getD i.val 0 :=
      List.map_congr_left (fun i _ => hos i)
    rw [h1]
    decide
  · have hQ'enum : enumeration (rawOf 11 (by decide) F 12 #v[0, 1, 2, 3] hbs) =
        (prodsA F (s 0) (s 1) (s 2) (s 3)).map fun g => permOf 11 (fd 4 g) := by
      rw [hsd 0, hsd 1, hsd 2, hsd 3]
      exact enumeration_rawOf4 hPairs hbs
    rw [← hQ'enum]
    exact perm_enumeration hQchk hQ'chk (hlev 0)

theorem m11K_sound' {gA gB : Equiv.Perm (Fin 11)} {words : List (List Int)}
    {hbs : (#v[0, 1, 2, 3] : Vector (Fin 11) 4).toList.Nodup}
    {tA tB : List Nat} {W : List (List Int)} {sh : Int → Int}
    (hsh : ∀ z, sh z = if 0 < z then z + 2 else z - 2) (hA : tA = imageList gA)
    (hB : tB = imageList gB) (hW : W = [[1], [2]] ++ words.map (List.map sh))
    {XL YL : List (Nat × Nat)} (hbase : m11Base tA tB W = true)
    (hX : m11Col tA tB W 1 = packPairs XL) (hY : m11Col tA tB W 3 = packPairs YL)
    (hXb : pairsBdd 44 XL = true) (hYb : pairsBdd 44 YL = true) :
    let Q := certificate (by decide) [gA, gB] words #v[0, 1, 2, 3] hbs
    let E := (enumeration Q).map tab
    (Q.check = true ∧ Q.orderCertificate = 7920)
    ∧ (orderIs gA 2 = true ∧ orderIs gB 4 = true ∧ orderIs (gA * gB) 11 = true ∧
      orderIs (gA * gB * gA⁻¹ * gB⁻¹) 6 = true ∧
      (E.filter (orderIs · 2)).length = XL.length ∧
      (E.filter (orderIs · 4)).length = YL.length ∧
      ((E.filter (orderIs · 2) ×ˢ E.filter (orderIs · 4)).filter
        fun q => orderIs (q.1 * q.2) 11 && orderIs (q.1 * q.2 * q.1⁻¹ * q.2⁻¹) 6).length =
        pairCntL XL YL) := by
  have hAPK : m11_PK (packL 4 tA) gA := m11_PK_pack hA
  have hBPK : m11_PK (packL 4 tB) gB := m11_PK_pack hB
  have hbase' := hbase
  simp only [m11Base, strictB_eq, bAnd_eq, Bool.and_eq_true] at hbase'
  obtain ⟨-, -, -, -, -, -, h7, h8, h9, h10, h11, h12, -, -, h15⟩ := hbase'
  have hlenW : W.length = 6 := by
    rw [← lenW_eq]
    exact Nat.eq_of_beq_eq_true h8
  have hwl : words.length = 4 := by
    rw [hW] at hlenW
    simpa using hlenW
  have hws : Mathieu.wordsOK ([[1], [2]] ++ words.map (List.map sh)) 0 = true := hW ▸ h7
  have hRel0 := m11_rel_letters (gA := gA) (gB := gB) hsh hAPK.2.1 hBPK.2.1 hAPK.2.2
    hBPK.2.2 hws
  rw [← hW] at hRel0
  have hLT0 : m11LT tA tB W = lettersP 11 4 15 44 17592186044415 (pidn 11 4) (packL 4 tA)
      (pinvS 11 4 15 (packL 4 tA)) (packL 4 tB) (pinvS 11 4 15 (packL 4 tB)) W 0 0 := by
    unfold m11LT
    simp only [strictN_eq]
  have hLT := m11_LT_eq hAPK hBPK h7
  rw [← hLT0, hlenW] at hLT
  generalize lettersFn 11 (m11_gens (fd 4 (packL 4 tA)) (fd 4 (packL 4 tB))) W = L at hRel0 hLT
  have hF12 : ∀ l < 12, ∀ x < 11, letF 11 4 (m11LT tA tB W) l x = L.getD l id x :=
    m11_letF (Fa := fun l => L.getD l id) hRel0.2.1 hLT
  have hLperm : ∀ l < 12, IsPermN 11 (letF 11 4 (m11LT tA tB W) l) := fun l hl =>
    m11_isPermN_congr (fun x hx => (hF12 l hl x hx).symm) (hRel0.2.1 l)
  have hP := m11_lev_pred hLperm
    (P := fun a b c d e => chainSch 11 4 15 44 17592186044415 (pidn 11 4) (m11LT tA tB W) 12
        [a, b, c, d] = true ∧ maskId 44 17592186044415 (pidn 11 4) (m11LT tA tB W) 12 e = true ∧
        sizesEq [a, b, c, d] [11, 10, 9, 8] = true)
    (fun a b c d e => by
      simp only [m11_nIf_iff, Bool.and_eq_true, and_assoc])
    (Nat.eq_of_beq_eq_true h15)
  obtain ⟨hch, hmask, hsz⟩ := hP
  obtain ⟨hsch, hterm, hs0, hs1, hs2, hs3⟩ := m11_chain_core hLperm hch hmask hsz
  have hS : (buildStrong [gA, gB] words).length = 6 := by
    rw [length_buildStrong]
    simp [hwl]
  have hPairs : PairsOK 11 (letF 11 4 (m11LT tA tB W)) 12 :=
    m11_PairsOK hF12 hRel0.2.1 (fun j hj => (hRel0.2.2 j (by rw [hS]; exact hj)).2)
  have hLetters : LettersOf 11 (letF 11 4 (m11LT tA tB W)) (buildStrong [gA, gB] words) := by
    intro j hj
    rw [hS] at hj
    have hj12 : 2 * j < 12 := by omega
    have hj12' : 2 * j + 1 < 12 := by omega
    obtain ⟨h1, h2⟩ := hRel0.2.2 j (by rw [hS]; exact hj)
    refine ⟨m11_isPermN_congr (fun x hx => (hF12 _ hj12 x hx).symm) (hRel0.2.1 _), ?_, ?_⟩
    · rw [← h1]
      exact permOf_congr (fun x hx => hF12 _ hj12 x hx)
    · intro x hx
      rw [hF12 _ hj12' x hx, h2]
      exact finv_congr (fun y hy => (hF12 _ hj12 y hy).symm) x
  obtain ⟨hQchk, hoc, hperm⟩ := m11_cert (gA := gA) (gB := gB) (hbs := hbs) hwl hPairs hLetters
    hsch hterm (s := m11Run (m11LT tA tB W)) (fun i => rfl) hs0 hs1 hs2 hs3
  have hgood : ∀ i, i < 4 → GoodBS 11 (letF 11 4 (m11LT tA tB W)) (m11Run (m11LT tA tB W) i) :=
    fun i hi => goodBS_run (by omega) (fun l hl => hLperm l (lvAt_sub _ _ _ _ l hl))
  have hPm := m11_prodsA_mem (hgood 0 (by decide)) (hgood 1 (by decide)) (hgood 2 (by decide))
    (hgood 3 (by decide))
  have hPlen : (prodsA (letF 11 4 (m11LT tA tB W)) (m11Run (m11LT tA tB W) 0)
      (m11Run (m11LT tA tB W) 1) (m11Run (m11LT tA tB W) 2)
      (m11Run (m11LT tA tB W) 3)).length < 65536 := by
    rw [m11_prodsA_length, hs0, hs1, hs2, hs3]
    norm_num
  have hcnt := m11_count hperm hPm hPlen hXb hYb ((m11Col_eq 1 hLperm).symm.trans hX)
    ((m11Col_eq 3 hLperm).symm.trans hY)
  refine ⟨⟨hQchk, hoc⟩, ?_, ?_, ?_, ?_, hcnt⟩
  · exact (m11_orderIs_iff hAPK).1 h9
  · exact (m11_orderIs_iff hBPK).1 h10
  · exact (m11_orderIs_iff (m11_PK_mul hAPK hBPK)).1 h11
  · have := (m11_orderIs_iff (m11_PK_mul hAPK (m11_PK_mul hBPK (m11_PK_mul (m11_PK_inv hAPK)
      (m11_PK_inv hBPK))))).1 h12
    simpa [mul_assoc] using this

end CFSG.KS.PK

end
