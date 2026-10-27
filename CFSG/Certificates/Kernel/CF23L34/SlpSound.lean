module

public import Certificates.Data.Kernel.CF23L34.Slp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Certificates.Kernel.Spor.RawOrbHead

public section

namespace CFSG.KC.CF23L34

open CFSG.QuasithinUnique.Setup.X1 CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin

section Group

variable {G : Type*} [Group G]

@[expose] def gLetter (R : List G) (z : ℤ) : G :=
  if z = 0 then 1
  else if 0 < z then R.getD (z.toNat - 1) 1 else (R.getD ((-z).toNat - 1) 1)⁻¹

@[expose] def gRun : List G → List (ℤ × ℤ) → List G
  | R, [] => R
  | R, pq :: rest => gRun (R ++ [gLetter R pq.1 * gLetter R pq.2]) rest

theorem gLetter_zero (R : List G) : gLetter R 0 = 1 := by simp [gLetter]

theorem gLetter_neg (R : List G) (z : ℤ) : gLetter R (-z) = (gLetter R z)⁻¹ := by
  unfold gLetter
  rcases lt_trichotomy z 0 with h | h | h
  · have h1 : -z ≠ 0 := by omega
    have h2 : 0 < -z := by omega
    have h3 : z ≠ 0 := by omega
    have h4 : ¬ 0 < z := by omega
    simp only [h1, h2, h3, h4, if_false, if_true, inv_inv]
  · subst h
    simp
  · have h1 : -z ≠ 0 := by omega
    have h2 : ¬ 0 < -z := by omega
    have h3 : z ≠ 0 := by omega
    simp only [h1, h2, h3, h, if_false, if_true, neg_neg]

theorem gLetter_append (R T : List G) {z : ℤ} (hz : z.natAbs ≤ R.length) :
    gLetter (R ++ T) z = gLetter R z := by
  unfold gLetter
  split_ifs with h0 h1
  · rfl
  · rw [List.getD_append _ _ _ _ (by omega)]
  · rw [List.getD_append _ _ _ _ (by omega)]

theorem gRun_append : ∀ (R : List G) (prog : List (ℤ × ℤ)), ∃ T, gRun R prog = R ++ T
  | R, [] => ⟨[], by simp [gRun]⟩
  | R, pq :: rest => by
    obtain ⟨T, hT⟩ := gRun_append (R ++ [gLetter R pq.1 * gLetter R pq.2]) rest
    exact ⟨_ :: T, by rw [gRun, hT, List.append_assoc, List.singleton_append]⟩

theorem gRun_length : ∀ (R : List G) (prog : List (ℤ × ℤ)),
    (gRun R prog).length = R.length + prog.length
  | R, [] => by simp [gRun]
  | R, pq :: rest => by
    rw [gRun, gRun_length, List.length_append, List.length_singleton, List.length_cons]
    omega

theorem gRun_step : ∀ (prog : List (ℤ × ℤ)) (R : List G),
    (∀ k (hk : k < prog.length), (prog[k].1).natAbs ≤ R.length + k ∧
      (prog[k].2).natAbs ≤ R.length + k) →
    ∀ k (hk : k < prog.length), (gRun R prog).getD (R.length + k) 1 =
      gLetter (gRun R prog) prog[k].1 * gLetter (gRun R prog) prog[k].2
  | [], _, _, k, hk => absurd hk (by simp)
  | pq :: rest, R, hwf, k, hk => by
    obtain ⟨T, hT⟩ := gRun_append (R ++ [gLetter R pq.1 * gLetter R pq.2]) rest
    rcases k with _ | k
    · have h0 := hwf 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      rw [gRun, hT, List.append_assoc, List.getElem_cons_zero, gLetter_append R _ h0.1,
        gLetter_append R _ h0.2, Nat.add_zero, List.getD_append_right _ _ _ _ (by omega),
        Nat.sub_self, List.singleton_append, List.getD_cons_zero]
    · have hwf' : ∀ j (hj : j < rest.length),
          (rest[j].1).natAbs ≤ (R ++ [gLetter R pq.1 * gLetter R pq.2]).length + j ∧
          (rest[j].2).natAbs ≤ (R ++ [gLetter R pq.1 * gLetter R pq.2]).length + j := by
        intro j hj
        have := hwf (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at this
        simp only [List.length_append, List.length_singleton]
        omega
      have ih := gRun_step rest _ hwf' k (by simp at hk; omega)
      simp only [List.length_append, List.length_singleton] at ih
      rw [gRun, show R.length + (k + 1) = R.length + 1 + k by omega, ih]
      rfl

theorem gRun_reg (prog : List (ℤ × ℤ)) (R : List G) (hR : R.length = 2)
    (hwf : ∀ k (hk : k < prog.length), (prog[k].1).natAbs ≤ k + 2 ∧ (prog[k].2).natAbs ≤ k + 2)
    (r : ℕ) (hr : 3 ≤ r) :
    gLetter (gRun R prog) (r : ℤ) = gLetter (gRun R prog) (prog.getD (r - 3) (0, 0)).1 *
      gLetter (gRun R prog) (prog.getD (r - 3) (0, 0)).2 := by
  have e1 : gLetter (gRun R prog) (r : ℤ) = (gRun R prog).getD (r - 1) 1 := by
    unfold gLetter
    rw [if_neg (by omega), if_pos (by omega), Int.toNat_natCast]
  rw [e1]
  by_cases hk : r - 3 < prog.length
  · have := gRun_step prog R (fun k hk => by rw [hR]; have := hwf k hk; omega) (r - 3) hk
    rw [hR, show 2 + (r - 3) = r - 1 by omega] at this
    rw [this, List.getD_eq_getElem _ _ hk]
  · rw [List.getD_eq_default _ _ (by rw [gRun_length, hR]; omega),
      List.getD_eq_default _ _ (by omega), gLetter_zero, mul_one]

theorem gLetter_mem {K : Subgroup G} {R : List G} (h : ∀ g ∈ R, g ∈ K) (z : ℤ) :
    gLetter R z ∈ K := by
  have hd : ∀ i, R.getD i 1 ∈ K := fun i => by
    by_cases hi : i < R.length
    · rw [List.getD_eq_getElem _ _ hi]
      exact h _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact K.one_mem
  unfold gLetter
  split_ifs
  · exact K.one_mem
  · exact hd _
  · exact K.inv_mem (hd _)

theorem gRun_mem {K : Subgroup G} : ∀ (prog : List (ℤ × ℤ)) {R : List G}, (∀ g ∈ R, g ∈ K) →
    ∀ g ∈ gRun R prog, g ∈ K
  | [], _, h => h
  | pq :: rest, R, h => by
    rw [gRun]
    refine gRun_mem rest fun g hg => ?_
    rcases List.mem_append.1 hg with hg | hg
    · exact h g hg
    · rw [List.mem_singleton] at hg
      rw [hg]
      exact K.mul_mem (gLetter_mem h _) (gLetter_mem h _)

variable {L : ℤ → G}

theorem frz_prod (hL : ∀ z, L (-z) = (L z)⁻¹) : ∀ w : List ℤ, ((frz w).map L).prod = (w.map L).prod
  | [] => rfl
  | z :: w => by
    have ih := frz_prod hL w
    rw [frz]
    split
    · next h =>
      rw [h] at ih
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] at ih ⊢
      rw [← ih]
    · next y u h =>
      rw [h] at ih
      split_ifs with hy
      · simp only [List.map_cons, List.prod_cons] at ih ⊢
        rw [← ih, hy, hL, ← mul_assoc, mul_inv_cancel, one_mul]
      · simp only [List.map_cons, List.prod_cons] at ih ⊢
        rw [← ih]

theorem neg_rev_prod (hL : ∀ z, L (-z) = (L z)⁻¹) (w : List ℤ) :
    ((w.reverse.map Neg.neg).map L).prod = ((w.map L).prod)⁻¹ := by
  rw [List.prod_inv_reverse, List.map_map, List.map_reverse, List.map_map]
  congr 2
  exact List.map_congr_left fun z _ => hL z

theorem slpX_prod {prog : List (ℤ × ℤ)} {keep : List ℕ} (hL : ∀ z, L (-z) = (L z)⁻¹)
    (h0 : L 0 = 1) (hS : ∀ r : ℕ, 3 ≤ r → L (r : ℤ) = L (prog.getD (r - 3) (0, 0)).1 * L (prog.getD (r - 3) (0, 0)).2) :
    ∀ (f : ℕ) (z : ℤ), ((slpX prog keep f z).map L).prod = L z
  | 0, z => by simp [slpX]
  | f + 1, z => by
    unfold slpX
    split_ifs with hz hk hp
    · simp [hz, h0]
    · simp
    · rw [List.map_append, List.prod_append, slpX_prod hL h0 hS f, slpX_prod hL h0 hS f,
        ← hS z.natAbs (by omega)]
      congr 1
      omega
    · rw [neg_rev_prod hL, List.map_append, List.prod_append, slpX_prod hL h0 hS f,
        slpX_prod hL h0 hS f, ← hS z.natAbs (by omega), ← hL]
      congr 1
      omega

theorem slpR_prod {prog : List (ℤ × ℤ)} {keep : List ℕ} (hL : ∀ z, L (-z) = (L z)⁻¹)
    (h0 : L 0 = 1)
    (hS : ∀ r : ℕ, 3 ≤ r → L (r : ℤ) = L (prog.getD (r - 3) (0, 0)).1 * L (prog.getD (r - 3) (0, 0)).2)
    (f r : ℕ) (hr : 3 ≤ r) : ((slpR prog keep f r).map L).prod = L r := by
  rw [slpR, frz_prod hL, List.map_append, List.prod_append, slpX_prod hL h0 hS, slpX_prod hL h0 hS,
    hS r hr]

end Group

variable {n : ℕ}

theorem getD_rel {P : PArr → Equiv.Perm (Fin n) → Prop} :
    ∀ {l : List PArr} {m : List (Equiv.Perm (Fin n))}, List.Forall₂ P l m →
      ∀ {d e} (i : ℕ), P d e → P (l.getD i d) (m.getD i e)
  | _, _, .nil, _, _, i, h => by simpa using h
  | _, _, .cons hab hl, _, _, i, h => by
    rcases i with _ | i
    · simpa using hab
    · simpa using getD_rel hl i h

theorem pLetter_rel {regs : List PArr} {R : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (PRep n) regs R) (z : ℤ) : PRep n (pLetter n regs z) (gLetter R z) := by
  unfold pLetter gLetter
  split_ifs
  · exact pRep_id
  · exact getD_rel h _ pRep_id
  · exact (getD_rel h _ pRep_id).inv

theorem forall₂_append {P : PArr → Equiv.Perm (Fin n) → Prop} {l₁ l₂ : List PArr}
    {m₁ m₂ : List (Equiv.Perm (Fin n))} (h₁ : List.Forall₂ P l₁ m₁) (h₂ : List.Forall₂ P l₂ m₂) :
    List.Forall₂ P (l₁ ++ l₂) (m₁ ++ m₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons h _ ih => exact .cons h ih

theorem pRun_rel : ∀ (prog : List (ℤ × ℤ)) {regs : List PArr} {R : List (Equiv.Perm (Fin n))},
    List.Forall₂ (PRep n) regs R → List.Forall₂ (PRep n) (pRun n regs prog) (gRun R prog)
  | [], _, _, h => h
  | pq :: rest, _, _, h => by
    rw [pRun, gRun]
    exact pRun_rel rest (forall₂_append h (.cons ((pLetter_rel h _).mul (pLetter_rel h _)) .nil))

variable {w : ℕ}

theorem strictN_eq (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem pp_of_permOK {p q : Nat} (hsz : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : PP n w p := by
  obtain ⟨h1, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h
  have hc : canonK n w (mask w) (n * w) p = true := by
    unfold canonK
    simp only [bAnd_iff]
    exact ⟨hsz, Nat.beq_eq.mpr h1,
      CFSG.KS.Raw.Orb.allN_iff.2 fun i hi => Nat.blt_eq.mpr (h3 i hi).1⟩
  refine ⟨hc, ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => ?_⟩⟩
  rw [← (h3 a ha).2, ← (h3 b hb).2, e]

theorem pg_of_rep {p : Nat} {g : Equiv.Perm (Fin n)} (hp : Rep n (unpack n w p) g) (x : Fin n) :
    pg w (mask w) p x = g x := by
  have := hp x
  rw [CFSG.KC.BfsPin.unpack_getElem!, if_pos x.2] at this
  exact this

theorem rep_inv_of_permOK {p q : Nat} {g : Equiv.Perm (Fin n)} (hsz : szOK n w = true)
    (hp : Rep n (unpack n w p) g) (h1 : permOK n w (mask w) (n * w) p q = true)
    (h2 : permOK n w (mask w) (n * w) q p = true) :
    Rep n (unpack n w q) g⁻¹ ∧ PP n w q := by
  refine ⟨fun x => ?_, pp_of_permOK hsz h2⟩
  obtain ⟨-, -, h3⟩ := CFSG.KS.Raw.Orb.permOK_facts h1
  rw [CFSG.KC.BfsPin.unpack_getElem!, if_pos x.2]
  have e := pg_of_rep hp (g⁻¹ x)
  rw [show g (g⁻¹ x) = x from Equiv.apply_symm_apply g x] at e
  rw [← e, (h3 _ (g⁻¹ x).2).2]

theorem wzK_nil {α : Type} (T : Nat → Nat) (c : α → Nat) : wzK n w T c [] = pidn n w := rfl

theorem wzK_cons {α : Type} (T : Nat → Nat) (c : α → Nat) (a : α) (L : List α) :
    wzK n w T c (a :: L) = pcomp n w (mask w) (T (c a)) (wzK n w T c L) :=
  strictN_eq _ _

theorem wzK_rep {α : Type} {T : Nat → Nat} {c : α → Nat} {V : α → Equiv.Perm (Fin n)}
    (hsz : szOK n w = true) : ∀ L : List α,
      (∀ a ∈ L, Rep n (unpack n w (T (c a))) (V a) ∧ PP n w (T (c a))) →
      Rep n (unpack n w (wzK n w T c L)) (L.map V).prod ∧ PP n w (wzK n w T c L)
  | [], _ => by
    rw [wzK_nil, ← idA_eq hsz]
    exact ⟨rep_idA, PP.id hsz⟩
  | a :: L, h => by
    obtain ⟨ih1, ih2⟩ := wzK_rep hsz L fun b hb => h b (List.mem_cons_of_mem a hb)
    obtain ⟨h1, h2⟩ := h a List.mem_cons_self
    rw [wzK_cons, List.map_cons, List.prod_cons, ← compA_PP h2 ih2]
    exact ⟨rep_compA h1 ih1, h2.mul ih2⟩

theorem tzK_cons {α : Type} (T : Nat → Nat) (c : α → Nat) (a : α) (L : List α) (x : Nat) :
    tzK w T c (a :: L) x = pg w (mask w) (T (c a)) (tzK w T c L x) :=
  strictN_eq _ _

theorem tzK_rep {α : Type} {T : Nat → Nat} {c : α → Nat} {V : α → Equiv.Perm (Fin n)} :
    ∀ L : List α, (∀ a ∈ L, Rep n (unpack n w (T (c a))) (V a)) →
      ∀ x : Fin n, tzK w T c L x = ((L.map V).prod x : ℕ)
  | [], _, x => rfl
  | a :: L, h, x => by
    rw [tzK_cons, tzK_rep L (fun b hb => h b (List.mem_cons_of_mem a hb)) x, List.map_cons,
      List.prod_cons, Equiv.Perm.mul_apply]
    exact pg_of_rep (h a List.mem_cons_self) _

end CFSG.KC.CF23L34

end
