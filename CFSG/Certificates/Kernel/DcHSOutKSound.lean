module

public import Certificates.Data.Kernel.DcHSOutK
public import CFSG.Certificates.Kernel.DcKInv
import CFSG.Certificates.Kernel.Spor.RawOrbEval
public import Certificates.Data.DcHS

public section

namespace CFSG.KC.DcHSOutK

open CFSG.Quasithin.H13.LocDbl.HSLoc CFSG.Quasithin.H13.LocDbl.DcNative
  CFSG.Quasithin.H13.LocDbl.DcRank CFSG.KC.E64F CFSG.KC.Enum

theorem nbeq (a b : Nat) : (a == b) = Nat.beq a b := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, Nat.beq_eq]

theorem allN_eq' (n : Nat) (f : Nat → Bool) : allN n f = (List.range n).all f :=
  CFSG.KS.Raw.Orb.allN_eq n f

theorem good_img {t : Array Nat} {f : Nat → Nat} (ht : Good 100 t f) {p : Nat} (hp : p < 100) :
    img t p = f p := (ht.2 p hp).1

theorem good_lt {t : Array Nat} {f : Nat → Nat} (ht : Good 100 t f) {p : Nat} (hp : p < 100) :
    f p < 100 := (ht.2 p hp).2

theorem good_compT {t u : Array Nat} {f g : Nat → Nat} (ht : Good 100 t f) (hu : Good 100 u g) :
    Good 100 (compT t u) (fun q => f (g q)) := by
  refine ⟨by simp [compT, hu.1], fun p hp => ?_⟩
  have hpu : p < u.size := by rw [hu.1]; exact hp
  unfold compT
  rw [getD_map_arr hpu]
  have e : u.getD p 0 = g p := (hu.2 p hp).1
  rw [e]
  exact ⟨good_img ht (good_lt hu hp), good_lt ht (good_lt hu hp)⟩

theorem good_conjT {g gi t : Array Nat} {f h s : Nat → Nat} (hg : Good 100 g f)
    (hgi : Good 100 gi h) (ht : Good 100 t s) :
    Good 100 (conjT g gi t) (fun q => f (s (h q))) :=
  good_compT hg (good_compT ht hgi)

theorem good_idT : Good 100 (idT 100) (fun q => q) := by
  refine ⟨by simp [idT], fun p hp => ⟨?_, hp⟩⟩
  simp [idT, Array.getD_eq_getD_getElem?, hp]

theorem good_invT {s : Array Nat} {f g : Nat → Nat} (hs : Good 100 s f)
    (hg : ∀ p < 100, g p < 100) (hgf : ∀ p < 100, g (f p) = p) (hfg : ∀ p < 100, f (g p) = p) :
    Good 100 (invT s) g := by
  have e : invT s = invTab s := by
    rw [CFSG.KC.DcK.invTab_eq, ← List.range_eq_range']
    rfl
  rw [e]
  exact CFSG.KC.DcK.invTab_good hs hg hgf hfg

theorem good_ext {s t : Array Nat} {f g : Nat → Nat} (hs : Good 100 s f) (ht : Good 100 t g)
    (h : ∀ p < 100, f p = g p) : s = t := by
  apply Array.ext
  · rw [hs.1, ht.1]
  · intro i h1 h2
    have e1 : s.getD i 0 = s[i] := by simp [Array.getD_eq_getD_getElem?, h1]
    have e2 : t.getD i 0 = t[i] := by simp [Array.getD_eq_getD_getElem?, h2]
    have hi : i < 100 := by rw [← hs.1]; exact h1
    rw [← e1, ← e2, (hs.2 i hi).1, (ht.2 i hi).1, h i hi]

theorem beq_eq {s t : Array Nat} {f g : Nat → Nat} (hs : Good 100 s f) (ht : Good 100 t g) :
    (s == t) = eqF f g := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, eqF, CFSG.KS.Raw.Orb.allN_iff]
  constructor
  · rintro rfl p hp
    rw [Nat.beq_eq, ← (hs.2 p hp).1, ← (ht.2 p hp).1]
  · intro h
    exact good_ext hs ht fun p hp => by have := h p hp; rwa [Nat.beq_eq] at this

theorem commT_eq {s t : Array Nat} {f g : Nat → Nat} (hs : Good 100 s f) (ht : Good 100 t g) :
    commT s t = commF f g := by
  unfold commT commF
  rw [allN_eq']
  apply all_congr'
  intro q hq
  have hq' : q < 100 := List.mem_range.1 hq
  rw [good_img ht hq', good_img hs hq', good_img hs (good_lt ht hq'),
    good_img ht (good_lt hs hq'), nbeq]

theorem fix_eq {t : Array Nat} {f : Nat → Nat} (ht : Good 100 t f) :
    (F0.all fun x => img t x == x) = fixF0 f := by
  unfold fixF0
  apply all_congr'
  intro x hx
  have hx' : x < 100 := by
    simp only [F0, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  rw [good_img ht hx', nbeq]

theorem pwDistinct_of_pairwise : ∀ {l : List (Array Nat)}, l.Pairwise (· ≠ ·) →
    pwDistinct l = true
  | [], _ => rfl
  | x :: l, h => by
    rw [List.pairwise_cons] at h
    unfold pwDistinct
    rw [Bool.and_eq_true, List.all_eq_true]
    exact ⟨fun y hy => by simpa using h.1 y hy, pwDistinct_of_pairwise h.2⟩

theorem ptsArr_spec {G : Array (Array Nat)} {Lm : Nat → Nat → Nat} {par lab : Array Nat}
    {N : Nat} {F : Nat → Nat → Nat} (q : Nat)
    (hG : ∀ t < G.size, Good 100 (G.getD t #[]) (Lm t)) (h0 : F 0 q = q)
    (hs : ∀ k, 0 < k → k < N → par.getD k 0 < k ∧ lab.getD k 0 < G.size ∧
      F k q = Lm (lab.getD k 0) (F (par.getD k 0) q))
    (hlt : ∀ k < N, F k q < 100) :
    ∀ k < N, (ptsArr G par lab N q).getD k 0 = F k q := by
  have key : ∀ j ≤ N, ((List.range j).foldl (ptsStep G par lab q) #[]).size = j ∧
      ∀ k < j, ((List.range j).foldl (ptsStep G par lab q) #[]).getD k 0 = F k q := by
    intro j
    induction j with
    | zero => intro _; exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    | succ j ih =>
      intro hj
      obtain ⟨hsz, hget⟩ := ih (by omega)
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      generalize (List.range j).foldl (ptsStep G par lab q) #[] = acc at hsz hget
      unfold ptsStep
      refine ⟨by simp [hsz], fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | hk
      · have e := hget k hk
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega),
          Option.getD_some] at e
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt (by omega)]
        exact e
      · rw [hk, Array.getD_eq_getD_getElem?, ← hsz, Array.getElem?_push_size, Option.getD_some,
          hsz]
        by_cases hj0 : j = 0
        · rw [if_pos hj0, hj0, h0]
        · rw [if_neg hj0]
          obtain ⟨hp, hl, hF⟩ := hs j (by omega) (by omega)
          rw [hget _ hp, hF]
          exact good_img (hG _ hl) (hlt _ (by omega))
  exact fun k hk => (key N (Nat.le_refl N)).2 k hk

section Paths

variable {P L : Nat → Nat} {A : Nat → Nat → Nat}

theorem ePath_zero (f q : Nat) : ePath P L A f 0 q = q := by cases f <;> rfl

theorem ePathI_zero (f q : Nat) : ePathI P L A f 0 q = q := by cases f <;> rfl

theorem ePath_succ {k : Nat} (hk : k ≠ 0) (f q : Nat) :
    ePath P L A (f + 1) k q = A (L k) (ePath P L A f (P k) q) := by
  simp [ePath, hk]

theorem ePathI_succ {k : Nat} (hk : k ≠ 0) (f q : Nat) :
    ePathI P L A (f + 1) k q = ePathI P L A f (P k) (A (invL (L k)) q) := by
  simp [ePathI, hk]

theorem ePath_stable {N : Nat} (hP : ∀ k, 0 < k → k < N → P k < k) :
    ∀ k < N, ∀ f g q, k < f → k < g → ePath P L A f k q = ePath P L A g k q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk f g q hf hg
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    by_cases h0 : k = 0
    · subst h0
      rw [ePath_zero, ePath_zero]
    · have hp := hP k (by omega) hk
      rw [ePath_succ h0, ePath_succ h0, ih (P k) hp (by omega) f g q (by omega) (by omega)]

theorem ePathI_stable {N : Nat} (hP : ∀ k, 0 < k → k < N → P k < k) :
    ∀ k < N, ∀ f g q, k < f → k < g → ePathI P L A f k q = ePathI P L A g k q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk f g q hf hg
    obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    by_cases h0 : k = 0
    · subst h0
      rw [ePathI_zero, ePathI_zero]
    · have hp := hP k (by omega) hk
      rw [ePathI_succ h0, ePathI_succ h0, ih (P k) hp (by omega) f g _ (by omega) (by omega)]

theorem ePath_step {N : Nat} (hP : ∀ k, 0 < k → k < N → P k < k) {k : Nat} (hk0 : k ≠ 0)
    (hk : k < N) (q : Nat) : ePath P L A N k q = A (L k) (ePath P L A N (P k) q) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hp := hP k (by omega) hk
  rw [ePath_succ hk0, ePath_stable hP (P k) (by omega) M (M + 1) q (by omega) (by omega)]

theorem ePathI_step {N : Nat} (hP : ∀ k, 0 < k → k < N → P k < k) {k : Nat} (hk0 : k ≠ 0)
    (hk : k < N) (q : Nat) :
    ePathI P L A N k q = ePathI P L A N (P k) (A (invL (L k)) q) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hp := hP k (by omega) hk
  rw [ePathI_succ hk0, ePathI_stable hP (P k) (by omega) M (M + 1) _ (by omega) (by omega)]

theorem ePath_lt {N : Nat} (hA : ∀ l < 4, ∀ q < 100, A l q < 100)
    (hL : ∀ k, 0 < k → k < N → L k < 4) (hP : ∀ k, 0 < k → k < N → P k < k) :
    ∀ f, ∀ k < N, ∀ q < 100, ePath P L A f k q < 100 := by
  intro f
  induction f with
  | zero => intro k _ q hq; exact hq
  | succ f ih =>
    intro k hk q hq
    by_cases h0 : k = 0
    · subst h0
      rw [ePath_zero]
      exact hq
    · rw [ePath_succ h0]
      exact hA _ (hL k (by omega) hk) _ (ih (P k) (by have := hP k (by omega) hk; omega) q hq)

theorem invL_lt {l : Nat} (hl : l < 4) : invL l < 4 := by
  unfold invL
  split <;> omega

theorem ePathI_lt {N : Nat} (hA : ∀ l < 4, ∀ q < 100, A l q < 100)
    (hL : ∀ k, 0 < k → k < N → L k < 4) (hP : ∀ k, 0 < k → k < N → P k < k) :
    ∀ f, ∀ k < N, ∀ q < 100, ePathI P L A f k q < 100 := by
  intro f
  induction f with
  | zero => intro k _ q hq; exact hq
  | succ f ih =>
    intro k hk q hq
    by_cases h0 : k = 0
    · subst h0
      rw [ePathI_zero]
      exact hq
    · rw [ePathI_succ h0]
      exact ih (P k) (by have := hP k (by omega) hk; omega) _
        (hA _ (invL_lt (hL k (by omega) hk)) q hq)

theorem ePath_inv {N : Nat} (hA : ∀ l < 4, ∀ q < 100, A l q < 100)
    (hinv : ∀ l < 4, ∀ q < 100, A (invL l) (A l q) = q ∧ A l (A (invL l) q) = q)
    (hL : ∀ k, 0 < k → k < N → L k < 4) (hP : ∀ k, 0 < k → k < N → P k < k) :
    ∀ k < N, ∀ q < 100, ePathI P L A N k (ePath P L A N k q) = q ∧
      ePath P L A N k (ePathI P L A N k q) = q := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk q hq
    by_cases h0 : k = 0
    · subst h0
      simp [ePath_zero, ePathI_zero]
    · have hp := hP k (by omega) hk
      have hl := hL k (by omega) hk
      have hy := ePath_lt hA hL hP N (P k) (by omega) q hq
      have hz := hA _ (invL_lt hl) q hq
      refine ⟨?_, ?_⟩
      · rw [ePath_step hP h0 hk, ePathI_step hP h0 hk, (hinv _ hl _ hy).1]
        exact (ih (P k) hp (by omega) q hq).1
      · rw [ePathI_step hP h0 hk, ePath_step hP h0 hk, (ih (P k) hp (by omega) _ hz).2]
        exact (hinv _ hl q hq).2

end Paths

theorem enumTabs_good {G : Array (Array Nat)} {Lm : Nat → Nat → Nat} {par lab : Array Nat}
    {N : Nat} {F : Nat → Nat → Nat}
    (hG : ∀ t < G.size, Good 100 (G.getD t #[]) (Lm t)) (h0 : ∀ q < 100, F 0 q = q)
    (hs : ∀ k, 0 < k → k < N → par.getD k 0 < k ∧ lab.getD k 0 < G.size ∧
      ∀ q < 100, F k q = Lm (lab.getD k 0) (F (par.getD k 0) q))
    (hlt : ∀ k < N, ∀ q < 100, F k q < 100) :
    ∀ k < N, Good 100 ((enumTabs G (par, lab) N).getD k #[]) (F k) := by
  intro k hk
  have hp : ∀ q < 100, (ptsArr G par lab N q).getD k 0 = F k q := fun q hq =>
    ptsArr_spec q hG (h0 q hq) (fun k' h1 h2 => ⟨(hs k' h1 h2).1, (hs k' h1 h2).2.1,
      (hs k' h1 h2).2.2 q hq⟩) (fun k' hk' => hlt k' hk' q hq) k hk
  have e : (enumTabs G (par, lab) N).getD k #[] =
      ((Array.range 100).map (ptsArr G par lab N)).map (fun A => A.getD k 0) := by
    simp [enumTabs, Array.getD_eq_getD_getElem?, hk]
  rw [e]
  refine ⟨by simp, fun p hpp => ⟨?_, hlt k hk p hpp⟩⟩
  have e2 : (((Array.range 100).map (ptsArr G par lab N)).map (fun A => A.getD k 0)).getD p 0 =
      (ptsArr G par lab N p).getD k 0 := by
    simp [Array.getD_eq_getD_getElem?, hpp]
  rw [e2]
  exact hp p hpp

end CFSG.KC.DcHSOutK

end
