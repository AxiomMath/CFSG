module

public import CFSG.Certificates.Kernel.Spor.SiftEq
public import Certificates.Data.Kernel.U6.Sec3K
public import CFSG.Certificates.Kernel.Spor.RawSlSound
public import CFSG.Certificates.Kernel.Spor.RawSound
public import CFSG.Certificates.NativeValidSchreier
public import CFSG.RankThree.Native.PermEnumeration
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Tabs
import CFSG.Certificates.Kernel.U6Sec3Defs
import CFSG.Certificates.Kernel.Spor.RawAgree
import CFSG.Certificates.Kernel.Spor.RawSiftK
import CFSG.Certificates.Kernel.Spor.PcompFacts
import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.Spor.PackWord
public import Mathlib.GroupTheory.Schreier
public import Std.Data.HashMap
import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.KC.U6Sec3.ProdPf

open CFSG.EvenSmallLie.UnitarySix.YamadaSec3 CFSG.Certificates.Native CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.RankThree.Native CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CFSG.KC.Enum

section Native

open CFSG.Certificates CFSG.Certificates.ChainArrays

variable {n : ℕ} {O S : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}

private noncomputable def gens (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (l : ℕ) :
    Set (Equiv.Perm (Fin n)) :=
  {g | ∃ j < S.size, fixesFirst base S[j]! l = true ∧ g = permOfArr n S[j]!}

private noncomputable def H (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (l : ℕ) :
    Subgroup (Equiv.Perm (Fin n)) :=
  Subgroup.closure (gens n S base l)

private theorem fixesFirst_mono {t : Array ℕ} {i j : ℕ} (hij : i ≤ j)
    (h : fixesFirst base t j = true) : fixesFirst base t i = true := by
  unfold fixesFirst at h ⊢
  rw [allLt_iff] at h ⊢
  exact fun k hk => h k (by omega)

private theorem H_anti {i j : ℕ} (hij : i ≤ j) : H n S base j ≤ H n S base i :=
  Subgroup.closure_mono fun _ ⟨k, hk, hf, e⟩ => ⟨k, hk, fixesFirst_mono hij hf, e⟩

private theorem mem_levelIdx {j l : ℕ} :
    j ∈ levelIdx S base l ↔ j < S.size ∧ fixesFirst base S[j]! l = true := by
  unfold levelIdx
  simp [List.mem_filter, List.mem_range]

variable {c : ℕ} (hF : ChainCheckFacts n O S base W c)
include hF

private theorem rep_S {j : ℕ} (hj : j < S.size) :
    Rep n S[j]! (permOfArr n S[j]!) ∧ Rep n (rawInvs n S)[j]! (permOfArr n S[j]!)⁻¹ :=
  rep_permOfArr (hF.strong_inv j hj)

private theorem H_top : ∀ g ∈ H n S base base.size, g = 1 := by
  intro g hg
  have hle : H n S base base.size ≤ ⊥ := (Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, hf, rfl⟩
    exact Subgroup.mem_bot.2 (eq_of_eqA (rep_S hF hj).1 rep_idA (hF.terminal j hj hf)))
  exact Subgroup.mem_bot.1 (hle hg)

private theorem step_mem {l j : ℕ} (hj : j < (rawSteps n S base l).size) :
    ∃ g ∈ H n S base l, Rep n (rawSteps n S base l)[j]! g := by
  have hm : (rawSteps n S base l)[j]! ∈ rawSteps n S base l := by
    rw [getElem!_pos _ j hj]
    exact Array.getElem_mem hj
  unfold rawSteps levelSteps at hm
  rw [Array.mem_append, List.mem_toArray, List.mem_toArray, List.mem_map, List.mem_map] at hm
  rcases hm with ⟨i, hi, e⟩ | ⟨i, hi, e⟩
  · obtain ⟨hi', hf⟩ := mem_levelIdx.1 hi
    refine ⟨_, Subgroup.subset_closure ⟨i, hi', hf, rfl⟩, ?_⟩
    unfold rawSteps levelSteps
    rw [← e]
    exact (rep_S hF hi').1
  · obtain ⟨hi', hf⟩ := mem_levelIdx.1 hi
    refine ⟨_, inv_mem (Subgroup.subset_closure ⟨i, hi', hf, rfl⟩), ?_⟩
    unfold rawSteps levelSteps
    rw [← e]
    exact (rep_S hF hi').2

private theorem gen_step {l : ℕ} {s : Equiv.Perm (Fin n)} (hs : s ∈ gens n S base l) :
    (∃ j < (rawSteps n S base l).size, Rep n (rawSteps n S base l)[j]! s) ∧
      ∃ j < (rawSteps n S base l).size, Rep n (rawSteps n S base l)[j]! s⁻¹ := by
  obtain ⟨i, hi, hf, rfl⟩ := hs
  have hidx : i ∈ levelIdx S base l := mem_levelIdx.2 ⟨hi, hf⟩
  constructor
  · have hm : S[i]! ∈ rawSteps n S base l := by
      unfold rawSteps levelSteps
      exact Array.mem_append.2 (Or.inl (List.mem_toArray.2 (List.mem_map.2 ⟨i, hidx, rfl⟩)))
    obtain ⟨j, hj, e⟩ := Array.mem_iff_getElem.1 hm
    exact ⟨j, hj, by rw [getElem!_pos _ j hj, e]; exact (rep_S hF hi).1⟩
  · have hm : (rawInvs n S)[i]! ∈ rawSteps n S base l := by
      unfold rawSteps levelSteps
      exact Array.mem_append.2 (Or.inr (List.mem_toArray.2 (List.mem_map.2 ⟨i, hidx, rfl⟩)))
    obtain ⟨j, hj, e⟩ := Array.mem_iff_getElem.1 hm
    exact ⟨j, hj, by rw [getElem!_pos _ j hj, e]; exact (rep_S hF hi).2⟩

private theorem facts {l : ℕ} (hl : l < base.size) :
    LevelFacts n base[l]! (rawSteps n S base l) (lev n S base l) :=
  levelFacts_of_levelOK (hF.level l hl)

private theorem rep_T {l k : ℕ} (hl : l < base.size) (hk : k < (lev n S base l).pts.size) :
    Rep n (lev n S base l).tr[k]! (levT n S base l k) ∧
      Rep n (lev n S base l).trInv[k]! (levT n S base l k)⁻¹ :=
  rep_permOfArr ((facts hF hl).tr_inv k hk)

private theorem T_zero {l : ℕ} (hl : l < base.size) : levT n S base l 0 = 1 :=
  eq_of_eqA (rep_T hF hl (facts hF hl).pos).1 rep_idA (facts hF hl).tr_zero

private theorem T_mem {l : ℕ} (hl : l < base.size) :
    ∀ k < (lev n S base l).pts.size, levT n S base l k ∈ H n S base l := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have F := facts hF hl
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · rw [T_zero hF hl]
      exact one_mem _
    · have hp := F.par_lt k hk hk0
      obtain ⟨g, hg, hr⟩ := step_mem hF (F.lab_lt k hk hk0)
      have e := eq_of_eqA (rep_T hF hl hk).1 (rep_compA hr (rep_T hF hl (by omega)).1)
        (F.tr_step k hk hk0)
      rw [e]
      exact mul_mem hg (ih _ hp (by omega))

private theorem sift_sound : ∀ d l, l + d = base.size → ∀ (a : Array ℕ) (g : Equiv.Perm (Fin n)),
    Rep n a g → siftA n (rawLevels n S base) base l a = true →
    ∃ κ : ℕ → ℕ, (∀ j < d, κ (l + j) < (lev n S base (l + j)).pts.size) ∧
      g = ((List.range d).map fun j => levT n S base (l + j) (κ (l + j))).prod := by
  intro d
  induction d with
  | zero =>
    intro l hl a g ha h
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega)] at h
    refine ⟨fun _ => 0, fun j hj => absurd hj (Nat.not_lt_zero _), ?_⟩
    rw [(eqA_iff ha rep_idA).1 h]
    rfl
  | succ d ih =>
    intro l hl a g ha h
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hk, h⟩ := h
    obtain ⟨κ, hκ, e⟩ := ih (l + 1) (by omega) _ _ (rep_compA (rep_T hF hlb hk).2 ha) h
    refine ⟨fun j => if j = l then (lev n S base l).pos[a[base[l]!]!]! else κ j,
      fun j hj => ?_, ?_⟩
    · rcases j with _ | j
      · simpa using hk
      · have := hκ j (by omega)
        simp only [show l + (j + 1) ≠ l by omega, if_false]
        rwa [show l + (j + 1) = l + 1 + j by omega]
    · rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons]
      have e2 : (List.range d).map ((fun j => levT n S base (l + j)
          (if l + j = l then (lev n S base l).pos[a[base[l]!]!]! else κ (l + j))) ∘ Nat.succ) =
          (List.range d).map fun j => levT n S base (l + 1 + j) (κ (l + 1 + j)) :=
        List.map_congr_left fun j _ => by
          simp only [Function.comp_apply, Nat.succ_eq_add_one,
            show l + (j + 1) = l + 1 + j by omega, show l + 1 + j ≠ l by omega, if_false]
      rw [e2, ← e]
      simp

private theorem mem_of_sift {l : ℕ} (hl : l ≤ base.size) {a : Array ℕ}
    {g : Equiv.Perm (Fin n)} (ha : Rep n a g)
    (h : siftA n (rawLevels n S base) base l a = true) : g ∈ H n S base l := by
  obtain ⟨κ, hκ, rfl⟩ := sift_sound hF (base.size - l) l (by omega) a g ha h
  refine list_prod_mem fun x hx => ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  have hj' := List.mem_range.1 hj
  exact H_anti (by omega : l ≤ l + j) (T_mem hF (by omega) _ (hκ j hj'))

omit hF in
private def SchP (n : ℕ) (S : Array (Array ℕ)) (base : Array ℕ) (l : ℕ)
    (g : Equiv.Perm (Fin n)) : Prop :=
  ∀ h < (lev n S base l).pts.size, ∀ z : Fin n, (z : ℕ) = (lev n S base l).pts[h]! →
    ∃ k < (lev n S base l).pts.size, (lev n S base l).pts[k]! = (g z : ℕ) ∧
      (levT n S base l k)⁻¹ * g * levT n S base l h ∈ H n S base (l + 1)

private theorem schP_step (hF1 : ChainCheckFacts n O S base W 1) {l : ℕ} (hl : l < base.size)
    {j : ℕ} (hj : j < (rawSteps n S base l).size) {s y : Equiv.Perm (Fin n)}
    (hs : Rep n (rawSteps n S base l)[j]! s) (hy : SchP n S base l y) :
    SchP n S base l (s * y) := by
  intro h hh z hz
  obtain ⟨k, hk, hpk, hmem⟩ := hy h hh z hz
  have F := facts hF hl
  have htest : allLt (rawSteps n S base l).size (fun j =>
      decide ((lev n S base l).pos[((rawSteps n S base l)[j]!)[(lev n S base l).pts[k]!]!]! <
        (lev n S base l).pts.size) &&
        siftA n (rawLevels n S base) base (l + 1)
          (compA n (lev n S base l).trInv[(lev n S base l).pos[((rawSteps n S base l)[j]!)[
            (lev n S base l).pts[k]!]!]!]!
            (compA n (rawSteps n S base l)[j]! (lev n S base l).tr[k]!))) = true :=
    parLt_spec (by norm_num) (hF1.schreier l hl) k hk
  have ht := allLt_spec htest hj
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hk', hsift⟩ := ht
  have hzv : ((rawSteps n S base l)[j]!)[(lev n S base l).pts[k]!]! = ((s * y) z : ℕ) := by
    rw [hs.apply (F.pts_lt k hk), Equiv.Perm.mul_apply]
    congr 2
    exact Fin.ext hpk
  rw [hzv] at hk' hsift
  refine ⟨_, hk', F.pts_pos _ (Fin.isLt _) hk', ?_⟩
  have hrep := rep_compA (rep_T hF hl hk').2 (rep_compA hs (rep_T hF hl hk).1)
  have hm := mem_of_sift hF1 (by omega) hrep hsift
  have e : (levT n S base l ((lev n S base l).pos[((s * y) z : ℕ)]!))⁻¹ * (s * y) *
      levT n S base l h =
      ((levT n S base l ((lev n S base l).pos[((s * y) z : ℕ)]!))⁻¹ * (s * levT n S base l k)) *
        ((levT n S base l k)⁻¹ * y * levT n S base l h) := by
    group
  rw [e]
  exact mul_mem hm hmem

private theorem schP_of_mem (hF1 : ChainCheckFacts n O S base W 1) {l : ℕ} (hl : l < base.size)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H n S base l) : SchP n S base l g := by
  refine Subgroup.closure_induction_left (p := fun g _ => SchP n S base l g) ?_ ?_ ?_ hg
  · intro h hh z hz
    refine ⟨h, hh, by rw [← hz]; rfl, ?_⟩
    rw [mul_one, inv_mul_cancel]
    exact one_mem _
  · intro s hs y _ hy
    obtain ⟨j, hj, hr⟩ := (gen_step hF hs).1
    exact schP_step hF hF1 hl hj hr hy
  · intro s hs y _ hy
    obtain ⟨j, hj, hr⟩ := (gen_step hF hs).2
    exact schP_step hF hF1 hl hj hr hy

omit hF in
private theorem sift_complete (hF1 : ChainCheckFacts n O S base W 1) :
    ∀ d l, l + d = base.size → ∀ (a : Array ℕ) (g : Equiv.Perm (Fin n)), Rep n a g →
      g ∈ H n S base l → siftA n (rawLevels n S base) base l a = true := by
  intro d
  induction d with
  | zero =>
    intro l hl a g ha hg
    have hle : l = base.size := by omega
    subst hle
    rw [siftA, dite_eq_right (by rw [chainLevels_size]; omega), eqA_iff ha rep_idA]
    exact H_top hF1 g hg
  | succ d ih =>
    intro l hl a g ha hg
    have hlb : l < base.size := by omega
    have hls : l < (rawLevels n S base).size := by rw [chainLevels_size]; exact hlb
    have F := facts hF1 hlb
    have hb : base[l]! < n := hF1.base_lt l hlb
    obtain ⟨k, hk, hpk, hmem⟩ :=
      schP_of_mem hF1 hF1 hlb hg 0 F.pos ⟨base[l]!, hb⟩ F.root.symm
    rw [T_zero hF1 hlb, mul_one] at hmem
    rw [siftA, dite_eq_left hls, chainLevels_getElem hls]
    have hpos : (lev n S base l).pos[a[base[l]!]!]! = k := by
      rw [ha.apply hb, ← hpk, F.pos_pts k hk]
    simp only [hpos, hk, decide_true, Bool.true_and]
    exact ih (l + 1) (by omega) _ _ (rep_compA (rep_T hF1 hlb hk).2 ha) hmem

omit hF in
private theorem decomp {kO : ℕ} (hF1 : ChainCheckFacts n (S.extract 0 kO) S base W 1)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ Subgroup.closure (permsA n (S.extract 0 kO))) :
    ∃ κ : ℕ → ℕ, (∀ j < base.size, κ j < (lev n S base j).pts.size) ∧
      x = ((List.range base.size).map fun j => levT n S base j (κ j)).prod := by
  have hx0 : x ∈ H n S base 0 := by
    refine Subgroup.closure_mono ?_ hx
    rintro _ ⟨j, hj, rfl⟩
    have hj0 : j < (S.extract 0 kO).size := hj
    have hj' : j < S.size := by simp at hj0; omega
    refine ⟨j, hj', ?_, ?_⟩
    · unfold fixesFirst
      exact allLt_iff.2 fun k hk => absurd hk (Nat.not_lt_zero _)
    · change permOfArr n (S.extract 0 kO)[j]! = permOfArr n S[j]!
      rw [getElem!_pos (S.extract 0 kO) j hj0, Array.getElem_extract, getElem!_pos S j hj']
      simp
  have ha : Rep n (Array.ofFn (n := n) fun i => (x i : ℕ)) x := fun z =>
    getElem!_ofFn_nat _ z.2
  have hs := sift_complete hF1 base.size 0 (by simp) _ _ ha hx0
  obtain ⟨κ, hκ, e⟩ := sift_sound hF1 base.size 0 (by simp) _ _ ha hs
  exact ⟨κ, fun j hj => by simpa using hκ j hj, by simpa using e⟩

end Native

private theorem prodAllK_spec {n w m nw : ℕ} {LR TR : ℕ → ℕ} {f : ℕ → Bool} (κ : ℕ → ℕ) :
    ∀ d i acc, prodAllK n w m nw LR TR f d i acc = true →
      (∀ j < d, κ (i + j) < rcnt (LR (i + j))) →
      f (((List.range d).map fun j => TR (roff n nw (LR (i + j)) + κ (i + j))).foldl
        (pcomp n w m) acc) = true
  | 0, i, acc, h, _ => by simpa [prodAllK_zero] using h
  | d + 1, i, acc, h, hκ => by
    rw [prodAllK_succ] at h
    have h1 := prodAllK_spec κ d (i + 1) _ (allN_spec h (κ i) (by simpa using hκ 0 (by omega)))
      (fun j hj => by
        have := hκ (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this)
    have e : (fun j => TR (roff n nw (LR (i + (j + 1))) + κ (i + (j + 1)))) =
        fun j => TR (roff n nw (LR (i + 1 + j)) + κ (i + 1 + j)) :=
      funext fun j => by rw [Nat.add_assoc, Nat.add_comm 1 j]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.foldl_cons, Nat.add_zero]
    simpa only [Function.comp_def, Nat.succ_eq_add_one, e] using h1

private theorem prodLazyK_spec {n nw : ℕ} {LR TR : ℕ → ℕ} {f : List ℕ → Bool} (κ : ℕ → ℕ) :
    ∀ d i L, prodLazyK n nw LR TR f d i L = true →
      (∀ j < d, κ (i + j) < rcnt (LR (i + j))) →
      f (((List.range d).map fun j => TR (roff n nw (LR (i + j)) + κ (i + j))).reverse ++ L) =
        true
  | 0, i, L, h, _ => by simpa [prodLazyK_zero] using h
  | d + 1, i, L, h, hκ => by
    rw [prodLazyK_succ] at h
    have h1 := prodLazyK_spec κ d (i + 1) _ (allN_spec h (κ i) (by simpa using hκ 0 (by omega)))
      (fun j hj => by
        have := hκ (j + 1) (by omega)
        rwa [show i + (j + 1) = i + 1 + j by omega] at this)
    have e : (fun j => TR (roff n nw (LR (i + (j + 1))) + κ (i + (j + 1)))) =
        fun j => TR (roff n nw (LR (i + 1 + j)) + κ (i + 1 + j)) :=
      funext fun j => by rw [Nat.add_assoc, Nat.add_comm 1 j]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons,
      List.append_assoc, List.singleton_append, Nat.add_zero]
    simpa only [Function.comp_def, Nat.succ_eq_add_one, e] using h1

private theorem canonK_foldl {n w : ℕ} : ∀ (L : List ℕ) (acc : ℕ),
    canonK n w (mask w) (n * w) acc = true → (∀ t ∈ L, canonK n w (mask w) (n * w) t = true) →
    canonK n w (mask w) (n * w) (L.foldl (pcomp n w (mask w)) acc) = true
  | [], _, h, _ => h
  | t :: L, acc, h, hL => canonK_foldl L _ (CFSG.KC.BfsPin.canonK_pcomp h (hL t (by simp)))
      fun t' ht' => hL t' (by simp [ht'])

private theorem pg_foldl_pcomp {n w : ℕ} (hn : n < 2 ^ 32) :
    ∀ {Ts : List ℕ} {Gs : List (Equiv.Perm (Fin n))},
      List.Forall₂ (fun t (g : Equiv.Perm (Fin n)) => ∀ z : Fin n, pg w (mask w) t z = g z) Ts Gs →
      ∀ (acc : ℕ) (A : Equiv.Perm (Fin n)), (∀ z : Fin n, pg w (mask w) acc z = A z) →
      ∀ z : Fin n, pg w (mask w) (Ts.foldl (pcomp n w (mask w)) acc) z = ((A * Gs.prod) z : ℕ)
  | [], [], .nil, _, A, hA, z => by simpa using hA z
  | t :: Ts, g :: Gs, .cons ht h, acc, A, hA, z => by
    rw [List.foldl_cons, pg_foldl_pcomp hn h (pcomp n w (mask w) acc t) (A * g) (fun y => by
      rw [CFSG.KS.PF.pg_pcomp hn y.2, ht y, hA (g y), Equiv.Perm.mul_apply]) z, List.prod_cons,
      mul_assoc]

private theorem pg_foldl {n w : ℕ} (hn : n < 2 ^ 32) :
    ∀ (L : List ℕ) (acc i : ℕ), i < n →
      pg w (mask w) (List.foldl (fun acc t => strictN acc fun acc => pcomp n w (mask w) t acc)
        acc L) i = ptL w (mask w) L (pg w (mask w) acc i)
  | [], _, _, _ => rfl
  | t :: L, acc, i, hi => by
    have e : ∀ (y : ℕ) (k : ℕ → ℕ), strictN y k = k y := fun y k => by cases y <;> rfl
    rw [List.foldl_cons, e, pg_foldl hn L _ i hi, CFSG.KS.PF.pg_pcomp hn hi]
    rfl

private theorem ptL_reverse {n w : ℕ} :
    ∀ {Ts : List ℕ} {Gs : List (Equiv.Perm (Fin n))},
      List.Forall₂ (fun t (g : Equiv.Perm (Fin n)) => ∀ z : Fin n, pg w (mask w) t z = g z) Ts Gs →
      ∀ z : Fin n, ptL w (mask w) Ts.reverse z = (Gs.prod z : ℕ)
  | [], [], .nil, _ => rfl
  | t :: Ts, g :: Gs, .cons ht h, z => by
    have e : ptL w (mask w) (Ts.reverse ++ [t]) z =
        pg w (mask w) t (ptL w (mask w) Ts.reverse z) := by
      simp only [ptL, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [List.reverse_cons, e, ptL_reverse h z, List.prod_cons, Equiv.Perm.mul_apply]
    exact ht _

private theorem canonK_of_permOK {n w p q : ℕ} (hs : szOK n w = true)
    (h : permOK n w (mask w) (n * w) p q = true) : canonK n w (mask w) (n * w) p = true := by
  refine (bAnd_iff _ _).2 ⟨hs, (bAnd_iff _ _).2 ⟨?_, range_of_permOK h⟩⟩
  unfold permOK at h
  exact ((bAnd_iff _ _).1 h).1

private theorem canonK_pidn {n w : ℕ} (hn : n < 16777216) (hw : n + 1 < 2 ^ w) :
    canonK n w (mask w) (n * w) (pidn n w) = true := by
  refine (bAnd_iff _ _).2 ⟨(bAnd_iff _ _).2 ⟨Nat.blt_eq.mpr hn, Nat.blt_eq.mpr ?_⟩,
    (bAnd_iff _ _).2 ⟨Nat.beq_eq.mpr (CFSG.KS.PF.pidn_shr hn hw),
      allN_of_forall fun i hi => Nat.blt_eq.mpr ?_⟩⟩
  · change n + 1 < 1 <<< w
    rw [Nat.shiftLeft_eq, Nat.one_mul]
    exact hw
  · rw [CFSG.KS.PF.pg_pidn hn hw hi]
    exact hi

private theorem kernel_T {n w kS kO nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {SA : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)}
    (hb : Binds n w PS kS nb BP SA base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hF : CFSG.Certificates.ChainCheckFacts n (SA.extract 0 kO) SA base W 1)
    {j k : ℕ} (hj : j < nb)
    (hk : k < (CFSG.Certificates.ChainArrays.lev n SA base j).pts.size) :
    k < rcnt (LR j) ∧ canonK n w (mask w) (n * w) (TR (roff n (n * w) (LR j) + k)) = true ∧
      ∀ z : Fin n, pg w (mask w) (TR (roff n (n * w) (LR j) + k)) z =
        (CFSG.Certificates.ChainArrays.levT n SA base j k z : ℕ) := by
  have hbl := Raw.Orb.base_lt_of_levels hb hl
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  obtain ⟨A, P⟩ := Raw.Orb.agree_levelK hb hp hbl (R := LR) (TRI := TRI) hj (hl j hj)
  have hkc : k < rcnt (LR j) := A.cnt ▸ hk
  obtain ⟨hsz, -, -, -, -, hperm⟩ := Raw.Orb.levelK_facts (hl j hj)
  refine ⟨hkc, canonK_of_permOK hsz (hperm _ hkc), fun z => ?_⟩
  have r3 := (rep_permOfArr
    ((CFSG.Certificates.ChainArrays.levelFacts_of_levelOK (hF.level j (hbs ▸ hj))).tr_inv k
      hk)).1 z
  exact ((P _ hkc).1 z).trans (((A.tr _ hk).1 z).symm.trans r3)

theorem forall_of_prodAllK' {n w kS kO nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {SA : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {f : ℕ → Bool}
    (hb : Binds n w PS kS nb BP SA base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hraw : rawChainOK n (SA.extract 0 kO) SA base W 1 = true)
    (hf : prodAllK n w (mask w) (n * w) LR TR f nb 0 (pidn n w) = true) :
    ∀ x ∈ Subgroup.closure (permsA n (SA.extract 0 kO)), ∃ X : ℕ,
      canonK n w (mask w) (n * w) X = true ∧ Rep n (unpack n w X) x ∧ f X = true := by
  intro x hx
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hw' : n + 1 < 2 ^ w := hb.2.1
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hF := CFSG.Certificates.chainCheckFacts hraw
  obtain ⟨κ, hK, hx'⟩ := decomp hF hx
  rw [hbs] at hK hx'
  have hTj := fun j (hj : j < nb) => kernel_T hb hp hl hF hj (hK j hj)
  let T : ℕ → ℕ := fun j => TR (roff n (n * w) (LR j) + κ j)
  refine ⟨((List.range nb).map T).foldl (pcomp n w (mask w)) (pidn n w), ?_, fun z => ?_, ?_⟩
  · refine canonK_foldl _ _ (canonK_pidn hn24 hw') fun t ht => ?_
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 ht
    exact (hTj j (List.mem_range.1 hj)).2.1
  · rw [Raw.Orb.unpack_get z.2, pg_foldl_pcomp hn32 (Gs := (List.range nb).map fun j =>
      CFSG.Certificates.ChainArrays.levT n SA base j (κ j)) ?_ (pidn n w) 1
      (fun y => by rw [CFSG.KS.PF.pg_pidn hn24 hw' y.2]; rfl) z, one_mul, hx']
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun j hj => (hTj j (List.mem_range.1 hj)).2.2
  · have := prodAllK_spec κ nb 0 (pidn n w) hf fun j hj => by
      simpa using (hTj j hj).1
    simpa using this

theorem forall_of_prodLazyK' {n w kS kO nb BP : ℕ} {PS PSI LR TR TRI : ℕ → ℕ}
    {SA : Array (Array ℕ)} {base : Array ℕ} {W : Array (List ℤ)} {f : List ℕ → Bool}
    (hb : Binds n w PS kS nb BP SA base)
    (hp : allN kS (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) = true)
    (hl : LevelsOK n w PS PSI LR TR TRI kS nb BP)
    (hraw : rawChainOK n (SA.extract 0 kO) SA base W 1 = true)
    (hf : prodLazyK n (n * w) LR TR f nb 0 [] = true) :
    ∀ x ∈ Subgroup.closure (permsA n (SA.extract 0 kO)), ∃ L : List ℕ,
      (∀ t ∈ L, canonK n w (mask w) (n * w) t = true) ∧
      Rep n (unpack n w (prodL n w (mask w) L)) x ∧ f L = true := by
  intro x hx
  have hn24 : n < 16777216 := by have := hb.2.2.1; omega
  have hn32 : n < 2 ^ 32 := by omega
  have hw' : n + 1 < 2 ^ w := hb.2.1
  have hbs : base.size = nb := hb.2.2.2.2.2.1
  have hF := CFSG.Certificates.chainCheckFacts hraw
  obtain ⟨κ, hK, hx'⟩ := decomp hF hx
  rw [hbs] at hK hx'
  have hTj := fun j (hj : j < nb) => kernel_T hb hp hl hF hj (hK j hj)
  let T : ℕ → ℕ := fun j => TR (roff n (n * w) (LR j) + κ j)
  refine ⟨((List.range nb).map T).reverse, fun t ht => ?_, fun z => ?_, ?_⟩
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 ht)
    exact (hTj j (List.mem_range.1 hj)).2.1
  · rw [Raw.Orb.unpack_get z.2, prodL, pg_foldl hn32 _ _ _ z.2, CFSG.KS.PF.pg_pidn hn24 hw' z.2,
      hx']
    refine ptL_reverse ?_ z
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.2 fun j hj => (hTj j (List.mem_range.1 hj)).2.2
  · have := prodLazyK_spec κ nb 0 [] hf fun j hj => by
      simpa using (hTj j hj).1
    simpa using this

end CFSG.KC.U6Sec3.ProdPf

end
