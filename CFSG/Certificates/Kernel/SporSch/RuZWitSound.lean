module

public import Certificates.Data.Kernel.SporSch.Ru2250K
public import CFSG.Sporadic.Schreier.RuTreeElt
public import Certificates.Certificate2259
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
import CFSG.Certificates.Kernel.SporSch.RuTreeIdxSound
import CFSG.Certificates.Kernel.SporSch.RuTreeSetsSound
import CFSG.Certificates.Kernel.Spor.PackFld

public section

set_option maxRecDepth 100000

namespace CFSG.KS.Ru2250

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Sporadic.RuSchreier

variable {PL : Nat → Nat} {G0 G1 Z : Nat}

theorem nIf_eq' (c : Bool) (a b : Nat) :
    Bool.rec (motive := fun _ => Nat) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem bIf_eq' (c a b : Bool) :
    Bool.rec (motive := fun _ => Bool) b a c = if c = true then a else b := by
  cases c <;> rfl

theorem treePar_get {j : Nat} (h1 : 1 ≤ j) (h2 : j < 593775) : ruTreePar[j]! = ruTreeParent j := by
  rw [ruTreePar, getElem!_pos _ j (by simpa using h2), Array.getElem_ofFn]
  simp only [show j ≠ 0 by omega, ↓reduceIte]

theorem treeLab_get {j : Nat} (h1 : 1 ≤ j) (h2 : j < 593775) : ruTreeLab[j]! = ruTreeGen j := by
  rw [ruTreeLab, getElem!_pos _ j (by simpa using h2), Array.getElem_ofFn]
  simp only [show j ≠ 0 by omega, ↓reduceIte]

theorem tree_facts {j : Nat} (h1 : 1 ≤ j) (h2 : j < 593775) :
    ruTreePar[j]! < j ∧ ruTreeLab[j]! < 2 := by
  obtain ⟨-, -, h, -⟩ := Certificates.certificate2259
  rw [treePar_get h1 h2, treeLab_get h1 h2]
  exact h j h1 h2

theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h

theorem pathK_succ (f j : Nat) (hj : j ≠ 0) :
    pathK PL (f + 1) j = PL j % 2 + 2 * pathK PL f (PL j / 16) := by
  change Bool.rec (motive := fun _ => Nat) (strictN (PL j) (fun pl => Nat.add (Nat.land pl 1)
    (Nat.mul 2 (pathK PL f (Nat.shiftRight pl 4))))) 1 (Nat.beq j 0) = _
  rw [beq_false hj, PackFld.strictN_eqP]
  have h1 : Nat.land (PL j) 1 = PL j % 2 := Nat.and_one_is_mod (PL j)
  have h2 : Nat.shiftRight (PL j) 4 = PL j / 16 := Nat.shiftRight_eq_div_pow (PL j) 4
  have e : Nat.add (Nat.land (PL j) 1) (Nat.mul 2 (pathK PL f (Nat.shiftRight (PL j) 4))) =
      PL j % 2 + 2 * pathK PL f (PL j / 16) := by
    rw [h1, h2]
    rfl
  exact e

theorem reachK_succ {f j : Nat} (hj : j ≠ 0) :
    reachK PL (f + 1) j = reachK PL f (PL j / 16) := by
  change Bool.rec (motive := fun _ => Bool) (strictB (PL j) (fun pl => reachK PL f
    (Nat.shiftRight pl 4))) true (Nat.beq j 0) = _
  rw [beq_false hj, PackFld.strictB_eqP]
  have h2 : Nat.shiftRight (PL j) 4 = PL j / 16 := Nat.shiftRight_eq_div_pow (PL j) 4
  have e : reachK PL f (Nat.shiftRight (PL j) 4) = reachK PL f (PL j / 16) := by rw [h2]
  exact e

theorem fixZ_mem {y : Nat} : y ∈ ruFixZ ↔ y < 4060 ∧ ruZA[y]! = y := by
  rw [ruFixZ, fixedList, List.mem_filter, List.mem_range, beq_iff_eq]

theorem fixZ_pairwise : ruFixZ.Pairwise (· < ·) :=
  List.pairwise_lt_range.filter _

theorem pathK_zero_j (f : Nat) : pathK PL f 0 = 1 := by
  cases f <;> rfl

theorem pathK_pos : ∀ f j, 1 ≤ pathK PL f j
  | 0, _ => le_refl _
  | f + 1, j => by
    by_cases hj : j = 0
    · subst hj
      rw [pathK_zero_j]
    · rw [pathK_succ f j hj]
      have := pathK_pos f (PL j / 16)
      omega

theorem pwK_succ (f P : Nat) (hP : 2 ≤ P) :
    pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) (f + 1) P =
      pcomp 4060 12 (mask 12) (if P % 2 = 0 then G0 else G1)
        (pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) f (P / 2)) := by
  change Bool.rec (motive := fun _ => Nat) (strictN (pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) f
    (Nat.shiftRight P 1)) (fun T => pcomp 4060 12 (mask 12)
      (Bool.rec (motive := fun _ => Nat) G1 G0 (Nat.beq (Nat.land P 1) 0)) T)) (pidn 4060 12)
    (Nat.ble P 1) = _
  have e : Nat.ble P 1 = false := by
    cases e : Nat.ble P 1
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true e) (by omega)
  rw [e, PackFld.strictN_eqP, nIf_eq']
  have h1 : Nat.land P 1 = P % 2 := Nat.and_one_is_mod P
  have h2 : Nat.shiftRight P 1 = P / 2 := Nat.shiftRight_eq_div_pow P 1
  have e2 : pcomp 4060 12 (mask 12) (if Nat.beq (Nat.land P 1) 0 = true then G0 else G1)
      (pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) f (Nat.shiftRight P 1)) =
      pcomp 4060 12 (mask 12) (if P % 2 = 0 then G0 else G1)
        (pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) f (P / 2)) := by
    rw [h1, h2]
    simp only [Nat.beq_eq]
  exact e2

theorem pwK_one (n w m idn f : Nat) : pwK n w m G0 G1 idn f 1 = idn := by
  cases f <;> rfl

theorem pwK_zero (n w m idn P : Nat) : pwK n w m G0 G1 idn 0 P = idn := rfl

theorem ruTElt_succ {f j : Nat} (hj : j ≠ 0) :
    ruTElt (f + 1) j = ruTGen ruTreeLab[j]! * ruTElt f ruTreePar[j]! := by
  rw [ruTElt, ite_eq_right hj]

theorem ruTElt_root (f : Nat) : ruTElt f 0 = 1 := by
  cases f
  · rfl
  · rw [ruTElt, ite_eq_left rfl]

theorem imgSorted_mem {g : Array Nat} {l : List Nat} {p : Nat} :
    p ∈ imgSorted g l ↔ ∃ q ∈ l, g[q]! = p := by
  rw [imgSorted, List.mem_mergeSort, List.mem_map]

theorem imgSorted_lt {g : Array Nat} {l : List Nat} (hl : l.Pairwise (· < ·))
    (hg : ∀ p ∈ l, ∀ q ∈ l, g[p]! = g[q]! → p = q) : (imgSorted g l).Pairwise (· < ·) := by
  have hle := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (l.map fun p => g[p]!)
  have hnd : (List.mergeSort (l.map fun p => g[p]!) fun a b => decide (a ≤ b)).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.2 (List.Nodup.map_on hg hl.nodup)
  unfold imgSorted
  refine (hle.and hnd).imp fun {a b} h => ?_
  simp only [decide_eq_true_eq] at h
  omega

theorem gensA {k : Nat} (hk : k < 2) : ruTreeGens[k]! = ruTGenA k := by
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · simp [ruTreeGens, ruTGenA]
  · simp [ruTreeGens, ruTGenA]

section Tree

variable (hPL : ∀ j, 1 ≤ j → j < 593775 → ruTreePar[j]! = PL j / 16 ∧ ruTreeLab[j]! = PL j % 16)
  (hG0 : Orb.PRep 4060 12 G0 ruA0) (hG1 : Orb.PRep 4060 12 G1 ruA1)
include hPL hG0 hG1

theorem pw_prep :
    ∀ f j, j < 593775 → Orb.PRep 4060 12
      (pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) f (pathK PL f j)) (ruTElt f j) := by
  intro f
  induction f with
  | zero =>
    intro j _ x
    rw [pwK_zero, PF.pg_pidn (by norm_num) (by norm_num) x.2]
    rfl
  | succ f ih =>
    intro j hj x
    by_cases j0 : j = 0
    · subst j0
      rw [pathK_zero_j, pwK_one, PF.pg_pidn (by norm_num) (by norm_num) x.2, ruTElt_root]
      rfl
    · obtain ⟨hp, hl⟩ := hPL j (by omega) hj
      obtain ⟨hpj, hlj⟩ := tree_facts (j := j) (by omega) hj
      have hP := pathK_pos (PL := PL) f (PL j / 16)
      rw [pathK_succ f j j0, pwK_succ f _ (by omega)]
      have e1 : (PL j % 2 + 2 * pathK PL f (PL j / 16)) / 2 = pathK PL f (PL j / 16) := by omega
      have e2 : (PL j % 2 + 2 * pathK PL f (PL j / 16)) % 2 = ruTreeLab[j]! := by omega
      rw [e1, e2, PF.pg_pcomp (by norm_num) x.2, ← hp, ih (ruTreePar[j]!) (by omega) x,
        ruTElt_succ j0, Equiv.Perm.mul_apply]
      by_cases l0 : ruTreeLab[j]! = 0
      · rw [ite_eq_left l0, ruTGen, ite_eq_left l0]
        exact hG0 _
      · rw [ite_eq_right l0, ruTGen, ite_eq_right l0]
        exact hG1 _

omit hG0 hG1 in
theorem sets_spec :
    ∀ f j, j < 593775 → reachK PL f j = true →
      ruTreeSets[j]!.Pairwise (· < ·) ∧ ∀ y, y ∈ ruTreeSets[j]! ↔
        ∃ x : Fin 4060, (x : Nat) ∈ ruFixZ ∧ ((ruTElt f j x : Fin 4060) : Nat) = y := by
  obtain ⟨-, hs0, hsj⟩ := CFSG.KS.RuTree.ruTreeSets_spec
  have root : ∀ f, ruTreeSets[0]!.Pairwise (· < ·) ∧ ∀ y, y ∈ ruTreeSets[0]! ↔
      ∃ x : Fin 4060, (x : Nat) ∈ ruFixZ ∧ ((ruTElt f 0 x : Fin 4060) : Nat) = y := by
    intro f
    rw [hs0, ruTElt_root]
    refine ⟨fixZ_pairwise, fun y => ⟨fun hy => ⟨⟨y, (fixZ_mem.1 hy).1⟩, hy, rfl⟩, ?_⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact hx
  intro f
  induction f with
  | zero =>
    intro j _ hr
    have : j = 0 := Nat.eq_of_beq_eq_true hr
    subst this
    exact root 0
  | succ f ih =>
    intro j hj hr
    by_cases j0 : j = 0
    · subst j0
      exact root (f + 1)
    · obtain ⟨hp, hl⟩ := hPL j (by omega) hj
      obtain ⟨hpj, hlj⟩ := tree_facts (j := j) (by omega) hj
      rw [reachK_succ j0, ← hp] at hr
      obtain ⟨IP, IM⟩ := ih _ (by omega) hr
      have hgen : ∀ x : Fin 4060, (ruTreeGens[ruTreeLab[j]!]!)[(x : Nat)]! =
          ((ruTGen ruTreeLab[j]! x : Fin 4060) : Nat) := by
        intro x
        rw [gensA hlj]
        exact rep_ruTGen _ x
      have hlt : ∀ p ∈ ruTreeSets[ruTreePar[j]!]!, p < 4060 := by
        intro p hp'
        obtain ⟨x, -, rfl⟩ := (IM p).1 hp'
        exact (ruTElt f _ x).2
      rw [hsj j (by omega) hj hpj]
      refine ⟨imgSorted_lt IP fun p hp q hq e => ?_, fun y => ?_⟩
      · have e' := e
        rw [hgen ⟨p, hlt p hp⟩, hgen ⟨q, hlt q hq⟩] at e'
        exact congrArg Fin.val ((ruTGen ruTreeLab[j]!).injective (Fin.ext e'))
      · rw [imgSorted_mem]
        constructor
        · rintro ⟨p, hp', rfl⟩
          obtain ⟨x, hx, rfl⟩ := (IM p).1 hp'
          refine ⟨x, hx, ?_⟩
          rw [hgen (ruTElt f _ x), ruTElt_succ j0, Equiv.Perm.mul_apply]
        · rintro ⟨x, hx, rfl⟩
          refine ⟨_, (IM _).2 ⟨x, hx, rfl⟩, ?_⟩
          rw [hgen (ruTElt f _ x), ruTElt_succ j0, Equiv.Perm.mul_apply]

theorem zwK_sound
    (hZ : Orb.PRep 4060 12 Z ruZ) {t : Array Nat} {g : Equiv.Perm (Fin 4060)} {T0 T1 j : Nat}
    (ht : ∀ x < 4060, t[x]! = tv 12 (mask 12) T0 T1 x) (hg : Rep 4060 t g)
    (h : zwK 4060 12 (mask 12) 593775 PL G0 G1 Z T0 T1 j = true) : ruZWit t = true := by
  unfold zwK at h
  obtain ⟨hj, h⟩ := (bAnd_iff _ _).1 h
  obtain ⟨hr, h⟩ := (bAnd_iff _ _).1 h
  rw [PackFld.strictB_eqP] at h
  have hj' : j < 593775 := Nat.blt_eq.mp hj
  set G := pwK 4060 12 (mask 12) G0 G1 (pidn 4060 12) 64 (pathK PL 64 j)
  have hG := pw_prep hPL hG0 hG1 64 j hj'
  set T := ruTElt 64 j
  have hgT : g * T = T * ruZ := by
    refine Equiv.ext fun x => Fin.ext ?_
    have e := Nat.eq_of_beq_eq_true (allN_spec h x x.2)
    rw [hZ x, hG x, hG (ruZ x)] at e
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ← e, ← hg (T x), ht _ (T x).2]
  have hgz : ruTZ j = g := by
    change T * ruZ * T⁻¹ = g
    rw [← hgT, mul_inv_cancel_right]
  obtain ⟨SP, SM⟩ := sets_spec hPL 64 j hj' hr
  have hfix : fixedList 4060 t = ruTreeSets[j]! := by
    refine List.Pairwise.eq_of_mem_iff (List.pairwise_lt_range.filter _) SP fun y => ?_
    rw [SM, fixedList, List.mem_filter, List.mem_range, beq_iff_eq]
    constructor
    · rintro ⟨hy, hfy⟩
      refine ⟨T⁻¹ ⟨y, hy⟩, ?_, congrArg Fin.val (T.apply_symm_apply ⟨y, hy⟩)⟩
      rw [fixZ_mem]
      refine ⟨(T⁻¹ ⟨y, hy⟩).2, ?_⟩
      rw [rep_ruZ (T⁻¹ ⟨y, hy⟩)]
      have e1 : g ⟨y, hy⟩ = ⟨y, hy⟩ := Fin.ext (by rw [← hg ⟨y, hy⟩]; exact hfy)
      have e2 : ruZ (T⁻¹ ⟨y, hy⟩) = T⁻¹ (g ⟨y, hy⟩) := by
        rw [← hgz]
        simp [ruTZ, T]
      rw [e2, e1]
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(T x).2, ?_⟩
      have hz : ruZ x = x := Fin.ext (by rw [← rep_ruZ x]; exact (fixZ_mem.1 hx).2)
      rw [hg (T x)]
      have e : g (T x) = T x := by
        rw [← Equiv.Perm.mul_apply, hgT, Equiv.Perm.mul_apply, hz]
      rw [e]
  have hidx : ruZIdx t = j := by
    obtain ⟨-, hsz, -, -, hsort⟩ := Certificates.certificate2259
    rw [ruZIdx, hfix, CFSG.KS.RuTree.ruTreeIdx_get hsort hsz hj']
    rfl
  rw [ruZWit, hidx]
  exact (eqA_iff (rep_ruTZ j) hg).2 hgz

end Tree

end CFSG.KS.Ru2250

end
