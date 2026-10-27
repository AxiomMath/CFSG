module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelAutXPermCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.ModelUniqueFCSpec
public import CFSG.Monster.B.Co2.PermArr
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

@[expose] def axSigma (g : ℕ → Equiv.Perm (Fin 3510)) (l : ℕ × Bool) : Equiv.Perm (Fin 3510) :=
  if l.2 then (g l.1)⁻¹ else g l.1

@[expose] def axB (g : ℕ → Equiv.Perm (Fin 3510)) (words : Array (List (ℕ × Bool))) (i : ℕ) :
    Equiv.Perm (Fin 3510) :=
  ((words[i]!).map (axSigma g)).prod

structure PermFacts (g : ℕ → Equiv.Perm (Fin 3510)) (words : Array (List (ℕ × Bool)))
    (gc : Array (Array ℕ)) : Prop where
  letters : ∀ i < 10, ∀ l ∈ words[i]!, l.1 < 9
  b_sq : ∀ i < 10, axB g words i * axB g words i = 1
  b_comm : ∀ i < 10, ∀ j < 10, axB g words i * axB g words j = axB g words j * axB g words i
  act : ∀ k < 10, ∀ i < 10, g k * axB g words i * (g k)⁻¹ = phi (axB g words) (gc[k]!)[i]!
  phi_inj : ∀ v < 1024, ∀ v' < 1024, phi (axB g words) v = phi (axB g words) v' → v = v'

theorem getElem!_map_range {α : Type} [Inhabited α] (f : ℕ → α) {n m : ℕ} (hm : m < n) :
    ((Array.range n).map f)[m]! = f m := by
  have hm' : m < (Array.range n).size := by simpa using hm
  rw [fcGetElem!_map _ _ hm', getElem!_pos (Array.range n) m hm', Array.getElem_range]

theorem rep_axLetterTab {G Ginv : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin 3510)}
    (hG : ∀ k < 10, Rep 3510 G[k]! (g k)) (hGi : ∀ k < 10, Rep 3510 Ginv[k]! (g k)⁻¹)
    {l : ℕ × Bool} (hl : l.1 < 10) : Rep 3510 (axLetterTab G Ginv l) (axSigma g l) := by
  obtain ⟨k, b⟩ := l
  cases b
  · exact hG k hl
  · exact hGi k hl

theorem rep_axWordTab {G Ginv : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin 3510)}
    (hG : ∀ k < 10, Rep 3510 G[k]! (g k)) (hGi : ∀ k < 10, Rep 3510 Ginv[k]! (g k)⁻¹) :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 10) →
      Rep 3510 (axWordTab G Ginv w) ((w.map (axSigma g)).prod)
  | [], _ => by
    simpa [axWordTab] using (rep_idA (n := 3510))
  | l :: w, hw => by
    have h1 := rep_axLetterTab hG hGi (hw l List.mem_cons_self)
    have h2 := rep_axWordTab hG hGi w fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    simpa [axWordTab] using rep_compA h1 h2

theorem rep_axPhiTab {B : Array (Array ℕ)} {b : ℕ → Equiv.Perm (Fin 3510)}
    (hB : ∀ i < 10, Rep 3510 B[i]! (b i)) (m : ℕ) :
    ∀ l : List ℕ, (∀ i ∈ l, i < 10) →
      Rep 3510 (l.foldr (fun i P => if m.testBit i then compA 3510 B[i]! P else P) (idA 3510))
        (phiL b m l)
  | [], _ => by
    simpa [phiL] using (rep_idA (n := 3510))
  | i :: l, hl => by
    have ih := rep_axPhiTab hB m l fun j hj => hl j (List.mem_cons_of_mem _ hj)
    have hi := hl i List.mem_cons_self
    rw [List.foldr_cons, phiL_cons]
    split_ifs
    · exact rep_compA (hB i hi) ih
    · exact ih

theorem axPermCheckT_sound {G Ginv : Array (Array ℕ)} {words : Array (List (ℕ × Bool))}
    {gc : Array (Array ℕ)} {g : ℕ → Equiv.Perm (Fin 3510)}
    (hG : ∀ k < 10, Rep 3510 G[k]! (g k)) (h : axPermCheckT G Ginv words gc = true) :
    PermFacts g words gc := by
  simp only [axPermCheckT, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range, and_assoc] at h
  obtain ⟨-, -, hw10, hinv, hlet, hsq, hcomm, hact, hdist⟩ := h
  have hGi : ∀ k < 10, Rep 3510 Ginv[k]! (g k)⁻¹ := fun k hk =>
    rep_inv_of_isInvA (hG k hk) (hinv k hk)
  have hLet : ∀ i < 10, ∀ l ∈ words[i]!, l.1 < 9 := by
    intro i hi l hl
    have hi' : i < words.size := by omega
    rw [getElem!_pos words i hi'] at hl
    simpa using List.all_eq_true.1 (Array.all_eq_true.1 hlet i hi') l hl
  have hB : ∀ i < 10,
      Rep 3510 (words.map (axWordTab G Ginv))[i]! (axB g words i) := by
    intro i hi
    have hi' : i < words.size := by omega
    rw [fcGetElem!_map _ _ hi']
    exact rep_axWordTab hG hGi _ fun l hl => by have := hLet i hi l hl; omega
  have hP : ∀ m, Rep 3510 (axPhiTab (words.map (axWordTab G Ginv)) m) (phi (axB g words) m) :=
    fun m => rep_axPhiTab hB m (List.range 10) fun i hi => List.mem_range.1 hi
  refine ⟨hLet, fun i hi => ?_, fun i hi j hj => ?_, fun k hk i hi => ?_, ?_⟩
  · exact eq_of_eqA (rep_compA (hB i hi) (hB i hi)) rep_idA (hsq i hi)
  · exact eq_of_eqA (rep_compA (hB i hi) (hB j hj)) (rep_compA (hB j hj) (hB i hi))
      (hcomm i hi j hj)
  · have h1 := eq_of_eqA (rep_compA (hG k hk) (hB i hi))
      (rep_compA (hP (gc[k]!)[i]!) (hG k hk)) (hact k hk i hi)
    exact mul_inv_eq_iff_eq_mul.2 h1
  · intro v hv v' hv' hvv
    have himg : ∀ m < 1024, ((Array.range 1024).map fun m => (axPhiTab (words.map
        (axWordTab G Ginv)) m)[0]!)[m]! = (axPhiTab (words.map (axWordTab G Ginv)) m)[0]! :=
      fun m hm => getElem!_map_range _ hm
    have h0 : ∀ m, (axPhiTab (words.map (axWordTab G Ginv)) m)[0]! =
        ((phi (axB g words) m) ⟨0, by norm_num⟩ : ℕ) := fun m => (hP m).apply (by norm_num)
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · have := hdist v' hv' v hlt
      rw [himg v' hv', himg v hv, h0, h0, hvv] at this
      simp at this
    · have := hdist v hv v' hgt
      rw [himg v hv, himg v' hv', h0, h0, hvv] at this
      simp at this

end CFSG.EvenSporadicStandard.TwoFi22.DS81
