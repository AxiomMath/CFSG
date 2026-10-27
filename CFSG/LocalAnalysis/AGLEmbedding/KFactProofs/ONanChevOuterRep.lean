module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterFrob

public section

namespace CFSG.AGLEmbedding.ChevOuter

open CFSG.Quasithin CFSG.AGLEmbedding.D4Two CFSG.RankThree.PartTwo.Sec4.Item434D42

@[expose] def frobArr (A : Array GF8) : Array GF8 := A.map frobF

@[expose] def frobPow : ℕ → Array GF8 → Array GF8
  | 0, A => A
  | n + 1, A => frobArr (frobPow n A)

abbrev Pr : Type := Array GF8 × ℕ

@[expose] def mulP (p q : Pr) : Pr := (mulArr p.1 (frobPow p.2 q.1), (p.2 + q.2) % 3)

@[expose] def oneP : Pr := (oneArr, 0)

@[expose] def powP (p : Pr) : ℕ → Pr
  | 0 => oneP
  | n + 1 => mulP p (powP p n)

@[expose] def symP (s : ℕ) : Pr := if s < 18 then (letterArr s, 0) else (oneArr, 1)

@[expose] def wordP (w : List ℕ) : Pr := w.foldr (fun s p => mulP (symP s) p) oneP

theorem getD_frobArr (A : Array GF8) (t : ℕ) : (frobArr A).getD t 0 = frobF (A.getD t 0) := by
  simp only [frobArr, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? <;> simp

theorem size_frobArr (A : Array GF8) : (frobArr A).size = A.size := by simp [frobArr]

theorem toMat_frobArr (A : Array GF8) : toMat (frobArr A) = (toMat A).map frobF := by
  ext i j
  simp only [toMat, Matrix.of_apply, Matrix.map_apply]
  exact getD_frobArr A _

theorem toMat_frobPow (n : ℕ) (A : Array GF8) :
    toMat (frobPow n A) = ((fun M : Matrix (Fin 8) (Fin 8) GF8 => M.map frobF)^[n]) (toMat A) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, toMat_frobArr, ih, Function.iterate_succ_apply']

theorem size_frobPow (n : ℕ) (A : Array GF8) : (frobPow n A).size = A.size := by
  induction n with
  | zero => rfl
  | succ n ih => rw [frobPow, size_frobArr, ih]

theorem coe_phiT_pow (n : ℕ) (g : lineGroup) :
    ((((phiT ^ n) g : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) =
      ((fun M : Matrix (Fin 8) (Fin 8) GF8 => M.map frobF)^[n])
        (((g : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    show ((((phiT ^ n) (phiT g) : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) = _
    rw [ih, Function.iterate_succ_apply]
    rw [coe_phiT, coe_frobGL]

theorem phiT_pow_mul_conj (n : ℕ) (h : lineGroup) :
    phiT ^ n * MulAut.conj h = MulAut.conj ((phiT ^ n) h) * phiT ^ n := by
  refine MulEquiv.ext fun x => ?_
  simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, mul_assoc]

@[expose] def Rep (p : Pr) (α : MulAut lineGroup) : Prop :=
  p.1.size = 64 ∧ p.2 < 3 ∧ ∃ g : lineGroup,
    toMat p.1 = (((g : lineGroup) : GL (Fin 8) GF8) : Matrix (Fin 8) (Fin 8) GF8) ∧
      α = MulAut.conj g * phiT ^ p.2

theorem rep_oneP : Rep oneP 1 :=
  ⟨size_oneArr, by decide, 1, by simp [oneP, oneArr, toMat_ofMat], by simp [oneP]⟩

theorem rep_mul {p q : Pr} {α β : MulAut lineGroup} (hp : Rep p α) (hq : Rep q β) :
    Rep (mulP p q) (α * β) := by
  obtain ⟨hps, hpj, g, hg, rfl⟩ := hp
  obtain ⟨hqs, hqj, h, hh, rfl⟩ := hq
  refine ⟨by simp [mulP, size_mulArr], by simp [mulP]; omega,
    g * (phiT ^ p.2) h, ?_, ?_⟩
  · simp only [mulP, toMat_mulArr, toMat_frobPow, hg, hh, Subgroup.coe_mul, Units.val_mul,
      coe_phiT_pow]
  · have h1 : MulAut.conj g * phiT ^ p.2 * (MulAut.conj h * phiT ^ q.2) =
        MulAut.conj (g * (phiT ^ p.2) h) * phiT ^ (p.2 + q.2) := by
      rw [map_mul, pow_add, ← mul_assoc, mul_assoc (MulAut.conj g), phiT_pow_mul_conj]
      group
    rw [h1]
    simp only [mulP]
    rw [pow_eq_pow_mod (p.2 + q.2) phiT_pow_three]

theorem rep_sym (s : ℕ) : Rep (symP s) (if s < 18 then MulAut.conj (letterX s) else phiT) := by
  by_cases hs : s < 18
  · simp only [symP, hs, ite_true]
    refine ⟨size_ofMat _, by simp, letterX s, ?_, by simp⟩
    simp [letterArr, toMat_ofMat, letterX, hs, letterGL]
  · simp only [symP, hs, ite_false]
    exact ⟨size_oneArr, by simp, 1, by simp [oneArr, toMat_ofMat], by simp⟩

@[expose] noncomputable def wordAut (w : List ℕ) : MulAut lineGroup :=
  (w.map fun s => if s < 18 then MulAut.conj (letterX s) else phiT).prod

theorem rep_wordP (w : List ℕ) : Rep (wordP w) (wordAut w) := by
  induction w with
  | nil => exact rep_oneP
  | cons s w ih =>
    simp only [wordP, List.foldr_cons, wordAut, List.map_cons, List.prod_cons]
    exact rep_mul (rep_sym s) ih

theorem rep_powP {p : Pr} {α : MulAut lineGroup} (hp : Rep p α) (n : ℕ) :
    Rep (powP p n) (α ^ n) := by
  induction n with
  | zero => exact rep_oneP
  | succ n ih =>
    rw [pow_succ']
    exact rep_mul hp ih

theorem rep_ext {p q : Pr} {α β : MulAut lineGroup} (hp : Rep p α) (hq : Rep q β) (h : p = q) :
    α = β := by
  subst h
  obtain ⟨-, -, g, hg, rfl⟩ := hp
  obtain ⟨-, -, g', hg', rfl⟩ := hq
  have : g = g' := Subtype.ext (Units.ext (hg.symm.trans hg'))
  rw [this]

theorem rep_one (hZ : Subgroup.center lineGroup = ⊥) {p : Pr} (hp : Rep p 1) : p = oneP := by
  obtain ⟨hs, hj, g, hg, h1⟩ := hp
  have hj' : p.2 = 0 := by
    by_contra hne
    have hc : phiT ^ p.2 = MulAut.conj g⁻¹ := by
      have : MulAut.conj g * phiT ^ p.2 = 1 := h1.symm
      rw [map_inv]
      exact (inv_eq_of_mul_eq_one_right this).symm
    interval_cases hv : p.2
    · exact hne rfl
    · exact phiT_ne_conj g⁻¹ (by simpa using hc)
    · apply phiT_ne_conj (g⁻¹ ^ 2)
      have h4 : phiT = phiT ^ 4 := by
        rw [show 4 = 1 + 3 by norm_num, pow_add, phiT_pow_three, mul_one, pow_one]
      rw [h4, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hc, ← map_pow]
  rw [hj'] at h1
  have hcg : MulAut.conj g = 1 := by simpa using h1.symm
  have hgz : g ∈ Subgroup.center lineGroup := by
    rw [Subgroup.mem_center_iff]
    intro z
    have := congrArg (fun α : MulAut lineGroup => α z) hcg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ, Subgroup.mem_bot] at hgz
  subst hgz
  have hm : toMat p.1 = toMat oneArr := by
    rw [hg]
    simp [oneArr, toMat_ofMat]
  exact Prod.ext (eq_of_toMat_eq hs size_oneArr hm) hj'

end CFSG.AGLEmbedding.ChevOuter
