module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.ComponentClassification.PSL3Four

open CFSG.PSL3Four CFSG.PSL3Four.Native

theorem TabRep.pow {n : ℕ} {t : Tab} {g : Equiv.Perm (Fin n)} (ht : TabRep t g) (k : ℕ) :
    TabRep (powTab n t k) (g ^ k) := by
  induction k with
  | zero => exact TabRep.idTab
  | succ k ih =>
    rw [pow_succ']
    exact ht.comp ih

theorem memTab_iff {T : Array Tab} {x : Tab} : memTab T x = true ↔ ∃ k < T.size, T[k]! = x := by
  simp [memTab, anyBelow_eq_true]

section Checks

variable {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))}

theorem centScanOK_spec {T D L : Array Tab} (hH : Enumerates H T.toList)
    (h : centScanOK n T D L = true) {g : Equiv.Perm (Fin n)} (hg : g ∈ H)
    (hcomm : ∀ i < D.size, ∃ a, TabRep D[i]! a ∧ a * g = g * a) : ∃ t ∈ L.toList, TabRep t g := by
  obtain ⟨k, hk, hrep⟩ := hH.exists_pos hg
  simp only [centScanOK, allBelow_eq_true] at h
  have hk' := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk'
  rcases hk' with hk' | hk'
  · have hall : allBelow D.size
        (fun a => Native.comp n D[a]! T[k]! == Native.comp n T[k]! D[a]!) = true := by
      rw [allBelow_eq_true]
      intro i hi
      obtain ⟨a, ha, hga⟩ := hcomm i hi
      exact ((ha.comp hrep).beq_iff (hrep.comp ha)).2 hga
    rw [hall] at hk'
    exact Bool.noConfusion hk'
  · obtain ⟨j, hj, hjk⟩ := memTab_iff.1 hk'
    exact ⟨L[j]!, getElem!_mem hj, hjk ▸ hrep⟩

theorem expOK_spec {T : Array Tab} (hH : Enumerates H T.toList) (h : expOK n T = true)
    {g : Equiv.Perm (Fin n)} (hg : g ∈ H) (h27 : g ^ 27 = 1) : g ^ 3 = 1 := by
  obtain ⟨k, hk, hrep⟩ := hH.exists_pos hg
  simp only [expOK, allBelow_eq_true] at h
  have hk' := h k hk
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at hk'
  rcases hk' with hk' | hk'
  · have : (powTab n T[k]! 27 == idTab n) = true := ((hrep.pow 27).beq_iff TabRep.idTab).2 h27
    rw [this] at hk'
    exact Bool.noConfusion hk'
  · exact ((hrep.pow 3).beq_iff TabRep.idTab).1 hk'

theorem witness_spec {p : ℕ} {D Di : Array Tab} {K : Subgroup (Equiv.Perm (Fin n))}
    (hD : Enumerates K D.toList) (hinv : invsOK n D Di = true) {y : Equiv.Perm (Fin n)} {yT : Tab}
    (hy : TabRep yT y) (h : witness n p D Di yT = true) :
    (∃ d ∈ K, (y * (d * y * d⁻¹)) ^ p ≠ 1) ∨
      (∃ d ∈ K, ∃ d' ∈ K, (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ p ≠ 1) := by
  simp only [witness, Bool.or_eq_true, anyBelow_eq_true, Bool.not_eq_true'] at h
  rcases h with ⟨a, ha, h⟩ | ⟨a, ha, b, hb, h⟩
  · left
    obtain ⟨d, hdK, hd⟩ := hD.exists_elt ha
    have hdi := invsOK_spec hinv ha hd
    have hc := (hy.comp (hd.conjTab hy hdi)).pow p
    refine ⟨d, hdK, fun h1 => ?_⟩
    have := (hc.beq_iff TabRep.idTab).2 h1
    rw [this] at h
    exact Bool.noConfusion h
  · right
    obtain ⟨d, hdK, hd⟩ := hD.exists_elt ha
    obtain ⟨d', hdK', hd'⟩ := hD.exists_elt hb
    have hdi := invsOK_spec hinv ha hd
    have hdi' := invsOK_spec hinv hb hd'
    have hc := (((hy.comp (hd.conjTab hy hdi)).comp (hd'.conjTab hy hdi'))).pow p
    refine ⟨d, hdK, d', hdK', fun h1 => ?_⟩
    have := (hc.beq_iff TabRep.idTab).2 h1
    rw [this] at h
    exact Bool.noConfusion h

theorem witOK_spec {p : ℕ} {T D Di exc : Array Tab} {K : Subgroup (Equiv.Perm (Fin n))}
    (hH : Enumerates H T.toList) (hD : Enumerates K D.toList) (hinv : invsOK n D Di = true)
    {rT : Tab} {r : Equiv.Perm (Fin n)} (hr : TabRep rT r)
    (h : witOK n p T D Di exc rT = true) (Exc : Equiv.Perm (Fin n) → Prop)
    (hexc : ∀ (y : Equiv.Perm (Fin n)) (t : Tab), TabRep t y → t ∈ exc.toList → Exc y)
    {y : Equiv.Perm (Fin n)} (hy : y ∈ H) (hy1 : y ≠ 1) (hyp : y ^ p = 1) (hry : r * y * r * y = 1) :
    Exc y ∨ (∃ d ∈ K, (y * (d * y * d⁻¹)) ^ p ≠ 1) ∨
      (∃ d ∈ K, ∃ d' ∈ K, (y * (d * y * d⁻¹) * (d' * y * d'⁻¹)) ^ p ≠ 1) := by
  obtain ⟨k, hk, hrep⟩ := hH.exists_pos hy
  simp only [witOK, allBelow_eq_true] at h
  have hk' := h k hk
  have hA0 : (T[k]! == idTab n) = false := by
    rw [← Bool.not_eq_true]
    exact fun hc => hy1 ((hrep.beq_iff TabRep.idTab).1 hc)
  have hB : (comp n (comp n (comp n rT T[k]!) rT) T[k]! == idTab n) = true :=
    ((((hr.comp hrep).comp hr).comp hrep).beq_iff TabRep.idTab).2 hry
  have hC : (powTab n T[k]! p == idTab n) = true := ((hrep.pow p).beq_iff TabRep.idTab).2 hyp
  have hAll : (!(T[k]! == idTab n) && comp n (comp n (comp n rT T[k]!) rT) T[k]! == idTab n &&
      powTab n T[k]! p == idTab n) = true := by
    rw [hA0, hB, hC]
    rfl
  rw [hAll] at hk'
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true] at hk'
  rcases hk' with hk' | hk'
  · obtain ⟨j, hj, hjk⟩ := memTab_iff.1 hk'
    exact Or.inl (hexc y exc[j]! (hjk ▸ hrep) (getElem!_mem hj))
  · rcases witness_spec hD hinv hrep hk' with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr h1)

end Checks

end CFSG.ComponentClassification.PSL3Four
