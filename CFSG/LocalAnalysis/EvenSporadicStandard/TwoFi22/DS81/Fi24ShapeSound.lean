module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24ShapeCheck
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81

open CFSG.Sporadic.FischerOddCore CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.ComponentClassification.RankTwoSporadic.Fi24Prime
open CFSG.Sporadic.Th (wordG)
open CFSG.Sporadic.Bridge (wordProd)
open CFSG.Sporadic.Bridge.TwoGen (img2)

@[expose] noncomputable def fi24PLetterG (z : ℤ) :
    Equiv.Perm (Fin 378) :=
  if z = 1 then fi24Pa else if z = -1 then fi24Pa⁻¹ else if z = 2 then fi24Pb else fi24Pb⁻¹

theorem rep_fi24PLetterA (z : ℤ) :
    Rep 378 (fi24PLetterA z) (fi24PLetterG z) := by
  unfold fi24PLetterA fi24PLetterG
  split_ifs
  · exact rep_fi24Pa
  · exact rep_inv_of_isInvA rep_fi24Pa (fi24P_isInvA (by norm_num))
  · exact rep_fi24Pb
  · exact rep_inv_of_isInvA rep_fi24Pb (fi24P_isInvA (by norm_num))

theorem fi24PWordA_nil : fi24PWordA [] = idA 378 := by
  rw [fi24PWordA, List.foldr_nil]

theorem fi24PWordA_cons (z : ℤ) (w : List ℤ) :
    fi24PWordA (z :: w) = compA 378 (fi24PLetterA z) (fi24PWordA w) := by
  rw [fi24PWordA, fi24PWordA, List.foldr_cons]

theorem rep_fi24PWordA (w : List ℤ) :
    Rep 378 (fi24PWordA w) (wordG fi24PLetterG w) := by
  induction w with
  | nil =>
    rw [wordG_nil, fi24PWordA_nil]
    exact rep_idA
  | cons z w ih =>
    rw [wordG_cons, fi24PWordA_cons]
    exact rep_compA (rep_fi24PLetterA z) ih

theorem fi24RelA_nil (X Xi Y Yi : Array ℕ) : fi24RelA X Xi Y Yi [] = idA 378 := by
  rw [fi24RelA, List.foldr_nil]

theorem fi24RelA_cons (X Xi Y Yi : Array ℕ) (l : Fin 2 × Bool) (v : List (Fin 2 × Bool)) :
    fi24RelA X Xi Y Yi (l :: v) = compA 378 (if l.1.val = 0 then (if l.2 then X else Xi)
      else (if l.2 then Y else Yi)) (fi24RelA X Xi Y Yi v) := by
  rw [fi24RelA, fi24RelA, List.foldr_cons]

theorem rep_fi24RelA {x y : Equiv.Perm (Fin 378)} {X Xi Y Yi : Array ℕ} (hx : Rep 378 X x)
    (hxi : Rep 378 Xi x⁻¹) (hy : Rep 378 Y y) (hyi : Rep 378 Yi y⁻¹)
    (v : List (Fin 2 × Bool)) :
    Rep 378 (fi24RelA X Xi Y Yi v) (wordProd (img2 x y) (v.map fun l => (l.1.val, l.2))) := by
  induction v with
  | nil =>
    rw [fi24RelA_nil, List.map_nil]
    have : wordProd (img2 x y) [] = 1 := by simp [wordProd]
    rw [this]
    exact rep_idA
  | cons l v ih =>
    have e : wordProd (img2 x y) ((l :: v).map fun l => (l.1.val, l.2)) =
        (if l.2 then img2 x y l.1.val else (img2 x y l.1.val)⁻¹) *
          wordProd (img2 x y) (v.map fun l => (l.1.val, l.2)) := by
      simp only [wordProd, List.map_cons, List.prod_cons]
    rw [e, fi24RelA_cons]
    refine rep_compA ?_ ih
    obtain ⟨i, s⟩ := l
    fin_cases i <;> cases s <;> simp [img2] <;> assumption

@[expose] noncomputable def fi24Zeta : Equiv.Perm (Fin 378) :=
  wordG fi24PLetterG fi24ShapeZ

@[expose] noncomputable def fi24PX : Equiv.Perm (Fin 378) :=
  wordG fi24PLetterG fi24ShapeX

@[expose] noncomputable def fi24PY : Equiv.Perm (Fin 378) :=
  wordG fi24PLetterG fi24ShapeY

structure Fi24ShapeFacts : Prop where
  z_mem : wordG fi24KLetterG fi24ShapeZ ∈ fi24Kd
  x_mem : wordG fi24KLetterG fi24ShapeX ∈ fi24Kd
  y_mem : wordG fi24KLetterG fi24ShapeY ∈ fi24Kd
  zeta_cube : fi24Zeta * (fi24Zeta * fi24Zeta) = 1
  zeta_ne : fi24Zeta ≠ 1
  gens_comm : ∀ k < 5, wordG fi24PLetterG fi24KdGenWords[k]! * fi24Zeta =
    fi24Zeta * wordG fi24PLetterG fi24KdGenWords[k]!
  b_conj : fi24Pb * fi24Zeta = (fi24Zeta * fi24Zeta) * fi24Pb
  rels : ∀ v ∈ CFSG.LieType.Multipliers.U43.rels,
    wordProd (img2 fi24PX fi24PY) (v.map fun l => (l.1.val, l.2)) = 1 ∨
    wordProd (img2 fi24PX fi24PY) (v.map fun l => (l.1.val, l.2)) = fi24Zeta ∨
    wordProd (img2 fi24PX fi24PY) (v.map fun l => (l.1.val, l.2)) = fi24Zeta * fi24Zeta
  x_not : fi24PX ≠ 1 ∧ fi24PX ≠ fi24Zeta ∧ fi24PX ≠ fi24Zeta * fi24Zeta

theorem mem_fi24Kd_of_fi24SiftW (hc : fi24KdChainsOK = true)
    {w : List ℤ} (h : fi24SiftW w = true) : wordG fi24KLetterG w ∈ fi24Kd :=
  mem_fi24Kd_of_siftA hc (rep_fi24KWordA w) h

theorem fi24ShapeCheck_facts (hc : fi24KdChainsOK = true)
    (h : fi24ShapeCheck = true) : Fi24ShapeFacts := by
  simp only [fi24ShapeCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hz, hx⟩, hy⟩, hP⟩ := h
  simp only [fi24ShapeP, Bool.and_eq_true, Bool.not_eq_true'] at hP
  obtain ⟨⟨⟨⟨⟨⟨⟨hXi, hYi⟩, hZ3⟩, hZne⟩, hgens⟩, hB⟩, hrels⟩, hXn⟩ := hP
  have hZr : Rep 378 (fi24PWordA fi24ShapeZ) fi24Zeta := rep_fi24PWordA _
  have hXr : Rep 378 (fi24PWordA fi24ShapeX) fi24PX := rep_fi24PWordA _
  have hYr : Rep 378 (fi24PWordA fi24ShapeY) fi24PY := rep_fi24PWordA _
  have hXir := rep_inv_of_isInvA hXr hXi
  have hYir := rep_inv_of_isInvA hYr hYi
  refine ⟨mem_fi24Kd_of_fi24SiftW hc hz, mem_fi24Kd_of_fi24SiftW hc hx,
    mem_fi24Kd_of_fi24SiftW hc hy, eq_of_eqA (rep_compA hZr (rep_compA hZr hZr)) rep_idA hZ3,
    fun h1 => ?_, fun k hk => ?_, eq_of_eqA (rep_compA rep_fi24Pb hZr)
      (rep_compA (rep_compA hZr hZr) rep_fi24Pb) hB, fun v hv => ?_, ?_⟩
  · rw [(eqA_iff hZr rep_idA).2 h1] at hZne
    exact Bool.noConfusion hZne
  · have hk' : k < fi24KdGenWords.length := by simpa [fi24KdGenWords] using hk
    have hmem : fi24KdGenWords[k]! ∈ fi24KdGenWords := by
      rw [getElem!_pos fi24KdGenWords k hk']
      exact List.getElem_mem hk'
    exact eq_of_eqA (rep_compA (rep_fi24PWordA _) hZr) (rep_compA hZr (rep_fi24PWordA _))
      (List.all_eq_true.1 hgens _ hmem)
  · have h1 := List.all_eq_true.1 hrels v hv
    have hR := rep_fi24RelA hXr hXir hYr hYir v
    simp only [Bool.or_eq_true] at h1
    rcases h1 with (h1 | h1) | h1
    · exact Or.inl (eq_of_eqA hR rep_idA h1)
    · exact Or.inr (Or.inl (eq_of_eqA hR hZr h1))
    · exact Or.inr (Or.inr (eq_of_eqA hR (rep_compA hZr hZr) h1))
  · simp only [Bool.or_eq_false_iff] at hXn
    obtain ⟨⟨h1, h2⟩, h3⟩ := hXn
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [(eqA_iff hXr rep_idA).2 h] at h1
      exact Bool.noConfusion h1
    · rw [(eqA_iff hXr hZr).2 h] at h2
      exact Bool.noConfusion h2
    · rw [(eqA_iff hXr (rep_compA hZr hZr)).2 h] at h3
      exact Bool.noConfusion h3

end CFSG.EvenSporadicStandard.TwoFi22.DS81
