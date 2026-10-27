module
public import CFSG.FeitThompson.Local.PrimePowerResidueRingUnits
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.RingTheory.LocalRing.Module

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Module LinearMap Matrix

section DiagProj

def diagProj (R : Type*) [Zero R] [One R] (d r : ℕ) : Matrix (Fin d) (Fin d) R :=
  Matrix.diagonal fun i => if (i : ℕ) < r then 1 else 0

variable {R : Type*} {d r : ℕ}

theorem diagProj_eq_diagonal [Zero R] [One R] :
    diagProj R d r = Matrix.diagonal (fun i : Fin d => if (i : ℕ) < r then (1 : R) else 0) := (rfl)

theorem diagProj_apply [Zero R] [One R] (i j : Fin d) :
    diagProj R d r i j = if i = j then (if (i : ℕ) < r then (1 : R) else 0) else 0 := by
  rw [diagProj_eq_diagonal, Matrix.diagonal_apply]

theorem diagProj_self [Zero R] [One R] : diagProj R d d = 1 := by
  rw [diagProj_eq_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  simp [i.2]

theorem diagProj_zero [Zero R] [One R] : diagProj R d 0 = 0 := by
  rw [diagProj_eq_diagonal, ← Matrix.diagonal_zero]
  congr 1

theorem isIdempotentElem_diagProj [NonAssocSemiring R] : IsIdempotentElem (diagProj R d r) := by
  change diagProj R d r * diagProj R d r = diagProj R d r
  rw [diagProj_eq_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split <;> simp

private theorem card_filter_lt (h : r ≤ d) :
    (Finset.univ.filter fun i : Fin d => (i : ℕ) < r).card = r := by
  have hmap : (Finset.univ.filter fun i : Fin d => (i : ℕ) < r)
      = Finset.map (Fin.castLEEmb h) Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    exact ⟨fun hi => ⟨⟨i, hi⟩, by ext; rfl⟩, by rintro ⟨a, rfl⟩; exact a.2⟩
  rw [hmap, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem trace_diagProj [AddCommMonoidWithOne R] (h : r ≤ d) :
    (diagProj R d r).trace = (r : R) := by
  rw [diagProj_eq_diagonal, Matrix.trace_diagonal, Finset.sum_ite, Finset.sum_const,
    Finset.sum_const_zero, add_zero, nsmul_one, card_filter_lt h]

theorem map_diagProj {S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] (f : R →+* S) :
    (diagProj R d r).map f = diagProj S d r := by
  rw [diagProj_eq_diagonal, diagProj_eq_diagonal, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  split <;> simp

theorem rank_diagProj {K : Type*} [Field K] (h : r ≤ d) : (diagProj K d r).rank = r := by
  classical
  have heq : (Finset.univ.filter fun x : Fin d => (if (x : ℕ) < r then (1 : K) else 0) ≠ 0)
      = (Finset.univ.filter fun i : Fin d => (i : ℕ) < r) := by ext i; simp
  rw [diagProj_eq_diagonal, Matrix.rank_diagonal, Fintype.card_subtype, heq, card_filter_lt h]

end DiagProj

section LocalRing

variable {R : Type*} [CommRing R] {d : ℕ}

private theorem rank_conj (V W D : Matrix (Fin d) (Fin d) R) (h1 : V * W = 1) (h2 : W * V = 1) :
    (V * D * W).rank = D.rank := by
  have hV : IsUnit V.det :=
    IsUnit.of_mul_eq_one (b := W.det) (by rw [← Matrix.det_mul, h1, Matrix.det_one])
  have hW : IsUnit W.det :=
    IsUnit.of_mul_eq_one (b := V.det) (by rw [← Matrix.det_mul, h2, Matrix.det_one])
  rw [Matrix.rank_mul_eq_left_of_isUnit_det W _ hW, Matrix.rank_mul_eq_right_of_isUnit_det V _ hV]

variable [IsLocalRing R]

theorem exists_conj_diagProj_of_isIdempotentElem
    {T : Matrix (Fin d) (Fin d) R} (hT : IsIdempotentElem T) :
    ∃ U : GL (Fin d) R, T = (U : Matrix (Fin d) (Fin d) R) * diagProj R d T.rank *
      (↑U⁻¹ : Matrix (Fin d) (Fin d) R) := by
  have hf : IsIdempotentElem T.mulVecLin := by
    change T.mulVecLin * T.mulVecLin = T.mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hT.eq]
  set f := T.mulVecLin with hfdef
  have hc : IsCompl (LinearMap.range f) (LinearMap.ker f) := hf.isCompl
  have hKfin : Module.Finite R (LinearMap.ker f) := by
    rw [hf.ker_eq_range_one_sub]; infer_instance
  have hprodproj : Module.Projective R (↥(LinearMap.range f) × ↥(LinearMap.ker f)) :=
    Module.Projective.of_equiv (Submodule.prodEquivOfIsCompl _ _ hc).symm
  have hPproj : Module.Projective R (↥(LinearMap.range f)) :=
    Module.Projective.of_split (M := ↥(LinearMap.range f) × ↥(LinearMap.ker f))
      (LinearMap.inl R _ _) (LinearMap.fst R _ _) (by ext x; simp)
  have hKproj : Module.Projective R (↥(LinearMap.ker f)) :=
    Module.Projective.of_split (M := ↥(LinearMap.range f) × ↥(LinearMap.ker f))
      (LinearMap.inr R _ _) (LinearMap.snd R _ _) (by ext x; simp)
  have hPfree : Module.Free R (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  have hKfree : Module.Free R (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set m := finrank R (LinearMap.range f) with hm
  set k := finrank R (LinearMap.ker f) with hk
  have hrankT : T.rank = m := rfl
  have hadd : m + k = d := by
    rw [hm, hk, ← Module.finrank_prod, (Submodule.prodEquivOfIsCompl _ _ hc).finrank_eq,
      Module.finrank_fin_fun]
  set bP := Module.finBasis R (LinearMap.range f) with hbP
  set bK := Module.finBasis R (LinearMap.ker f) with hbK
  set ε : Fin m ⊕ Fin k ≃ Fin d := finSumFinEquiv.trans (finCongr hadd) with hε
  set b : Basis (Fin d) R (Fin d → R) :=
    ((bP.prod bK).map (Submodule.prodEquivOfIsCompl _ _ hc)).reindex ε with hb
  have hbleft : ∀ a : Fin m, b (ε (Sum.inl a)) = (bP a : Fin d → R) := by
    intro a
    rw [hb, Basis.reindex_apply, Equiv.symm_apply_apply]
    simp [Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  have hbright : ∀ c : Fin k, b (ε (Sum.inr c)) = (bK c : Fin d → R) := by
    intro c
    rw [hb, Basis.reindex_apply, Equiv.symm_apply_apply]
    simp [Basis.map_apply, Submodule.coe_prodEquivOfIsCompl']
  have hεleft : ∀ a : Fin m, ((ε (Sum.inl a) : Fin d) : ℕ) = (a : ℕ) := by intro a; simp [hε]
  have hεright : ∀ c : Fin k, ((ε (Sum.inr c) : Fin d) : ℕ) = m + (c : ℕ) := by intro c; simp [hε]
  have key : LinearMap.toMatrix b b f = diagProj R d m := by
    ext i j
    rw [LinearMap.toMatrix_apply, diagProj_apply]
    obtain ⟨x, rfl⟩ : ∃ x, ε x = j := ⟨ε.symm j, ε.apply_symm_apply j⟩
    cases x with
    | inl a =>
      have hfb : f (b (ε (Sum.inl a))) = b (ε (Sum.inl a)) := by
        rw [hbleft]; exact (hf.isProj_range f).map_id _ (bP a).2
      rw [hfb, Basis.repr_self_apply]
      by_cases h : i = ε (Sum.inl a)
      · subst h; rw [if_pos rfl, if_pos rfl, hεleft a, if_pos a.2]
      · rw [if_neg (Ne.symm h), if_neg h]
    | inr c =>
      have hfb : f (b (ε (Sum.inr c))) = 0 := by rw [hbright]; exact (bK c).2
      rw [hfb, map_zero]
      by_cases h : i = ε (Sum.inr c)
      · subst h
        rw [if_pos rfl, Finsupp.coe_zero, Pi.zero_apply, if_neg]
        rw [hεright]; omega
      · rw [if_neg h, Finsupp.coe_zero, Pi.zero_apply]
  set E : Basis (Fin d) R (Fin d → R) := Pi.basisFun R (Fin d) with hE
  have hTmat : LinearMap.toMatrix E E f = T := by
    rw [hE, LinearMap.toMatrix_eq_toMatrix']
    exact (LinearEquiv.eq_symm_apply LinearMap.toMatrix').mp rfl
  refine ⟨⟨E.toMatrix ⇑b, b.toMatrix ⇑E, E.toMatrix_mul_toMatrix_flip b,
    b.toMatrix_mul_toMatrix_flip E⟩, ?_⟩
  have hchange := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix E b E b f
  rw [key, hTmat] at hchange
  rw [hrankT]
  exact hchange.symm

theorem trace_eq_rank_of_isIdempotentElem
    {T : Matrix (Fin d) (Fin d) R} (hT : IsIdempotentElem T) : T.trace = (T.rank : R) := by
  obtain ⟨U, hU⟩ := exists_conj_diagProj_of_isIdempotentElem hT
  conv_lhs => rw [hU]
  rw [Matrix.trace_units_conj U, trace_diagProj (Matrix.rank_le_width T)]

end LocalRing

section ResidueRing

variable {p e d : ℕ}

theorem isLocalRing_zmod_pow (hp : p.Prime) (he : e ≠ 0) : IsLocalRing (ZMod (p ^ e)) := by
  have : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow he hp.one_lt⟩
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [mem_nonunits_iff, isUnit_iff_castHom_ne_zero hp he] at ha hb ⊢
  simp only [not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

theorem rank_mapMatrix_eq_rank_of_isIdempotentElem (hp : p.Prime) (he : e ≠ 0)
    {T : Matrix (Fin d) (Fin d) (ZMod (p ^ e))} (hT : IsIdempotentElem T) :
    ((ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix T).rank = T.rank := by
  have := Fact.mk hp
  have := isLocalRing_zmod_pow hp he
  set φ : Matrix (Fin d) (Fin d) (ZMod (p ^ e)) →+* Matrix (Fin d) (Fin d) (ZMod p) :=
    (ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix with hφ
  obtain ⟨U, hU⟩ := exists_conj_diagProj_of_isIdempotentElem hT
  have hUU : (U : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) *
      (↑U⁻¹ : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) = 1 := by simp
  have hUU' : (↑U⁻¹ : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) *
      (U : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) = 1 := by simp
  have hdp : φ (diagProj (ZMod (p ^ e)) d T.rank) = diagProj (ZMod p) d T.rank := by
    rw [hφ, RingHom.mapMatrix_apply, map_diagProj]
  have hmap : φ T = φ (U : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) * diagProj (ZMod p) d T.rank *
      φ (↑U⁻¹ : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) := by
    conv_lhs => rw [hU]
    rw [map_mul, map_mul, hdp]
  rw [hmap, rank_conj _ _ _ (by rw [← map_mul, hUU, map_one]) (by rw [← map_mul, hUU', map_one]),
    rank_diagProj (Matrix.rank_le_width T)]

theorem exists_conj_diagProj_zmod_of_isIdempotentElem (hp : p.Prime) (he : e ≠ 0)
    {T : Matrix (Fin d) (Fin d) (ZMod (p ^ e))} (hT : IsIdempotentElem T)
    {r : ℕ} (hr : r = ((ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix T).rank) :
    ∃ U : GL (Fin d) (ZMod (p ^ e)), T = (U : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) *
      diagProj (ZMod (p ^ e)) d r * (↑U⁻¹ : Matrix (Fin d) (Fin d) (ZMod (p ^ e))) := by
  have := isLocalRing_zmod_pow hp he
  rw [hr, rank_mapMatrix_eq_rank_of_isIdempotentElem hp he hT]
  exact exists_conj_diagProj_of_isIdempotentElem hT

theorem trace_eq_rank_map_of_isIdempotentElem_zmod (hp : p.Prime) (he : e ≠ 0)
    {T : Matrix (Fin d) (Fin d) (ZMod (p ^ e))} (hT : IsIdempotentElem T)
    {r : ℕ} (hr : r = ((ZMod.castHom (dvd_pow_self p he) (ZMod p)).mapMatrix T).rank) :
    T.trace = (r : ZMod (p ^ e)) := by
  have := isLocalRing_zmod_pow hp he
  rw [hr, rank_mapMatrix_eq_rank_of_isIdempotentElem hp he hT]
  exact trace_eq_rank_of_isIdempotentElem hT

end ResidueRing

end CFSG.FeitThompson
