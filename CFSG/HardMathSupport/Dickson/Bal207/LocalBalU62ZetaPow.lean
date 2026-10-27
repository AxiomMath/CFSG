module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBBlocks
import CFSG.HardMathSupport.Dickson.Bal207.LocalBalU62ZetaPowAux
import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealArith
import CFSG.HardMathSupport.Timmesfeld.CrossChar.UnitaryBalBlock

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open Polynomial CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
  CFSG.HardMathSupport.Dickson.Sec6.I1431 CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem u62lb_zeta_pow_nine {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)
    (A : primeFormUnitary h (idGram K 6)) {c : Kˣ}
    (hA3 : (A : GL (Fin 6) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c) (hc : c ≠ 1)
    (Y : primeFormUnitary h (idGram K 6)) (hYA : Y * A = A * Y)
    (hY : ∀ i : t6psub_Idx h 6 A, ∀ s ∈ t6psub_block A i,
      (Y : GL (Fin 6) K) * (s : GL (Fin 6) K) = (s : GL (Fin 6) K) * (Y : GL (Fin 6) K)) :
    Y ^ 9 = 1 := by
  haveI := h.finite
  have hcard : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, h.card]
    norm_num
  have hcube : ∀ a : Kˣ, a ^ 3 ≠ c := fun a ha =>
    hc (ha.symm.trans (by rw [← hcard]; exact pow_card_eq_one'))
  have H : UnitaryPrimaryData h.bar (idForm h 6) (t6psub_toLin A) :=
    t6psuh_primaryData_toLin' h A.2 Nat.prime_three (by norm_num) hA3
  set x : Module.End K (Fin 6 → K) :=
    ((t6psub_toLin A : LinearMap.GeneralLinearGroup K (Fin 6 → K)) : Module.End K (Fin 6 → K))
  set p : K[X] := X ^ 3 - C (c : K)
  have hpirr : Irreducible p := u6r_irreducible hcube
  have hpmon : p.Monic := monic_X_pow_sub_C _ (by norm_num)
  have hpdeg : p.natDegree = 3 := natDegree_X_pow_sub_C
  have hpx : aeval x p = 0 := aeval_X_pow_sub_C_eq_zero hA3
  have hmin : p = minpoly K x := minpoly.eq_of_irreducible_of_monic hpirr hpx hpmon
  have hpmem : p ∈ primaryFactors x := by
    rw [mem_primaryFactors]
    exact ⟨hpirr, hpmon, hmin ▸ dvd_refl _⟩
  have honly : ∀ b ∈ primaryFactors x, b = p := by
    intro b hb
    obtain ⟨hbirr, hbmon, hbdvd⟩ := mem_primaryFactors.1 hb
    rw [← hmin] at hbdvd
    exact eq_of_monic_of_associated hbmon hpmon (hbirr.associated_of_dvd hpirr hbdvd)
  have hmem : ∀ v : Fin 6 → K, v ∈ primaryComponent x p := fun v => by
    rw [mem_primaryComponent, hpx]
    rfl
  have hcomp : primaryComponent x p = ⊤ := eq_top_iff.2 fun v _ => hmem v
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hmult : primaryMultiplicity x p = 2 := by
    have h1 := finrank_primaryComponent x (a := p)
    have h6 : Module.finrank K (primaryComponent x p) = 6 := by
      rw [hcomp, finrank_top, Module.finrank_fin_fun]
    rw [h6, hpdeg] at h1
    show Module.finrank (AdjoinRoot p) (primaryComponent x p) = 2
    omega
  have hself : dualPoly h.bar p = p := honly _ (dualPoly_mem_primaryFactors H hpmem)
  have hgood : IsGoodBlock h (t6psub_toLin A) ⟨p, hpmem⟩ := by
    refine ⟨by rw [hmult], fun _ => ?_⟩
    change (primaryMultiplicity x p, 2 ^ (1 * p.natDegree)) ∉
      ({(2, 2), (2, 3), (3, 2)} : Set (ℕ × ℕ))
    rw [hmult, hpdeg]
    simp
  set i₀ : t6psub_Idx h 6 A := ⟨⟨p, hpmem⟩, hgood⟩
  have hblock : ∀ g ∈ gBlock h A p, Y * g = g * Y := by
    intro g hg
    have hg' : toLinU h 6 g ∈ specialBlock (idForm h 6) (t6psub_toLin A) (i₀.1 : K[X]) := hg
    obtain ⟨s, hs⟩ := t6psub_specialBlock_le_range A H i₀ hg'
    have hsb : s ∈ t6psub_block A i₀ := by
      rw [t6psub_block, Subgroup.mem_comap, hs]
      exact hg'
    have hsg : (s : GL (Fin 6) K) = (g : GL (Fin 6) K) :=
      Matrix.GeneralLinearGroup.toLin.injective hs
    have := hY i₀ s hsb
    rw [hsg] at this
    exact Subtype.ext this
  obtain ⟨e, he⟩ := exists_eScalar_of_commute_gBlock (by norm_num : 2 ≤ 2 ^ 1) H ⟨p, hpmem⟩ hgood
    Y hYA hblock
  set Yend : Module.End K (Fin 6 → K) :=
    ((toLinU h 6 Y : LinearMap.GeneralLinearGroup K (Fin 6 → K)) : Module.End K (Fin 6 → K))
  have hYe : ∀ v : primaryComponent x p, Yend (v : Fin 6 → K) =
      ((e • v : primaryComponent x p) : Fin 6 → K) := he
  have hYB : ∀ v w : primaryComponent x p, idForm h 6 (Yend (v : Fin 6 → K))
      (Yend (w : Fin 6 → K)) = idForm h 6 (v : Fin 6 → K) (w : Fin 6 → K) :=
    fun v w => toLinU_mem Y v w
  have hbar := u62lb_bar_mul_eq_one h H hpmem hself e Yend hYe hYB
  have he9 : e ^ 9 = 1 := by
    have h8 : (unitaryFieldData_adjoinRoot h (a := p)).bar e = e ^ 8 := by
      rw [UnitaryFieldData.bar_apply, hpdeg]
      norm_num
    rw [h8] at hbar
    calc e ^ 9 = e ^ 8 * e := pow_succ e 8
      _ = 1 := hbar
  have hpow : ∀ k : ℕ, ∀ v : primaryComponent x p,
      (Yend ^ k) (v : Fin 6 → K) = ((e ^ k • v : primaryComponent x p) : Fin 6 → K) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply, ih v, hYe (e ^ k • v), ← mul_smul, ← pow_succ']
  apply toLinU_injective (h := h) (n := 6)
  rw [map_pow, map_one]
  apply Units.ext
  apply LinearMap.ext
  intro v
  have h9 := hpow 9 ⟨v, hmem v⟩
  rw [he9, one_smul] at h9
  rw [Units.val_pow_eq_pow_val]
  exact h9

end CFSG.HardMathSupport.Dickson.Bal207

end
