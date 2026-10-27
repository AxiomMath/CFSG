module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.SPLCellLinBlock
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.PerfectQuotient

public section

open Polynomial Module Matrix CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCLinComm
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

namespace CFSG.HardMathSupport.Malle.E27Lie

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem three_dvd_card_SL {E : Type} [Field E] [Finite E] (h3 : (3 : E) ≠ 0) {m : ℕ}
    (hm : 2 ≤ m) : 3 ∣ Nat.card (SpecialLinearGroup (Fin m) E) := by
  rw [card_SL_eq (by omega)]
  have h2 : (2 : ℕ) ∈ Finset.Icc 2 m := Finset.mem_Icc.2 ⟨le_rfl, hm⟩
  refine Dvd.dvd.mul_left ((?_ : 3 ∣ Nat.card E ^ 2 - 1).trans
    (Finset.dvd_prod_of_mem (fun j => Nat.card E ^ j - 1) h2)) _
  have hcop : ¬ 3 ∣ Nat.card E := by
    intro h
    letI := Fintype.ofFinite E
    obtain ⟨d, hp, hcard⟩ := FiniteField.card E (ringChar E)
    rw [Nat.card_eq_fintype_card, hcard] at h
    have h3p : 3 ∣ ringChar E := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    have hp3 : ringChar E = 3 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3p).symm
    apply h3
    have := ringChar.Nat.cast_ringChar (R := E)
    rwa [hp3] at this
  have hmod : Nat.card E % 3 = 1 ∨ Nat.card E % 3 = 2 := by omega
  have hc1 : 1 ≤ Nat.card E := Nat.card_pos
  have hsq : Nat.card E ^ 2 - 1 = (Nat.card E - 1) * (Nat.card E + 1) := by
    rw [show Nat.card E ^ 2 - 1 = Nat.card E ^ 2 - 1 ^ 2 by norm_num, Nat.sq_sub_sq]; ring
  rw [hsq]
  rcases hmod with h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _
  · exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _

set_option maxHeartbeats 1000000 in
open scoped _root_.Classical in
theorem exists_perfect_three_dvd_autFix_of_block (h3 : (3 : K) ≠ 0) {y : GL (Fin n) K}
    (hx : Squarefree (minpoly K (linEnd y))) (a : primaryFactors (linEnd y))
    (ha : 2 ≤ mult (linEnd y) a)
    (hE : 3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a)) :
    ∃ Q : Subgroup (projectiveSL n K),
      Q ≤ Curtis.Coordinator.autFix (conjAut n K y) ∧ ⁅Q, Q⁆ = Q ∧ 3 ∣ Nat.card Q := by
  have hq := isQuasisimple_blockImage_of_card hx a ha hE
  have hle := blockImage_le_range_toGL_of_card hx a ha hE
  have hcen := blockImage_le_centralizer hx a
  set B := blockImage hx a with hB
  let toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K := SpecialLinearGroup.toGL
  have hinj : Function.Injective toGL := SpecialLinearGroup.toGL_injective
  let BS : Subgroup (SpecialLinearGroup (Fin n) K) := B.comap toGL
  have hBS : BS.map toGL = B := Subgroup.map_comap_eq_self hle
  have hperfBS : ⁅BS, BS⁆ = BS := by
    apply Subgroup.map_injective hinj
    rw [Subgroup.map_commutator, hBS]
    exact CFSG.RankThree.PartOne.KCUnitary.commutator_eq_of_isPerfect hq.1
  let Q : Subgroup (projectiveSL n K) := BS.map (proj n K)
  have hQperf : ⁅Q, Q⁆ = Q := by rw [← Subgroup.map_commutator, hperfBS]
  have hQfix : Q ≤ Curtis.Coordinator.autFix (conjAut n K y) := by
    rintro _ ⟨g, hg, rfl⟩
    show conjAut n K y (proj n K g) = proj n K g
    rw [conjAut_proj]
    congr 1
    apply hinj
    have hc : toGL g * y = y * toGL g :=
      Subgroup.mem_centralizer_singleton_iff.1 (hcen hg)
    have e : toGL (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K y g) =
        y * toGL g * y⁻¹ :=
      Units.ext (by
        rw [Units.val_mul, Units.val_mul]
        exact coe_slConjugation y g)
    rw [e, ← hc, mul_assoc, mul_inv_cancel, mul_one]
  refine ⟨Q, hQfix, hQperf, ?_⟩
  have hFin : Finite (Efac (linEnd y) a) := finite_efac a
  have : Fact (Irreducible (a : K[X])) := ⟨irreducible_of_mem_primaryFactors a.2⟩
  have h3E : (3 : Efac (linEnd y) a) ≠ 0 := fun h =>
    h3 ((algebraMap K (Efac (linEnd y) a)).injective (by rw [map_ofNat, h, map_zero]))
  have hBSB : BS ≃* B := (Subgroup.equivMapOfInjective BS toGL hinj).trans (MulEquiv.subgroupCongr hBS)
  have hBB : B ≃* blockSL (Efac (linEnd y)) (mult (linEnd y)) a :=
    (Subgroup.equivMapOfInjective _ _ (blockTheta_injective hx)).symm
  have hSL : blockSL (Efac (linEnd y)) (mult (linEnd y)) a ≃*
      SpecialLinearGroup (Fin (mult (linEnd y) a)) (Efac (linEnd y) a) :=
    (MonoidHom.ofInjective (blockEmbed_injective a)).symm
  have h3BS : 3 ∣ Nat.card BS := by
    rw [Nat.card_congr (hBSB.trans (hBB.trans hSL)).toEquiv]
    exact three_dvd_card_SL h3E ha
  let f : BS →* projectiveSL n K := (proj n K).comp BS.subtype
  have hrange : f.range = Q := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : f.ker ≤ Subgroup.center BS := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    have hg' : (proj n K) (g : SpecialLinearGroup (Fin n) K) = 1 := hg
    have hc : (g : SpecialLinearGroup (Fin n) K) ∈ Subgroup.center (SpecialLinearGroup (Fin n) K) := by
      rw [← scalars_eq_center, ← ker_proj]
      exact hg'
    exact Subtype.ext ((Subgroup.mem_center_iff.1 hc) (h : SpecialLinearGroup (Fin n) K))
  have hperfG : commutator BS = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperfBS)
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := dvd_card_quotient_of_perfect (p := 3) hperfG h3BS (N := f.ker) hker
  rwa [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h

theorem autFix_le_centralizer {g : SpecialLinearGroup (Fin n) K} {Q : Subgroup (projectiveSL n K)}
    (hQ : Q ≤ Curtis.Coordinator.autFix (conjAut n K (SpecialLinearGroup.toGL g))) :
    Q ≤ Subgroup.centralizer ({proj n K g} : Set (projectiveSL n K)) := by
  intro h hh
  obtain ⟨s, rfl⟩ := proj_surjective n K h
  rw [Subgroup.mem_centralizer_singleton_iff]
  have h1 : conjAut n K (SpecialLinearGroup.toGL g) (proj n K s) = proj n K s := hQ hh
  rw [conjAut_proj] at h1
  have h2 : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation n K
      (SpecialLinearGroup.toGL g) s = g * s * g⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
    simp [map_mul, map_inv]
  rw [h2, map_mul, map_mul, map_inv] at h1
  exact (mul_inv_eq_iff_eq_mul.mp h1).symm

open scoped _root_.Classical in
theorem exists_block_of_pow_three (h3 : (3 : K) ≠ 0) (hK : 4 ≤ Nat.card K)
    {y : GL (Fin n) K} (c : Kˣ) (hyp : y ^ 3 = GeneralLinearGroup.scalar (Fin n) c)
    (hn : 4 ≤ n) :
    ∃ a : primaryFactors (linEnd y), 2 ≤ mult (linEnd y) a ∧
      (3 ≤ mult (linEnd y) a ∨ 4 ≤ Nat.card (Efac (linEnd y) a)) := by
  have hx := squarefree_minpoly_linEnd_of_pow_scalar h3 c hyp
  by_contra hcon
  push Not at hcon
  have hle : ∀ a : primaryFactors (linEnd y), mult (linEnd y) a ≤ 1 := by
    intro a
    by_contra h
    push Not at h
    have hE := hcon a h
    have := finite_efac a
    have hle : Nat.card K ≤ Nat.card (Efac (linEnd y) a) :=
      Nat.card_le_card_of_injective _ (algebraMap K (Efac (linEnd y) a)).injective
    omega
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx
  rw [Module.finrank_fin_fun] at hsum
  have h1 : n ≤ ∑ a : primaryFactors (linEnd y), (a : K[X]).natDegree := by
    refine hsum.le.trans ?_
    exact Finset.sum_le_sum fun a _ => by
      have := hle a
      change (a : K[X]).natDegree * mult (linEnd y) a ≤ _
      nlinarith
  have hprod := prod_primaryFactors hx
  have hne : ∀ a ∈ primaryFactors (linEnd y), a ≠ 0 := fun a ha =>
    (UniqueFactorizationMonoid.irreducible_of_normalized_factor a
      (Multiset.mem_toFinset.1 ha)).ne_zero
  have hdeg : (minpoly K (linEnd y)).natDegree = ∑ a ∈ primaryFactors (linEnd y), a.natDegree := by
    rw [← hprod, Polynomial.natDegree_prod _ _ hne]
  have h2 : ∑ a : primaryFactors (linEnd y), (a : K[X]).natDegree =
      ∑ a ∈ primaryFactors (linEnd y), a.natDegree :=
    Finset.sum_coe_sort (primaryFactors (linEnd y)) fun a => a.natDegree
  have hdvd : minpoly K (linEnd y) ∣ (X ^ 3 - C (c : K) : K[X]) :=
    minpoly.dvd K _ (aeval_linEnd_X_pow_sub_C c hyp)
  have hne0 : (X ^ 3 - C (c : K) : K[X]) ≠ 0 := (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have h4 := Polynomial.natDegree_le_of_dvd hdvd hne0
  rw [natDegree_X_pow_sub_C] at h4
  omega

theorem exists_perfect_three_dvd_centralizer_PSL (h3 : (3 : K) ≠ 0) (hK : 4 ≤ Nat.card K)
    (hn : 4 ≤ n) {z : projectiveSL n K} (hz : z ^ 3 = 1) :
    ∃ Q : Subgroup (projectiveSL n K), Q ≤ Subgroup.centralizer ({z} : Set (projectiveSL n K)) ∧
      ⁅Q, Q⁆ = Q ∧ 3 ∣ Nat.card Q := by
  obtain ⟨g, rfl⟩ := proj_surjective n K z
  have hg : g ^ 3 ∈ scalars n K := by
    rw [← ker_proj, MonoidHom.mem_ker, map_pow]; exact hz
  obtain ⟨c, -, hc⟩ := hg
  have hyp : (SpecialLinearGroup.toGL g) ^ 3 = GeneralLinearGroup.scalar (Fin n) c := by
    apply Units.ext
    have h1 : ((g ^ 3 : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) ^ 3 := by simp
    simp only [Units.val_pow_eq_pow_val]
    have h2 : ((SpecialLinearGroup.toGL g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (g : Matrix (Fin n) (Fin n) K) := rfl
    rw [h2, ← h1, hc]
    simp [GeneralLinearGroup.scalar]
  obtain ⟨a, ha, hE⟩ := exists_block_of_pow_three h3 hK c hyp hn
  obtain ⟨Q, hQ, hQp, hQ3⟩ := exists_perfect_three_dvd_autFix_of_block h3
    (squarefree_minpoly_linEnd_of_pow_scalar h3 c hyp) a ha hE
  exact ⟨Q, autFix_le_centralizer hQ, hQp, hQ3⟩

end CFSG.HardMathSupport.Malle.E27Lie
