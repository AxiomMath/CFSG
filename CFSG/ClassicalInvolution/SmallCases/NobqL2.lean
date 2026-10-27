module

public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Blueprint.Catalog
import CFSG.Dihedral.GorensteinWalter.PGL2CharTwo

public section

namespace CFSG.ClassicalInvolution.Nobq

open Matrix CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter

theorem sq_eq_one_of_commute {K : Type*} [Field K] [CharP K 2] {T C : Matrix (Fin 2) (Fin 2) K}
    (hT : T * T = 1) (hT1 : T ≠ 1) (hdC : C.det = 1) (hTC : C * T = T * C) :
    C * C = 1 := by
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  rw [Matrix.det_fin_two] at hdC
  have e00 := congrFun (congrFun hT 0) 0
  have e01 := congrFun (congrFun hT 0) 1
  have e10 := congrFun (congrFun hT 1) 0
  have e11 := congrFun (congrFun hT 1) 1
  have f00 := congrFun (congrFun hTC 0) 0
  have f01 := congrFun (congrFun hTC 0) 1
  have f10 := congrFun (congrFun hTC 1) 0
  have f11 := congrFun (congrFun hTC 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11 f00 f01 f10 f11
  set a := T 0 0
  set b := T 0 1
  set c := T 1 0
  set d := T 1 1
  set x := C 0 0
  set y := C 0 1
  set z := C 1 0
  set w := C 1 1
  have hsq : (a + d) ^ 2 = 0 := by
    linear_combination e00 + e11 + (a * d - b * c + 1) * h2
  have hsum : a + d = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 hsq
  have hda : d = a := by linear_combination hsum - a * h2
  have hbc : b ≠ 0 ∨ c ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hb0, hc0⟩ := hcon
    have ha1 : a = 1 := by
      have h1 : (a + 1) ^ 2 = 0 := by
        rw [hb0, hc0] at e00
        linear_combination e00 + (a + 1) * h2
      have h3 : a + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
      linear_combination h3 - h2
    apply hT1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact ha1
    · exact hb0
    · exact hc0
    · exact hda.trans ha1
  have hxw : x = w := by
    rcases hbc with hb | hc
    · have : b * (x - w) = 0 := by
        rw [hda] at f01
        linear_combination f01
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hb
      · linear_combination h
    · have : c * (w - x) = 0 := by
        rw [hda] at f10
        linear_combination f10
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hc
      · linear_combination -h
  rw [← hxw] at hdC
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · show x * x + y * z = 1
    linear_combination hdC + (y * z) * h2
  · show x * y + y * w = 0
    rw [← hxw]
    linear_combination (x * y) * h2
  · show z * x + w * z = 0
    rw [← hxw]
    linear_combination (x * z) * h2
  · show z * y + w * w = 1
    rw [← hxw]
    linear_combination hdC + (y * z) * h2

theorem toPGL_surjective_of_charTwo (K : Type*) [Field K] [Finite K] [CharP K 2] :
    Function.Surjective (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)) :=
  CFSG.GorensteinWalter.toPGL_surjective_of_charTwo' K

theorem isCyclic_outer_psl2_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    IsCyclic (Outer (PSL2 K)) := by
  have hker : (quotientFieldProjection K).ker = ⊥ := by
    rw [quotientFieldProjection_ker, eq_bot_iff]
    rintro _ ⟨g, rfl⟩
    obtain ⟨y, rfl⟩ := toPGL_surjective_of_charTwo K g
    rw [Subgroup.mem_bot]
    change QuotientGroup.mk' (pGammaL2PSLRange K) (SemidirectProduct.inl
      (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_pGammaL2PSLRange_iff K _).2 ⟨y, rfl⟩
  have hinj : Function.Injective (quotientFieldProjection K) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have : IsCyclic (K ≃+* K) := fieldAut_isCyclic K
  have hcyc : IsCyclic (SemilinearQuotient K) := isCyclic_of_injective_hom _ hinj
  exact isCyclic_of_surjective (outerEquivSemilinearQuotient K).toMonoidHom
    (outerEquivSemilinearQuotient K).surjective

theorem outTwoCyclic_psl2_of_charTwo (K : Type) [Field K] [Finite K] [CharP K 2] :
    OutTwoCyclic (PSL2 K) := by
  have := isCyclic_outer_psl2_of_charTwo K
  intro P _
  exact Subgroup.isCyclic P

theorem center_specialLinear_eq_bot_of_charTwo (K : Type*) [Field K] [CharP K 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hr1 : r = 1 := by
    have hr2 : r ^ 2 = 1 := by simpa using hr
    have : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    have := pow_eq_zero_iff (two_ne_zero) |>.1 this
    linear_combination this
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

noncomputable def psl2MulEquivSL2 (K : Type*) [Field K] [CharP K 2] :
    PSL2 K ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
  (QuotientGroup.quotientMulEquivOfEq (center_specialLinear_eq_bot_of_charTwo K)).trans
    QuotientGroup.quotientBot

theorem noUniqueInvNormal_specialLinear_of_charTwo (K : Type*) [Field K] [CharP K 2] :
    NoUniqueInvNormal (Matrix.SpecialLinearGroup (Fin 2) K) := by
  intro t N ht hN
  obtain ⟨s, hsN, hs4⟩ := hN.exists_orderOf_eq_four
  have hsC := hN.le_centralizer hsN
  rw [Subgroup.mem_centralizer_singleton_iff] at hsC
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht, pow_two] at this
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hss : s * s = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    refine sq_eq_one_of_commute (T := (t : Matrix (Fin 2) (Fin 2) K)) ?_ ?_
      (Matrix.SpecialLinearGroup.det_coe s) ?_
    · rw [← Matrix.SpecialLinearGroup.coe_mul, htt, Matrix.SpecialLinearGroup.coe_one]
    · intro h
      exact ht1 (Subtype.ext (by rw [h, Matrix.SpecialLinearGroup.coe_one]))
    · rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hsC]
  have h2 : orderOf s ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  rw [hs4] at h2
  omega

theorem noDatum_of_statedPSL_two_even (F : Type) [Group F] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel F .PSL 2 2 f) : NoDatum F := by
  obtain ⟨-, K, hK, hfin, hcard, ⟨e⟩⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcp : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card]
    exact hcard)
  let e1 : F ≃* PSL2 K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  exact noDatum_of_noUniqueInvNormal
    (NoUniqueInvNormal.of_mulEquiv (e1.trans (psl2MulEquivSL2 K))
      (noUniqueInvNormal_specialLinear_of_charTwo K))
    (OutTwoCyclic.of_mulEquiv e1 (outTwoCyclic_psl2_of_charTwo K))

theorem noDatum_of_lieModel_psl_two_even (F : Type) [Group F] {f : ℕ}
    (h : CFSG.Blueprint.LieModel F .PSL 2 2 f) : NoDatum F := by
  rcases h with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · exact noDatum_of_statedPSL_two_even F h
  all_goals exact absurd h (by norm_num)

end CFSG.ClassicalInvolution.Nobq
