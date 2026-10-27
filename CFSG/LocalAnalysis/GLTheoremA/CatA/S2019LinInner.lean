module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalParts
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019Quadratic
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.CALinearPrimary
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem one_add_pow_of_mul_self_eq_zero {M : Type*} [Ring M] {N : M} (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : M) * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ, mul_add, add_mul, add_mul, one_mul, one_mul, mul_one,
      mul_assoc, hN, mul_zero, add_zero, add_mul, one_mul]
    abel

theorem pow_char_eq_one_of_sq_sub_one_eq_zero {F M : Type*} [Field F] [Ring M] [Algebra F M]
    {q : ℕ} [CharP F q] {x : M} (hx : (x - 1) ^ 2 = 0) : x ^ q = 1 := by
  have hNN : (x - 1) * (x - 1) = 0 := by rw [← sq]; exact hx
  have h1 := one_add_pow_of_mul_self_eq_zero hNN q
  have hq : (q : M) = 0 := by
    rw [← map_natCast (algebraMap F M) q, CharP.cast_eq_zero, map_zero]
  rw [hq, zero_mul, add_zero, add_sub_cancel] at h1
  exact h1

section Block

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {x : LinearMap.GeneralLinearGroup k V}

theorem exists_quadratic_linearSpecialBlock (hsq : Squarefree (minpoly k (x : Module.End k V)))
    {h : k[X]} (hh : h ∈ primaryFactors (x : Module.End k V))
    (hm : 2 ≤ primaryMultiplicity (x : Module.End k V) h) :
    ∃ g ∈ linearSpecialBlock x h, ∃ g' ∈ linearSpecialBlock x h,
      ((g : Module.End k V) - 1) ^ 2 = 0 ∧
        ∀ c : k, (g : Module.End k V) * g' ≠ c • ((g' : Module.End k V) * g) := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  set W := primaryComponent (x : Module.End k V) h with hW
  let b : Module.Basis (Fin (primaryMultiplicity (x : Module.End k V) h)) (AdjoinRoot h) W :=
    Module.finBasisOfFinrankEq _ _ rfl
  let i0 : Fin (primaryMultiplicity (x : Module.End k V) h) := ⟨0, by omega⟩
  let i1 : Fin (primaryMultiplicity (x : Module.End k V) h) := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := fun he => by simpa [i0, i1] using congrArg Fin.val he
  set N : W →ₗ[AdjoinRoot h] W := Matrix.toLin b b (Matrix.single i0 i1 1) with hNdef
  set N' : W →ₗ[AdjoinRoot h] W := Matrix.toLin b b (Matrix.single i1 i0 1) with hN'def
  set τ := Matrix.SpecialLinearGroup.toLin_equiv b
    (Matrix.SpecialLinearGroup.transvection h01 (1 : AdjoinRoot h)) with hτdef
  set τ' := Matrix.SpecialLinearGroup.toLin_equiv b
    (Matrix.SpecialLinearGroup.transvection h01.symm (1 : AdjoinRoot h)) with hτ'def
  have hτ : ∀ w : W, ((τ : W ≃ₗ[AdjoinRoot h] W) w) = w + N w := by
    intro w
    have e1 := LinearMap.congr_fun (Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b
      (Matrix.SpecialLinearGroup.transvection h01 (1 : AdjoinRoot h))) w
    rw [Matrix.SpecialLinearGroup.transvection_coe, map_add, Matrix.toLin_one] at e1
    exact e1
  have hτ' : ∀ w : W, ((τ' : W ≃ₗ[AdjoinRoot h] W) w) = w + N' w := by
    intro w
    have e1 := LinearMap.congr_fun (Matrix.SpecialLinearGroup.toLin_equiv.toLinearMap_eq b
      (Matrix.SpecialLinearGroup.transvection h01.symm (1 : AdjoinRoot h))) w
    rw [Matrix.SpecialLinearGroup.transvection_coe, map_add, Matrix.toLin_one] at e1
    exact e1
  have hNN : ∀ w : W, N (N w) = 0 := by
    intro w
    have e0 : Matrix.single i0 i1 (1 : AdjoinRoot h) * Matrix.single i0 i1 1 = 0 := by
      ext a d
      rw [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.single_apply, Matrix.single_apply]
      split_ifs with h1 h2
      · exact absurd (h2.1.trans h1.2.symm) h01
      · rw [mul_zero]
      · rw [zero_mul]
      · rw [zero_mul]
    have e1 : N.comp N = 0 := by
      rw [hNdef, ← Matrix.toLin_mul, e0, map_zero]
    exact LinearMap.congr_fun e1 w
  have hN0 : N (b i0) = 0 := by
    rw [hNdef, Matrix.toLin_self]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.single_apply, if_neg (fun hc => h01 hc.2.symm), zero_smul]
  have hN'0 : N' (b i0) = b i1 := by
    rw [hN'def, Matrix.toLin_self, Finset.sum_eq_single i1]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_smul]
    · intro l _ hl
      rw [Matrix.single_apply, if_neg (fun hc => hl hc.1.symm), zero_smul]
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  have hN1 : N (b i1) = b i0 := by
    rw [hNdef, Matrix.toLin_self, Finset.sum_eq_single i0]
    · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_smul]
    · intro l _ hl
      rw [Matrix.single_apply, if_neg (fun hc => hl hc.1.symm), zero_smul]
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  obtain ⟨g, hg⟩ := linearSpecialBlockRestrict_surjective hsq hh τ
  obtain ⟨g', hg'⟩ := linearSpecialBlockRestrict_surjective hsq hh τ'
  have hgW : ∀ w : W, (g.1 : Module.End k V) (w : V) = (((τ : W ≃ₗ[AdjoinRoot h] W) w : W) : V) := by
    intro w
    have e1 := coe_linearSpecialBlockRestrict g w
    rw [hg] at e1
    exact e1.symm
  have hg'W : ∀ w : W,
      (g'.1 : Module.End k V) (w : V) = (((τ' : W ≃ₗ[AdjoinRoot h] W) w : W) : V) := by
    intro w
    have e1 := coe_linearSpecialBlockRestrict g' w
    rw [hg'] at e1
    exact e1.symm
  refine ⟨g.1, g.2, g'.1, g'.2, ?_, ?_⟩
  ·
    refine ext_primaryComponent hsq fun a ha v hv => ?_
    simp only [pow_two, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply]
    by_cases hah : a = h
    · subst hah
      set w : W := ⟨v, hv⟩ with hw
      have e1 : (g.1 : Module.End k V) v - v = ((N w : W) : V) := by
        have e := hgW w
        rw [hτ, Submodule.coe_add] at e
        change (g.1 : Module.End k V) v = v + ((N w : W) : V) at e
        rw [e, add_sub_cancel_left]
      have e2 : (g.1 : Module.End k V) ((N w : W) : V) - ((N w : W) : V) = 0 := by
        have e := hgW (N w)
        rw [hτ, hNN, add_zero] at e
        rw [e, sub_self]
      rw [e1, e2]
    · have e1 : (g.1 : Module.End k V) v = v := g.2.2.1 a ha hah v hv
      rw [e1, sub_self, map_zero, sub_self]
  ·
    intro c hc
    have hgb0 : (g.1 : Module.End k V) (b i0 : V) = (b i0 : V) := by
      rw [hgW, hτ, hN0, add_zero]
    have hg'b0 : (g'.1 : Module.End k V) (b i0 : V) = ((b i0 + b i1 : W) : V) := by
      rw [hg'W, hτ', hN'0]
    have hgb01 : (g.1 : Module.End k V) ((b i0 + b i1 : W) : V) =
        ((b i0 + b i1 + (0 + b i0) : W) : V) := by
      rw [hgW, hτ, map_add, hN0, hN1]
    have e1 := LinearMap.congr_fun hc (b i0 : V)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at e1
    rw [hg'b0, hgb01, hgb0, hg'b0] at e1
    have e2 : (b i0 + b i1 + (0 + b i0) : W) =
        (algebraMap k (AdjoinRoot h) c) • (b i0 + b i1) := by
      rw [algebraMap_smul]
      apply Subtype.ext
      rw [SetLike.val_smul]
      exact e1
    have e3 := congrArg (fun w => b.repr w i0) e2
    have e4 := congrArg (fun w => b.repr w i1) e2
    simp only [map_add, map_zero, map_smul, Module.Basis.repr_self, Finsupp.add_apply,
      Finsupp.smul_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply, if_pos rfl,
      if_neg h01, if_neg h01.symm, zero_add, add_zero, smul_eq_mul, mul_one, mul_zero,
      ↓reduceIte] at e3 e4
    have : (1 : AdjoinRoot h) = 0 := by linear_combination e3 - e4
    exact one_ne_zero this

end Block

theorem s2019LinInner_five : S2019LinInner (5 ≤ ·) := by
  intro p q hp hp2 hq hq2 hqp hq5 F _ _ _ n A c hA L hL T hT2 hLT
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hpk : (p : F) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff F q]
    intro hdvd
    exact hqp ((Nat.prime_dvd_prime_iff_eq hq hp).1 hdvd)
  have hperf : ⁅L, L⁆ = L := glaPComponent_perfect hL
  have hle := perfectInLayer_conjAut hpk hA L hL.1 hperf
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hL hle
  obtain ⟨⟨⟨h, hh⟩, hgood⟩, hLeq⟩ := LieComp.linear_inner_components hpk hA L hcomp
  have hsq := squarefree_minpoly_glA hpk hA
  have hm : 2 ≤ primaryMultiplicity (glA A : Module.End F (Fin n → F)) h := by
    rcases hgood with h3 | ⟨h2, -⟩
    · exact le_trans (by norm_num) h3
    · exact h2
  obtain ⟨g, hg, g', hg', hg2, hnc⟩ := exists_quadratic_linearSpecialBlock hsq hh hm
  obtain ⟨u, hu⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg)
  obtain ⟨u', hu'⟩ := mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock hsq hh hg')
  have huF : u ∈ specialFactor A h := by
    rw [specialFactor, Subgroup.mem_comap, hu]
    exact hg
  have hu'F : u' ∈ specialFactor A h := by
    rw [specialFactor, Subgroup.mem_comap, hu']
    exact hg'
  have huL : LinearFlag.proj n F u ∈ L := by
    rw [hLeq]
    exact Subgroup.mem_map_of_mem _ huF
  have hu'L : LinearFlag.proj n F u' ∈ L := by
    rw [hLeq]
    exact Subgroup.mem_map_of_mem _ hu'F
  have hTq : ∀ t ∈ T, ¬ q ∣ orderOf t := by
    intro t ht hdvd
    obtain ⟨j, hj⟩ := hT2 ⟨t, ht⟩
    have h1 : orderOf t ∣ 2 ^ j := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg Subtype.val hj
      simpa using this
    have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (hdvd.trans h1)
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h2)
  have hkerq : ∀ s ∈ (LinearFlag.proj n F).ker, ¬ q ∣ orderOf s := by
    intro s hs hdvd
    rw [LinearFlag.ker_proj] at hs
    obtain ⟨c₀, -, hc₀⟩ := LinearFlag.mem_scalars.1 hs
    have hs1 : s ^ Nat.card Fˣ = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, hc₀, Matrix.SpecialLinearGroup.coe_one, ← map_pow,
        ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
    have h1 : q ∣ Nat.card Fˣ := hdvd.trans (orderOf_dvd_of_pow_eq_one hs1)
    rw [Nat.card_units] at h1
    haveI := Fintype.ofFinite F
    obtain ⟨e, -, he⟩ := FiniteField.card F q
    have h2 : q ∣ Nat.card F := by
      rw [Nat.card_eq_fintype_card, he]
      exact dvd_pow_self q e.pos.ne'
    have h3 : q ∣ 1 := by
      have := Nat.dvd_sub h2 h1
      rwa [Nat.sub_sub_self (Nat.one_le_iff_ne_zero.2 Nat.card_pos.ne')] at this
    exact hq.one_lt.ne' (Nat.dvd_one.1 h3)
  have hnz : LinearFlag.proj n F u' * LinearFlag.proj n F u ≠
      LinearFlag.proj n F u * LinearFlag.proj n F u' := by
    intro heq
    rw [← map_mul, ← map_mul] at heq
    have hmem : (u * u')⁻¹ * (u' * u) ∈ LinearFlag.scalars n F := by
      rw [← LinearFlag.ker_proj, MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
    obtain ⟨c₀, -, hc₀⟩ := LinearFlag.mem_scalars.1 hmem
    set X := (u * u')⁻¹ * (u' * u) with hX
    have hprod : u' * u = (u * u') * X := by rw [hX]; group
    have hsc : ((slGL n F X : LinearMap.GeneralLinearGroup F (Fin n → F)) :
        Module.End F (Fin n → F)) = (c₀ : F) • 1 := by
      rw [coe_slGL, hc₀]
      ext v i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have h1 := congrArg (fun z => ((slGL n F z : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F))) hprod
    simp only [map_mul, Units.val_mul] at h1
    rw [hsc, hu, hu', mul_smul_comm, mul_one] at h1
    apply hnc (c₀ : F)⁻¹
    rw [h1, smul_smul, inv_mul_cancel₀ (Units.ne_zero c₀), one_smul]
  have huq : u ^ q = 1 := by
    apply slGL_injective
    rw [map_pow, map_one, hu]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact pow_char_eq_one_of_sq_sub_one_eq_zero (F := F) hg2
  have hu2 : (((slGL n F u : LinearMap.GeneralLinearGroup F (Fin n → F)) :
      Module.End F (Fin n → F)) - 1) ^ 2 = 0 := by
    rw [hu]
    exact hg2
  exact commutator_eq_bot_of_quadratic_lift hq5 hcomp.2.2 hLT hTq (LinearFlag.proj n F)
    (LinearFlag.proj_surjective n F) hkerq (slGL n F) slGL_injective huL ⟨_, hu'L, hnz⟩ huq hu2

end CFSG.LocalAnalysis.GLTheoremA.S2019
