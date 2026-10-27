module

public import CFSG.ClassicalInvolution.Asc77.AscT8W13
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscT8V12
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section TwinStd

variable {F : Type} [Field F]

theorem twin_std_y' (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1)
    (hx'1 : x' ≠ 1) (hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F)) :
    ∃ g : SL(4, F),
      R = (blockSL F 4 2 0 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      R' = (blockSL F 4 2 2 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      x' = g * negTwo F * g⁻¹ := by
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two h2 hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two h2 hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroup h2
  have hR'lr := hi'.eq_longRootGroup h2
  obtain ⟨g, hRg, hig⟩ := hi
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hxx : ((x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx2, Matrix.SpecialLinearGroup.coe_one]
  have hxx' : ((x' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x' : Matrix (Fin 4) (Fin 4) F) =
      1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hx'2, Matrix.SpecialLinearGroup.coe_one]
  have hx'x : (x' : Matrix (Fin 4) (Fin 4) F) = r • (x : Matrix (Fin 4) (Fin 4) F) := by
    have h1 : (x' : Matrix (Fin 4) (Fin 4) F) =
        ((x' * x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
    rw [h1, ← hrA, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
      Matrix.one_mul]
  have hr2 : r * r = 1 := by
    have h1 : ((x' : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * (x' : Matrix (Fin 4) (Fin 4) F) =
        (r * r) • (1 : Matrix (Fin 4) (Fin 4) F) := by
      rw [hx'x, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [hxx'] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · exfalso
    apply hne
    have hxx'' : x' = x := by
      apply Subtype.ext
      rw [hx'x, hr1, one_smul]
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · have hneg : -(!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) F) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    have hX' : (x' : Matrix (Fin 4) (Fin 4) F) = (g : Matrix (Fin 4) (Fin 4) F) *
        negBlock F 4 2 * ((g⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) := by
      rw [hx'x, hr1, neg_one_smul, hxi, hig, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.coe_mul, coe_rootInv, negBlock_four, negBlock_four_two,
        ← hneg, Matrix.mul_neg, Matrix.neg_mul]
    refine ⟨g, hRg, ?_, ?_⟩
    · rw [hR'lr, ← hxi', hX', longRootGroup_conj, range_blockSL_eq_longRootGroup h2]
    · apply Subtype.ext
      rw [hX', Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_negTwo,
        negBlock_four_two]

end TwinStd

section Wrapper

variable {p e : ℕ} [Fact p.Prime]


theorem sl4_gen_of_pair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) {X : Type} [Group X]
    (ψ : SL(4, GaloisField p e) →* X) {R R' : Subgroup SL(4, GaloisField p e)}
    {y y' : SL(4, GaloisField p e)} (hP : T8V.E4Pair ψ R R' y y')
    (hR : R ∈ longRootSet (K := GaloisField p e) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := GaloisField p e) (show 2 ≤ 4 by norm_num))
    (σ : MulAut X) (hσ2 : ∀ x, σ (σ x) = x) (hσR : ∀ r ∈ R, σ (ψ r) = ψ r)
    (hσnt : ∃ r ∈ R', σ (ψ r) ≠ ψ r) :
    Subgroup.closure ({g | σ g = g} ∪ {g | σ (ψ y' * g * (ψ y')⁻¹) = g}) = ⊤ := by
  classical
  have h2 : (2 : GaloisField p e) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField e hp2
  have hc : y' * y⁻¹ ∈ Subgroup.center SL(4, GaloisField p e) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, hy'g⟩ := twin_std_y' h2 hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy' hP.hy'2
    hP.hy'1 hc
  set ψ₀ : SL(4, GaloisField p e) →* X := ψ.comp (MulAut.conj g).toMonoidHom with hψ₀
  have hψ₀s : Function.Surjective ψ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : ψ₀.ker ≤ Subgroup.center SL(4, GaloisField p e) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Subgroup.center SL(4, GaloisField p e) := hP.ker hx
    have h2' := (Subgroup.center SL(4, GaloisField p e)).normal_of_characteristic.conj_mem
      (g * x * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  have hperf0 : (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range ≤
      ⁅(blockSL (GaloisField p e) 4 2 0 (by norm_num)).range,
        (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range⁆ := by
    have h1 := hP.perfR
    rw [hRg, ← Subgroup.map_commutator] at h1
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp h1
  have h0 : ∀ r ∈ (blockSL (GaloisField p e) 4 2 0 (by norm_num)).range, σ (ψ₀ r) = ψ₀ r := by
    intro r hr
    apply hσR
    rw [hRg]
    exact ⟨r, hr, rfl⟩
  have hnt : ∃ r ∈ (blockSL (GaloisField p e) 4 2 2 (by norm_num)).range, σ (ψ₀ r) ≠ ψ₀ r := by
    obtain ⟨r', hr', hne⟩ := hσnt
    rw [hR'g] at hr'
    obtain ⟨r, hr, rfl⟩ := hr'
    exact ⟨r, hr, hne⟩
  have key := sl4_gen_std hp2 hq ψ₀ hψ₀s hker₀ hP.perf hperf0 σ hσ2 h0 hnt
  have hψ₀y : ψ₀ (negTwo (GaloisField p e)) = ψ y' := by
    rw [hy'g]
    simp [hψ₀, MulAut.conj_apply]
  rw [hψ₀y] at key
  exact key

end Wrapper

section Tag

variable {p f : ℕ} [Fact p.Prime]


theorem e4_gen_sl4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {e : ℕ} (M : Ih8Model p f Φ .PSL 4 e)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X)
    (σ : MulAut X) (hσ2 : σ * σ = 1) (hσA : ∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A)
    (hσnt : ¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) :
    Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
      {g | σ (x' * g * x'⁻¹) = g}) = ⊤ := by
  have hG2 : StatedLieTag.PSL ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSL ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSL = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSL 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSL 4 p e Fact.out trivial M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    T8V.e4_pair_of_model hp2 hq hΦ M hG2 hD4 hnpsl hSperf hnt htrans hA hB hxA hxB hcen
  have hA0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR
  have hB0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR'
  have he : e = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ e := by rw [he]; exact hq
  have hRl := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR)
  have hRl' := CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3)
    (by norm_num) (M.cls_sub hR')
  subst hAR hBR hy hy'
  have hσ2' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : MulAut X => τ z) hσ2
    simpa using this
  have hσR : ∀ r ∈ R, σ (M.ψ r) = M.ψ r := by
    intro r hr
    have h := hσA (M.ψ r) (Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  have hσnt' : ∃ r ∈ R', σ (M.ψ r) ≠ M.ψ r := by
    by_contra hcon
    push Not at hcon
    apply hσnt
    rintro k ⟨r, hr, rfl⟩
    rw [hB0, Subgroup.mem_bot, mul_inv_eq_one]
    exact hcon r hr
  have key := sl4_gen_of_pair hp2 hq' M.ψ hP hRl hRl' σ hσ2' hσR hσnt'
  rw [eq_top_iff] at key ⊢
  refine key.trans (Subgroup.closure_mono ?_)
  intro g hg
  rcases hg with hg | hg
  · exact Or.inl (Or.inl hg)
  · exact Or.inr hg

end Tag

end CFSG.ClassicalInvolution.Asc77.T8W
