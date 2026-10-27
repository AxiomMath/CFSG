module

public import CFSG.ClassicalInvolution.Asc77.AscT8W17
public import CFSG.ClassicalInvolution.Asc77.AscT8V16

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.T8W

open Matrix CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU
  CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterU4 CFSG.ClassicalGroups.Unitary
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section TwinStdU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem twin_std_u_y' (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {R R' : Subgroup (Su K p f 4)}
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hne : R ≠ R') {x x' : Su K p f 4} (hxR : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx'R' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hc : x' * x⁻¹ ∈ Subgroup.center (Su K p f 4)) :
    ∃ g : Su K p f 4,
      R = (blockEmb K p f 4 2 0 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      R' = (blockEmb K p f 4 2 2 (by norm_num)).range.map (MulAut.conj g).toMonoidHom ∧
      x' = g * negTwoSU K p f * g⁻¹ := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two (K := K) hp
  have hσ : IsUnitaryInvolution (unitaryInvolution K p f) :=
    isUnitaryInvolution_unitaryInvolution hK
  obtain ⟨i, hi⟩ := hR
  obtain ⟨i', hi'⟩ := hR'
  have hxi : x = i := hi.eq_of_orderOf_eq_two hK hp hxR (orderOf_eq_prime (by rwa [pow_two]) hx1)
  have hxi' : x' = i' :=
    hi'.eq_of_orderOf_eq_two hK hp hx'R' (orderOf_eq_prime (by rwa [pow_two]) hx'1)
  have hRlr := hi.eq_longRootGroupSU h2
  have hR'lr := hi'.eq_longRootGroupSU h2
  obtain ⟨g, hRg, hig⟩ := hi
  obtain ⟨r, hr⟩ := exists_scalar_of_mem_center hσ (by norm_num : 3 ≤ 4) hc
  have hr' : suMat (x' * x⁻¹) = Matrix.scalar (Fin 4) (r : K) := hr
  have hxx : suMat x * suMat x = 1 := by rw [← suMat_mul, hx2, suMat_one]
  have hxx' : suMat x' * suMat x' = 1 := by rw [← suMat_mul, hx'2, suMat_one]
  have hx'x : suMat x' = (r : K) • suMat x := by
    calc suMat x' = suMat (x' * x⁻¹) * suMat x := by
          rw [suMat_mul, Matrix.mul_assoc, suMat_inv_mul_suMat, Matrix.mul_one]
      _ = (r : K) • suMat x := by
          rw [hr', Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
            Matrix.one_mul]
  have hr2 : (r : K) * r = 1 := by
    have h1 : suMat x' * suMat x' = ((r : K) * r) • (1 : Matrix (Fin 4) (Fin 4) K) := by
      rw [hx'x, Matrix.smul_mul, Matrix.mul_smul, hxx, smul_smul]
    rw [hxx'] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this.symm
  rcases mul_self_eq_one_iff.mp hr2 with hr1 | hr1
  · exfalso
    apply hne
    have hxx'' : x' = x := by
      apply suMat_injective
      rw [hx'x, hr1, one_smul]
    rw [hRlr, hR'lr, ← hxi, ← hxi', hxx'']
  · have hneg : -(!![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :
        Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp
    have hX' : suMat x' = suMat g * negBlock K 4 2 * suMat g⁻¹ := by
      rw [hx'x, hr1, neg_one_smul, hxi, hig, suMat_mul, suMat_mul, suMat_rootInvSU_four,
        negBlock_four_two, ← hneg, Matrix.mul_neg, Matrix.neg_mul]
    refine ⟨g, hRg, ?_, ?_⟩
    · rw [hR'lr, ← hxi', hX', longRootGroupSU_conj, range_blockEmb_eq_longRootGroupSU h2]
    · apply suMat_injective
      rw [hX', suMat_mul, suMat_mul, suMat_negTwoSU, negBlock_four_two]

end TwinStdU

section WrapperU

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su4_gen_of_pair (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type}
    [Group X] (θ : Su K p f 4 →* X) {R R' : Subgroup (Su K p f 4)} {y y' : Su K p f 4}
    (hP : T8V.E4Pair θ R R' y y')
    (hR : R ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSetU (K := K) (p := p) (f := f) (show 2 ≤ 4 by norm_num))
    (σ : MulAut X) (hσ2 : ∀ x, σ (σ x) = x) (hσR : ∀ r ∈ R, σ (θ r) = θ r)
    (hσnt : ∃ r ∈ R', σ (θ r) ≠ θ r) :
    Subgroup.closure ({g | σ g = g} ∪ {g | σ (θ y' * g * (θ y')⁻¹) = g}) = ⊤ := by
  classical
  have hc : y' * y⁻¹ ∈ Subgroup.center (Su K p f 4) := by
    have := hP.cen
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hP.hy2
    rw [hyi, ← hP.comm y hP.hy y' hP.hy']
    exact this
  obtain ⟨g, hRg, hR'g, hy'g⟩ := twin_std_u_y' hK hp hR hR' hP.ne hP.hy hP.hy2 hP.hy1 hP.hy'
    hP.hy'2 hP.hy'1 hc
  set θ₀ : Su K p f 4 →* X := θ.comp (MulAut.conj g).toMonoidHom with hθ₀
  have hθ₀s : Function.Surjective θ₀ := hP.surj.comp (MulAut.conj g).surjective
  have hker₀ : θ₀.ker ≤ Subgroup.center (Su K p f 4) := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ Subgroup.center (Su K p f 4) := hP.ker hx
    have h2' := (Subgroup.center (Su K p f 4)).normal_of_characteristic.conj_mem
      (g * x * g⁻¹) h1 g⁻¹
    simpa [mul_assoc] using h2'
  have h0 : ∀ A : Su K p f 2, σ (θ₀ (blockEmb K p f 4 2 0 (by norm_num) A)) =
      θ₀ (blockEmb K p f 4 2 0 (by norm_num) A) := by
    intro A
    apply hσR
    rw [hRg]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩
  have hnt : ∃ A : Su K p f 2, σ (θ₀ (blockEmb K p f 4 2 2 (by norm_num) A)) ≠
      θ₀ (blockEmb K p f 4 2 2 (by norm_num) A) := by
    obtain ⟨r', hr', hne⟩ := hσnt
    rw [hR'g] at hr'
    obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hr'
    exact ⟨A, hne⟩
  have key := su4_gen_std hK hp hq θ₀ hθ₀s hker₀ σ hσ2 h0 hnt
  have hψ₀y : θ₀ (negTwoSU K p f) = θ y' := by
    rw [hy'g]
    simp [hθ₀, MulAut.conj_apply]
  rw [hψ₀y] at key
  exact key

end WrapperU

section TagU

variable {p f : ℕ} [Fact p.Prime]


theorem e4_gen_su4 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X] [Finite X]
    {Φ : Set (Subgroup X)} (hΦ : HypOmegaMod p f Φ) {e : ℕ} (M : Ih8Model p f Φ .PSU 4 e)
    (hnt : ∀ K ∈ Φ, ∀ K' ∈ twinSet Φ K, K' = K)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) {A B : Subgroup X} (hA : A ∈ Φ)
    (hB : B ∈ omegaNbr Φ A) {x x' : X} (hxA : IsUniqueInvolution A x)
    (hxB : IsUniqueInvolution B x') (hcen : x * x' ∈ Subgroup.center X)
    (σ : MulAut X) (hσ2 : σ * σ = 1) (hσA : ∀ k ∈ A, σ k * k⁻¹ ∈ oddCoreOf A)
    (hσnt : ¬ ∀ k ∈ B, σ k * k⁻¹ ∈ oddCoreOf B) :
    Subgroup.closure ({g | σ g = g} ∪ {g | x' * g = g * x'} ∪
      {g | σ (x' * g * x'⁻¹) = g}) = ⊤ := by
  have hG2 : StatedLieTag.PSU ≠ .G2 := by decide
  have hD4 : StatedLieTag.PSU ≠ .trialityD4 := by decide
  have hnpsl : ¬ (StatedLieTag.PSU = .PSL ∧ (4 : ℕ) = 2) := by simp
  have hSperf : Group.IsPerfect (modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (ModelFacts.modelClauseZero .PSU 4 p e Fact.out trivial M.admissible).1.1
  obtain ⟨R, R', y, y', hR, hR', hAR, hBR, hy, hy', hP⟩ :=
    T8V.e4_pair_of_model hp2 hq hΦ M hG2 hD4 hnpsl hSperf hnt htrans hA hB hxA hxB hcen
  have hA0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR
  have hB0 := M.oddCore_eq_bot hΦ hp2 hq hG2 hD4 hR'
  have he : e = f := M.exp_eq_f hD4
  have hq' : 5 ≤ p ^ e := by rw [he]; exact hq
  have hf1 : 1 ≤ e := M.admissible.2.1
  have hK := CFSG.LieType.Universal.card_galoisField_two_mul p e hf1
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 M.admissible
  have hP' := hP.map_equiv φ
  have hRl := (hφ R).mp (M.cls_sub hR)
  have hRl' := (hφ R').mp (M.cls_sub hR')
  subst hAR hBR hy hy'
  have hσ2' : ∀ z, σ (σ z) = z := fun z => by
    have := congrArg (fun τ : MulAut X => τ z) hσ2
    simpa using this
  have hσR : ∀ r ∈ R.map φ.toMonoidHom, σ ((M.ψ.comp φ.symm.toMonoidHom) r) =
      (M.ψ.comp φ.symm.toMonoidHom) r := by
    rintro _ ⟨r, hr, rfl⟩
    have h := hσA (M.ψ r) (Subgroup.mem_map_of_mem _ hr)
    rw [hA0, Subgroup.mem_bot, mul_inv_eq_one] at h
    simpa using h
  have hσnt' : ∃ r ∈ R'.map φ.toMonoidHom, σ ((M.ψ.comp φ.symm.toMonoidHom) r) ≠
      (M.ψ.comp φ.symm.toMonoidHom) r := by
    by_contra hcon
    push Not at hcon
    apply hσnt
    rintro k ⟨r, hr, rfl⟩
    rw [hB0, Subgroup.mem_bot, mul_inv_eq_one]
    have := hcon (φ r) (Subgroup.mem_map_of_mem _ hr)
    simpa using this
  have key := su4_gen_of_pair hK hp2 hq' (M.ψ.comp φ.symm.toMonoidHom) hP' hRl hRl' σ hσ2'
    hσR hσnt'
  have hy'eq : (M.ψ.comp φ.symm.toMonoidHom) (φ y') = M.ψ y' := by simp
  rw [hy'eq] at key
  rw [eq_top_iff] at key ⊢
  refine key.trans (Subgroup.closure_mono ?_)
  intro g hg
  rcases hg with hg | hg
  · exact Or.inl (Or.inl hg)
  · exact Or.inr hg

end TagU

end CFSG.ClassicalInvolution.Asc77.T8W
