module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SpModelsThree
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ThreeCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019SympInner
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.SympAut

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open Polynomial CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open scoped commutatorElement

section Pull

variable {r : ℕ} {K : Type} [Field K] [NeZero r]

private theorem mem_commutator_subtype {G : Type*} [Group G] {Γ : Subgroup G} {y : Γ}
    (hy : (y : G) ∈ ⁅Γ, Γ⁆) : y ∈ commutator Γ := by
  rw [← Subgroup.map_subtype_commutator] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rwa [show y = z from Subtype.ext hzy.symm]

private theorem map_commutator_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator, Subgroup.map_top,
    (MonoidHom.range_eq_top (f := e.toMonoidHom)).2 e.surjective]

theorem exists_three_of_modelThree {R : Type*} [Field R]
    {W : Submodule K (Fin r ⊕ Fin r → K)} [Module R W]
    {Γ : Subgroup (LinearMap.GeneralLinearGroup R W)}
    {A : Subgroup (StatedSp r K)} (φ : A ≃* Γ)
    (hφ : ∀ (g : A) (v : Fin r ⊕ Fin r → K) (hv : v ∈ W),
      ((((φ g : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : Fin r ⊕ Fin r → K) =
        spEnd (g : StatedSp r K) v)
    (hM : SpBlock.ModelThree Γ) :
    ∃ P : Subgroup (StatedSp r K), P ≤ ⁅A, A⁆ ∧ IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ j ∈ ⁅A, A⁆, u * j = j * u) → u = 1) ∧
      ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 → ∃ hu : u ∈ A,
        ((((φ ⟨u, hu⟩ : Γ) : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
        ∀ v ∈ W, ((spEnd u - 1) ^ 2 : Module.End K (Fin r ⊕ Fin r → K)) v = 0 := by
  obtain ⟨P₀, hP₀Γ, hP₀3, hP₀9, hP₀Z, hP₀q⟩ := hM
  have hP₀le : P₀ ≤ Γ := hP₀Γ.trans (Subgroup.commutator_le_self Γ)
  set ψ : Γ →* StatedSp r K := A.subtype.comp φ.symm.toMonoidHom with hψ
  have hψinj : Function.Injective ψ := A.subtype_injective.comp φ.symm.injective
  have hψcomm : ∀ y : Γ, y ∈ commutator Γ → ψ y ∈ ⁅A, A⁆ := by
    intro y hy
    rw [← Subgroup.map_subtype_commutator]
    refine ⟨φ.symm y, ?_, rfl⟩
    rw [← map_commutator_mulEquiv φ.symm]
    exact ⟨y, hy, rfl⟩
  refine ⟨(P₀.subgroupOf Γ).map ψ, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hψcomm y (mem_commutator_subtype (hP₀Γ (Subgroup.mem_subgroupOf.1 hy)))
  · exact (hP₀3.of_equiv (Subgroup.subgroupOfEquivOfLe hP₀le).symm).map ψ
  · rw [Subgroup.card_map_of_injective hψinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀le).toEquiv]
    exact hP₀9
  · rintro _ ⟨y, hy, rfl⟩ hcomm
    have hy1 : (y : LinearMap.GeneralLinearGroup R W) = 1 := by
      refine hP₀Z _ (Subgroup.mem_subgroupOf.1 hy) fun j hj => ?_
      have hjΓ : j ∈ Γ := Subgroup.commutator_le_self Γ hj
      have hz := hψcomm ⟨j, hjΓ⟩ (mem_commutator_subtype hj)
      have h1 := hcomm _ hz
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hψinj h1)
    rw [show y = 1 from Subtype.ext hy1, map_one]
  · rintro _ ⟨y, hy, rfl⟩ hcent hcube
    have hyP₀ : (y : LinearMap.GeneralLinearGroup R W) ∈ P₀ := Subgroup.mem_subgroupOf.1 hy
    have hcent' : ∀ w ∈ P₀, (y : LinearMap.GeneralLinearGroup R W) * w = w * y := by
      intro w hw
      have h1 := hcent (ψ ⟨w, hP₀le hw⟩) ⟨⟨w, hP₀le hw⟩, Subgroup.mem_subgroupOf.2 hw, rfl⟩
      rw [← map_mul, ← map_mul] at h1
      exact congrArg Subtype.val (hψinj h1)
    have hcube' : (y : LinearMap.GeneralLinearGroup R W) ^ 3 = 1 := by
      have h1 : ψ (y ^ 3) = ψ 1 := by rw [map_pow, hcube, map_one]
      rw [← Subgroup.coe_pow, hψinj h1, Subgroup.coe_one]
    have hq := hP₀q _ hyP₀ hcent' hcube'
    have hφy : φ ⟨ψ y, (φ.symm y).2⟩ = y := by
      rw [show (⟨ψ y, (φ.symm y).2⟩ : A) = φ.symm y from Subtype.ext rfl,
        MulEquiv.apply_symm_apply]
    refine ⟨(φ.symm y).2, by rw [hφy]; exact hq, fun v hv => ?_⟩
    have hsub : ∀ (z : W), (spEnd (ψ y) - 1) (z : Fin r ⊕ Fin r → K) =
        ((((y : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) - 1) z : Fin r ⊕ Fin r → K) := by
      intro z
      have h1 := hφ ⟨ψ y, (φ.symm y).2⟩ z z.2
      rw [hφy] at h1
      rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.sub_apply, Module.End.one_apply,
        Submodule.coe_sub]
      rw [← h1]
    rw [sq, Module.End.mul_apply, hsub ⟨v, hv⟩, hsub, ← Module.End.mul_apply, ← sq, hq,
      LinearMap.zero_apply, Submodule.coe_zero]

theorem exists_three_of_modelThree_top {R : Type*} [Field R]
    {W : Submodule K (Fin r ⊕ Fin r → K)} [Module R W] {A : Subgroup (StatedSp r K)}
    (φ : A ≃* LinearMap.GeneralLinearGroup R W)
    (hφ : ∀ (g : A) (v : Fin r ⊕ Fin r → K) (hv : v ∈ W),
      (((φ g : LinearMap.GeneralLinearGroup R W) : W →ₗ[R] W) ⟨v, hv⟩ : Fin r ⊕ Fin r → K) =
        spEnd (g : StatedSp r K) v)
    (hM : SpBlock.ModelThree (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
    ∃ P : Subgroup (StatedSp r K), P ≤ ⁅A, A⁆ ∧ IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
      (∀ u ∈ P, (∀ j ∈ ⁅A, A⁆, u * j = j * u) → u = 1) ∧
      ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 → ∃ hu : u ∈ A,
        ((((φ ⟨u, hu⟩ : LinearMap.GeneralLinearGroup R W)) : W →ₗ[R] W) - 1) ^ 2 = 0 ∧
        ∀ v ∈ W, ((spEnd u - 1) ^ 2 : Module.End K (Fin r ⊕ Fin r → K)) v = 0 := by
  obtain ⟨P, h1, h2, h3, h4, h5⟩ :=
    exists_three_of_modelThree (φ.trans Subgroup.topEquiv.symm) (fun g v hv => hφ g v hv) hM
  exact ⟨P, h1, h2, h3, h4, h5⟩

end Pull

section Blocks

variable {r : ℕ} {K : Type} [Field K] [NeZero r]

@[expose] def SpBlockThree (A : Subgroup (StatedSp r K)) : Prop :=
  ∃ P : Subgroup (StatedSp r K), P ≤ ⁅A, A⁆ ∧ IsPGroup 3 P ∧ 9 ≤ Nat.card P ∧
    (∀ u ∈ P, (∀ j ∈ ⁅A, A⁆, u * j = j * u) → u = 1) ∧
    ∀ u ∈ P, (∀ w ∈ P, u * w = w * u) → u ^ 3 = 1 → (spEnd u - 1) ^ 2 = 0

private theorem false_of_isQuasisimple_of_isSolvable'' {G : Type*} [Group G]
    (h : CFSG.IsQuasisimple G) (hs : Group.IsSolvable G) : False := by
  obtain ⟨hp, -, a, b, hab⟩ := h
  haveI : Nontrivial G := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨a * b, b * a, fun h => hab ?_⟩
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]
  haveI := hp
  exact Group.IsPerfect.not_isSolvable G hs

private theorem exists_ne_zero_sq_ne_one'' {F : Type*} [Field F] [Finite F] (hF : 4 ≤ Nat.card F) :
    ∃ l : F, l ≠ 0 ∧ l ^ 2 ≠ 1 := by
  classical
  by_contra h
  push Not at h
  haveI := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1, -1} := by
    intro l _
    by_cases hl : l = 0
    · simp [hl]
    · rcases sq_eq_one_iff.1 (h l hl) with h1 | h1 <;> simp [h1]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at h1
  have h3 : ({0, 1, -1} : Finset F).card ≤ 3 := Finset.card_le_three
  omega

private theorem nine_le_card_of_ne_three {F : Type*} [Field F] [Finite F] [CharP F 3]
    (h : Nat.card F ≠ 3) : 9 ≤ Nat.card F := by
  haveI := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 3
  rw [Nat.card_eq_fintype_card, hn] at h ⊢
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra hlt
    exact h (by rw [show (n : ℕ) = 1 by have := n.pos; omega, pow_one])
  calc 9 = 3 ^ 2 := by norm_num
    _ ≤ 3 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2

variable {ℓ f p : ℕ} {x : StatedSp r K} {a : StatedProj (StatedSp r K)}

theorem spBlockThree_fixed [Finite K] [CharP K 3] (blocks : SpPrimaryBlocks ℓ f p x a)
    (hsq : Squarefree (minpoly K (spEnd x))) (hX1 : (X - 1 : K[X]) ∈ primaryFactors (spEnd x))
    (hq : CFSG.IsQuasisimple ↥⁅spSupported x {X - 1}, spSupported x {X - 1}⁆) :
    SpBlockThree (spSupported x {X - 1}) := by
  classical
  obtain ⟨φ, hφ⟩ := blocks.fixedFactor hX1
  let W := primaryComponent (spEnd x) (X - 1)
  let B₁ := (spForm r K).restrict W
  have hB₁ : B₁.IsAlt := fun z => spForm_isAlt (z : Fin r ⊕ Fin r → K)
  have hBn : B₁.Nondegenerate := blocks.fixed_nondegenerate
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hX1)
  obtain ⟨n, b, hfin, hb⟩ := CFSG.RankThree.PartOne.KCAlternating.exists_isSymplecticBasis hB₁ hBn
  obtain ⟨s, hs, ⟨e⟩⟩ :=
    CFSG.RankThree.PartOne.KCSpIsotypic.exists_mulEquiv_sesqUnitaryGroup_statedSp hB₁ hBn
  have hns : n = s := by omega
  subst hns
  have hn1 : 1 ≤ n := by
    have := Module.finrank_pos (R := K) (M := W)
    omega
  have hK3 : 3 ≤ Nat.card K := by
    haveI := Fintype.ofFinite K
    obtain ⟨m, -, hm⟩ := FiniteField.card K 3
    rw [Nat.card_eq_fintype_card, hm]
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) m.pos)
  obtain ⟨hbll, hbrr, hblr⟩ := hb
  let i0 : Fin n := ⟨0, by omega⟩
  have hvw : B₁ (b (Sum.inl i0)) (b (Sum.inr i0)) = 1 := by rw [hblr, if_pos rfl]
  have hM : SpBlock.ModelThree (sesqUnitaryGroup B₁) := by
    by_cases h9 : 9 ≤ Nat.card K
    · obtain ⟨l, hl, hl2⟩ := exists_ne_zero_sq_ne_one'' (by omega : 4 ≤ Nat.card K)
      exact SpBlock.modelThree_alt_root hB₁ hvw hl hl2 h9
    · have hK : Nat.card K = 3 := by
        by_contra hne
        exact h9 (nine_le_card_of_ne_three hne)
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn : n = 1 := by omega
        subst hn
        apply false_of_isQuasisimple_of_isSolvable'' hq
        have hcard : Nat.card (spSupported x {X - 1}) = 2 ^ 3 * 3 ^ 1 := by
          rw [Nat.card_congr (φ.trans e).toEquiv, SymplecticFlag.card_statedSp, hK]
          norm_num [Finset.Icc_self]
        haveI : Group.IsSolvable (spSupported x {X - 1}) :=
          isSolvable_of_card_primeFactors_le_two (by
            rw [hcard, Nat.primeFactors_mul (by norm_num) (by norm_num),
              Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two,
              Nat.primeFactors_prime_pow (by norm_num) Nat.prime_three]
            exact (Finset.card_union_le _ _).trans (by simp))
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.inclusion (Subgroup.commutator_le_self (spSupported x {X - 1})) :
            ↥⁅spSupported x {X - 1}, spSupported x {X - 1}⁆ →* ↥(spSupported x {X - 1})))
          (Subgroup.inclusion_injective _)
      have hqs := CFSG.LieType.Universal.Symplectic.isQuasisimple n K hn1
        (Or.inr (Or.inl ⟨hK, hn2⟩))
      have hperf : ⁅sesqUnitaryGroup B₁, sesqUnitaryGroup B₁⁆ = sesqUnitaryGroup B₁ := by
        haveI := hqs.1
        haveI : Group.IsPerfect ↥(sesqUnitaryGroup B₁) :=
          Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
        rw [← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
          Subgroup.map_top, Subgroup.range_subtype]
      let i1 : Fin n := ⟨1, by omega⟩
      have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
      exact SpBlock.modelThree_alt_two hB₁ hperf hvw (v' := b (Sum.inl i1))
        (w' := b (Sum.inr i1)) (hbll i0 i1)
        (by rw [← LinearMap.IsAlt.neg hB₁ (b (Sum.inl i1)) (b (Sum.inr i0)), hblr,
          if_neg h01.symm, neg_zero])
        (by rw [hblr, if_pos rfl])
  obtain ⟨P, hPA, hP3, hP9, hPZ, hPq⟩ :=
    exists_three_of_modelThree (R := K) φ (fun g v hv => hφ g ⟨v, hv⟩) hM
  refine ⟨P, hPA, hP3, hP9, hPZ, fun u hu hcent hcube => ?_⟩
  obtain ⟨huA, -, hWq⟩ := hPq u hu hcent hcube
  apply eq_zero_of_forall_primaryComponent blocks.isInternal
  intro k hk v hv
  by_cases hkX : k = X - 1
  · subst hkX
    exact hWq v hv
  · exact sq_apply_eq_zero_of_not_mem huA hk (by simpa using hkX) hv

private theorem sq_inv_sub_one_eq_zero'' {R : Type*} [Ring R] (u : Rˣ)
    (hu : ((u : R) - 1) ^ 2 = 0) :
    (((u⁻¹ : Rˣ) : R) - 1) ^ 2 = 0 := by
  have hab : (u : R) * ((u⁻¹ : Rˣ) : R) = 1 := u.mul_inv
  have hba : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := u.inv_mul
  have e1 : ((u⁻¹ : Rˣ) : R) - 1 = -(((u : R) - 1) * ((u⁻¹ : Rˣ) : R)) := by
    rw [sub_mul, hab, one_mul, neg_sub]
  have e2 : ((u⁻¹ : Rˣ) : R) * ((u : R) - 1) = ((u : R) - 1) * ((u⁻¹ : Rˣ) : R) := by
    rw [mul_sub, sub_mul, hba, hab, mul_one, one_mul]
  calc (((u⁻¹ : Rˣ) : R) - 1) ^ 2
      = ((u : R) - 1) * (((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) * ((u⁻¹ : Rˣ) : R) := by
        rw [sq, e1, neg_mul_neg, mul_assoc, mul_assoc, mul_assoc]
    _ = ((u : R) - 1) ^ 2 * (((u⁻¹ : Rˣ) : R) * ((u⁻¹ : Rˣ) : R)) := by
        rw [e2, sq, mul_assoc, mul_assoc, mul_assoc]
    _ = 0 := by rw [hu, zero_mul]

private theorem sq_inv_sub_one_eq_zero_gl'' {E M : Type*} [CommRing E] [AddCommGroup M]
    [Module E M] (u : LinearMap.GeneralLinearGroup E M) (hu : ((u : M →ₗ[E] M) - 1) ^ 2 = 0) :
    (((u⁻¹ : LinearMap.GeneralLinearGroup E M) : M →ₗ[E] M) - 1) ^ 2 = 0 :=
  sq_inv_sub_one_eq_zero'' u hu

open CFSG.RankThree.PartOne.KCUnitary (blockApply blockApply_mem blockApply_blockApply
  blockApply_one blockGL)

private theorem gl_comm_of_le_one' {E : Type*} [Field E] {m : ℕ} (hm : m ≤ 1)
    (g g' : GL (Fin m) E) : g * g' = g' * g := by
  apply Units.ext
  haveI : Subsingleton (Fin m) := Fin.subsingleton_iff_le_one.2 hm
  ext i j
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply,
    Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, Subsingleton.elim j i, mul_comm]

private theorem nine_le_of_dvd_sub_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq3 : q = 3)
    (hdvd : p ∣ q - 1) : False := by
  subst hq3
  have : p ∣ 2 := hdvd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem spBlockThree_paired [Finite K] [CharP K 3] [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    (blocks : SpPrimaryBlocks ℓ f p x a) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : primaryFactors (spEnd x)) (hne : (h : K[X]) ≠ reciprocalPolynomial (h : K[X]))
    (hnc : ¬ ∀ g ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])},
      ∀ g' ∈ spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}, g * g' = g' * g) :
    SpBlockThree (spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])}) := by
  have P := blocks.paired h hne
  obtain ⟨φ, hφ1, hφ2⟩ := P.factor
  haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot (h : K[X])) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (h : K[X]))).injective 3
  obtain ⟨ψ⟩ := P.matrixFactor
  have hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) := by
    by_contra hlt
    push Not at hlt
    apply hnc
    intro g hg g' hg'
    have h1 := gl_comm_of_le_one' (by omega) (ψ ⟨g, hg⟩) (ψ ⟨g', hg'⟩)
    rw [← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (ψ.injective h1)
  have hE9 : 9 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
    refine nine_le_card_of_ne_three fun h3 => ?_
    have hdvd := P.dvd
    rw [← P.card_field, h3] at hdvd
    exact nine_le_of_dvd_sub_one hp hp2 rfl hdvd
  obtain ⟨l, hl, hl2⟩ :=
    exists_ne_zero_sq_ne_one'' (by omega : 4 ≤ Nat.card (AdjoinRoot (h : K[X])))
  let b : Module.Basis (Fin (primaryMultiplicity (spEnd x) (h : K[X]))) (AdjoinRoot (h : K[X]))
      (primaryComponent (spEnd x) (h : K[X])) := Module.finBasisOfFinrankEq _ _ rfl
  have hij : (⟨0, by omega⟩ : Fin (primaryMultiplicity (spEnd x) (h : K[X]))) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  have hM := SpBlock.modelThree_lin b hij hl hl2 hE9
  obtain ⟨Pg, hPA, hP3, hP9, hPZ, hPq⟩ :=
    exists_three_of_modelThree_top φ (fun g v hv => hφ1 g v hv) hM
  refine ⟨Pg, hPA, hP3, hP9, hPZ, fun u hu hcent hcube => ?_⟩
  obtain ⟨huA, hγ', hWq⟩ := hPq u hu hcent hcube
  set uA : spSupported x {(h : K[X]), reciprocalPolynomial (h : K[X])} := ⟨u, huA⟩ with huA'
  have hcommx : Commute (spEnd u) (spEnd x) := by
    have h1 := (mem_spSupported.1 huA).1
    change spEnd u * spEnd x = spEnd x * spEnd u
    have hmul : ∀ a b : StatedSp r K, spEnd (a * b) = spEnd a * spEnd b := fun a b => by
      change ((spLin r K (a * b) : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) = _
      rw [map_mul, Units.val_mul]
    rw [← hmul, ← hmul, h1]
  have hGi : ((((φ uA)⁻¹ : blockGL (spEnd x) (h : K[X])) :
      Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) - 1) ^ 2 = 0 :=
    sq_inv_sub_one_eq_zero_gl'' (φ uA) hγ'
  have key : ∀ y ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])),
      ∀ v' : primaryComponent (spEnd x) (h : K[X]),
      spForm r K (v' : Fin r ⊕ Fin r → K) ((spEnd u - 1) y) =
        spForm r K ((((((φ uA)⁻¹ : blockGL (spEnd x) (h : K[X])) :
          Module.End (AdjoinRoot (h : K[X])) (primaryComponent (spEnd x) (h : K[X]))) - 1) v' :
            primaryComponent (spEnd x) (h : K[X])) : Fin r ⊕ Fin r → K) y := by
    intro y hy v'
    have h1 := hφ2 uA (blockApply (φ uA)⁻¹ v' v'.2) y (blockApply_mem _ _ _) hy
    rw [blockApply_blockApply, mul_inv_cancel, blockApply_one] at h1
    rw [LinearMap.sub_apply, Module.End.one_apply, map_sub, h1, LinearMap.sub_apply,
      Module.End.one_apply, Submodule.coe_sub, map_sub, LinearMap.sub_apply]
    rfl
  apply eq_zero_of_forall_primaryComponent blocks.isInternal
  intro k hk w hw
  by_cases hkh : k = h
  · subst hkh
    exact hWq w hw
  by_cases hks : k = reciprocalPolynomial (h : K[X])
  · subst hks
    have hpres : ∀ y ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])),
        (spEnd u - 1) y ∈ primaryComponent (spEnd x) (reciprocalPolynomial (h : K[X])) := by
      intro y hy
      exact Submodule.sub_mem _ (apply_mem_primaryComponent hcommx hy) hy
    apply P.perfect_right _ (by rw [sq, Module.End.mul_apply]; exact hpres _ (hpres w hw))
    intro v hv
    rw [sq, Module.End.mul_apply, key _ (hpres w hw) ⟨v, hv⟩, key w hw, ← Module.End.mul_apply,
      ← sq, hGi, LinearMap.zero_apply, Submodule.coe_zero, map_zero, LinearMap.zero_apply]
  · exact sq_apply_eq_zero_of_not_mem huA hk (by simp [hkh, hks]) hw

theorem spBlockThree_selfDual [Finite K] [CharP K 3] [FiniteDimensional K (Fin r ⊕ Fin r → K)]
    (blocks : SpPrimaryBlocks ℓ f p x a) (hp : p.Prime) (hp2 : p ≠ 2)
    (h : primaryFactors (spEnd x)) (hX : (h : K[X]) ≠ X - 1)
    (hsd : reciprocalPolynomial (h : K[X]) = h)
    (hnc : ¬ ∀ g ∈ spSupported x {(h : K[X])}, ∀ g' ∈ spSupported x {(h : K[X])},
      g * g' = g' * g) :
    SpBlockThree (spSupported x {(h : K[X])}) := by
  haveI : Fact (Irreducible (h : K[X])) := ⟨irreducible_of_mem_primaryFactors h.2⟩
  haveI : Finite (AdjoinRoot (h : K[X])) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot (h : K[X])) 3 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot (h : K[X]))).injective 3
  obtain ⟨d, -, hdvd, σ, -, -, -, -, -, hE, hbar, Hf, hHs, -, ⟨η, hη0, hη, -⟩, ⟨e, he⟩, φ, hφ⟩ :=
    (blocks.selfDual h hX hsd).exists_half
  have hm : 2 ≤ primaryMultiplicity (spEnd x) (h : K[X]) := by
    by_contra hlt
    push Not at hlt
    apply hnc
    intro g hg g' hg'
    have hcommEnd : ∀ F F' : Module.End (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X])), F * F' = F' * F := by
      intro F F'
      apply (LinearMap.toMatrixAlgEquiv e).injective
      rw [map_mul, map_mul]
      haveI : Subsingleton (Fin (primaryMultiplicity (spEnd x) (h : K[X]))) :=
        Fin.subsingleton_iff_le_one.2 (by omega)
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_subsingleton _ i,
        Fintype.sum_subsingleton _ i, Subsingleton.elim j i, mul_comm]
    have h1 : (φ ⟨g, hg⟩ : LinearMap.GeneralLinearGroup (AdjoinRoot (h : K[X]))
        (primaryComponent (spEnd x) (h : K[X]))) * φ ⟨g', hg'⟩ = φ ⟨g', hg'⟩ * φ ⟨g, hg⟩ :=
      Units.ext (hcommEnd _ _)
    have h2' : φ (⟨g, hg⟩ * ⟨g', hg'⟩) = φ (⟨g', hg'⟩ * ⟨g, hg⟩) := by
      rw [map_mul, map_mul]
      exact Subtype.ext h1
    exact congrArg Subtype.val (φ.injective h2')
  haveI : Finite hE.fixedField := Finite.of_injective _ Subtype.val_injective
  haveI : CharP hE.fixedField 3 := inferInstance
  have hE₀9 : 9 ≤ Nat.card hE.fixedField := by
    refine nine_le_card_of_ne_three fun h3 => ?_
    rw [UnitaryFieldData.card_fixedField, pow_mul] at h3
    rw [h3] at hdvd
    have : p ∣ 4 := hdvd
    have h4 : p ∣ 2 ^ 2 := this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  obtain ⟨l₀, hl₀, hl₀2⟩ := exists_ne_zero_sq_ne_one'' (by omega : 4 ≤ Nat.card hE.fixedField)
  have hm1 : (-1 : AdjoinRoot (h : K[X])) ∈ hE.fixedField := by
    rw [hE.mem_fixedField, map_neg, map_one]
  obtain ⟨μ, hμ'⟩ := hE.normHom_surjective ⟨-1, hm1⟩
  have hμ : μ * hE.bar μ = -1 := congrArg Subtype.val hμ'
  set i₀ : Fin (primaryMultiplicity (spEnd x) (h : K[X])) := ⟨0, by omega⟩
  set i₁ : Fin (primaryMultiplicity (spEnd x) (h : K[X])) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  have h00 : Hf (e i₀) (e i₀) = 1 := by rw [he, if_pos rfl]
  have h11 : Hf (e i₁) (e i₁) = 1 := by rw [he, if_pos rfl]
  have h01' : Hf (e i₀) (e i₁) = 0 := by rw [he, if_neg h01]
  have h10' : Hf (e i₁) (e i₀) = 0 := by rw [he, if_neg h01.symm]
  have h2E : (2 : AdjoinRoot (h : K[X])) ≠ 0 := by
    intro h0
    have h3 : (3 : AdjoinRoot (h : K[X])) = 0 := by
      exact_mod_cast CharP.cast_eq_zero (AdjoinRoot (h : K[X])) 3
    have : (1 : AdjoinRoot (h : K[X])) = 0 := by linear_combination h3 - h0
    exact one_ne_zero this
  have hvv : Hf (e i₀ + μ • e i₁) (e i₀ + μ • e i₁) = 0 := by
    simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    linear_combination hμ
  have hww : Hf ((2 : AdjoinRoot (h : K[X]))⁻¹ • (e i₀ - μ • e i₁))
      ((2 : AdjoinRoot (h : K[X]))⁻¹ • (e i₀ - μ • e i₁)) = 0 := by
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, map_smul,
      smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    linear_combination (hE.bar (2 : AdjoinRoot (h : K[X]))⁻¹ * (2 : AdjoinRoot (h : K[X]))⁻¹) * hμ
  have hvw : Hf (e i₀ + μ • e i₁) ((2 : AdjoinRoot (h : K[X]))⁻¹ • (e i₀ - μ • e i₁)) = 1 := by
    simp only [map_add, map_sub, map_smulₛₗ, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, map_smul, smul_eq_mul, h00, h11, h01', h10', RingHom.id_apply]
    field_simp
    linear_combination -hμ
  have hM := SpBlock.modelThree_herm hHs hvv hww hvw hE.fixedField
    (fun t ht => (hE.mem_fixedField).1 ht) hE₀9 (l := (l₀ : AdjoinRoot (h : K[X]))) l₀.2
    (fun h0 => hl₀ (Subtype.ext h0))
    (fun h1 => hl₀2 (Subtype.ext (by simpa using h1))) hη0 hη
  obtain ⟨Pg, hPA, hP3, hP9, hPZ, hPq⟩ := exists_three_of_modelThree φ (fun g v hv => hφ g v hv) hM
  refine ⟨Pg, hPA, hP3, hP9, hPZ, fun u hu hcent hcube => ?_⟩
  obtain ⟨huA, -, hWq⟩ := hPq u hu hcent hcube
  apply eq_zero_of_forall_primaryComponent blocks.isInternal
  intro k hk w hw
  by_cases hkh : k = h
  · subst hkh
    exact hWq w hw
  · exact sq_apply_eq_zero_of_not_mem huA hk (by simpa using hkh) hw

end Blocks

section Main

variable {r : ℕ} {K : Type} [Field K] [Finite K]

private theorem sq_eq_one_of_mem_ker_proj' [NeZero r] {s : StatedSp r K}
    (hs : s ∈ (proj r K).ker) : s ^ 2 = 1 := by
  rw [SymplecticHigher.ker_proj] at hs
  obtain ⟨c, hc2, hc⟩ := CFSG.RankThree.PartOne.KCSpComm.exists_scalar_of_mem_spScalars hs
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hc2, map_one, Subgroup.coe_one]

theorem s2019FixCentralizes_conj_proj_sp_three {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 3 ^ f)
    (hr : 1 ≤ r) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) (x : StatedSp r K)
    (hx : x ^ p = 1) (hx1 : x ≠ 1) : S2019FixCentralizes p (MulAut.conj (proj r K x)) := by
  classical
  haveI : NeZero r := ⟨by omega⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 3 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  intro L hL T hT hLT
  have hperf : ⁅L, L⁆ = L := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL
  have hle := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfectInLayer_conj_sp
    Nat.prime_three hf hK hr hp hp2 hp3 x hx L hL.1 hperf
  obtain ⟨hcomp, -⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hL hle
  have hZc : (proj r K).ker ≤ Subgroup.center (StatedSp r K) := by
    rw [SymplecticHigher.ker_proj]
    exact SymplecticHigher.spScalars_le_center
  have ha1 : proj r K x ≠ 1 := by
    intro h
    apply hx1
    have h2x := sq_eq_one_of_mem_ker_proj' (MonoidHom.mem_ker.2 h)
    have hdvd : orderOf x ∣ Nat.gcd 2 p :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2x) (orderOf_dvd_of_pow_eq_one hx)
    rw [(Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2), Nat.dvd_one, orderOf_eq_one_iff]
      at hdvd
    exact hdvd
  have ha : orderOf (proj r K x) = p := orderOf_eq_prime (by rw [← map_pow, hx, map_one]) ha1
  have hxp : orderOf x = p := orderOf_eq_prime hx hx1
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_three hf hK hp hp2
    hp3 hr _ ha).2 x rfl hxp
  have hpK : (p : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K 3] at h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hsq := (altPrimaryData_spLin hpK hx).squarefree
  haveI : Finite (reciprocalOrbits (spEnd x)) :=
    (Set.Finite.image _ (Finset.finite_toSet _)).to_subtype
  obtain ⟨hcomm, -, hjoin⟩ := blocks.directProduct
  have hp3' : 3 ≤ p := by have := hp.two_le; omega
  have hqf : 2 ≤ 3 ^ f := le_trans (by omega) (Nat.le_self_pow (by omega) 3)
  obtain ⟨O, hOq, hLO⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.components_conj_of_orbit_family
    (proj r K) SymplecticHigher.proj_surjective hZc x
    (fun O : reciprocalOrbits (spEnd x) => spSupported x (O : Set K[X]))
    (fun i j hij a ha b hb => hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) a ha b hb)
    hjoin (fun O =>
      CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.quasisimple_or_solvable_spSupported
        hp3' hqf hsq blocks O) L hcomp
  have hnc : ¬ ∀ a ∈ spSupported x (O : Set K[X]), ∀ b ∈ spSupported x (O : Set K[X]),
      a * b = b * a := by
    intro hc
    have hbot : ⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hc a ha b hb).symm
    obtain ⟨-, -, a, b, hab⟩ := hOq
    apply hab
    haveI : Subsingleton ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ := by
      rw [hbot]
      infer_instance
    haveI : Subsingleton (↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆ ⧸
      Subgroup.center ↥⁅spSupported x (O : Set K[X]), spSupported x (O : Set K[X])⁆) :=
      Quotient.instSubsingletonQuotient _
    exact Subsingleton.elim _ _
  obtain ⟨P, hPJ, hP3, hP9, hPZ, hPq⟩ : SpBlockThree (spSupported x (O : Set K[X])) := by
    obtain ⟨O, h, hh, rfl⟩ := O
    have hh' : h ∈ primaryFactors (spEnd x) := Finset.mem_coe.1 hh
    by_cases hX : h = X - 1
    · subst hX
      have hO : ({X - 1, reciprocalPolynomial (X - 1)} : Set K[X]) = {X - 1} := by
        rw [reciprocalPolynomial_X_sub_one, Set.pair_eq_singleton]
      change SpBlockThree (spSupported x {X - 1, reciprocalPolynomial (X - 1)})
      have hOq2 : CFSG.IsQuasisimple ↥⁅spSupported x {X - 1, reciprocalPolynomial (X - 1)},
          spSupported x {X - 1, reciprocalPolynomial (X - 1)}⁆ := hOq
      rw [hO] at hOq2 ⊢
      exact spBlockThree_fixed blocks hsq hh' hOq2
    · by_cases hsd : reciprocalPolynomial h = h
      · have hO : ({h, reciprocalPolynomial h} : Set K[X]) = {h} := by
          rw [hsd, Set.pair_eq_singleton]
        change SpBlockThree (spSupported x {h, reciprocalPolynomial h})
        have hnc2 : ¬ ∀ g ∈ spSupported x {h, reciprocalPolynomial h},
            ∀ g' ∈ spSupported x {h, reciprocalPolynomial h}, g * g' = g' * g := hnc
        rw [hO] at hnc2 ⊢
        exact spBlockThree_selfDual blocks hp hp2 ⟨h, hh'⟩ hX hsd hnc2
      · exact spBlockThree_paired blocks hp hp2 ⟨h, hh'⟩ (Ne.symm hsd) hnc
  exact commutator_eq_bot_of_quadratic_lift_three hcomp.2.2 hLT hT (proj r K)
    SymplecticHigher.proj_surjective hZc (spLin r K) spLin_injective
    (Subgroup.isPerfect_iff.mp hOq.1) hLO.symm hPJ hP3 hP9 hPZ hPq

theorem s2019SympInner_three : S2019SympInner (· = 3) := by
  intro p q hp hp2 hq hq2 hqp hq3 G _ n f hG a ha
  change q = 3 at hq3
  subst hq3
  obtain ⟨⟨-, hf, hn, -⟩, K, _, _, hK, ⟨e⟩⟩ := hG
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  refine s2019FixCentralizes_of_congr hp e (MulAut.conj a) ?_
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]
  have hea : (e a) ^ p = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨x, hx, hxp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.exists_proj_eq_pow_eq_one_sp
      (by omega) hp hp2 hea
  rw [← hx]
  by_cases hx1 : x = 1
  · subst hx1
    rw [map_one, map_one]
    have hne : ¬(n = 2 ∧ Nat.card K = 2) := by
      rintro ⟨-, h2⟩
      rw [hK] at h2
      have h1 : 3 ∣ 2 := by
        rw [← h2]
        exact dvd_pow_self 3 (by omega)
      omega
    obtain ⟨hs, hperf⟩ := CFSG.RankThree.PartOne.KCSpComm.simple_perfect_statedProj (k := K) hn hne
    exact s2019FixCentralizes_one_of_isSimpleGroup hs hperf hp
  · exact s2019FixCentralizes_conj_proj_sp_three hf hK (by omega) hp hp2 hqp.symm x hxp hx1

theorem s2019FactClassicalOn_symplectic_proved : S2019FactClassicalOn .symplectic :=
  s2019FactClassicalOn_symplectic_of_three s2019SympInner_three

end Main

end CFSG.LocalAnalysis.GLTheoremA.S2019
