module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PslBadEigen
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuHBlocks
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Matrix CFSG CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open scoped commutatorElement

section Abstract

variable {Xs T : Type} [Group Xs] [Group T]

theorem t6psub_isSolvable_fixSub (π : Xs →* T) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Xs) (α : MulAut Xs) (β : MulAut T)
    (hαβ : ∀ x, π (α x) = β (π x)) (hsolv : Group.IsSolvable ↥(fixSubgroup α)) :
    Group.IsSolvable ↥(Lemma510Ns.fixSub β) := by
  classical
  set C := fixSubgroup α with hC
  set X := Lemma510Ns.fixSub β with hX
  set X₀ : Subgroup T := C.map π with hX₀
  haveI : Group.IsSolvable ↥X₀ :=
    Group.isSolvable_of_surjective (f := π.subgroupMap C) (π.subgroupMap_surjective C)
  have hX₀X : X₀ ≤ X := map_fixSubgroup_le π hker α β hαβ
  have hcomm : ∀ a ∈ X, ∀ b ∈ X, ⁅a, b⁆ ∈ X₀ := by
    intro a ha b hb
    obtain ⟨xa, rfl⟩ := hπ a
    obtain ⟨xb, rfl⟩ := hπ b
    exact ⟨⁅xa, xb⁆, comm_mem_fixSubgroup π hker α β hαβ ha hb, map_commutatorElement π xa xb⟩
  set N : Subgroup ↥X := X₀.subgroupOf X with hN
  haveI : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hX₀X).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hX₀X).injective
  have hbase : derivedSeries ↥X 1 ≤ N := by
    rw [derivedSeries_succ, derivedSeries_zero]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [hN, Subgroup.mem_subgroupOf]
    exact hcomm a a.2 b b.2
  have hstep : ∀ k : ℕ, derivedSeries ↥X (k + 1) ≤ (derivedSeries ↥N k).map N.subtype := by
    intro k
    induction k with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hbase
    | succ k ih =>
      rw [derivedSeries_succ, derivedSeries_succ ↥N k, Subgroup.map_commutator]
      exact Subgroup.commutator_mono ih ih
  obtain ⟨d, hd⟩ := (inferInstance : Group.IsSolvable ↥N).solvable
  refine ⟨⟨d + 1, ?_⟩⟩
  have := hstep d
  rw [hd, Subgroup.map_bot] at this
  exact le_bot_iff.1 this

end Abstract

section Action

variable {ℓ f n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) (n)

@[expose] noncomputable def t6psub_actSU :
    primeFormUnitary h (idGram K n) →* MulAut ↥(gramSU h (idGram K n)) where
  toFun B := primeFormConjSU h (idGram K n) B
  map_one' := MulEquiv.ext fun g => Subtype.ext (by
    change ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (g : GL (Fin n) K) *
      ((1 : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ = g
    rw [Subgroup.coe_one, one_mul, inv_one, mul_one])
  map_mul' A B := MulEquiv.ext fun g => Subtype.ext (by
    change ((A * B : primeFormUnitary h (idGram K n)) : GL (Fin n) K) * (g : GL (Fin n) K) *
      ((A * B : primeFormUnitary h (idGram K n)) : GL (Fin n) K)⁻¹ = (A : GL (Fin n) K) *
        ((B : GL (Fin n) K) * g * (B : GL (Fin n) K)⁻¹) * (A : GL (Fin n) K)⁻¹
    rw [Subgroup.coe_mul]
    group)

variable {h n}

theorem t6psub_actSU_coe (B : primeFormUnitary h (idGram K n)) (x : ↥(gramSU h (idGram K n))) :
    ((t6psub_actSU h n B x : ↥(gramSU h (idGram K n))) : GL (Fin n) K) =
      (B : GL (Fin n) K) * (x : GL (Fin n) K) * (B : GL (Fin n) K)⁻¹ := rfl

theorem t6psub_hact (B : primeFormUnitary h (idGram K n)) (x : ↥(gramSU h (idGram K n))) :
    QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) (t6psub_actSU h n B x) =
      primeFormConjHom h (idGram K n) B
        (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n) x) :=
  (primeFormConjHom_mk h (idGram K n) B x).symm

@[expose] noncomputable def t6psub_toLin (B : primeFormUnitary h (idGram K n)) :
    LinearMap.GeneralLinearGroup K (Fin n → K) :=
  Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K)

theorem t6psub_mem_fix_iff (B : primeFormUnitary h (idGram K n)) (x : ↥(gramSU h (idGram K n))) :
    x ∈ fixSubgroup (t6psub_actSU h n B) ↔
      t6psuh_toLinSU h n x ∈ gl_centralizer (t6psub_toLin B) := by
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  have e : t6psuh_toLinSU h n x * t6psub_toLin B = t6psub_toLin B * t6psuh_toLinSU h n x ↔
      (x : GL (Fin n) K) * (B : GL (Fin n) K) = (B : GL (Fin n) K) * (x : GL (Fin n) K) := by
    change Matrix.GeneralLinearGroup.toLin (x : GL (Fin n) K) *
      Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) =
        Matrix.GeneralLinearGroup.toLin (B : GL (Fin n) K) *
          Matrix.GeneralLinearGroup.toLin (x : GL (Fin n) K) ↔ _
    rw [← map_mul, ← map_mul]
    exact Matrix.GeneralLinearGroup.toLin.injective.eq_iff
  rw [e]
  constructor
  · intro hα
    have h1 : (B : GL (Fin n) K) * x * (B : GL (Fin n) K)⁻¹ = x := congrArg Subtype.val hα
    calc (x : GL (Fin n) K) * (B : GL (Fin n) K)
        = ((B : GL (Fin n) K) * x * (B : GL (Fin n) K)⁻¹) * (B : GL (Fin n) K) := by rw [h1]
      _ = (B : GL (Fin n) K) * x := by group
  · intro hc
    apply Subtype.ext
    change (B : GL (Fin n) K) * x * (B : GL (Fin n) K)⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact hc.symm

theorem t6psub_toLinSU_mem_unitaryCentralizer (B : primeFormUnitary h (idGram K n))
    {x : ↥(gramSU h (idGram K n))} (hx : x ∈ fixSubgroup (t6psub_actSU h n B)) :
    t6psuh_toLinSU h n x ∈ unitaryCentralizer (idForm h n) (t6psub_toLin B) :=
  Subgroup.mem_inf.mpr ⟨sesqSpecialUnitaryGroup_le _ (t6psuh_toLinSU_mem_sesqSpecialUnitaryGroup x),
    (t6psub_mem_fix_iff B x).mp hx⟩

end Action

section Eigen

variable {K : Type} [Field K]

theorem t6psub_injective_of_glUnit {W : Type*} [AddCommGroup W] [Module K W]
    (u : LinearMap.GeneralLinearGroup K W) : Function.Injective (u : Module.End K W) := by
  intro a b hab
  have h1 : ((u⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)
      ((u : Module.End K W) a) = a := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  have h2 : ((u⁻¹ : LinearMap.GeneralLinearGroup K W) : Module.End K W)
      ((u : Module.End K W) b) = b := by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel]
    rfl
  rw [← h1, ← h2, hab]

theorem t6psub_glA_scalar_apply {n : ℕ} (ν : Kˣ) (v : Fin n → K) :
    ((Matrix.GeneralLinearGroup.toLin (Matrix.GeneralLinearGroup.scalar (Fin n) ν) :
      LinearMap.GeneralLinearGroup K (Fin n → K)) : Module.End K (Fin n → K)) v =
        (ν : K) • v := by
  show (Matrix.toLin' ((Matrix.GeneralLinearGroup.scalar (Fin n) ν : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K)) v = (ν : K) • v
  rw [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

theorem t6psub_exists_eigenspace_two {x : Module.End K (Fin 3 → K)} {b : K[X]}
    (hb : b ∈ primaryFactors x) (hm2 : 2 ≤ primaryMultiplicity x b) :
    ∃ c : K, 2 ≤ Module.finrank K (Module.End.eigenspace x c) := by
  haveI : Fact (Irreducible b) := ⟨irreducible_of_mem_primaryFactors hb⟩
  have hdeg : 1 ≤ b.natDegree := (Fact.out : Irreducible b).natDegree_pos
  have hrk := finrank_primaryComponent x (a := b)
  have hle : Module.finrank K (primaryComponent x b) ≤ 3 := by
    have := Submodule.finrank_le (primaryComponent x b)
    simpa using this
  have hd1 : b.natDegree = 1 := by
    rw [hrk] at hle
    by_contra hne
    have : 2 ≤ b.natDegree := by omega
    nlinarith
  have hmonic := monic_of_mem_primaryFactors hb
  have hform : b = X + C (b.coeff 0) := hmonic.eq_X_add_C hd1
  refine ⟨-(b.coeff 0), ?_⟩
  have hcomp : primaryComponent x b = Module.End.eigenspace x (-(b.coeff 0)) := by
    ext v
    rw [mem_primaryComponent, Module.End.mem_eigenspace_iff]
    conv_lhs => rw [hform]
    simp only [map_add, aeval_X, aeval_C, LinearMap.add_apply, Module.algebraMap_end_apply]
    constructor
    · intro h0
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h0
    · intro h0
      rw [neg_smul] at h0
      rw [h0]
      simp
  rw [← hcomp, hrk, hd1, one_mul]
  exact hm2

theorem t6psub_no_twist {G M : GL (Fin 3) K} {μ : Kˣ}
    (hGM : G * M = Matrix.GeneralLinearGroup.scalar (Fin 3) μ * M * G) {b : K[X]}
    (hb : b ∈ primaryFactors ((Matrix.GeneralLinearGroup.toLin G :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K)))
    (hm2 : 2 ≤ primaryMultiplicity ((Matrix.GeneralLinearGroup.toLin G :
      LinearMap.GeneralLinearGroup K (Fin 3 → K)) : Module.End K (Fin 3 → K)) b) : μ = 1 := by
  by_contra hμ
  obtain ⟨c, hc⟩ := t6psub_exists_eigenspace_two hb hm2
  have key : ∀ v, ((Matrix.GeneralLinearGroup.toLin G : LinearMap.GeneralLinearGroup K
        (Fin 3 → K)) : Module.End K (Fin 3 → K))
      (((Matrix.GeneralLinearGroup.toLin M : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) v) =
      (μ : K) • ((Matrix.GeneralLinearGroup.toLin M : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K))
        (((Matrix.GeneralLinearGroup.toLin G : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
          Module.End K (Fin 3 → K)) v) := by
    intro v
    have h1 := congrArg (fun u : GL (Fin 3) K =>
      ((Matrix.GeneralLinearGroup.toLin u : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
        Module.End K (Fin 3 → K)) v) hGM
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, t6psub_glA_scalar_apply] at h1
    exact h1
  exact eigen_twist_false _ (t6psub_injective_of_glUnit _) (by simp) (M :=
    ((Matrix.GeneralLinearGroup.toLin M : LinearMap.GeneralLinearGroup K (Fin 3 → K)) :
      Module.End K (Fin 3 → K))) (t6psub_injective_of_glUnit _) (μ := (μ : K))
    (fun h1 => hμ (Units.ext h1)) key hc

end Eigen

end CFSG.HardMathSupport.Dickson.Sec6.I1431
