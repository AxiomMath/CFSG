module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.ClassTwo
public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Defs
public import CFSG.RankThree.PartTwo.Sec13.Item135CritProof
public import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniAutomorphismKernel
public import CFSG.LocalAnalysis.SectionRank.PRank
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Matrix CFSG.RankThree.SubgroupLists
open scoped commutatorElement

section Linear

variable {r : ℕ} [Fact r.Prime]

private theorem exists_matrixHom_of_addAction {G V ι : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod r) V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι (ZMod r) V)
    (σ : G →* AddMonoid.End V) :
    ∃ f : G →* GL ι (ZMod r), (∀ g, f g = 1 → σ g = 1) ∧ ∀ g,
      (f g : Matrix ι ι (ZMod r)) = LinearMap.toMatrix b b ((σ g : V →+ V).toZModLinearMap r) := by
  let τ : G →* Module.End (ZMod r) V :=
    { toFun := fun g => (σ g : V →+ V).toZModLinearMap r
      map_one' := by ext v; rw [map_one]; rfl
      map_mul' := fun g h => by ext v; rw [map_mul]; rfl }
  refine ⟨((LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMonoidHom.comp τ).toHomUnits,
    fun g hg => ?_, fun g => rfl⟩
  have h1 : LinearMap.toMatrixAlgEquiv b (τ g) = LinearMap.toMatrixAlgEquiv b 1 := by
    rw [map_one]
    exact congrArg Units.val hg
  have h2 := (LinearMap.toMatrixAlgEquiv b).injective h1
  ext v
  exact congrArg (fun φ : Module.End (ZMod r) V => φ v) h2

private theorem transpose_mul_mul_of_similitude {K V ι : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
    (β : LinearMap.BilinForm K V) (φ : V →ₗ[K] V) (μ : K)
    (h : ∀ u v, β (φ u) (φ v) = μ * β u v) :
    (LinearMap.toMatrix b b φ)ᵀ * LinearMap.BilinForm.toMatrix b β * LinearMap.toMatrix b b φ =
      μ • LinearMap.BilinForm.toMatrix b β := by
  rw [← LinearMap.BilinForm.toMatrix_comp (b := b) (c := b), ← map_smul]
  congr 1
  ext u v
  simp [h]

private theorem exists_basis_toMatrix_eq_spFourJ {K : Type} {V : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {β : LinearMap.BilinForm K V}
    (hβ : β.IsAlt) (hnd : β.Nondegenerate) (h4 : Module.finrank K V = 4) :
    ∃ b : Module.Basis (Fin 2 ⊕ Fin 2) K V, LinearMap.BilinForm.toMatrix b β = spFourJ K := by
  obtain ⟨m, b, hb⟩ := hβ.exists_basis_toMatrix_eq_J hnd
  have hm : m = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [h4, Fintype.card_sum, Fintype.card_fin] at this
    omega
  subst hm
  refine ⟨b.reindex (Equiv.sumComm _ _), ?_⟩
  ext i j
  have := congrFun₂ hb (Equiv.sumComm _ _ i) (Equiv.sumComm _ _ j)
  rw [LinearMap.BilinForm.toMatrix_apply] at this ⊢
  rcases i with i | i <;> rcases j with j | j <;>
    simpa [Module.Basis.reindex_apply, Matrix.J, Matrix.fromBlocks] using this

private theorem toAdd_map_ofAdd_eq_mul (ψ : Multiplicative (ZMod r) →* Multiplicative (ZMod r))
    (t : ZMod r) :
    Multiplicative.toAdd (ψ (Multiplicative.ofAdd t)) =
      t * Multiplicative.toAdd (ψ (Multiplicative.ofAdd 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, (n : ZMod r) = t := ⟨t.val, ZMod.natCast_zmod_val t⟩
  rw [show Multiplicative.ofAdd (n : ZMod r) = Multiplicative.ofAdd 1 ^ n by
    rw [← ofAdd_nsmul, nsmul_one], map_pow, toAdd_pow, nsmul_eq_mul]

end Linear

section CommForm

variable {D : Type*} [Group D]

private theorem exists_eq_ofMul_of (u : Additive (Abelianization D)) :
    ∃ x : D, u = Additive.ofMul (Abelianization.of x) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (s := commutator D) (Additive.toMul u)
  exact ⟨x, (congrArg Additive.ofMul hx).symm⟩

private noncomputable def abelAct (D : Type*) [Group D] :
    MulAut D →* AddMonoid.End (Additive (Abelianization D)) where
  toFun α := (Abelianization.map (α : D →* D)).toAdditive
  map_one' := by
    ext u
    obtain ⟨x, rfl⟩ := exists_eq_ofMul_of u
    rfl
  map_mul' α α' := by
    ext u
    obtain ⟨x, rfl⟩ := exists_eq_ofMul_of u
    rfl

private theorem mem_ker_of_abelAct_eq_one (N : Subgroup D) [N.Characteristic]
    (hle : commutator D ≤ N) {α : MulAut D} (h : abelAct D α = 1) :
    α ∈ (CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction N).ker := by
  rw [CFSG.RankThreeEvenClassification.Helpers.characteristicQuotientAction_mem_kernel_iff]
  intro x
  have hx : Abelianization.of (α x) = Abelianization.of x :=
    congrArg Additive.toMul (DFunLike.congr_fun h (Additive.ofMul (Abelianization.of x)))
  exact QuotientGroup.eq.mpr (hle ((QuotientGroup.eq (s := commutator D)).mp hx))

private def commD (x y : D) : commutator D :=
  ⟨⁅x, y⁆, Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

private theorem commD_mul_left (hcl : commutator D ≤ Subgroup.center D) (x x' y : D) :
    commD (x * x') y = commD x y * commD x' y := by
  apply Subtype.ext
  have hc : x * ⁅x', y⁆ = ⁅x', y⁆ * x := Subgroup.mem_center_iff.mp (hcl (commD x' y).2) x
  have hc2 : ⁅x, y⁆ * ⁅x', y⁆ = ⁅x', y⁆ * ⁅x, y⁆ :=
    Subgroup.mem_center_iff.mp (hcl (commD x' y).2) ⁅x, y⁆
  change ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆
  calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * (y * x⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]; group
    _ = ⁅x', y⁆ * x * (y * x⁻¹ * y⁻¹) := by rw [hc]
    _ = ⁅x', y⁆ * ⁅x, y⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x', y⁆ := hc2.symm

private theorem commD_mul_right (hcl : commutator D ≤ Subgroup.center D) (x y y' : D) :
    commD x (y * y') = commD x y * commD x y' := by
  apply Subtype.ext
  have hc : x * y * x⁻¹ * ⁅x, y'⁆ = ⁅x, y'⁆ * (x * y * x⁻¹) :=
    Subgroup.mem_center_iff.mp (hcl (commD x y').2) (x * y * x⁻¹)
  have hc2 : ⁅x, y⁆ * ⁅x, y'⁆ = ⁅x, y'⁆ * ⁅x, y⁆ :=
    Subgroup.mem_center_iff.mp (hcl (commD x y').2) ⁅x, y⁆
  change ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆
  calc ⁅x, y * y'⁆ = x * y * x⁻¹ * ⁅x, y'⁆ * y⁻¹ := by
          simp only [commutatorElement_def]; group
    _ = ⁅x, y'⁆ * (x * y * x⁻¹) * y⁻¹ := by rw [hc]
    _ = ⁅x, y'⁆ * ⁅x, y⁆ := by simp only [commutatorElement_def]; group
    _ = ⁅x, y⁆ * ⁅x, y'⁆ := hc2.symm

variable {r : ℕ}

private def commRight (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) (x : D) : D →* Multiplicative (ZMod r) where
  toFun y := e (commD x y)
  map_one' := by
    rw [show commD x 1 = 1 from Subtype.ext (commutatorElement_one_right x), map_one]
  map_mul' y y' := by rw [commD_mul_right hcl, map_mul]

private def commHom (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) :
    D →* (Abelianization D →* Multiplicative (ZMod r)) where
  toFun x := Abelianization.lift (commRight hcl e x)
  map_one' := Abelianization.hom_ext _ _ (MonoidHom.ext fun y => by
    change e (commD 1 y) = 1
    rw [show commD 1 y = 1 from Subtype.ext (commutatorElement_one_left y), map_one])
  map_mul' x x' := Abelianization.hom_ext _ _ (MonoidHom.ext fun y => by
    change e (commD (x * x') y) = e (commD x y) * e (commD x' y)
    rw [commD_mul_left hcl, map_mul])

private def commLift (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) :
    Abelianization D →* (Abelianization D →* Multiplicative (ZMod r)) :=
  Abelianization.lift (A := Abelianization D →* Multiplicative (ZMod r)) (commHom hcl e)

private def commForm (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) [Module (ZMod r) (Additive (Abelianization D))] :
    LinearMap.BilinForm (ZMod r) (Additive (Abelianization D)) :=
  LinearMap.mk₂ (ZMod r)
    (fun u v => Multiplicative.toAdd (commLift hcl e u.toMul v.toMul))
    (fun u u' v => by simp only [toMul_add, map_mul, MonoidHom.mul_apply, toAdd_mul])
    (fun c u v => ZMod.map_smul (F := Additive (Abelianization D) →+ ZMod r)
      (MonoidHom.toAdditiveLeft ((MonoidHom.eval (Additive.toMul v)).comp (commLift hcl e))) c u)
    (fun u v v' => by simp only [toMul_add, map_mul, toAdd_mul])
    (fun c u v => ZMod.map_smul (F := Additive (Abelianization D) →+ ZMod r)
      (MonoidHom.toAdditiveLeft (commLift hcl e u.toMul)) c v)

variable [Module (ZMod r) (Additive (Abelianization D))]

private theorem commForm_of (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) (x y : D) :
    commForm hcl e (Additive.ofMul (Abelianization.of x)) (Additive.ofMul (Abelianization.of y)) =
      Multiplicative.toAdd (e (commD x y)) := rfl

private theorem commForm_isAlt (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) : (commForm hcl e).IsAlt := by
  intro u
  obtain ⟨x, rfl⟩ := exists_eq_ofMul_of u
  rw [commForm_of, show commD x x = 1 from Subtype.ext (commutatorElement_self x), map_one,
    toAdd_one]

private theorem commForm_nondegenerate (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) (hZ : Subgroup.center D ≤ commutator D) :
    (commForm hcl e).Nondegenerate := by
  refine (LinearMap.IsAlt.isRefl (commForm_isAlt hcl e)).nondegenerate_iff_separatingLeft.mpr
    fun u hu => ?_
  obtain ⟨x, rfl⟩ := exists_eq_ofMul_of u
  have hc : ∀ y, y * x = x * y := fun y => by
    have h := hu (Additive.ofMul (Abelianization.of y))
    rw [commForm_of, toAdd_eq_zero, ← map_one e] at h
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val (e.injective h))).symm
  have hx := hZ (Subgroup.mem_center_iff.mpr hc)
  exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff (N := commutator D) x).mpr hx)

private theorem commForm_similitude [Fact r.Prime] (hcl : commutator D ≤ Subgroup.center D)
    (e : commutator D ≃* Multiplicative (ZMod r)) (α : MulAut D) :
    ∃ μ : ZMod r, ∀ u v, commForm hcl e (abelAct D α u) (abelAct D α v) =
      μ * commForm hcl e u v := by
  let ψ : Multiplicative (ZMod r) →* Multiplicative (ZMod r) :=
    e.toMonoidHom.comp ((MulAut.characteristic (commutator D) α).toMonoidHom.comp
      e.symm.toMonoidHom)
  refine ⟨Multiplicative.toAdd (ψ (Multiplicative.ofAdd 1)), fun u v => ?_⟩
  obtain ⟨x, rfl⟩ := exists_eq_ofMul_of u
  obtain ⟨y, rfl⟩ := exists_eq_ofMul_of v
  change Multiplicative.toAdd (e (commD (α x) (α y))) = _ * Multiplicative.toAdd (e (commD x y))
  have h1 : commD (α x) (α y) = MulAut.characteristic (commutator D) α (commD x y) :=
    Subtype.ext (map_commutatorElement α x y).symm
  have h2 : e (commD (α x) (α y)) =
      ψ (Multiplicative.ofAdd (Multiplicative.toAdd (e (commD x y)))) := by
    simp [ψ, h1]
  rw [h2, toAdd_map_ofAdd_eq_mul ψ, mul_comm]

private theorem exists_basis_similitude [Fact r.Prime] [Finite D]
    (hcl : commutator D ≤ Subgroup.center D) (h1 : Nat.card (commutator D) = r)
    (hZ : Subgroup.center D = commutator D) (h4 : Nat.card (D ⧸ commutator D) = r ^ 4) :
    ∃ b : Module.Basis (Fin 2 ⊕ Fin 2) (ZMod r) (Additive (Abelianization D)),
      ∀ α : MulAut D, ∃ μ : ZMod r,
        (LinearMap.toMatrix b b ((abelAct D α : _ →+ _).toZModLinearMap r))ᵀ * spFourJ (ZMod r) *
          LinearMap.toMatrix b b ((abelAct D α : _ →+ _).toZModLinearMap r) =
            μ • spFourJ (ZMod r) := by
  let e : commutator D ≃* Multiplicative (ZMod r) := mulEquivOfPrimeCardEq h1 (by simp)
  have : Module.Finite (ZMod r) (Additive (Abelianization D)) := Module.Finite.of_finite
  have hfr : Module.finrank (ZMod r) (Additive (Abelianization D)) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod r) (V := Additive (Abelianization D))
    rw [Nat.card_zmod] at h
    exact Nat.pow_right_injective (Fact.out : r.Prime).two_le (h.symm.trans h4)
  obtain ⟨b, hb⟩ := exists_basis_toMatrix_eq_spFourJ (commForm_isAlt hcl e)
    (commForm_nondegenerate hcl e hZ.le) hfr
  refine ⟨b, fun α => ?_⟩
  obtain ⟨μ, hμ⟩ := commForm_similitude hcl e α
  refine ⟨μ, ?_⟩
  rw [← hb]
  exact transpose_mul_mul_of_similitude b _ _ μ hμ

end CommForm

private theorem isPGroup_ker_of_abelAct {r : ℕ} [Fact r.Prime] {R : Type} [Group R] [Finite R]
    (hR : IsPGroup r R) (D : Subgroup R) [D.Characteristic]
    (hfix : IsPGroup r (fixingSubgroup (MulAut R) (D : Set R))) {B : Subgroup (MulAut R)}
    {H : Type*} [Group H] (f : B →* H)
    (hf : ∀ b, f b = 1 → abelAct D (MulAut.characteristic D b) = 1) : IsPGroup r f.ker := by
  let res : B →* MulAut D := (MulAut.characteristic D).comp B.subtype
  have hres : IsPGroup r res.ker := by
    refine (hfix.comap_of_injective B.subtype Subtype.val_injective).to_le fun b hb => ?_
    rw [Subgroup.mem_comap, mem_fixingSubgroup_iff]
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hb) ⟨x, hx⟩)
  have hF := CFSG.RankThreeEvenClassification.Helpers.frattini_automorphism_kernel_isPGroup r
    Fact.out (hR.to_subgroup D)
  have hle : commutator D ≤ frattini D := Subgroup.commutator_le.mpr fun x _ y _ =>
    CFSG.SectionRank.Ccomm.commutator_mem_frattini (hR.to_subgroup D) x y
  exact (hF.comap_of_ker_isPGroup res hres).to_le fun b hb =>
    mem_ker_of_abelAct_eq_one _ hle (hf b hb)

private theorem exists_linear_of_module {r : ℕ} [Fact r.Prime] {R : Type} [Group R]
    [Finite R] (hR : IsPGroup r R) (D : Subgroup R) [D.Characteristic]
    [Module (ZMod r) (Additive (Abelianization D))]
    (hfix : IsPGroup r (fixingSubgroup (MulAut R) (D : Set R))) (hexp : ∀ x : D, x ^ r = 1)
    (hcl : commutator D ≤ Subgroup.center D) (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3)
    (B : Subgroup (MulAut R)) :
    (∃ (d : ℕ) (_ : d ≤ 3) (f : B →* GL (Fin d) (ZMod r)), IsPGroup r f.ker) ∨
      ∃ f : B →* GL (Fin 2 ⊕ Fin 2) (ZMod r), IsPGroup r f.ker ∧
        ∀ b, ∃ μ : ZMod r, (f b : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
          (f b : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r) := by
  have : Module.Finite (ZMod r) (Additive (Abelianization D)) := Module.Finite.of_finite
  have hcard : Nat.card (D ⧸ commutator D) =
      r ^ Module.finrank (ZMod r) (Additive (Abelianization D)) := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod r) (V := Additive (Abelianization D))
    rwa [Nat.card_zmod] at h
  let σ : B →* AddMonoid.End (Additive (Abelianization D)) :=
    (abelAct D).comp ((MulAut.characteristic D).comp B.subtype)
  by_cases hd : Module.finrank (ZMod r) (Additive (Abelianization D)) ≤ 3
  · obtain ⟨f, hf, -⟩ := exists_matrixHom_of_addAction
      (Module.finBasis (ZMod r) (Additive (Abelianization D))) σ
    exact Or.inl ⟨_, hd, f, isPGroup_ker_of_abelAct hR D hfix f hf⟩
  · have h4 : r ^ 4 ≤ Nat.card (D ⧸ commutator D) := by
      rw [hcard]
      exact Nat.pow_le_pow_right (Fact.out : r.Prime).pos (by omega)
    obtain ⟨h1, hZ, h4'⟩ := card_commutator_eq_of_pRank_le_three Fact.out hexp hcl hrk h4
    obtain ⟨b, hb⟩ := exists_basis_similitude hcl h1 hZ h4'
    obtain ⟨f, hf, hfM⟩ := exists_matrixHom_of_addAction b σ
    exact Or.inr ⟨f, isPGroup_ker_of_abelAct hR D hfix f hf, fun g => by
      rw [hfM]
      exact hb _⟩

private theorem exists_linear_of_characteristic {r : ℕ} [Fact r.Prime] {R : Type} [Group R]
    [Finite R] (hR : IsPGroup r R) (D : Subgroup R) [D.Characteristic]
    (hfix : IsPGroup r (fixingSubgroup (MulAut R) (D : Set R))) (hexp : ∀ x : D, x ^ r = 1)
    (hcl : commutator D ≤ Subgroup.center D) (hrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 3)
    (B : Subgroup (MulAut R)) :
    (∃ (d : ℕ) (_ : d ≤ 3) (f : B →* GL (Fin d) (ZMod r)), IsPGroup r f.ker) ∨
      ∃ f : B →* GL (Fin 2 ⊕ Fin 2) (ZMod r), IsPGroup r f.ker ∧
        ∀ b, ∃ μ : ZMod r, (f b : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
          (f b : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r) := by
  have hW : ∀ u : Additive (Abelianization D), r • u = 0 := fun u => by
    obtain ⟨x, rfl⟩ := exists_eq_ofMul_of u
    rw [← ofMul_pow, ← map_pow, hexp x, map_one, ofMul_one]
  let : Module (ZMod r) (Additive (Abelianization D)) := AddCommGroup.zmodModule hW
  exact exists_linear_of_module hR D hfix hexp hcl hrk B

theorem exists_linear_of_pRank_le_three {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) {R : Type}
    [Group R] [Finite R] (hR : IsPGroup r R) (hrk : CFSG.Open.pRank r (⊤ : Subgroup R) ≤ 3)
    (B : Subgroup (MulAut R)) :
    (∃ (d : ℕ) (_ : d ≤ 3) (f : B →* GL (Fin d) (ZMod r)), IsPGroup r f.ker) ∨
      ∃ f : B →* GL (Fin 2 ⊕ Fin 2) (ZMod r), IsPGroup r f.ker ∧
        ∀ b, ∃ μ : ZMod r, (f b : Matrix _ _ (ZMod r))ᵀ * spFourJ (ZMod r) *
          (f b : Matrix _ _ (ZMod r)) = μ • spFourJ (ZMod r) := by
  obtain ⟨C, -, -, -, -, hDchar, -, hcomm, hexp, hfix, -⟩ :=
    CFSG.RankThree.PartTwo.Sec13.CritProof.exists_isThompsonCritical_omega hr2 hR
  set D := CFSG.RankThree.PartTwo.Sec13.CritProof.omegaOneIn r C
  have hexpD : ∀ x : D, x ^ r = 1 := fun x => Subtype.ext (by simp [hexp x x.2])
  have hclD : commutator D ≤ Subgroup.center D := by
    refine Subgroup.commutator_le.mpr fun x _ y _ =>
      Subgroup.mem_center_iff.mpr fun z => Subtype.ext ?_
    have hm := (Subgroup.mem_inf.mp
      (hcomm (Subgroup.commutator_mem_commutator x.2 (Subgroup.mem_top (y : R))))).2
    exact Subgroup.mem_centralizer_iff.mp hm z z.2
  have hrkD := (CFSG.SectionRank.pRank_top_le_of_injective (Fact.out : r.Prime).one_lt D.subtype
    D.subtype_injective).trans hrk
  exact exists_linear_of_characteristic hR D hfix hexpD hclD hrkD B

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
