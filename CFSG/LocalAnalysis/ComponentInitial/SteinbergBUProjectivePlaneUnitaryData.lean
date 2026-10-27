module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormTransport
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneTransport

public section

namespace CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane

variable {p f : ℕ} {K : Type} [Field K]

@[expose] def linearSimilitudes (h : UnitaryFieldData p f K) (r ε : ℕ) :
    Subgroup (GL (HypIndex r ε) K) :=
  (semilinearSimilitudes h r ε).comap SemidirectProduct.inl

variable {r ε : ℕ}

theorem mem_linearSimilitudes {h : UnitaryFieldData p f K} {A : GL (HypIndex r ε) K} :
    A ∈ linearSimilitudes h r ε ↔ ∃ μ : K, μ ≠ 0 ∧ h.bar μ = μ ∧
      ((A : Matrix (HypIndex r ε) (HypIndex r ε) K).map h.bar)ᵀ * hypGram r ε K * A =
        μ • hypGram r ε K :=
  Iff.rfl

variable (h : UnitaryFieldData p f K)

@[expose] def linearToSemilinear : linearSimilitudes h r ε →* semilinearSimilitudes h r ε :=
  SemidirectProduct.inl.subgroupComap (semilinearSimilitudes h r ε)

theorem linearToSemilinear_left (A : linearSimilitudes h r ε) :
    (linearToSemilinear h A : SemiGL (HypIndex r ε) K).left = A :=
  rfl

theorem linearToSemilinear_right (A : linearSimilitudes h r ε) :
    (linearToSemilinear h A : SemiGL (HypIndex r ε) K).right = 1 :=
  rfl

variable (hr : 1 ≤ r) (hε : ε ≤ 1)

@[expose] noncomputable def linearSimAut : linearSimilitudes h r ε →* MulAut (hypPSU h r ε) :=
  (semilinearAutHom h hr hε).comp (linearToSemilinear h)

@[expose] noncomputable def linearSimAutGroup : Subgroup (MulAut (hypPSU h r ε)) :=
  (linearSimAut h hr hε).range

theorem linearSimAut_mem (A : linearSimilitudes h r ε) :
    linearSimAut h hr hε A ∈ linearSimAutGroup h hr hε :=
  ⟨A, rfl⟩

theorem conj_mem_hypSU_of_linear (A : linearSimilitudes h r ε) (g : hypSU h r ε) :
    (A : GL (HypIndex r ε) K) * g * (A : GL (HypIndex r ε) K)⁻¹ ∈ hypSU h r ε := by
  have := conj_mem_hypSU (linearToSemilinear h A).2 g
  rwa [linearToSemilinear_right, map_one, MulAut.one_apply] at this

theorem linearSimAut_apply (A : linearSimilitudes h r ε) (g : hypSU h r ε) :
    linearSimAut h hr hε A (hypProj h r ε g) =
      hypProj h r ε ⟨_, conj_mem_hypSU_of_linear h A g⟩ := by
  rw [linearSimAut, MonoidHom.comp_apply, semilinearAutHom_apply]
  congr 2

theorem linearSimAut_eq_one_iff (hn : 3 ≤ 2 * r + ε) (A : linearSimilitudes h r ε) :
    linearSimAut h hr hε A = 1 ↔
      ∃ c : Kˣ, (A : GL (HypIndex r ε) K) = GeneralLinearGroup.scalar _ c := by
  rw [linearSimAut, MonoidHom.comp_apply, semilinearAutHom_eq_one_iff h hr hε hn]
  exact ⟨fun ⟨_, hc⟩ => hc, fun hc => ⟨rfl, hc⟩⟩

abbrev semilinearFieldPart : semilinearSimilitudes h r ε →* (K ≃+* K) :=
  SemidirectProduct.rightHom.comp (semilinearSimilitudes h r ε).subtype

variable (hn : 3 ≤ 2 * r + ε) (hq : ¬(2 * r + ε = 3 ∧ p ^ f = 2))

include hn in
theorem ker_semilinearAutHom_le :
    (semilinearAutHom h hr hε).ker ≤ (semilinearFieldPart h).ker := fun x hx =>
  ((semilinearAutHom_eq_one_iff h hr hε hn x).mp hx).1

@[expose] noncomputable def autFieldPart : MulAut (hypPSU h r ε) →* (K ≃+* K) :=
  (semilinearAutHom h hr hε).liftOfSurjective
    (semilinearAutHom_surjective_of_admissible h hr hε hn hq)
    ⟨semilinearFieldPart h, ker_semilinearAutHom_le h hr hε hn⟩

theorem autFieldPart_apply (x : semilinearSimilitudes h r ε) :
    autFieldPart h hr hε hn hq (semilinearAutHom h hr hε x) =
      (x : SemiGL (HypIndex r ε) K).right :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x

theorem ker_autFieldPart : (autFieldPart h hr hε hn hq).ker = linearSimAutGroup h hr hε := by
  ext α
  constructor
  · intro hα
    obtain ⟨x, rfl⟩ := semilinearAutHom_surjective_of_admissible h hr hε hn hq α
    rw [MonoidHom.mem_ker, autFieldPart_apply] at hα
    have hx : SemidirectProduct.inl (x : SemiGL (HypIndex r ε) K).left =
        (x : SemiGL (HypIndex r ε) K) := SemidirectProduct.ext rfl hα.symm
    have hxl : (x : SemiGL (HypIndex r ε) K).left ∈ linearSimilitudes h r ε := by
      change SemidirectProduct.inl (x : SemiGL (HypIndex r ε) K).left ∈ semilinearSimilitudes h r ε
      rw [hx]
      exact x.2
    refine ⟨⟨_, hxl⟩, ?_⟩
    rw [linearSimAut, MonoidHom.comp_apply]
    exact congrArg _ (Subtype.ext hx)
  · rintro ⟨A, rfl⟩
    rw [MonoidHom.mem_ker, linearSimAut, MonoidHom.comp_apply, autFieldPart_apply]
    rfl

include hn hq in
theorem linearSimAutGroup_normal : (linearSimAutGroup h hr hε).Normal := by
  rw [← ker_autFieldPart h hr hε hn hq]
  exact MonoidHom.normal_ker _

include h in
theorem unitaryFieldAut_isCyclic : IsCyclic (K ≃+* K) := by
  obtain ⟨σ, -, -, hσ, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      h.prime (by have := h.one_le; omega) h.card
  exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨σ, hσ⟩

include hn hq in
theorem commutator_mem_linearSimAutGroup (α β : MulAut (hypPSU h r ε)) :
    α * β * α⁻¹ * β⁻¹ ∈ linearSimAutGroup h hr hε := by
  rw [← ker_autFieldPart h hr hε hn hq, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv,
    map_inv]
  have := unitaryFieldAut_isCyclic h
  have hc : ∀ a b : K ≃+* K, a * b = b * a := fun a b =>
    (IsCyclic.commGroup (α := K ≃+* K)).mul_comm a b
  rw [hc (autFieldPart h hr hε hn hq α), mul_inv_cancel_right, mul_inv_cancel]

include hn in
theorem linearSimAut_eq_one_iff_reindex {n : ℕ} (e : HypIndex r ε ≃ Fin n)
    (A : linearSimilitudes h r ε) :
    linearSimAut h hr hε A = 1 ↔
      ∃ u : Kˣ, glReindex e (A : GL (HypIndex r ε) K) = GeneralLinearGroup.scalar (Fin n) u := by
  rw [linearSimAut_eq_one_iff h hr hε hn]
  exact exists_congr fun u => (glReindex_eq_scalar_iff e _ u).symm

include hn in
theorem linearSimAut_plane {p₀ : ℕ} (hp₀ : p₀.Prime) (hn₀ : 2 * r + ε = p₀)
    (D : Subgroup (MulAut (hypPSU h r ε))) (hDI : D ≤ linearSimAutGroup h hr hε)
    (hDab : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hDp : ∀ x ∈ D, x ^ p₀ = 1)
    (hcard : Nat.card D = p₀ ^ 2)
    (hna : ¬ ∀ A ∈ D.comap (linearSimAut h hr hε), ∀ B ∈ D.comap (linearSimAut h hr hε),
      A * B = B * A) :
    ringChar K ≠ p₀ ∧ (∀ x ∈ linearSimAutGroup h hr hε, (∀ d ∈ D, d * x = x * d) → x ∈ D) ∧
      ∀ A B : linearSimilitudes h r ε,
        Subgroup.closure {linearSimAut h hr hε A, linearSimAut h hr hε B} = D →
        ∃ ζ : K, IsPrimitiveRoot ζ p₀ ∧
          ((A : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
              (B : GL (HypIndex r ε) K) =
            ζ • (((B : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) *
              (A : GL (HypIndex r ε) K)) := by
  have hcardI : Fintype.card (HypIndex r ε) = p₀ := by
    change Fintype.card (Fin r ⊕ Fin ε ⊕ Fin r) = p₀
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  let e : HypIndex r ε ≃ Fin p₀ := Fintype.equivFinOfCardEq hcardI
  let τ : linearSimilitudes h r ε →* GL (Fin p₀) K :=
    (glReindex e).toMonoidHom.comp (linearSimilitudes h r ε).subtype
  have hτ : Function.Injective τ :=
    (glReindex e).injective.comp (linearSimilitudes h r ε).subtype_injective
  obtain ⟨hchar, hcent, hroot⟩ := plane_transport hp₀ (linearSimAut h hr hε) τ hτ
    (fun A => linearSimAut_eq_one_iff_reindex h hr hε hn e A) D hDI hDab hDp hcard hna
  refine ⟨hchar, hcent, fun A B hAB => ?_⟩
  obtain ⟨ζ, hζ, hAB'⟩ := hroot A B hAB
  refine ⟨ζ, hζ, (Matrix.reindexAlgEquiv K K e).injective ?_⟩
  rw [map_mul, map_smul, map_mul]
  exact hAB'

end CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
