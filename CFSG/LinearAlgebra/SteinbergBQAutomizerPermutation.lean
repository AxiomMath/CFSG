module

public import CFSG.Walter.ReeOrder.JT.AuxWeights
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public noncomputable section

namespace CFSG.LinearAlgebra.SteinbergBQ

open Module TensorProduct
open CFSG.Walter.JT (weightSpace mem_weightSpace weights)

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable (L : Type*) [Field L] [Algebra k L]

@[expose] def bcEnd (g : LinearMap.GeneralLinearGroup k V) : Module.End L (L ⊗[k] V) :=
  Module.End.baseChangeHom k L V (g : V →ₗ[k] V)

theorem bcEnd_mul (g h : LinearMap.GeneralLinearGroup k V) :
    bcEnd L (g * h) = bcEnd L g * bcEnd L h := by
  rw [bcEnd, bcEnd, bcEnd, Units.val_mul, map_mul]

theorem bcEnd_one : bcEnd L (1 : LinearMap.GeneralLinearGroup k V) = 1 := by
  rw [bcEnd, Units.val_one, map_one]

theorem bcEnd_inv_apply (g : LinearMap.GeneralLinearGroup k V) (x : L ⊗[k] V) :
    bcEnd L g⁻¹ (bcEnd L g x) = x := by
  rw [← Module.End.mul_apply, ← bcEnd_mul, inv_mul_cancel, bcEnd_one, Module.End.one_apply]

theorem bcEnd_injective : Function.Injective (bcEnd (k := k) (V := V) L) := by
  intro g h hgh
  obtain ⟨φ, hφ⟩ : ∃ φ : L →ₗ[k] k, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact one_ne_zero ((Module.forall_dual_apply_eq_zero_iff k (1 : L)).1 hcon)
    exact ⟨(φ 1)⁻¹ • φ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ]⟩
  let π : L ⊗[k] V →ₗ[k] V := (TensorProduct.lid k V).toLinearMap ∘ₗ φ.rTensor V
  have hπ : ∀ v : V, π (1 ⊗ₜ v) = v := fun v => by
    simp [π, hφ]
  refine Units.ext (LinearMap.ext fun v => ?_)
  have h1 := LinearMap.congr_fun hgh (1 ⊗ₜ v)
  change ((g : V →ₗ[k] V).baseChange L) (1 ⊗ₜ v) = ((h : V →ₗ[k] V).baseChange L) (1 ⊗ₜ v) at h1
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at h1
  rw [← hπ ((g : V →ₗ[k] V) v), h1, hπ]

@[expose] def bcRep (A : Subgroup (LinearMap.GeneralLinearGroup k V)) :
    Representation L A (L ⊗[k] V) :=
  (Module.End.baseChangeHom k L V).toMonoidHom.comp ((Units.coeHom _).comp A.subtype)

theorem bcRep_apply (A : Subgroup (LinearMap.GeneralLinearGroup k V)) (a : A) :
    bcRep L A a = bcEnd L (a : LinearMap.GeneralLinearGroup k V) := rfl

variable {A : Subgroup (LinearMap.GeneralLinearGroup k V)}

theorem conj_mem_of_mem_normalizerGL
    (g : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) (a : A) :
    (g : LinearMap.GeneralLinearGroup k V)⁻¹ * a * g ∈ A :=
  (Subgroup.mem_normalizer_iff''.mp g.2 a).mp a.2

@[expose] def twistGL (g : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (χ : (⊤ : Subgroup A) → L) : (⊤ : Subgroup A) → L :=
  fun a => χ ⟨⟨_, conj_mem_of_mem_normalizerGL g a.1⟩, Subgroup.mem_top _⟩

theorem map_mem_weightSpace_twistGL
    (g : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    {χ : (⊤ : Subgroup A) → L} {v : L ⊗[k] V} (hv : v ∈ weightSpace (bcRep L A) ⊤ χ) :
    bcEnd L g v ∈ weightSpace (bcRep L A) ⊤ (twistGL L g χ) := by
  rw [mem_weightSpace] at hv ⊢
  intro a
  have e : ((a : A) : LinearMap.GeneralLinearGroup k V) * g =
      g * ((g : LinearMap.GeneralLinearGroup k V)⁻¹ * a * g) := by group
  change bcEnd L ((a : A) : LinearMap.GeneralLinearGroup k V) (bcEnd L g v) =
    χ ⟨⟨_, conj_mem_of_mem_normalizerGL g a.1⟩, Subgroup.mem_top _⟩ • bcEnd L g v
  rw [← Module.End.mul_apply, ← bcEnd_mul, e, bcEnd_mul, Module.End.mul_apply, ← map_smul]
  congr 1
  exact hv ⟨⟨_, conj_mem_of_mem_normalizerGL g a.1⟩, Subgroup.mem_top _⟩

theorem weightSpace_twistGL_ne_bot
    (g : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    {χ : (⊤ : Subgroup A) → L} (hχ : weightSpace (bcRep L A) ⊤ χ ≠ ⊥) :
    weightSpace (bcRep L A) ⊤ (twistGL L g χ) ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  refine fun h0 => hv0 ?_
  have h1 := map_mem_weightSpace_twistGL L g hv
  rw [h0, Submodule.mem_bot] at h1
  rw [← bcEnd_inv_apply L (g : LinearMap.GeneralLinearGroup k V) v, h1, map_zero]

omit [Field L] [Algebra k L] in
theorem twistGL_one (χ : (⊤ : Subgroup A) → L) :
    twistGL L (1 : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) χ = χ :=
  funext fun a => congrArg χ (Subtype.ext (Subtype.ext (by simp)))

omit [Field L] [Algebra k L] in
theorem twistGL_mul (g h : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (χ : (⊤ : Subgroup A) → L) :
    twistGL L (g * h) χ = twistGL L g (twistGL L h χ) :=
  funext fun a => congrArg χ (Subtype.ext (Subtype.ext (by simp [mul_assoc])))

@[expose, instance_reducible] def weightActionGL (A : Subgroup (LinearMap.GeneralLinearGroup k V)) :
    MulAction (Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
      (weights (bcRep L A) ⊤) where
  smul g χ := ⟨twistGL L g χ.1, weightSpace_twistGL_ne_bot L g χ.2⟩
  one_smul χ := Subtype.ext (twistGL_one L χ.1)
  mul_smul g h χ := Subtype.ext (twistGL_mul L g h χ.1)

@[expose] def weightPermGL (A : Subgroup (LinearMap.GeneralLinearGroup k V)) :
    Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)) →*
      Equiv.Perm (weights (bcRep L A) ⊤) :=
  @MulAction.toPermHom _ _ _ (weightActionGL L A)

theorem weightPermGL_apply_val
    (g : Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V)))
    (χ : weights (bcRep L A) ⊤) : (weightPermGL L A g χ).1 = twistGL L g χ.1 := rfl

theorem ker_weightPermGL [IsAlgClosed L] [FiniteDimensional k V] [Finite A]
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAchar : ((Nat.card A : ℕ) : L) ≠ 0) :
    (weightPermGL L A).ker =
      (Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V))).subgroupOf
        (Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) := by
  have hcomm : ∀ a ∈ (⊤ : Subgroup A), ∀ b ∈ (⊤ : Subgroup A),
      bcRep L A a * bcRep L A b = bcRep L A b * bcRep L A a := by
    intro a _ b _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm a a.2 b b.2)
  have hchar : ((Nat.card (⊤ : Subgroup A) : ℕ) : L) ≠ 0 := by
    rw [Subgroup.card_top]
    exact hAchar
  have htop := (CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top (bcRep L A) ⊤ hcomm
    hchar).2
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
  set g' : LinearMap.GeneralLinearGroup k V := g.1 with hg'
  constructor
  · intro hg a ha
    have hle : ∀ χ, weightSpace (bcRep L A) ⊤ χ ≤
        LinearMap.eqLocus (bcEnd L (g'⁻¹ * a * g')) (bcEnd L a) := by
      intro χ v hv
      by_cases hχ : weightSpace (bcRep L A) ⊤ χ = ⊥
      · rw [hχ, Submodule.mem_bot] at hv
        rw [hv]
        exact (LinearMap.eqLocus _ _).zero_mem
      · have hfix : twistGL L g χ = χ := by
          have := congrArg (fun τ : Equiv.Perm (weights (bcRep L A) ⊤) => (τ ⟨χ, hχ⟩).1) hg
          simpa [weightPermGL_apply_val] using this
        have hv' := (mem_weightSpace.1 hv)
        change bcEnd L (g'⁻¹ * a * g') v = bcEnd L a v
        have h1 := hv' ⟨⟨_, conj_mem_of_mem_normalizerGL g ⟨a, ha⟩⟩, Subgroup.mem_top _⟩
        have h2 := hv' ⟨⟨a, ha⟩, Subgroup.mem_top _⟩
        rw [bcRep_apply] at h1 h2
        rw [h1, h2]
        have h3 := congrFun hfix ⟨⟨a, ha⟩, Subgroup.mem_top _⟩
        rw [← h3]
        rfl
    have h1 : LinearMap.eqLocus (bcEnd L (g'⁻¹ * a * g')) (bcEnd L a) = ⊤ := by
      rw [eq_top_iff, ← htop]
      exact iSup_le hle
    have h2 := bcEnd_injective L (LinearMap.eqLocus_eq_top.mp h1)
    calc a * g' = g' * (g'⁻¹ * a * g') := by group
      _ = g' * a := by rw [h2]
  · intro hg
    refine Equiv.ext fun χ => Subtype.ext ?_
    rw [weightPermGL_apply_val]
    refine funext fun a => congrArg χ.1 (Subtype.ext (Subtype.ext ?_))
    change g'⁻¹ * ((a : A) : LinearMap.GeneralLinearGroup k V) * g' = a
    rw [mul_assoc, hg _ a.1.2, ← mul_assoc, inv_mul_cancel, one_mul]

end CFSG.LinearAlgebra.SteinbergBQ

namespace CFSG.LinearAlgebra

open Module TensorProduct SteinbergBQ
open CFSG.Walter.JT (weightSpace weights)

theorem abelian_coprime_matrix_automizer_permutation_embedding {k V : Type*} [Field k] {p : ℕ}
    [hp : Fact p.Prime] [CharP k p] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hn : 1 ≤ finrank k V) (A : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite A]
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : Nat.Coprime (Nat.card A) p) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ finrank k V ∧
      ∃ f : ↥(Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) ⧸
          (Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V))).subgroupOf
            (Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) →*
          Equiv.Perm (Fin r),
        Function.Injective f ∧
        (finrank k V ≤ 4 → Group.IsSolvable
          (↥(Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))) ⧸
            (Subgroup.centralizer (A : Set (LinearMap.GeneralLinearGroup k V))).subgroupOf
              (Subgroup.normalizer (A : Set (LinearMap.GeneralLinearGroup k V))))) := by
  classical
  set L := AlgebraicClosure k
  have : CharP L p := charP_of_injective_algebraMap (algebraMap k L).injective p
  have hAchar : ((Nat.card A : ℕ) : L) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff L p] at h
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm hAp) h
    exact hp.out.one_lt.ne' this
  have hcomm : ∀ a ∈ (⊤ : Subgroup A), ∀ b ∈ (⊤ : Subgroup A),
      bcRep L A a * bcRep L A b = bcRep L A b * bcRep L A a := by
    intro a _ b _
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hAcomm a a.2 b b.2)
  have hchar : ((Nat.card (⊤ : Subgroup A) : ℕ) : L) ≠ 0 := by
    rw [Subgroup.card_top]
    exact hAchar
  obtain ⟨hfin, hcard⟩ := CFSG.Walter.JT.finite_weights_and_card_le (bcRep L A) ⊤ hcomm hchar
  rw [Module.finrank_baseChange] at hcard
  have hpos : 1 ≤ Nat.card (weights (bcRep L A) ⊤) := by
    have htop := (CFSG.Walter.JT.iSupIndep_weightSpace_and_iSup_eq_top (bcRep L A) ⊤ hcomm
      hchar).2
    by_contra h0
    have hempty : IsEmpty (weights (bcRep L A) ⊤) := by
      rw [← Finite.card_eq_zero_iff]
      omega
    have hall : ∀ χ, weightSpace (bcRep L A) ⊤ χ = ⊥ := fun χ => by
      by_contra hχ
      exact hempty.false ⟨χ, hχ⟩
    have hbot : (⊤ : Submodule L (L ⊗[k] V)) = ⊥ := by
      rw [← htop]
      exact iSup_eq_bot.2 hall
    have h1 := finrank_top L (L ⊗[k] V)
    rw [hbot, finrank_bot, Module.finrank_baseChange] at h1
    omega
  set r := Nat.card (weights (bcRep L A) ⊤)
  let e : weights (bcRep L A) ⊤ ≃ Fin r := Finite.equivFin _
  have hker := ker_weightPermGL L hAcomm hAchar
  let f₁ := QuotientGroup.quotientMulEquivOfEq hker.symm
  let f₂ := QuotientGroup.kerLift (weightPermGL L A)
  let f₃ := Equiv.permCongrHom e
  let f := f₃.toMonoidHom.comp (f₂.comp f₁.toMonoidHom)
  have hf : Function.Injective f := by
    intro x y hxy
    apply f₁.injective
    apply QuotientGroup.kerLift_injective (weightPermGL L A)
    apply f₃.injective
    exact hxy
  refine ⟨r, hpos, hcard, f, hf, fun h4 => ?_⟩
  have : Group.IsSolvable (Equiv.Perm (Fin r)) := Equiv.Perm.isSolvable (by simp; omega)
  exact Group.isSolvable_of_isSolvable_injective hf

end CFSG.LinearAlgebra
