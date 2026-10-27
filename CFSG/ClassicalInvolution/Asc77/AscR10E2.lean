module

public import CFSG.ClassicalInvolution.Asc77.AscR10E1
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2UnitaryHom

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.Levi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups CFSG.LieType.Universal CFSG.LieType
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Timmesfeld
  CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Models CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Steinberg CFSG.ClassicalInvolution.WeakCT Matrix
open scoped MatrixGroups



section Hom

variable {p e : ℕ} [Fact p.Prime] [NeZero e]

theorem exists_unitary_hom_odd {τ : Tag} {θ δ : Fin τ.rank → ℤ} (hp2 : p ≠ 2) 
    (hθ : IsRoot τ θ) (hδ : IsRoot τ δ) (hpair : A2Pairing θ δ)
    (Em : A2Embedding τ θ δ (GaloisField p (2 * e)))
    {c : ↥(adjointGroup τ (GaloisField p e))} {v d : ModGL τ (AlgClosGF p e)}
    (hd : v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
        (c : ModGL τ (GaloisField p e)) * v⁻¹ = d)
    (hcocycle : ∃ Λ₀ Λ₁ Λ₂ Λ₃ : AlgClosGF p e, Λ₀ * Λ₁ = 1 ∧ Λ₂ * Λ₃ = 1 ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) θ x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) (-θ) (Λ₀ * x)) ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) (-θ) x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) θ (Λ₁ * x)) ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) δ x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) (-δ) (Λ₂ * x)) ∧
      (∀ x : AlgClosGF p e, (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹) *
        pinnedX τ (AlgClosGF p e) (-δ) x * (entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹)⁻¹ =
          pinnedX τ (AlgClosGF p e) δ (Λ₃ * x)))
    (hdt : ∀ t ∈ torusGroup τ (AlgClosGF p e), d * t = t * d)
    (hvadj : ∀ t ∈ torusGroup τ (AlgClosGF p e), t * v ∈ adjointGroup τ (AlgClosGF p e))
    (hvconj : ∀ t ∈ torusGroup τ (AlgClosGF p e), ∀ A : SL2 (AlgClosGF p e),
      ∃ A' : SL2 (AlgClosGF p e), (t * v)⁻¹ * rootSL2 τ (AlgClosGF p e) θ A * (t * v) =
        rootSL2 τ (AlgClosGF p e) θ A')
    (hsign : ∀ j : GaloisField p (2 * e) →+* AlgClosGF p e,
      baseChangeGL j (rootSL2 τ (GaloisField p (2 * e)) δ
        (HSL (-1 : (GaloisField p (2 * e))ˣ))) = d) :
    ∃ θ' : Su (GaloisField p (2 * e)) p e 3 →* ↥(adjointGroup τ (GaloisField p e)),
      Function.Injective θ' ∧
      (∀ A : Su (GaloisField p (2 * e)) p e 2, ∃ A₀ : SL2 (GaloisField p e),
        ((θ' (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) :
          ↥(adjointGroup τ (GaloisField p e))) : ModGL τ (GaloisField p e)) =
            rootSL2 τ (GaloisField p e) θ A₀) ∧
      θ' (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 0
        (suNegOne (GaloisField p (2 * e)) p e)) = c := by
  classical
  have hcardq : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e (NeZero.ne e)
  have h2e : NeZero (2 * e) := ⟨by have := NeZero.ne e; omega⟩
  have hcardE : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := by
    rw [GaloisField.card p (2 * e) (NeZero.ne _), pow_mul' p 2 e]
  have hk2 : ringChar (AlgClosGF p e) ≠ 2 := by
    rw [ringChar.eq (AlgClosGF p e) p]
    exact hp2
  have hE2 : ringChar (GaloisField p (2 * e)) ≠ 2 := by
    rw [ringChar.eq (GaloisField p (2 * e)) p]
    exact hp2
  obtain ⟨j⟩ := nonempty_ringHom_galoisField_algClos (p := p) (e := e) (2 * e)
  have hj : ∀ x : GaloisField p (2 * e),
      j (unitaryInvolution (GaloisField p (2 * e)) p e x) = j x ^ p ^ e := fun x => by
    rw [unitaryInvolution_apply, map_pow]
  obtain ⟨Λ₀, Λ₁, Λ₂, Λ₃, e1, e2, a0, a1, a2, a3⟩ := hcocycle
  have sq : ∀ {x : GaloisField p (2 * e)}, x * x = 1 → j x * j x = 1 := fun {x} h => by
    rw [← map_mul, h, map_one]
  have s₀ := sq Em.sq₀
  have s₁ := sq Em.sq₁
  have s₂ := sq Em.sq₂
  have s₃ := sq Em.sq₃
  have hκ₀ : (-(j Em.m₁ * j Em.m₀)) * (-(j Em.m₁ * j Em.m₀)) = 1 := by
    linear_combination (j Em.m₁ * j Em.m₁) * s₀ + s₁
  have hκ₂ : (-(j Em.m₃ * j Em.m₂)) * (-(j Em.m₃ * j Em.m₂)) = 1 := by
    linear_combination (j Em.m₃ * j Em.m₃) * s₂ + s₃
  obtain ⟨t, ht, hmod⟩ := exists_torusMod hθ hδ hpair p e e1 e2 hκ₀ hκ₂
  set v' := t * v with hv'def
  set u := entrywiseFrobGL τ (AlgClosGF p e) p e v * v⁻¹ with hu
  set u' := entrywiseFrobGL τ (AlgClosGF p e) p e t * u * t⁻¹ with hu'
  obtain ⟨b₀, b₁, b₂, b₃⟩ := hmod u u' rfl a0 a1 a2 a3
  have hτ := conj_iota_eq_tau Em j b₀ b₁ b₂ b₃ rfl rfl
  have hv'adj : v' ∈ adjointGroup τ (AlgClosGF p e) := hvadj t ht
  have hd' : v' * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
      (c : ModGL τ (GaloisField p e)) * v'⁻¹ = d := by
    have hcomm : d * t = t * d :=
      hdt t ht
    calc v' * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
          (c : ModGL τ (GaloisField p e)) * v'⁻¹ =
        t * (v * baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
          (c : ModGL τ (GaloisField p e)) * v⁻¹) * t⁻¹ := by rw [hv'def]; group
      _ = t * d * t⁻¹ := by rw [hd]
      _ = d := by rw [← hcomm]; group
  have hFv' : entrywiseFrobGL τ (AlgClosGF p e) p e v' = u' * v' := by
    rw [hv'def, map_mul]
    have : entrywiseFrobGL τ (AlgClosGF p e) p e v = u * v := by rw [hu]; group
    rw [this, hu']
    group
  let α : Su (GaloisField p (2 * e)) p e 3 →* ModGL τ (AlgClosGF p e) :=
    (MulAut.conj v'⁻¹).toMonoidHom.comp (((baseChangeGL j).comp Em.ι).comp
      (suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 3))
  have hα : ∀ y, α y = v'⁻¹ * baseChangeGL j (Em.ι (suToSL (unitaryInvolution
      (GaloisField p (2 * e)) p e) 3 y)) * v' := fun y => by
    simp [α]
  have hαF : ∀ y, entrywiseFrobGL τ (AlgClosGF p e) p e (α y) = α y := fun y => by
    rw [hα]
    exact frob_alpha p e hp2 Em j
      ((unitaryInvolution (GaloisField p (2 * e)) p e : GaloisField p (2 * e) ≃+*
        GaloisField p (2 * e)) : GaloisField p (2 * e) →+* GaloisField p (2 * e)) hj hFv' hτ
      (map_suToSL_eq_tau y)
  have hKodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcardq]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2 |>.pow
  have hFrFun : ∀ x : AlgClosGF p e,
      iterateFrobenius (AlgClosGF p e) p e x = x ^ Nat.card (GaloisField p e) :=
    iterateFrobenius_algClos
  obtain ⟨-, -, -, hder⟩ := exceptional_Lang_Frobenius_fixed_derived_root_group τ
    (GaloisField p e) hKodd (AlgClosGF p e) (iterateFrobenius (AlgClosGF p e) p e) hFrFun
  have hαR : α.range ≤ adjointGroup τ (AlgClosGF p e) ⊓
      (Units.map (entrywiseHom (iterateFrobenius (AlgClosGF p e) p e))).eqLocus
        (MonoidHom.id _) := by
    rintro _ ⟨y, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, hαF y⟩
    rw [hα]
    exact mul_mem (mul_mem (inv_mem hv'adj) (baseChangeGL_mem_adjointGroup j (Em.mem _))) hv'adj
  have hrange : α.range ≤ (adjointGroup τ (GaloisField p e)).map
      (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))) := by
    rw [← hder]
    exact (CFSG.ClassicalInvolution.Asc77.T3CII.su_range_le_commutator_odd hcardE hp2 α).trans
      (Subgroup.commutator_mono hαR hαR)
  let ψ : ↥(adjointGroup τ (GaloisField p e)) →* ModGL τ (AlgClosGF p e) :=
    (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))).comp
      (adjointGroup τ (GaloisField p e)).subtype
  have hψinj : Function.Injective ψ := fun x y h =>
    Subtype.ext (baseChangeGL_injective _ h)
  have hψr : ψ.range = (adjointGroup τ (GaloisField p e)).map
      (baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  obtain ⟨φ, hφ⟩ := exists_lift_of_range ψ hψinj α
    (fun y => by rw [hψr]; exact hrange ⟨y, rfl⟩)
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro y₁ y₂ h
    have h1 : α y₁ = α y₂ := by rw [← hφ y₁, ← hφ y₂, h]
    rw [hα, hα] at h1
    have h2 := mul_left_cancel (mul_right_cancel h1)
    exact suToSL_injective (Em.inj (baseChangeGL_injective j h2))
  · intro A
    have h3 : suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 3
        (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
        blk (GaloisField p (2 * e)) 0
          (suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) := by
      rw [embSUid_two_eq_blockEmb, suToSL_blockEmb]
      rfl
    obtain ⟨B₁, hB₁⟩ := Em.blk_zero_mem hθ
      (suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A)
    obtain ⟨A', hA'⟩ := hvconj t ht (Matrix.SpecialLinearGroup.map j B₁)
    have hαy : α (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
        rootSL2 τ (AlgClosGF p e) θ A' := by
      rw [hα, h3, ← hB₁, baseChangeGL_rootSL2', hA']
    have hfix := hαF (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A)
    rw [hαy] at hfix
    obtain ⟨A₀, hA₀⟩ := exists_rootSL2_of_frobFixed hθ hp2 hfix
    have hmem : rootSL2 τ (GaloisField p e) θ A₀ ∈ adjointGroup τ (GaloisField p e) :=
      rootSL2_mem_adjointGroup _ _
    have hφy : φ (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 2 A) =
        ⟨rootSL2 τ (GaloisField p e) θ A₀, hmem⟩ := by
      apply hψinj
      rw [hφ, hαy, hA₀]
      rfl
    rw [hφy]
    exact ⟨A₀, rfl⟩
  · have h3 : suToSL (unitaryInvolution (GaloisField p (2 * e)) p e) 3
        (embSUid (unitaryInvolution (GaloisField p (2 * e)) p e) 0
          (suNegOne (GaloisField p (2 * e)) p e)) =
        blk (GaloisField p (2 * e)) 1 (HSL (-1 : (GaloisField p (2 * e))ˣ)) := by
      rw [embSUid_zero_eq_blockEmb, suToSL_blockEmb, suToSL_suNegOne]
      rfl
    apply hψinj
    rw [hφ, hα, h3, Em.blk_one_neg_one hE2 hδ, hsign j]
    change _ = baseChangeGL (algebraMap (GaloisField p e) (AlgClosGF p e))
      (c : ModGL τ (GaloisField p e))
    have hd'' : d = v' * baseChangeGL
        (algebraMap (GaloisField p e) (AlgClosGF p e)) (c : ModGL τ (GaloisField p e)) * v'⁻¹ :=
      hd'.symm
    change v'⁻¹ * d * v' = _
    rw [hd'']
    group

end Hom

end CFSG.ClassicalInvolution.ModelFacts.Levi
