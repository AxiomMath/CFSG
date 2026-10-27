module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeFormRealization
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherAntiunitaryTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.AS35UB
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35K

open Subgroup Matrix CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Blueprint.Fischer (K)

variable {m : ℕ}

theorem SUid_eq_gramSU (m : ℕ) :
    SUid frob m = gramSU AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := AS35U.hF.finite
  have : CharP K 2 := AS35U.hF.charP
  rw [Units.val_one, ← unitarySU_eq_gramSU AS35U.hF m, unitarySU,
    ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K m]

@[expose] noncomputable def suEquiv (m : ℕ) :
    SUid frob m ≃* gramSU AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
  MulEquiv.subgroupCongr (SUid_eq_gramSU m)

@[simp] theorem coe_suEquiv (g : SUid frob m) :
    ((suEquiv m g : gramSU AS35U.hF _) : GL (Fin m) K) = g := rfl

@[simp] theorem coe_suEquiv_symm
    (g : gramSU AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
    (((suEquiv m).symm g : SUid frob m) : GL (Fin m) K) = g := rfl

theorem map_center_suEquiv (hm : 3 ≤ m) :
    (center (SUid frob m)).map (suEquiv m : SUid frob m →* _) =
      normOneScalars AS35U.hF (gramSU AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K))
        m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := AS35U.hF.finite
  have : CharP K 2 := AS35U.hF.charP
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ center (SUid frob m) := hx
    rw [center_SUid hm, mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
      MonoidHom.mem_range] at hx'
    obtain ⟨c, hc⟩ := hx'
    have hx3 : (x : GL (Fin m) K) ∈ unitarySU 2 1 K m := by
      rw [unitarySU, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU card_K m]
      exact x.2
    have hmem := (CFSG.LinearGroups.scalar_mem_statedSU_iff AS35U.hF.prime AS35U.hF.card_eq_sq
      (by omega) c).mp (hc ▸ hx3)
    refine ⟨c, ?_, hmem.1, hc.symm⟩
    rw [AS35U.hF.norm_eq_pow, ← Units.val_pow_eq_pow_val, hmem.2, Units.val_one]
  · rintro ⟨c, -, -, hc⟩
    refine ⟨(suEquiv m).symm y, ?_, MulEquiv.apply_symm_apply _ _⟩
    show (suEquiv m).symm y ∈ center (SUid frob m)
    rw [center_SUid hm, mem_subgroupOf, CFSG.Assembly.LowTwoRank.StatedScalars,
      MonoidHom.mem_range]
    exact ⟨c, hc.symm⟩

@[expose] noncomputable def pgPrimeEquiv (hm : 3 ≤ m) :
    PG m ≃* primeFormP AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
  QuotientGroup.congr _ _ (suEquiv m) (map_center_suEquiv hm)

theorem pgPrimeEquiv_mk (hm : 3 ≤ m) (g : SUid frob m) :
    pgPrimeEquiv hm (QuotientGroup.mk g) = (QuotientGroup.mk (suEquiv m g) : primeFormP _ _) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem pgPrimeEquiv_symm_mk (hm : 3 ≤ m)
    (g : gramSU AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) :
    (pgPrimeEquiv hm).symm (QuotientGroup.mk g : primeFormP _ _) =
      QuotientGroup.mk ((suEquiv m).symm g) := by
  rw [MulEquiv.symm_apply_eq, pgPrimeEquiv_mk, MulEquiv.apply_symm_apply]

theorem exists_realize (hm : 4 ≤ m) (β : MulAut (PG m)) :
    ∃ A : primeFormUnitary AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K),
      ∃ φ : K ≃+* K, ∀ g : SUid frob m, ∃ g' : SUid frob m,
        (g' : GL (Fin m) K) = (A : GL (Fin m) K) * glAut φ g * (A : GL (Fin m) K)⁻¹ ∧
          β (QuotientGroup.mk g) = QuotientGroup.mk g' := by
  have hm3 : 3 ≤ m := by omega
  set Θ := pgPrimeEquiv hm3
  obtain ⟨φ, ⟨A, hA⟩, -⟩ := existsUnique_primeFormFieldFactor AS35U.hF isPrimeFormGram_one
    hm3 (by omega) (Θ.symm.trans (β.trans Θ))
  refine ⟨A, φ, fun g => ?_⟩
  set g₁ := primeFormFieldSU AS35U.hF isPrimeFormGram_one φ (suEquiv m g)
  set g₂ : gramSU AS35U.hF ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) :=
    ⟨A * g₁ * (A : GL (Fin m) K)⁻¹, conj_mem_gramSU AS35U.hF _ A.2 g₁.2⟩
  refine ⟨(suEquiv m).symm g₂, rfl, ?_⟩
  have h1 : Θ (β (QuotientGroup.mk g)) = (primeFormConjHom AS35U.hF _ A)
      ((primeFormFieldHom AS35U.hF isPrimeFormGram_one φ) (Θ (QuotientGroup.mk g))) := by
    have h2 := congrArg (fun α : MulAut _ => α (Θ (QuotientGroup.mk g))) hA
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.mul_apply] at h2
    exact h2
  have h3 : β (QuotientGroup.mk g) = Θ.symm ((primeFormConjHom AS35U.hF _ A)
      ((primeFormFieldHom AS35U.hF isPrimeFormGram_one φ) (Θ (QuotientGroup.mk g)))) := by
    rw [← h1, MulEquiv.symm_apply_apply]
  rw [h3, pgPrimeEquiv_mk]
  change Θ.symm (primeFormConjHom AS35U.hF _ A (primeFormFieldAut AS35U.hF isPrimeFormGram_one φ
    (QuotientGroup.mk (suEquiv m g)))) = _
  rw [primeFormFieldAut_mk, primeFormConjHom_mk, pgPrimeEquiv_symm_mk]

theorem herm_mulVec_of_unitary
    {A : GL (Fin m) K} (hA : A ∈ primeFormUnitary AS35U.hF
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) (x y : Fin m → K) :
    herm frob ((A : Matrix (Fin m) (Fin m) K) *ᵥ x) ((A : Matrix (Fin m) (Fin m) K) *ᵥ y) =
      herm frob x y := by
  have h1 : conjTr frob (A : Matrix (Fin m) (Fin m) K) * (A : Matrix (Fin m) (Fin m) K) = 1 := by
    have h2 := mem_primeFormUnitary.mp hA
    rw [Units.val_one, Matrix.mul_one] at h2
    have h3 : (A : Matrix (Fin m) (Fin m) K).map AS35U.hF.bar =
        (A : Matrix (Fin m) (Fin m) K).map frob := by
      ext i j
      exact AS35U.bar_eq _
    rw [conjTr, ← h3]
    exact h2
  rw [herm_mulVec, h1, one_mulVec]

theorem frob_comm (φ : K ≃+* K) (c : K) : φ (frob c) = frob (φ c) := by
  rw [frob_apply, frob_apply, map_pow]

theorem herm_comp (φ : K ≃+* K) (x y : Fin m → K) :
    herm frob (φ ∘ x) (φ ∘ y) = φ (herm frob x y) := by
  simp only [herm, map_sum, map_mul, Function.comp_apply, frob_comm]

theorem glAut_mulVec (φ : K ≃+* K) (g : GL (Fin m) K) (x : Fin m → K) :
    ((glAut φ g : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ (φ ∘ x) =
      φ ∘ ((g : Matrix (Fin m) (Fin m) K) *ᵥ x) := by
  funext i
  rw [coe_glAut, Function.comp_apply]
  exact (RingHom.map_mulVec (φ : K →+* K) (g : Matrix (Fin m) (Fin m) K) x i).symm

theorem gl_ext {g g' : GL (Fin m) K}
    (h : ∀ x, (g : Matrix (Fin m) (Fin m) K) *ᵥ x = (g' : Matrix (Fin m) (Fin m) K) *ᵥ x) :
    g = g' :=
  Units.ext (Matrix.toLin'.injective (LinearMap.ext fun x => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h]))

theorem glAut_tvU (φ : K ≃+* K) {v : Fin m → K} (hv : herm frob v v = 0) :
    glAut φ (tvU v : GL (Fin m) K) = (tvU (φ ∘ v) : GL (Fin m) K) := by
  have hv' : herm frob (φ ∘ v) (φ ∘ v) = 0 := by rw [herm_comp, hv, map_zero]
  refine gl_ext fun x => ?_
  obtain ⟨y, rfl⟩ : ∃ y, φ ∘ y = x := ⟨φ.symm ∘ x, by
    funext i
    simp⟩
  rw [glAut_mulVec, coe_tvU_mulVec hv, coe_tvU_mulVec hv', herm_comp]
  funext i
  simp

theorem conj_tvU_of_unitary {A : GL (Fin m) K} (hA : A ∈ primeFormUnitary AS35U.hF
      ((1 : GL (Fin m) K) : Matrix (Fin m) (Fin m) K)) {v : Fin m → K}
    (hv : herm frob v v = 0) :
    A * (tvU v : GL (Fin m) K) * A⁻¹ =
      (tvU ((A : Matrix (Fin m) (Fin m) K) *ᵥ v) : GL (Fin m) K) := by
  have hAv : herm frob ((A : Matrix (Fin m) (Fin m) K) *ᵥ v)
      ((A : Matrix (Fin m) (Fin m) K) *ᵥ v) = 0 := by rw [herm_mulVec_of_unitary hA, hv]
  refine gl_ext fun x => ?_
  have hx : x = (A : Matrix (Fin m) (Fin m) K) *ᵥ (((A⁻¹ : GL (Fin m) K) :
      Matrix (Fin m) (Fin m) K) *ᵥ x) := by
    rw [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_tvU_mulVec hv,
    coe_tvU_mulVec hAv, mulVec_add, mulVec_smul]
  conv_rhs => rw [hx, herm_mulVec_of_unitary hA]

theorem map_DG (hm : 4 ≤ m) (β : MulAut (PG m)) {d : PG m} (hd : d ∈ DG m) : β d ∈ DG m := by
  obtain ⟨v, hv0, hv, rfl⟩ := hd
  obtain ⟨A, φ, hβ⟩ := exists_realize hm β
  obtain ⟨g', hg', hβg⟩ := hβ (tvU v)
  set w := ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ (φ ∘ v)
  have hφv : herm frob (φ ∘ v) (φ ∘ v) = 0 := by rw [herm_comp, hv, map_zero]
  have hw : herm frob w w = 0 := by rw [herm_mulVec_of_unitary A.2, hφv]
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv0
    have h1 : φ ∘ v = 0 := by
      have h2 := congrArg (fun y => ((A⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ y) h0
      simp only [mulVec_zero] at h2
      rw [← h2, show w = ((A : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ (φ ∘ v) from rfl,
        mulVec_mulVec,
        ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
    funext i
    have := congrFun h1 i
    simpa using this
  refine ⟨w, hw0, hw, ?_⟩
  have hg'w : g' = tvU w := Subtype.ext (by
    rw [hg', glAut_tvU φ hv, conj_tvU_of_unitary A.2 hφv])
  change tq w = β (tq v)
  rw [hβg, hg'w]

end CFSG.LargeExtraspecial.AS35K
