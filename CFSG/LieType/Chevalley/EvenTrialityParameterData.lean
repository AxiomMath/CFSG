module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Blueprint.ChevalleyRootGroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (K : Type) [Field K] (σ : K →+* K)

@[expose] def trialityFixedField : Subfield K :=
  RingHom.eqLocusField σ (RingHom.id K)

@[expose] def trialityRoot : Fin 6 → Fin TwistTag.D4.tag.rank → ℤ :=
  ![![1, 0, 0, 0], ![0, 0, 1, 0], ![1, 0, 1, 0], ![0, 1, 1, 1], ![1, 1, 1, 1], ![1, 1, 2, 1]]

@[expose] def trialityOrbitProd
    (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    adjointGroup TwistTag.D4.tag K :=
  ((List.range 3).map fun h => (⟨pinnedX TwistTag.D4.tag K
    (permLattice (TwistTag.D4.perm ^ h) α) ((σ ^ h) c), pinnedX_mem_adjointGroup _ _⟩ :
      adjointGroup TwistTag.D4.tag K)).prod

@[expose] def trialityX₁
    (c : K) : adjointGroup TwistTag.D4.tag K :=
  trialityOrbitProd K σ (trialityRoot 0) c

@[expose] def trialityX₃
    (c : K) : adjointGroup TwistTag.D4.tag K :=
  trialityOrbitProd K σ (trialityRoot 2) c

@[expose] def trialityX₄
    (c : K) : adjointGroup TwistTag.D4.tag K :=
  trialityOrbitProd K σ (trialityRoot 3) c

@[expose] def trialityX₂
    (c : trialityFixedField K σ) : adjointGroup TwistTag.D4.tag K :=
  ⟨pinnedX TwistTag.D4.tag K (trialityRoot 1) c, pinnedX_mem_adjointGroup _ _⟩

@[expose] def trialityX₅
    (c : trialityFixedField K σ) : adjointGroup TwistTag.D4.tag K :=
  ⟨pinnedX TwistTag.D4.tag K (trialityRoot 4) c, pinnedX_mem_adjointGroup _ _⟩

@[expose] def trialityX₆
    (c : trialityFixedField K σ) : adjointGroup TwistTag.D4.tag K :=
  ⟨pinnedX TwistTag.D4.tag K (trialityRoot 5) c, pinnedX_mem_adjointGroup _ _⟩

variable {K σ}

theorem mem_trialityFixedField {c : K} : c ∈ trialityFixedField K σ ↔ σ c = c :=
  Iff.rfl

theorem ringHom_apply_apply_apply_of_pow_three {σ : K →+* K} (hσ : σ ^ 3 = 1) (c : K) :
    σ (σ (σ c)) = c :=
  congrArg (fun f : K →+* K => f c) hσ

theorem trace_mem_trialityFixedField (hσ : σ ^ 3 = 1) (c : K) :
    c + σ c + σ (σ c) ∈ trialityFixedField K σ := by
  rw [mem_trialityFixedField, map_add, map_add, ringHom_apply_apply_apply_of_pow_three hσ]
  ring

variable (K σ) in
@[expose] def trialityTrace (hσ : σ ^ 3 = 1) (c : K) : trialityFixedField K σ :=
  ⟨c + σ c + σ (σ c), trace_mem_trialityFixedField hσ c⟩

theorem isRoot_trialityRoot (j : Fin 6) (h : ℕ) :
    IsRoot TwistTag.D4.tag (permLattice (TwistTag.D4.perm ^ h) (trialityRoot j)) ∧
      0 < height (permLattice (TwistTag.D4.perm ^ h) (trialityRoot j)) := by
  have hroot : ∀ j : Fin 6, ∀ h : Fin 3, ∃ k : Fin 24,
      TwistTag.D4.tag.rootCertificate.root k =
        permLattice (TwistTag.D4.perm ^ (h : ℕ)) (trialityRoot j) ∧
      0 < height (permLattice (TwistTag.D4.perm ^ (h : ℕ)) (trialityRoot j)) := by
    decide +kernel
  have hper : TwistTag.D4.perm ^ h = TwistTag.D4.perm ^ (h % 3) := by
    have h3 : TwistTag.D4.perm ^ 3 = 1 := by decide
    conv_lhs => rw [← Nat.div_add_mod h 3, pow_add, pow_mul, h3, one_pow, one_mul]
  obtain ⟨k, hk, hpos⟩ := hroot j ⟨h % 3, Nat.mod_lt _ (by norm_num)⟩
  rw [hper]
  exact ⟨(RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).2 ⟨k, k.2, hk⟩, hpos⟩

theorem permLattice_trialityRoot_fixed :
    permLattice TwistTag.D4.perm (trialityRoot 1) = trialityRoot 1 ∧
      permLattice TwistTag.D4.perm (trialityRoot 4) = trialityRoot 4 ∧
      permLattice TwistTag.D4.perm (trialityRoot 5) = trialityRoot 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> exact List.ofFn_injective (by decide +kernel)

theorem coe_trialityOrbitProd
    (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    (trialityOrbitProd K σ α c : ModGL TwistTag.D4.tag K) =
      pinnedX TwistTag.D4.tag K α c *
        pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (σ c) *
          pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) (σ (σ c)) := by
  have e0 : permLattice (TwistTag.D4.perm ^ 0) α = α := rfl
  simp only [trialityOrbitProd, List.range_succ, List.range_zero, List.nil_append,
    List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, Subgroup.coe_mul, e0, pow_one, RingHom.coe_pow,
    Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq, mul_assoc]

end CFSG.LieType.Chevalley
