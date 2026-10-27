module

public import CFSG.LieType.Simplicity.TitsElements
public import CFSG.LieType.Ree.LargeReeRootInvolution

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Simplicity

theorem label_position_injective
    {τ : Tag} : Function.Injective (Label.position (τ := τ)) := by
  intro a b h
  by_contra hab
  rcases Label.precedes_or_precedes hab with h' | h'
  · exact (Label.position_lt_position h').ne h
  · exact (Label.position_lt_position h').ne h.symm

namespace ReeTag

abbrev titsGamma :
    Subgroup (ModGL F4.tag (ZMod 2)) :=
  @reeGamma F4 (ZMod 2) _ _ (ZMod.charP 2) 0
   

abbrev titsBorel
    : Subgroup (ModGL F4.tag (ZMod 2)) :=
  @reeFixedBorel F4 (ZMod 2) _ _ (ZMod.charP 2) 0
   

variable (K : Type) [Field K]

@[expose] def titsGen0
    : ModGL F4.tag K :=
  xUnit F4.tag K (0 : Fin 4) 1 * xUnit F4.tag K (3 : Fin 4) 1

@[expose] def titsGen1
    : ModGL F4.tag K :=
  xUnit F4.tag K (2 : Fin 4) 1 * xUnit F4.tag K (1 : Fin 4) 1 *
    pinnedX F4.tag K (![0, 1, 2, 0] : Fin 4 → ℤ) 1

@[expose] def titsGen2
    : ModGL F4.tag K :=
  weylElt F4.tag K (0 : Fin 4) 1 * weylElt F4.tag K (3 : Fin 4) 1

@[expose] def titsGen3
    : ModGL F4.tag K :=
  weylElt F4.tag K (1 : Fin 4) 1 * weylElt F4.tag K (2 : Fin 4) 1 *
    weylElt F4.tag K (1 : Fin 4) 1 * weylElt F4.tag K (2 : Fin 4) 1

@[expose] def titsGenSubgroup
    : Subgroup (ModGL F4.tag K) :=
  Subgroup.closure {titsGen0 K, titsGen1 K, titsGen2 K, titsGen3 K}

theorem titsGen0_mem_adjointGroup
    : titsGen0 K ∈ adjointGroup F4.tag K :=
  mul_mem (xUnit_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _)

theorem titsGen1_mem_adjointGroup
    : titsGen1 K ∈ adjointGroup F4.tag K :=
  mul_mem (mul_mem (xUnit_mem_adjointGroup _ _) (xUnit_mem_adjointGroup _ _))
    (pinnedX_mem_adjointGroup _ _)

theorem titsGen2_mem_adjointGroup
    : titsGen2 K ∈ adjointGroup F4.tag K :=
  mul_mem (weylElt_mem_adjointGroup _ _) (weylElt_mem_adjointGroup _ _)

theorem titsGen3_mem_adjointGroup
    : titsGen3 K ∈ adjointGroup F4.tag K :=
  mul_mem (mul_mem (mul_mem (weylElt_mem_adjointGroup _ _) (weylElt_mem_adjointGroup _ _))
    (weylElt_mem_adjointGroup _ _)) (weylElt_mem_adjointGroup _ _)

theorem titsGenSubgroup_le_adjointGroup
    : titsGenSubgroup K ≤ adjointGroup F4.tag K := by
  refine (Subgroup.closure_le _).2 ?_
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
  exact ⟨titsGen0_mem_adjointGroup K, titsGen1_mem_adjointGroup K, titsGen2_mem_adjointGroup K,
    titsGen3_mem_adjointGroup K⟩

theorem coe_titsG0
    : ((titsG0 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen0 K :=
  rfl

theorem weylElt_conj_xUnit_eq_pinnedX
    (h2 : (2 : K) = 0) :
    weylElt F4.tag K (2 : Fin 4) 1 * xUnit F4.tag K (1 : Fin 4) 1 *
        (weylElt F4.tag K (2 : Fin 4) 1)⁻¹ = pinnedX F4.tag K (![0, 1, 2, 0] : Fin 4 → ℤ) 1 := by
  have hr : reflect F4.tag (2 : Fin 4) (Pi.single (1 : Fin 4) 1) = (![0, 1, 2, 0] : Fin 4 → ℤ) := by
    funext k
    fin_cases k <;> rfl
  have h := weylElt_conj_pinnedX_of_two_eq_zero (τ := F4.tag) h2 (2 : Fin 4)
    (isRoot_single F4.tag (1 : Fin 4)) (1 : K)
  rw [← pinnedX_single F4.tag K (1 : Fin 4) (1 : K)]
  exact h.trans (congrArg (fun v => pinnedX F4.tag K v 1) hr)

theorem coe_titsG1
    (h2 : (2 : K) = 0) :
    ((titsG1 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen1 K := by
  rw [titsGen1, ← weylElt_conj_xUnit_eq_pinnedX K h2]
  rfl

theorem coe_titsZ1
    : ((titsZ1 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen2 K := by
  rw [titsZ1_eq_evalG]
  simp only [titsZ1Word, TitsBits.evalG_cons, TitsBits.evalG_nil, mul_one, Subgroup.coe_mul]
  rfl

theorem coe_titsZ2
    : ((titsZ2 K : adjointGroup F4.tag K) : ModGL F4.tag K) = titsGen3 K := by
  rw [titsZ2_eq_evalG]
  simp only [titsZ2Word, TitsBits.evalG_cons, TitsBits.evalG_nil, mul_one, Subgroup.coe_mul,
    titsGen3, mul_assoc]
  rfl

theorem card_label_F4 : Fintype.card (Label F4.tag) = 52 := by
  rw [card_label, Nat.card_eq_fintype_card, card_isRoot]
  rfl

@[expose] def titsLabelEquiv : Label F4.tag ≃ Fin 52 :=
  Equiv.ofBijective (fun a => ⟨a.position, lt_of_lt_of_eq a.position_lt_card card_label_F4⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun _ _ h => label_position_injective (congrArg Fin.val h), by
        rw [card_label_F4, Fintype.card_fin]⟩)

theorem coe_titsLabelEquiv
    (a : Label F4.tag) : (titsLabelEquiv a : ℕ) = a.position :=
  rfl

theorem titsLabelEquiv_lt_iff {a b : Label F4.tag} :
    titsLabelEquiv a < titsLabelEquiv b ↔ a.Precedes b := by
  change a.position < b.position ↔ _
  refine ⟨fun h => ?_, Label.position_lt_position⟩
  have hab : a ≠ b := fun e => by rw [e] at h; exact lt_irrefl _ h
  rcases Label.precedes_or_precedes hab with h' | h'
  · exact h'
  · exact absurd (Label.position_lt_position h') (not_lt.2 h.le)

@[expose] def titsBasis
    : Module.Basis (Fin 52) K (RootModule F4.tag K) :=
  Finsupp.basisSingleOne.reindex titsLabelEquiv

theorem titsBasis_apply (j : Fin 52) :
    titsBasis K j = Finsupp.single (titsLabelEquiv.symm j) 1 := by
  rw [titsBasis, Module.Basis.reindex_apply, Finsupp.coe_basisSingleOne]

theorem titsBasis_repr_apply (v : RootModule F4.tag K) (i : Fin 52) :
    (titsBasis K).repr v i = v (titsLabelEquiv.symm i) := by
  rw [titsBasis, Module.Basis.repr_reindex_apply, Finsupp.basisSingleOne_repr]
  rfl

@[expose] def titsMatrix : ModGL F4.tag K →* GL (Fin 52) K :=
  Units.map (LinearMap.toMatrixAlgEquiv (titsBasis K)).toRingEquiv.toMonoidHom

theorem titsMatrix_apply (g : ModGL F4.tag K) (i j : Fin 52) :
    (titsMatrix K g : Matrix (Fin 52) (Fin 52) K) i j =
      (g : Module.End K (RootModule F4.tag K)) (Finsupp.single (titsLabelEquiv.symm j) 1)
        (titsLabelEquiv.symm i) := by
  change LinearMap.toMatrixAlgEquiv (titsBasis K) (g : Module.End K (RootModule F4.tag K)) i j = _
  rw [LinearMap.toMatrixAlgEquiv_apply, titsBasis_repr_apply, titsBasis_apply]

theorem titsMatrix_injective : Function.Injective (titsMatrix K) :=
  Units.map_injective (LinearMap.toMatrixAlgEquiv (titsBasis K)).injective

variable {K}

@[expose] def titsRowFlag (M : Matrix (Fin 52) (Fin 52) K) (j : Fin 52) :
    Submodule K (Fin 52 → K) :=
  Submodule.span K (Set.range fun i : {i : Fin 52 // 51 ≤ i.val + j.val} => M i)

@[expose] def titsFlagSmul (g : GL (Fin 52) K) (F : Fin 52 → Submodule K (Fin 52 → K))
    (j : Fin 52) : Submodule K (Fin 52 → K) :=
  (F j).map (Matrix.vecMulLinear ((g⁻¹ : GL (Fin 52) K) : Matrix (Fin 52) (Fin 52) K))

variable (K) in
@[expose] def titsBaseFlag : Fin 52 → Submodule K (Fin 52 → K) :=
  titsRowFlag (1 : Matrix (Fin 52) (Fin 52) K)

theorem titsFlagSmul_titsRowFlag (g : GL (Fin 52) K) (M : Matrix (Fin 52) (Fin 52) K) :
    titsFlagSmul g (titsRowFlag M) =
      titsRowFlag (M * ((g⁻¹ : GL (Fin 52) K) : Matrix (Fin 52) (Fin 52) K)) := by
  funext j
  rw [titsFlagSmul, titsRowFlag, titsRowFlag, Submodule.map_span, ← Set.range_comp]
  rfl

theorem titsFlagSmul_one (F : Fin 52 → Submodule K (Fin 52 → K)) : titsFlagSmul 1 F = F := by
  have h : Matrix.vecMulLinear (1 : Matrix (Fin 52) (Fin 52) K) = LinearMap.id :=
    LinearMap.ext fun v => Matrix.vecMul_one v
  funext j
  rw [titsFlagSmul, inv_one, Units.val_one, h, Submodule.map_id]

theorem titsFlagSmul_mul (g h : GL (Fin 52) K) (F : Fin 52 → Submodule K (Fin 52 → K)) :
    titsFlagSmul (g * h) F = titsFlagSmul g (titsFlagSmul h F) := by
  have e : Matrix.vecMulLinear (((g * h)⁻¹ : GL (Fin 52) K) : Matrix (Fin 52) (Fin 52) K) =
      (Matrix.vecMulLinear ((g⁻¹ : GL (Fin 52) K) : Matrix (Fin 52) (Fin 52) K)).comp
        (Matrix.vecMulLinear ((h⁻¹ : GL (Fin 52) K) : Matrix (Fin 52) (Fin 52) K)) :=
    LinearMap.ext fun v => by
      rw [mul_inv_rev, Units.val_mul, LinearMap.comp_apply, Matrix.vecMulLinear_apply,
        Matrix.vecMulLinear_apply, Matrix.vecMulLinear_apply, Matrix.vecMul_vecMul]
  funext j
  rw [titsFlagSmul, titsFlagSmul, titsFlagSmul, e, Submodule.map_comp]

variable (K) in
@[expose, instance_reducible] def titsFlagAction :
    MulAction (GL (Fin 52) K) (Fin 52 → Submodule K (Fin 52 → K)) where
  smul := titsFlagSmul
  one_smul := titsFlagSmul_one
  mul_smul := titsFlagSmul_mul

theorem titsFlagSmul_titsBaseFlag (g : GL (Fin 52) K) :
    titsFlagSmul g (titsBaseFlag K) =
      titsRowFlag ((g⁻¹ : GL (Fin 52) K) : Matrix (Fin 52) (Fin 52) K) := by
  rw [titsBaseFlag, titsFlagSmul_titsRowFlag, one_mul]

end ReeTag

end CFSG.LieType.Ree
