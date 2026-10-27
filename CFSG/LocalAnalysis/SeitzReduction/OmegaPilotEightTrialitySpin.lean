module

public import CFSG.LieType.Steinberg.Classical.SpinPlus

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.OmegaPilot

open CFSG.LieType.Steinberg CFSG.LieType.Universal.Spin CFSG.LieType.RootSystem
open scoped commutatorElement

section Lattice

variable {I : Type} [Fintype I] [DecidableEq I]

@[expose] def fundPerm (π : Equiv.Perm I) : (I → ℤ) →+ (I → ℤ) where
  toFun v := v ∘ π.symm
  map_zero' := rfl
  map_add' _ _ := rfl

theorem fundPerm_apply (π : Equiv.Perm I) (v : I → ℤ) (j : I) :
    fundPerm π v j = v (π.symm j) := rfl

theorem fundPerm_single (π : Equiv.Perm I) (i : I) :
    fundPerm π (Pi.single i 1) = Pi.single (π i) 1 := by
  funext j
  simp only [fundPerm_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem fundPerm_mul (π π' : Equiv.Perm I) (v : I → ℤ) :
    fundPerm (π * π') v = fundPerm π (fundPerm π' v) := by
  funext j
  simp only [fundPerm_apply, Equiv.Perm.mul_def, Equiv.symm_trans_apply]

theorem fundPerm_one (v : I → ℤ) : fundPerm (1 : Equiv.Perm I) v = v := rfl

theorem fundPerm_symm_fundPerm (π : Equiv.Perm I) (v : I → ℤ) :
    fundPerm π.symm (fundPerm π v) = v := by
  funext j
  simp only [fundPerm_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

theorem fundPerm_fundPerm_symm (π : Equiv.Perm I) (v : I → ℤ) :
    fundPerm π (fundPerm π.symm v) = v := by
  funext j
  simp only [fundPerm_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

theorem fundPerm_nsmul (π : Equiv.Perm I) (k : ℕ) (v : I → ℤ) :
    fundPerm π (k • v) = k • fundPerm π v :=
  map_nsmul (fundPerm π) k v

theorem fundPerm_reflection {A : Matrix I I ℤ} {π : Equiv.Perm I}
    (hπ : ∀ i j, A (π i) (π j) = A i j) (i : I) (v : I → ℤ) :
    fundPerm π (reflection A i v) = reflection A (π i) (fundPerm π v) := by
  have hsum : ∑ j, A (π i) j * v (π.symm j) = ∑ j, A i j * v j := by
    rw [← Equiv.sum_comp π]
    simp [hπ]
  funext k
  simp only [fundPerm_apply, reflection_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hsum]
  congr 2
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

theorem exists_weylAction_fundPerm {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    {π : Equiv.Perm I} (hπ : ∀ i j, A (π i) (π j) = A i j) (w : (coxeterMatrix hA).Group) :
    ∃ w' : (coxeterMatrix hA).Group,
      ∀ v, fundPerm π (weylAction hA w v) = weylAction hA w' (fundPerm π v) := by
  refine (coxeterMatrix hA).toCoxeterSystem.simple_induction_left
    (p := fun w => ∃ w' : (coxeterMatrix hA).Group,
      ∀ v, fundPerm π (weylAction hA w v) = weylAction hA w' (fundPerm π v)) w ?_ ?_
  · exact ⟨1, fun v => by simp⟩
  · rintro w i ⟨w', hw'⟩
    refine ⟨(coxeterMatrix hA).toCoxeterSystem.simple (π i) * w', fun v => ?_⟩
    rw [weylAction_mul_apply, weylAction_simple, fundPerm_reflection hπ, hw',
      weylAction_mul_apply, weylAction_simple]

theorem fundPerm_mem_roots {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    {π : Equiv.Perm I} (hπ : ∀ i j, A (π i) (π j) = A i j) {γ : I → ℤ}
    (hγ : γ ∈ roots hA ∅) : fundPerm π γ ∈ roots hA ∅ := by
  rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩
  · obtain ⟨w', hw'⟩ := exists_weylAction_fundPerm hA hπ w
    exact Or.inl ⟨w', π i, by rw [hw', fundPerm_single]⟩
  · exact absurd hi (Set.notMem_empty i)

theorem cartan_symm_of_perm {A : Matrix I I ℤ} {π : Equiv.Perm I}
    (hπ : ∀ i j, A (π i) (π j) = A i j) (i j : I) : A (π.symm i) (π.symm j) = A i j := by
  simpa using (hπ (π.symm i) (π.symm j)).symm

theorem fundPerm_mem_roots_iff {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)
    {π : Equiv.Perm I} (hπ : ∀ i j, A (π i) (π j) = A i j) {γ : I → ℤ} :
    fundPerm π γ ∈ roots hA ∅ ↔ γ ∈ roots hA ∅ := by
  refine ⟨fun h => ?_, fundPerm_mem_roots hA hπ⟩
  have h' := fundPerm_mem_roots hA (cartan_symm_of_perm hπ) h
  rwa [fundPerm_symm_fundPerm] at h'

end Lattice

section Diagram

@[expose] def d4TrialityPerm : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 0 2

@[expose] def d4ForkPerm : Equiv.Perm (Fin 4) := Equiv.swap 2 3

theorem d4TrialityPerm_apply_zero : d4TrialityPerm 0 = 2 := by decide

theorem d4TrialityPerm_apply_one : d4TrialityPerm 1 = 1 := by decide

theorem d4TrialityPerm_apply_two : d4TrialityPerm 2 = 3 := by decide

theorem d4TrialityPerm_apply_three : d4TrialityPerm 3 = 0 := by decide

theorem cartanD_submatrix_d4TrialityPerm :
    (cartanD 4).submatrix d4TrialityPerm d4TrialityPerm = cartanD 4 := by decide

theorem cartanD_submatrix_d4ForkPerm : (cartanD 4).submatrix d4ForkPerm d4ForkPerm = cartanD 4 := by
  decide

theorem cartanD_d4TrialityPerm (i j : Fin 4) :
    cartanD 4 (d4TrialityPerm i) (d4TrialityPerm j) = cartanD 4 i j :=
  congrFun (congrFun cartanD_submatrix_d4TrialityPerm i) j

theorem cartanD_d4ForkPerm (i j : Fin 4) :
    cartanD 4 (d4ForkPerm i) (d4ForkPerm j) = cartanD 4 i j :=
  congrFun (congrFun cartanD_submatrix_d4ForkPerm i) j

theorem d4TrialityPerm_pow_three : d4TrialityPerm ^ 3 = 1 := by decide

theorem d4ForkPerm_mul_self : d4ForkPerm * d4ForkPerm = 1 := by decide

theorem d4ForkPerm_conj_d4TrialityPerm :
    d4ForkPerm * d4TrialityPerm * d4ForkPerm = d4TrialityPerm⁻¹ := by decide

@[expose] def d4DiagramGroup : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {π | ∀ i j, cartanD 4 (π i) (π j) = cartanD 4 i j}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {π π'} hπ hπ' i j => by
    simp only [Equiv.Perm.mul_apply]
    rw [hπ, hπ']
  inv_mem' := fun {π} hπ i j => cartan_symm_of_perm hπ i j

theorem mem_d4DiagramGroup_iff {π : Equiv.Perm (Fin 4)} :
    π ∈ d4DiagramGroup ↔ ∀ i j, cartanD 4 (π i) (π j) = cartanD 4 i j := Iff.rfl

@[expose] def d4TrialitySym : d4DiagramGroup := ⟨d4TrialityPerm, cartanD_d4TrialityPerm⟩

@[expose] def d4ForkSym : d4DiagramGroup := ⟨d4ForkPerm, cartanD_d4ForkPerm⟩

theorem d4TrialitySym_pow_three : d4TrialitySym ^ 3 = 1 :=
  Subtype.ext d4TrialityPerm_pow_three

theorem d4ForkSym_mul_self : d4ForkSym * d4ForkSym = 1 :=
  Subtype.ext d4ForkPerm_mul_self

theorem d4ForkSym_conj_d4TrialitySym : d4ForkSym * d4TrialitySym * d4ForkSym = d4TrialitySym⁻¹ :=
  Subtype.ext d4ForkPerm_conj_d4TrialityPerm

end Diagram

section Spin

variable {F : Type} [Field F]

theorem d4_three_le : 3 ≤ 4 := by norm_num

theorem d4_roots_eq : (SpinPlus.Φ 4 F d4_three_le).roots = roots (isFiniteType_cartanD 4) ∅ :=
  rfl

theorem fundPerm_mem_spinRoots (π : d4DiagramGroup) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) :
    fundPerm (π : Equiv.Perm (Fin 4)) γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots :=
  fundPerm_mem_roots (isFiniteType_cartanD 4) π.2 hγ

theorem fundPerm_mem_spinRoots_iff (π : d4DiagramGroup) {γ : Fin 4 → ℤ} :
    fundPerm (π : Equiv.Perm (Fin 4)) γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots ↔
      γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots :=
  fundPerm_mem_roots_iff (isFiniteType_cartanD 4) π.2

variable [CharP F 2]

theorem intCast_commC_eq_one (α β : Fin 4 → ℤ) (p : ℕ × ℕ) :
    ((SpinPlus.commC α β p : ℤ) : F) = 1 := by
  rcases Int.natAbs_eq_iff.1 (SpinPlus.commC_natAbs α β p) with h | h <;> rw [h]
  · simp
  · simp [CharTwo.neg_eq]

theorem commutatorFormula_fundPerm (π : d4DiagramGroup)
    (O : CommOrder (SpinPlus.Φ 4 F d4_three_le)) :
    CommutatorFormula
      (fun γ c => SpinPlus.x 4 F d4_three_le (fundPerm (π : Equiv.Perm (Fin 4)) γ) c)
      O SpinPlus.commC := by
  intro α hα β hβ hαβ c d
  have hα' := fundPerm_mem_spinRoots π hα
  have hβ' := fundPerm_mem_spinRoots π hβ
  have hαβ' : fundPerm (π : Equiv.Perm (Fin 4)) α + fundPerm (π : Equiv.Perm (Fin 4)) β ≠ 0 := by
    rw [← map_add]
    intro h
    apply hαβ
    have h' := congrArg (fundPerm (π : Equiv.Perm (Fin 4)).symm) h
    rwa [fundPerm_symm_fundPerm, map_zero] at h'
  have hroot : fundPerm (π : Equiv.Perm (Fin 4)) α + fundPerm (π : Equiv.Perm (Fin 4)) β ∈
      (SpinPlus.Φ 4 F d4_three_le).roots ↔ α + β ∈ (SpinPlus.Φ 4 F d4_three_le).roots := by
    rw [← map_add]
    exact fundPerm_mem_spinRoots_iff π
  have hcomm := SpinPlus.commutatorFormula d4_three_le O _ hα' _ hβ' hαβ' c d
  by_cases hr : α + β ∈ (SpinPlus.Φ 4 F d4_three_le).roots
  · rw [(SpinPlus.commOrder_list_eq d4_three_le O hα hβ hαβ).1 hr]
    rw [(SpinPlus.commOrder_list_eq d4_three_le O hα' hβ' hαβ').1 (hroot.2 hr)] at hcomm
    simp only [List.map_singleton, List.prod_singleton, one_smul, pow_one,
      intCast_commC_eq_one, one_mul] at hcomm ⊢
    rw [hcomm, map_add]
  · rw [(SpinPlus.commOrder_list_eq d4_three_le O hα hβ hαβ).2 hr]
    rw [(SpinPlus.commOrder_list_eq d4_three_le O hα' hβ' hαβ').2 (fun h => hr (hroot.1 h))]
      at hcomm
    exact hcomm

theorem spin8_rels_fundPerm (π : d4DiagramGroup) (O : CommOrder (SpinPlus.Φ 4 F d4_three_le)) :
    ∀ r ∈ relA (SpinPlus.Φ 4 F d4_three_le) F ∪ relB (SpinPlus.Φ 4 F d4_three_le) F O
      SpinPlus.commC,
      FreeGroup.lift (chevEval (fun γ c =>
        SpinPlus.x 4 F d4_three_le (fundPerm (π : Equiv.Perm (Fin 4)) γ) c)) r = 1 :=
  chevEval_rels
    (fun _ hγ c d => ((SpinPlus.isParametrization d4_three_le) _
      (fundPerm_mem_spinRoots π hγ)).2.1 c d)
    (commutatorFormula_fundPerm π O)

variable [Finite F]

variable (F) in
@[expose] noncomputable def spin8CommOrder : CommOrder (SpinPlus.Φ 4 F d4_three_le) :=
  (SpinPlus.conclusionB (K := F) d4_three_le).2.1.some

theorem spin8_presentation :
    ∃ h : ∀ r ∈ relA (SpinPlus.Φ 4 F d4_three_le) F ∪
        relB (SpinPlus.Φ 4 F d4_three_le) F (spin8CommOrder F) SpinPlus.commC,
        FreeGroup.lift (chevEval (SpinPlus.x 4 F d4_three_le)) r = 1,
      Function.Bijective (PresentedGroup.toGroup h) :=
  (SpinPlus.presentationB d4_three_le (spin8CommOrder F)).2 SpinPlus.commC
    (SpinPlus.commutatorFormula d4_three_le _)

variable (F) in
@[expose] noncomputable def spin8PresEquiv :
    ChevPresented (SpinPlus.Φ 4 F d4_three_le) F (spin8CommOrder F) SpinPlus.commC ≃*
      spinGroup (quadPlus 4 F) :=
  MulEquiv.ofBijective (PresentedGroup.toGroup spin8_presentation.fst) spin8_presentation.snd

theorem spin8PresEquiv_of {γ : Fin 4 → ℤ} (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    spin8PresEquiv F (PresentedGroup.of (⟨γ, hγ⟩, c)) = SpinPlus.x 4 F d4_three_le γ c := by
  rw [spin8PresEquiv, MulEquiv.ofBijective_apply, PresentedGroup.toGroup.of]
  rfl

theorem spin8PresEquiv_symm_x {γ : Fin 4 → ℤ} (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots)
    (c : F) :
    (spin8PresEquiv F).symm (SpinPlus.x 4 F d4_three_le γ c) = PresentedGroup.of (⟨γ, hγ⟩, c) := by
  rw [MulEquiv.symm_apply_eq, spin8PresEquiv_of]

theorem spin8_hom_ext {G : Type*} [Group G] {f g : spinGroup (quadPlus 4 F) →* G}
    (h : ∀ γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots, ∀ c : F,
      f (SpinPlus.x 4 F d4_three_le γ c) = g (SpinPlus.x 4 F d4_three_le γ c)) : f = g := by
  have h1 : f.comp (spin8PresEquiv F).toMonoidHom = g.comp (spin8PresEquiv F).toMonoidHom := by
    apply PresentedGroup.ext
    rintro ⟨⟨γ, hγ⟩, c⟩
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spin8PresEquiv_of]
    exact h γ hγ c
  ext y
  obtain ⟨z, rfl⟩ := (spin8PresEquiv F).surjective y
  exact DFunLike.congr_fun h1 z

theorem spin8_mulAut_ext {f g : MulAut (spinGroup (quadPlus 4 F))}
    (h : ∀ γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots, ∀ c : F,
      f (SpinPlus.x 4 F d4_three_le γ c) = g (SpinPlus.x 4 F d4_three_le γ c)) : f = g := by
  have h' := spin8_hom_ext (f := f.toMonoidHom) (g := g.toMonoidHom) h
  exact MulEquiv.ext fun y => DFunLike.congr_fun h' y

@[expose] noncomputable def spinGraphHom (π : d4DiagramGroup) :
    spinGroup (quadPlus 4 F) →* spinGroup (quadPlus 4 F) :=
  (PresentedGroup.toGroup (spin8_rels_fundPerm π (spin8CommOrder F))).comp
    (spin8PresEquiv F).symm.toMonoidHom

theorem spinGraphHom_x (π : d4DiagramGroup) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    spinGraphHom π (SpinPlus.x 4 F d4_three_le γ c) =
      SpinPlus.x 4 F d4_three_le (fundPerm (π : Equiv.Perm (Fin 4)) γ) c := by
  rw [spinGraphHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, spin8PresEquiv_symm_x hγ,
    PresentedGroup.toGroup.of]
  rfl

theorem spinGraphHom_mul (π π' : d4DiagramGroup) :
    spinGraphHom (F := F) (π * π') = (spinGraphHom π).comp (spinGraphHom π') := by
  refine spin8_hom_ext fun γ hγ c => ?_
  rw [MonoidHom.comp_apply, spinGraphHom_x _ hγ, spinGraphHom_x _ hγ,
    spinGraphHom_x _ (fundPerm_mem_spinRoots π' hγ), Subgroup.coe_mul, fundPerm_mul]

theorem spinGraphHom_one : spinGraphHom (F := F) 1 = MonoidHom.id _ := by
  refine spin8_hom_ext fun γ hγ c => ?_
  rw [spinGraphHom_x _ hγ, MonoidHom.id_apply]
  rfl

@[expose] noncomputable def spinGraphAut : d4DiagramGroup →* MulAut (spinGroup (quadPlus 4 F)) where
  toFun π := MonoidHom.toMulEquiv (spinGraphHom π) (spinGraphHom π⁻¹)
    (by rw [← spinGraphHom_mul, inv_mul_cancel, spinGraphHom_one])
    (by rw [← spinGraphHom_mul, mul_inv_cancel, spinGraphHom_one])
  map_one' := by
    apply MulEquiv.ext
    intro y
    change spinGraphHom 1 y = y
    rw [spinGraphHom_one, MonoidHom.id_apply]
  map_mul' π π' := by
    apply MulEquiv.ext
    intro y
    change spinGraphHom (π * π') y = spinGraphHom π (spinGraphHom π' y)
    rw [spinGraphHom_mul, MonoidHom.comp_apply]

theorem spinGraphAut_apply (π : d4DiagramGroup) (y : spinGroup (quadPlus 4 F)) :
    spinGraphAut π y = spinGraphHom π y := rfl

theorem spinGraphAut_x (π : d4DiagramGroup) {γ : Fin 4 → ℤ}
    (hγ : γ ∈ (SpinPlus.Φ 4 F d4_three_le).roots) (c : F) :
    spinGraphAut π (SpinPlus.x 4 F d4_three_le γ c) =
      SpinPlus.x 4 F d4_three_le (fundPerm (π : Equiv.Perm (Fin 4)) γ) c :=
  spinGraphHom_x π hγ c

theorem fundPerm_neg_single (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    fundPerm π (-Pi.single k 1) = -Pi.single (π k) 1 := by
  rw [map_neg, fundPerm_single]

theorem torusD_eq_x (k : Fin 4) (s : Fˣ) :
    torusD F d4_three_le k s =
      SpinPlus.x 4 F d4_three_le (Pi.single k 1) s *
        SpinPlus.x 4 F d4_three_le (-Pi.single k 1) (-(s⁻¹ : Fˣ) : F) *
        SpinPlus.x 4 F d4_three_le (Pi.single k 1) s *
        (SpinPlus.x 4 F d4_three_le (Pi.single k 1) (((-1 : Fˣ) : Fˣ) : F) *
        SpinPlus.x 4 F d4_three_le (-Pi.single k 1) (-((-1 : Fˣ)⁻¹ : Fˣ) : F) *
        SpinPlus.x 4 F d4_three_le (Pi.single k 1) (((-1 : Fˣ) : Fˣ) : F)) := by
  change rankOneD F d4_three_le k (diagSL2 s) = _
  simp only [diagSL2_eq, weylSL2_eq, map_mul, SpinPlus.x_single, SpinPlus.x_neg_single]

theorem spinGraphAut_torusD (π : d4DiagramGroup) (k : Fin 4) (s : Fˣ) :
    spinGraphAut π (torusD F d4_three_le k s) =
      torusD F d4_three_le ((π : Equiv.Perm (Fin 4)) k) s := by
  have hk := (SpinPlus.Φ 4 F d4_three_le).single_mem k
  have hk' := (SpinPlus.Φ 4 F d4_three_le).neg_mem _ hk
  rw [torusD_eq_x, torusD_eq_x]
  simp only [map_mul, spinGraphAut_x π hk, spinGraphAut_x π hk', fundPerm_single,
    fundPerm_neg_single]

end Spin

end CFSG.SeitzReduction.OmegaPilot
