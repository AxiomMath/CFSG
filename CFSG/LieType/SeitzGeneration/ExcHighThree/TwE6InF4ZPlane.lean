module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZWeyl
public import CFSG.LieType.SeitzGeneration.ExcHighThree.TwE6InF4ZSL2
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcHighThree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.Tables.T1b

set_option linter.unusedSectionVars false


abbrev f4One : Fin Tag.F4.rank := ⟨1, by decide⟩

abbrev f4Two : Fin Tag.F4.rank := ⟨2, by decide⟩

abbrev f4Three : Fin Tag.F4.rank := ⟨3, by decide⟩

@[expose] def f4Word : Fin 3 → List (Fin Tag.F4.rank)
  | 0 => []
  | 1 => [f4Two]
  | 2 => [f4Three, f4Two]

@[expose] def f4Gamma : Fin 3 → (Fin Tag.F4.rank → ℤ)
  | 0 => ![0, 1, 0, 0]
  | 1 => ![0, 1, 2, 0]
  | 2 => ![0, 1, 2, 2]

theorem wordProd_f4Word (i : Fin 3) :
    (coxeterSystem Tag.F4).wordProd (f4Word i) • (Pi.single f4One 1 : Fin Tag.F4.rank → ℤ) =
      f4Gamma i := by
  fin_cases i
  · simp only [f4Word, CoxeterSystem.wordProd_nil, one_smul]
    decide +kernel
  · simp only [f4Word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      simple_smul]
    decide +kernel
  · simp only [f4Word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one,
      mul_smul, simple_smul]
    decide +kernel

theorem isRoot_f4Gamma (i : Fin 3) : IsRoot Tag.F4 (f4Gamma i) := by
  rw [← wordProd_f4Word]
  exact IsRoot.smul (isRoot_single _ _) _

theorem f4Gamma_orth : ∀ i j : Fin 3, i < j →
    iform (f4Gamma i) (f4Gamma j) = 0 ∧ List.ofFn (f4Gamma i + f4Gamma j) ∉ Tag.F4.artifactRoots ∧
      List.ofFn (f4Gamma i - f4Gamma j) ∉ Tag.F4.artifactRoots := by
  decide +kernel

section Groups

variable {L : Type} [Field L]

@[expose] def f4Rho (L : Type) [Field L] : SL2 L →* ModGL Tag.F4 L :=
  simpleRootSL2 Tag.F4 L f4One

@[expose] def f4Phi (L : Type) [Field L] (i : Fin 3) : SL2 L →* ModGL Tag.F4 L :=
  (MulAut.conj (weylWord L (f4Word i))).toMonoidHom.comp (f4Rho L)

theorem f4Phi_apply (i : Fin 3) (A : SL2 L) :
    f4Phi L i A = weylWord L (f4Word i) * f4Rho L A * (weylWord L (f4Word i))⁻¹ := rfl

theorem f4Phi_mem (i : Fin 3) (A : SL2 L) :
    f4Phi L i A ∈ rootRankOneGroup Tag.F4 L (f4Gamma i) := by
  have h := conj_mem_rootRankOneGroup (L := L) (f4Word i) (isRoot_single Tag.F4 f4One)
    (simpleRootSL2_mem_rootRankOneGroup f4One A)
  rwa [wordProd_f4Word] at h

theorem f4Phi_mem_adjointGroup (i : Fin 3) (A : SL2 L) : f4Phi L i A ∈ adjointGroup Tag.F4 L := by
  rw [f4Phi_apply]
  exact mul_mem (mul_mem (weylWord_mem_adjointGroup _) (simpleRootSL2_mem_adjointGroup _ A))
    (inv_mem (weylWord_mem_adjointGroup _))

theorem f4Phi_commute {i j : Fin 3} (h : i < j) (A B : SL2 L) :
    Commute (f4Phi L i A) (f4Phi L j B) := by
  obtain ⟨h0, hp, hm⟩ := f4Gamma_orth i j h
  have hp' : ¬ IsRoot Tag.F4 (f4Gamma i + f4Gamma j) := fun hr =>
    hp (isRoot_iff_mem_artifactRoots.1 hr)
  have hm' : ¬ IsRoot Tag.F4 (f4Gamma i - f4Gamma j) := fun hr =>
    hm (isRoot_iff_mem_artifactRoots.1 hr)
  exact exceptional_Lang_strongly_orthogonal_root_rank_one_commutation Tag.F4 L (isRoot_f4Gamma i)
    (isRoot_f4Gamma j) h0 hp' hm' _ (f4Phi_mem i A) _ (f4Phi_mem j B)

variable (L) in
@[expose] def f4Phi12 : SL2 L × SL2 L →* ModGL Tag.F4 L :=
  (f4Phi L 1).noncommCoprod (f4Phi L 2) fun A B => f4Phi_commute (by decide) A B

variable (L) in
@[expose] def f4PhiAll : SL2 L × (SL2 L × SL2 L) →* ModGL Tag.F4 L :=
  (f4Phi L 0).noncommCoprod (f4Phi12 L) fun A BC =>
    (f4Phi_commute (by decide) A BC.1).mul_right (f4Phi_commute (by decide) A BC.2)

theorem f4PhiAll_apply (A B C : SL2 L) :
    f4PhiAll L (A, B, C) = f4Phi L 0 A * (f4Phi L 1 B * f4Phi L 2 C) := rfl

theorem f4PhiAll_mem_adjointGroup (x : SL2 L × (SL2 L × SL2 L)) :
    f4PhiAll L x ∈ adjointGroup Tag.F4 L := by
  obtain ⟨A, B, C⟩ := x
  rw [f4PhiAll_apply]
  exact mul_mem (f4Phi_mem_adjointGroup 0 A)
    (mul_mem (f4Phi_mem_adjointGroup 1 B) (f4Phi_mem_adjointGroup 2 C))

@[expose] def f4S (L : Type) [Field L] : ModGL Tag.F4 L :=
  xUnit Tag.F4 L f4One 1 * yUnit Tag.F4 L f4One (-3)

theorem f4Rho_zA : f4Rho L zA = f4S L := by
  rw [zA, map_mul, f4Rho, simpleRootSL2_uSL, simpleRootSL2_vSL, f4S]

variable (L) in
@[expose] def f4Z : ModGL Tag.F4 L := f4PhiAll L (zA, zA, zA)

theorem f4Z_eq : f4Z L = f4Phi L 0 zA * (f4Phi L 1 zA * f4Phi L 2 zA) := rfl

theorem f4Phi_zA (i : Fin 3) :
    f4Phi L i zA = weylWord L (f4Word i) * f4S L * (weylWord L (f4Word i))⁻¹ := by
  rw [f4Phi_apply, f4Rho_zA]

theorem f4Z_mem_adjointGroup : f4Z L ∈ adjointGroup Tag.F4 L := f4PhiAll_mem_adjointGroup _

theorem baseChangeGL_f4Z {k Ω : Type} [Field k] [Field Ω] (f : k →+* Ω) :
    baseChangeGL f (f4Z k) = f4Z Ω := by
  have hS : baseChangeGL f (f4S k) = f4S Ω := by
    rw [f4S, f4S, map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit, map_one, map_neg,
      map_ofNat]
  have hP : ∀ i : Fin 3, baseChangeGL f (f4Phi k i zA) = f4Phi Ω i zA := fun i => by
    rw [f4Phi_zA, f4Phi_zA, map_mul, map_mul, map_inv, baseChangeGL_weylWord, hS]
  rw [f4Z_eq, f4Z_eq, map_mul, map_mul, hP, hP, hP]

theorem prod_zpow_eq_zpow_sum_f4 {G ι : Type*} [CommGroup G] (ξ : G) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, ξ ^ f i = ξ ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]

theorem rootChar_zpow_tuple {τ : Tag} {Ω : Type} [Field Ω] (ω : Ωˣ) (c v : Fin τ.rank → ℤ) :
    rootChar (fun l => ω ^ c l) v = ω ^ (∑ l, v l * c l) := by
  simp only [rootChar, ← zpow_mul]
  rw [prod_zpow_eq_zpow_sum_f4]
  exact congrArg _ (Finset.sum_congr rfl fun l _ => mul_comm _ _)

theorem weylAct_zpow_tuple {τ : Tag} {Ω : Type} [Field Ω] (w : WeylGroup τ) (ω : Ωˣ)
    (c : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    weylAct w (fun l => ω ^ c l) j = ω ^ (∑ l, (w⁻¹ • (Pi.single j 1 : Fin τ.rank → ℤ)) l * c l) :=
  rootChar_zpow_tuple ω c _

@[expose] def f4Exp : Fin Tag.F4.rank → ℤ := ![-3, 2, 0, 0]

theorem f4_exp_sum (j : Fin Tag.F4.rank) :
    (∑ l, (((coxeterSystem Tag.F4).wordProd (f4Word 0))⁻¹ • (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) l *
        Tag.F4.cartan f4One l) +
      ((∑ l, (((coxeterSystem Tag.F4).wordProd (f4Word 1))⁻¹ •
          (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) l * Tag.F4.cartan f4One l) +
        (∑ l, (((coxeterSystem Tag.F4).wordProd (f4Word 2))⁻¹ •
          (Pi.single j 1 : Fin Tag.F4.rank → ℤ)) l * Tag.F4.cartan f4One l)) = f4Exp j := by
  simp only [f4Word, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_inv_rev,
    CoxeterSystem.inv_simple, inv_one, one_smul, mul_smul, simple_smul]
  revert j
  decide +kernel

theorem f4_tuple_prod {Ω : Type} [Field Ω] (ω₀ : Ωˣ) :
    weylAct ((coxeterSystem Tag.F4).wordProd (f4Word 0)) (fun l => ω₀ ^ Tag.F4.cartan f4One l) *
      (weylAct ((coxeterSystem Tag.F4).wordProd (f4Word 1)) (fun l => ω₀ ^ Tag.F4.cartan f4One l) *
        weylAct ((coxeterSystem Tag.F4).wordProd (f4Word 2))
          (fun l => ω₀ ^ Tag.F4.cartan f4One l)) = fun j => ω₀ ^ f4Exp j := by
  funext j
  simp only [Pi.mul_apply, weylAct_zpow_tuple, ← zpow_add]
  rw [f4_exp_sum]

theorem f4Phi_HSL (i : Fin 3) {Ω : Type} [Field Ω] (c : Ωˣ) :
    f4Phi Ω i (HSL c) = rootDiagUnit Tag.F4 (weylAct ((coxeterSystem Tag.F4).wordProd (f4Word i))
      (fun l => c ^ Tag.F4.cartan f4One l)) := by
  rw [f4Phi_apply, f4Rho, simpleRootSL2_HSL, torusElt_eq_rootDiagUnit, weylWord_conj_rootDiagUnit]

theorem f4Z_diag {Ω : Type} [Field Ω] (ω₀ : Ωˣ) (h2 : (ω₀ : Ω) ^ 2 + ω₀ + 1 = 0)
    (h1 : (ω₀ : Ω) ≠ 1) :
    ∃ P : ModGL Tag.F4 Ω, P ∈ adjointGroup Tag.F4 Ω ∧
      P⁻¹ * f4Z Ω * P = rootDiagUnit Tag.F4 (fun j => ω₀ ^ f4Exp j) := by
  obtain ⟨M, hM⟩ := exists_conj_zA_eq_HSL ω₀ h2 h1
  refine ⟨f4PhiAll Ω (M, M, M), f4PhiAll_mem_adjointGroup _, ?_⟩
  have hprod : ((M, M, M) : SL2 Ω × (SL2 Ω × SL2 Ω))⁻¹ * (zA, zA, zA) * (M, M, M) =
      (HSL ω₀, HSL ω₀, HSL ω₀) := by
    simp only [Prod.inv_mk, Prod.mk_mul_mk, hM]
  have e1 : (f4PhiAll Ω (M, M, M))⁻¹ * f4Z Ω * f4PhiAll Ω (M, M, M) =
      f4PhiAll Ω (HSL ω₀, HSL ω₀, HSL ω₀) := by
    rw [← hprod, map_mul, map_mul, map_inv]
    rfl
  rw [e1, f4PhiAll_apply, f4Phi_HSL, f4Phi_HSL, f4Phi_HSL, ← f4_tuple_prod ω₀]
  simp only [rootDiagUnit_mul]

end Groups

end CFSG.LieType.SeitzGeneration.ExcHighThree
