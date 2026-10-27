module

public import CFSG.LieType.Chevalley.Native
public import CFSG.LieType.Chevalley.FixedBruhat
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

section Lattice

variable {τ : Tag}

theorem permLattice_add (π : Equiv.Perm (Fin τ.rank)) (u v : Fin τ.rank → ℤ) :
    permLattice π (u + v) = permLattice π u + permLattice π v :=
  rfl

theorem permLattice_neg (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice π (-v) = -permLattice π v :=
  rfl

theorem permLattice_sub (π : Equiv.Perm (Fin τ.rank)) (u v : Fin τ.rank → ℤ) :
    permLattice π (u - v) = permLattice π u - permLattice π v :=
  rfl

theorem permLattice_zsmul (π : Equiv.Perm (Fin τ.rank)) (k : ℤ) (v : Fin τ.rank → ℤ) :
    permLattice π (k • v) = k • permLattice π v :=
  rfl

theorem permLattice_symm_permLattice (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice π.symm (permLattice π v) = v := by
  ext j
  simp [permLattice]

theorem permLattice_permLattice_symm (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    permLattice π (permLattice π.symm v) = v := by
  simpa using permLattice_symm_permLattice π.symm v

theorem permLattice_injective (π : Equiv.Perm (Fin τ.rank)) :
    Function.Injective (permLattice (τ := τ) π) := fun u v h => by
  simpa [permLattice_symm_permLattice] using congrArg (permLattice π.symm) h

theorem height_permLattice (π : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    height (permLattice π v) = height v :=
  Equiv.sum_comp π.symm v

theorem permLattice_add_smul_single (π : Equiv.Perm (Fin τ.rank)) (i : Fin τ.rank)
    (v : Fin τ.rank → ℤ) (k : ℤ) :
    permLattice π (v + k • Pi.single i 1) = permLattice π v + k • Pi.single (π i) 1 := by
  rw [permLattice_add, permLattice_zsmul, permLattice_single]

theorem permLattice_sub_smul_single (π : Equiv.Perm (Fin τ.rank)) (i : Fin τ.rank)
    (v : Fin τ.rank → ℤ) (k : ℤ) :
    permLattice π (v - k • Pi.single i 1) = permLattice π v - k • Pi.single (π i) 1 := by
  rw [permLattice_sub, permLattice_zsmul, permLattice_single]

theorem permLattice_neg_single (π : Equiv.Perm (Fin τ.rank)) (i : Fin τ.rank) :
    permLattice π (-Pi.single i 1) = -Pi.single (π i) 1 := by
  rw [permLattice_neg, permLattice_single]

variable {π : Equiv.Perm (Fin τ.rank)} (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
include hπ

theorem isRoot_permLattice_iff {v : Fin τ.rank → ℤ} :
    IsRoot τ (permLattice π v) ↔ IsRoot τ v := by
  refine ⟨fun h => ?_, fun h => h.permLattice hπ⟩
  simpa [permLattice_symm_permLattice] using h.permLattice (cartan_perm_symm hπ)

theorem stringUp_permLattice (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    stringUp τ (π i) (permLattice π α) = stringUp τ i α := by
  unfold stringUp
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  rw [← permLattice_single, ← permLattice_zsmul, ← permLattice_add, isRoot_permLattice_iff hπ]

theorem stringDown_permLattice (i : Fin τ.rank) (α : Fin τ.rank → ℤ) :
    stringDown τ (π i) (permLattice π α) = stringDown τ i α := by
  unfold stringDown
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq]
  rw [← permLattice_single, ← permLattice_zsmul, ← permLattice_sub, isRoot_permLattice_iff hπ]

end Lattice

section DiagramMap

variable (t : TwistTag) (K : Type) [Field K]

theorem diagramMap_apply_rootVec (β : Fin t.tag.rank → ℤ) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) (rootVec t.tag K β) =
      rootVec t.tag K (permLattice t.perm β) := by
  by_cases hβ : IsRoot t.tag β
  · exact diagramMap_rootVec t K β hβ
  · have hβ' : ¬IsRoot t.tag (permLattice t.perm β) :=
      (isRoot_permLattice_iff t.cartan_perm).not.2 hβ
    simp [rootVec, hβ, hβ']

private theorem end_ext_basis {τ : Tag} {f g : Module.End K (RootModule τ K)}
    (hh : ∀ j, f (hVec τ K j) = g (hVec τ K j))
    (hr : ∀ α, IsRoot τ α → f (rootVec τ K α) = g (rootVec τ K α)) : f = g := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rcases b with j | ⟨α, hα⟩
  · exact hh j
  · rw [← rootVec_eq_single hα]
    exact hr α hα

theorem diagramMap_mul_xCoeff (i : Fin t.tag.rank) (k : ℕ) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) * xCoeff t.tag K i k =
      xCoeff t.tag K (t.perm i) k * (diagramMap t K : Module.End K (RootModule t.tag K)) := by
  refine end_ext_basis K (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, diagramMap_hVec, xCoeff_hVec, t.cartan_perm]
    split_ifs <;> simp [diagramMap_hVec, diagramMap_apply_rootVec, permLattice_single]
  · simp only [Module.End.mul_apply, diagramMap_apply_rootVec]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [permLattice_single, xCoeff_rootVec_single, xCoeff_rootVec_single]
      split_ifs <;> simp [diagramMap_apply_rootVec, permLattice_single]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [permLattice_neg_single, xCoeff_rootVec_neg_single, xCoeff_rootVec_neg_single]
      split_ifs <;> simp [diagramMap_apply_rootVec, diagramMap_hVec, permLattice_single,
        permLattice_neg_single]
    have hα' := hα.permLattice t.cartan_perm
    have h₁' : permLattice t.perm α ≠ Pi.single (t.perm i) 1 := by
      rw [← permLattice_single]
      exact (permLattice_injective _).ne h₁
    have h₂' : permLattice t.perm α ≠ -Pi.single (t.perm i) 1 := by
      rw [← permLattice_neg_single]
      exact (permLattice_injective _).ne h₂
    rw [xCoeff_rootVec_of_ne i k hα h₁ h₂, xCoeff_rootVec_of_ne (t.perm i) k hα' h₁' h₂',
      map_smul, diagramMap_apply_rootVec, permLattice_add_smul_single,
      stringDown_permLattice t.cartan_perm]

theorem diagramMap_mul_yCoeff (i : Fin t.tag.rank) (k : ℕ) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) * yCoeff t.tag K i k =
      yCoeff t.tag K (t.perm i) k * (diagramMap t K : Module.End K (RootModule t.tag K)) := by
  refine end_ext_basis K (fun j => ?_) (fun α hα => ?_)
  · simp only [Module.End.mul_apply, diagramMap_hVec, yCoeff_hVec, t.cartan_perm]
    split_ifs <;> simp [diagramMap_hVec, diagramMap_apply_rootVec, permLattice_neg_single]
  · simp only [Module.End.mul_apply, diagramMap_apply_rootVec]
    by_cases h₂ : α = -Pi.single i 1
    · subst h₂
      rw [permLattice_neg_single, yCoeff_rootVec_neg_single, yCoeff_rootVec_neg_single]
      split_ifs <;> simp [diagramMap_apply_rootVec, permLattice_neg_single]
    by_cases h₁ : α = Pi.single i 1
    · subst h₁
      rw [permLattice_single, yCoeff_rootVec_single, yCoeff_rootVec_single]
      split_ifs <;> simp [diagramMap_apply_rootVec, diagramMap_hVec, permLattice_single,
        permLattice_neg_single]
    have hα' := hα.permLattice t.cartan_perm
    have h₁' : permLattice t.perm α ≠ Pi.single (t.perm i) 1 := by
      rw [← permLattice_single]
      exact (permLattice_injective _).ne h₁
    have h₂' : permLattice t.perm α ≠ -Pi.single (t.perm i) 1 := by
      rw [← permLattice_neg_single]
      exact (permLattice_injective _).ne h₂
    rw [yCoeff_rootVec_of_ne i k hα h₁ h₂, yCoeff_rootVec_of_ne (t.perm i) k hα' h₁' h₂',
      map_smul, diagramMap_apply_rootVec, permLattice_sub_smul_single,
      stringUp_permLattice t.cartan_perm]

theorem diagramMap_mul_xOp (i : Fin t.tag.rank) (c : K) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) * xOp t.tag K i c =
      xOp t.tag K (t.perm i) c * (diagramMap t K : Module.End K (RootModule t.tag K)) := by
  rw [xOp_eq_sum_xCoeff, xOp_eq_sum_xCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, diagramMap_mul_xCoeff]

theorem diagramMap_mul_yOp (i : Fin t.tag.rank) (c : K) :
    (diagramMap t K : Module.End K (RootModule t.tag K)) * yOp t.tag K i c =
      yOp t.tag K (t.perm i) c * (diagramMap t K : Module.End K (RootModule t.tag K)) := by
  rw [yOp_eq_sum_yCoeff, yOp_eq_sum_yCoeff, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, diagramMap_mul_yCoeff]

end DiagramMap

section Entrywise

variable {τ : Tag} {K : Type} [Field K] (σ : K →+* K)

private theorem mapRange_smul_ringHom (c : K) (x : RootModule τ K) :
    Finsupp.mapRange σ σ.map_zero (c • x) = σ c • Finsupp.mapRange σ σ.map_zero x := by
  ext a
  simp

theorem entrywise_sum_smul {ι : Type*} (s : Finset ι) (c : ι → K)
    (A : ι → Module.End K (RootModule τ K)) :
    entrywise σ (∑ k ∈ s, c k • A k) = ∑ k ∈ s, σ (c k) • entrywise σ (A k) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, entrywise_single]
  rw [Finsupp.mapRange_finsetSum σ]
  simp only [mapRange_smul_ringHom]

theorem entrywise_xCoeff (i : Fin τ.rank) (k : ℕ) :
    entrywise σ (xCoeff τ K i k) = xCoeff τ K i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, mapRange_xCoeff_single]

theorem entrywise_yCoeff (i : Fin τ.rank) (k : ℕ) :
    entrywise σ (yCoeff τ K i k) = yCoeff τ K i k := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, mapRange_yCoeff_single]

theorem entrywise_xOp (i : Fin τ.rank) (c : K) :
    entrywise σ (xOp τ K i c) = xOp τ K i (σ c) := by
  simp only [xOp_eq_sum_xCoeff, entrywise_sum_smul, entrywise_xCoeff, map_pow]

theorem entrywise_yOp (i : Fin τ.rank) (c : K) :
    entrywise σ (yOp τ K i c) = yOp τ K i (σ c) := by
  simp only [yOp_eq_sum_yCoeff, entrywise_sum_smul, entrywise_yCoeff, map_pow]

theorem entrywise_injective : Function.Injective (entrywise (τ := τ) σ) := by
  intro A B h
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have hb := LinearMap.congr_fun h (Finsupp.single b 1)
  rw [entrywise_single, entrywise_single] at hb
  exact Finsupp.mapRange_injective σ σ.map_zero σ.injective hb

end Entrywise

section Generators

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem twistHom_xUnit (i : Fin t.tag.rank) (c : K) :
    twistHom t K σ (xUnit t.tag K i c) = xUnit t.tag K (t.perm i) (σ c) := by
  refine Units.ext ?_
  rw [coe_twistHom, coe_xUnit, coe_xUnit, entrywise_xOp, diagramMap_mul_xOp, mul_assoc,
    Units.mul_inv, mul_one]

theorem twistHom_yUnit (i : Fin t.tag.rank) (c : K) :
    twistHom t K σ (yUnit t.tag K i c) = yUnit t.tag K (t.perm i) (σ c) := by
  refine Units.ext ?_
  rw [coe_twistHom, coe_yUnit, coe_yUnit, entrywise_yOp, diagramMap_mul_yOp, mul_assoc,
    Units.mul_inv, mul_one]

theorem twistHom_weylElt (i : Fin t.tag.rank) (u : Kˣ) :
    twistHom t K σ (weylElt t.tag K i u) =
      weylElt t.tag K (t.perm i) (Units.map σ.toMonoidHom u) := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, twistHom_xUnit, twistHom_yUnit,
    weylElt_eq_xUnit_mul, ← map_inv, Units.coe_map, Units.coe_map]
  simp

theorem twistHom_weylElt_one (i : Fin t.tag.rank) :
    twistHom t K σ (weylElt t.tag K i 1) = weylElt t.tag K (t.perm i) 1 := by
  rw [twistHom_weylElt, map_one]

theorem twistHom_torusElt (i : Fin t.tag.rank) (u : Kˣ) :
    twistHom t K σ (torusElt t.tag K i u) =
      torusElt t.tag K (t.perm i) (Units.map σ.toMonoidHom u) := by
  have h : Units.map σ.toMonoidHom (-1) = -1 := Units.ext (by simp)
  rw [torusElt, map_mul, twistHom_weylElt, twistHom_weylElt, torusElt, h]

theorem twistHom_injective : Function.Injective (twistHom t K σ) := by
  intro g h hgh
  have h' : Units.map (entrywiseHom σ) g = Units.map (entrywiseHom σ) h :=
    (MulAut.conj (diagramMap t K)).injective hgh
  exact Units.map_injective (f := entrywiseHom σ) (entrywise_injective σ) h'

theorem adjointGroup_le_comap_twistHom :
    adjointGroup t.tag K ≤ (adjointGroup t.tag K).comap (twistHom t K σ) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · have hg' : g = xUnit t.tag K i c := Units.ext hg
    subst hg'
    change twistHom t K σ (xUnit t.tag K i c) ∈ adjointGroup t.tag K
    rw [twistHom_xUnit]
    exact xUnit_mem_adjointGroup _ _
  · have hg' : g = yUnit t.tag K i c := Units.ext hg
    subst hg'
    change twistHom t K σ (yUnit t.tag K i c) ∈ adjointGroup t.tag K
    rw [twistHom_yUnit]
    exact yUnit_mem_adjointGroup _ _

theorem twistHom_mem_adjointGroup {g : ModGL t.tag K} (hg : g ∈ adjointGroup t.tag K) :
    twistHom t K σ g ∈ adjointGroup t.tag K :=
  adjointGroup_le_comap_twistHom t K σ hg

theorem map_twistHom_adjointGroup (hσ : Function.Surjective σ) :
    (adjointGroup t.tag K).map (twistHom t K σ) = adjointGroup t.tag K := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (adjointGroup_le_comap_twistHom t K σ)) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨j, d, hg | hg⟩
  · obtain ⟨c, rfl⟩ := hσ d
    refine ⟨xUnit t.tag K (t.perm.symm j) c, xUnit_mem_adjointGroup _ _, ?_⟩
    rw [twistHom_xUnit, Equiv.apply_symm_apply]
    exact (Units.ext hg).symm
  · obtain ⟨c, rfl⟩ := hσ d
    refine ⟨yUnit t.tag K (t.perm.symm j) c, yUnit_mem_adjointGroup _ _, ?_⟩
    rw [twistHom_yUnit, Equiv.apply_symm_apply]
    exact (Units.ext hg).symm

end Generators

section Restriction

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

@[expose] noncomputable def twistC : adjointGroup t.tag K →* adjointGroup t.tag K where
  toFun g := ⟨twistHom t K σ g, twistHom_mem_adjointGroup t K σ g.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

@[simp] theorem coe_twistC (g : adjointGroup t.tag K) :
    (twistC t K σ g : ModGL t.tag K) = twistHom t K σ g :=
  rfl

theorem twistC_injective : Function.Injective (twistC t K σ) := fun _ _ hgh =>
  Subtype.ext (twistHom_injective t K σ (congrArg Subtype.val hgh))

theorem twistC_surjective (hσ : Function.Surjective σ) : Function.Surjective (twistC t K σ) := by
  rintro ⟨y, hy⟩
  rw [← map_twistHom_adjointGroup t K σ hσ] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, hx⟩, rfl⟩

@[expose] noncomputable def twistEquiv (hσ : Function.Surjective σ) :
    adjointGroup t.tag K ≃* adjointGroup t.tag K :=
  MulEquiv.ofBijective (twistC t K σ) ⟨twistC_injective t K σ, twistC_surjective t K σ hσ⟩

@[simp] theorem twistEquiv_apply (hσ : Function.Surjective σ) (g : adjointGroup t.tag K) :
    twistEquiv t K σ hσ g = twistC t K σ g :=
  rfl

theorem surjective_ringHom_of_finite [Finite K] : Function.Surjective σ :=
  Finite.surjective_of_injective σ.injective

theorem twistC_xElement (i : Fin t.tag.rank) (c : K) :
    twistC t K σ (xElement i c) = xElement (t.perm i) (σ c) :=
  Subtype.ext (twistHom_xUnit t K σ i c)

theorem twistC_yElement (i : Fin t.tag.rank) (c : K) :
    twistC t K σ (yElement i c) = yElement (t.perm i) (σ c) :=
  Subtype.ext (twistHom_yUnit t K σ i c)

theorem twistC_weylElement (i : Fin t.tag.rank) :
    twistC t K σ (weylElement t.tag K i) = weylElement t.tag K (t.perm i) :=
  Subtype.ext (twistHom_weylElt_one t K σ i)

theorem twistC_torusElement (i : Fin t.tag.rank) (u : Kˣ) :
    twistC t K σ (torusElement t.tag K i u) =
      torusElement t.tag K (t.perm i) (Units.map σ.toMonoidHom u) :=
  Subtype.ext (twistHom_torusElt t K σ i u)

end Restriction

section Weyl

open CFSG.LieType.RootSystem

variable {τ : Tag} {π : Equiv.Perm (Fin τ.rank)}

theorem coxeterMatrix_apply_perm (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
    (i j : Fin τ.rank) :
    (coxeterMatrix (isFiniteType_cartan τ)).M (π i) (π j) =
      (coxeterMatrix (isFiniteType_cartan τ)).M i j := by
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hπ]

theorem isLiftable_simple_comp_perm (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) :
    (coxeterMatrix (isFiniteType_cartan τ)).IsLiftable fun i => simple τ (π i) := fun i j => by
  have h := (coxeterSystem τ).simple_mul_simple_pow (π i) (π j)
  rwa [coxeterMatrix_apply_perm hπ] at h

variable (π) in
@[expose] noncomputable def weylGroupPerm (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j) :
    WeylGroup τ →* WeylGroup τ :=
  (coxeterSystem τ).lift ⟨fun i => simple τ (π i), isLiftable_simple_comp_perm hπ⟩

theorem weylGroupPerm_simple (hπ : ∀ i j, τ.cartan (π i) (π j) = τ.cartan i j)
    (i : Fin τ.rank) : weylGroupPerm π hπ (simple τ i) = simple τ (π i) :=
  (coxeterSystem τ).lift_apply_simple (isLiftable_simple_comp_perm hπ) i

end Weyl

section WeylTwist

variable (t : TwistTag)

@[expose] noncomputable def weylTwist : WeylGroup t.tag ≃* WeylGroup t.tag :=
  MonoidHom.toMulEquiv (weylGroupPerm t.perm t.cartan_perm)
    (weylGroupPerm t.perm.symm (cartan_perm_symm t.cartan_perm))
    ((coxeterSystem t.tag).ext_simple fun i => by
      rw [MonoidHom.comp_apply, weylGroupPerm_simple, weylGroupPerm_simple,
        Equiv.symm_apply_apply, MonoidHom.id_apply])
    ((coxeterSystem t.tag).ext_simple fun i => by
      rw [MonoidHom.comp_apply, weylGroupPerm_simple, weylGroupPerm_simple,
        Equiv.apply_symm_apply, MonoidHom.id_apply])

theorem weylTwist_simple (i : Fin t.tag.rank) :
    weylTwist t (simple t.tag i) = simple t.tag (t.perm i) :=
  weylGroupPerm_simple t.cartan_perm i

theorem weylTwist_symm_simple (i : Fin t.tag.rank) :
    (weylTwist t).symm (simple t.tag i) = simple t.tag (t.perm.symm i) :=
  weylGroupPerm_simple (cartan_perm_symm t.cartan_perm) i

theorem weylTwist_wordProd (ω : List (Fin t.tag.rank)) :
    weylTwist t ((coxeterSystem t.tag).wordProd ω) =
      (coxeterSystem t.tag).wordProd (ω.map t.perm) := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, weylTwist_simple, ih, List.map_cons,
      CoxeterSystem.wordProd_cons]

theorem weylTwist_symm_wordProd (ω : List (Fin t.tag.rank)) :
    (weylTwist t).symm ((coxeterSystem t.tag).wordProd ω) =
      (coxeterSystem t.tag).wordProd (ω.map t.perm.symm) := by
  induction ω with
  | nil => simp [CoxeterSystem.wordProd_nil]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul, weylTwist_symm_simple, ih, List.map_cons,
      CoxeterSystem.wordProd_cons]

theorem length_weylTwist_le (w : WeylGroup t.tag) :
    (coxeterSystem t.tag).length (weylTwist t w) ≤ (coxeterSystem t.tag).length w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem t.tag).exists_isReduced w
  rw [weylTwist_wordProd, hω.eq]
  exact ((coxeterSystem t.tag).length_wordProd_le _).trans (by rw [List.length_map])

theorem length_weylTwist_symm_le (w : WeylGroup t.tag) :
    (coxeterSystem t.tag).length ((weylTwist t).symm w) ≤ (coxeterSystem t.tag).length w := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem t.tag).exists_isReduced w
  rw [weylTwist_symm_wordProd, hω.eq]
  exact ((coxeterSystem t.tag).length_wordProd_le _).trans (by rw [List.length_map])

theorem length_weylTwist (w : WeylGroup t.tag) :
    (coxeterSystem t.tag).length (weylTwist t w) = (coxeterSystem t.tag).length w := by
  refine le_antisymm (length_weylTwist_le t w) ?_
  have h := length_weylTwist_symm_le t (weylTwist t w)
  rwa [MulEquiv.symm_apply_apply] at h

theorem isReduced_map_twist {ω : List (Fin t.tag.rank)}
    (hω : (coxeterSystem t.tag).IsReduced ω) : (coxeterSystem t.tag).IsReduced (ω.map t.perm) := by
  change (coxeterSystem t.tag).length ((coxeterSystem t.tag).wordProd (ω.map t.perm)) =
    (ω.map t.perm).length
  rw [← weylTwist_wordProd, length_weylTwist, List.length_map]
  exact hω

theorem weylTwist_smul_permLattice (w : WeylGroup t.tag) (v : Fin t.tag.rank → ℤ) :
    weylTwist t w • permLattice t.perm v = permLattice t.perm (w • v) := by
  induction w using (coxeterSystem t.tag).simple_induction_left generalizing v with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul, mul_smul, mul_smul, ih, weylTwist_simple, simple_smul, simple_smul,
      permLattice_reflect t.cartan_perm]

@[expose] def rootTwist : Root t.tag ≃ Root t.tag where
  toFun α := ⟨permLattice t.perm α.1, α.2.permLattice t.cartan_perm⟩
  invFun α := ⟨permLattice t.perm.symm α.1, α.2.permLattice (cartan_perm_symm t.cartan_perm)⟩
  left_inv α := Subtype.ext (permLattice_symm_permLattice t.perm α.1)
  right_inv α := Subtype.ext (permLattice_permLattice_symm t.perm α.1)

@[simp] theorem coe_rootTwist (α : Root t.tag) :
    (rootTwist t α : Fin t.tag.rank → ℤ) = permLattice t.perm α.1 :=
  rfl

theorem rootTwist_simpleRoot (i : Fin t.tag.rank) :
    rootTwist t (simpleRoot t.tag i) = simpleRoot t.tag (t.perm i) :=
  Subtype.ext (permLattice_single _ _)

theorem height_rootTwist (α : Root t.tag) : height (rootTwist t α).1 = height α.1 :=
  height_permLattice _ _

theorem weylTwist_smul_rootTwist (w : WeylGroup t.tag) (α : Root t.tag) :
    weylTwist t w • rootTwist t α = rootTwist t (w • α) :=
  Subtype.ext (weylTwist_smul_permLattice t w α.1)

end WeylTwist

section Representatives

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem twistC_nrep (w : WeylGroup t.tag) :
    twistC t K σ (nrep t.tag K w) = nrep t.tag K (weylTwist t w) := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem t.tag).exists_isReduced w
  rw [nrep_eq_prod _ _ hω, weylTwist_wordProd, nrep_eq_prod _ _ (isReduced_map_twist t hω),
    map_list_prod, List.map_map, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => twistC_weylElement t K σ i)

end Representatives

section RootSubgroups

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem RootOperatorFamily.exists_twistC_eltElement (Fam : RootOperatorFamily t.tag)
    (α : Root t.tag) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ c : K,
      twistC t K σ (Fam.eltElement α c) = Fam.eltElement (rootTwist t α) ((ε : K) * σ c) := by
  obtain ⟨v, hv⟩ := α
  induction hv with
  | basis j =>
    refine ⟨1, .inl rfl, fun c => Subtype.ext ?_⟩
    change twistHom t K σ (Fam.eltUnit K (simpleRoot t.tag j) c) =
      Fam.eltUnit K (rootTwist t (simpleRoot t.tag j)) _
    rw [rootTwist_simpleRoot, Fam.eltUnit_simple, Fam.eltUnit_simple, twistHom_xUnit,
      Int.cast_one, one_mul]
  | @reflect i v hv ih =>
    obtain ⟨ε, hε, h⟩ := ih
    set α : Root t.tag := ⟨v, hv⟩
    have hα : simple t.tag i • α = ⟨reflect t.tag i v, IsRoot.reflect i hv⟩ :=
      Subtype.ext (simple_smul i v)
    have hρ : simple t.tag (t.perm i) • rootTwist t α = rootTwist t (simple t.tag i • α) := by
      rw [← weylTwist_simple, weylTwist_smul_rootTwist]
    refine ⟨Fam.sign (t.perm i) (rootTwist t α) * ε * Fam.sign i α, ?_, fun c => ?_⟩
    · rcases hε with rfl | rfl <;> rcases Fam.sign_eq (t.perm i) (rootTwist t α) with h' | h' <;>
        rcases Fam.sign_eq i α with h'' | h'' <;> rw [h', h''] <;> norm_num
    · have key := Fam.weylElement_mul_eltElement_mul_inv i α ((Fam.sign i α : K) * c)
      rw [← mul_assoc, Fam.sign_cast_mul_self, one_mul, hα] at key
      rw [← key, map_mul, map_mul, map_inv, twistC_weylElement, h, map_mul, map_intCast,
        Fam.weylElement_mul_eltElement_mul_inv, hρ, hα]
      congr 1
      push_cast
      ring

theorem RootOperatorFamily.twistC_mem_rootSubgroup (Fam : RootOperatorFamily t.tag)
    {α : Root t.tag} {x : adjointGroup t.tag K} (hx : x ∈ Fam.rootSubgroup K α) :
    twistC t K σ x ∈ Fam.rootSubgroup K (rootTwist t α) := by
  obtain ⟨c, rfl⟩ := Fam.mem_rootSubgroup.1 hx
  obtain ⟨ε, -, h⟩ := Fam.exists_twistC_eltElement t K σ α
  rw [h c]
  exact Fam.eltElement_mem_rootSubgroup _ _

theorem RootOperatorFamily.map_twistC_rootSubgroup (Fam : RootOperatorFamily t.tag)
    (hσ : Function.Surjective σ) (α : Root t.tag) :
    (Fam.rootSubgroup K α).map (twistC t K σ) = Fam.rootSubgroup K (rootTwist t α) := by
  obtain ⟨ε, hε, h⟩ := Fam.exists_twistC_eltElement t K σ α
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun x hx =>
    Fam.twistC_mem_rootSubgroup t K σ hx) fun y hy => ?_
  obtain ⟨d, rfl⟩ := Fam.mem_rootSubgroup.1 hy
  obtain ⟨c, hc⟩ := hσ ((ε : K) * d)
  refine ⟨Fam.eltElement α c, Fam.eltElement_mem_rootSubgroup _ _, ?_⟩
  have hεε : (ε : K) * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  rw [h c, hc, ← mul_assoc, hεε, one_mul]

theorem twistC_mem_nativeRootSubgroups {α : Root t.tag} {x : adjointGroup t.tag K}
    (hx : x ∈ (nativeRootSubgroups t.tag K).X α) :
    twistC t K σ x ∈ (nativeRootSubgroups t.tag K).X (rootTwist t α) :=
  (rootOperatorFamily t.tag).twistC_mem_rootSubgroup t K σ hx

theorem map_twistC_nativeRootSubgroups (hσ : Function.Surjective σ) (α : Root t.tag) :
    ((nativeRootSubgroups t.tag K).X α).map (twistC t K σ) =
      (nativeRootSubgroups t.tag K).X (rootTwist t α) :=
  (rootOperatorFamily t.tag).map_twistC_rootSubgroup t K σ hσ α

theorem Uminus_le_comap_twistC (w : WeylGroup t.tag) :
    Uminus t.tag K w ≤ (Uminus t.tag K (weylTwist t w)).comap (twistC t K σ) :=
  iSup₂_le fun α hα x hx => by
    refine le_iSup₂_of_le (f := fun (β : Root t.tag)
      (_ : 0 < height β.1 ∧ height (weylTwist t w • β).1 < 0) => (nativeRootSubgroups t.tag K).X β)
      (rootTwist t α) ?_ le_rfl (twistC_mem_nativeRootSubgroups t K σ hx)
    rw [weylTwist_smul_rootTwist, height_rootTwist, height_rootTwist]
    exact hα

theorem twistC_mem_Uminus {w : WeylGroup t.tag} {u : adjointGroup t.tag K}
    (hu : u ∈ Uminus t.tag K w) : twistC t K σ u ∈ Uminus t.tag K (weylTwist t w) :=
  Uminus_le_comap_twistC t K σ w hu

theorem map_twistC_Uminus (hσ : Function.Surjective σ) (w : WeylGroup t.tag) :
    (Uminus t.tag K w).map (twistC t K σ) = Uminus t.tag K (weylTwist t w) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (Uminus_le_comap_twistC t K σ w)) ?_
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨α, rfl⟩ := (rootTwist t).surjective β
  rw [← map_twistC_nativeRootSubgroups t K σ hσ]
  refine Subgroup.map_mono (le_iSup₂_of_le (f := fun (γ : Root t.tag)
      (_ : 0 < height γ.1 ∧ height (w • γ).1 < 0) => (nativeRootSubgroups t.tag K).X γ) α ?_ le_rfl)
  rw [weylTwist_smul_rootTwist, height_rootTwist, height_rootTwist] at hβ
  exact hβ

end RootSubgroups

section Borel

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem monomialGroup_le_comap_twistC :
    monomialGroup t.tag K ≤ (monomialGroup t.tag K).comap (twistC t K σ) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨i, rfl⟩ | ⟨⟨i, u⟩, rfl⟩)
  · change twistC t K σ (weylElement t.tag K i) ∈ monomialGroup t.tag K
    rw [twistC_weylElement]
    exact weylElement_mem_monomialGroup _
  · change twistC t K σ (torusElement t.tag K i u) ∈ monomialGroup t.tag K
    rw [twistC_torusElement]
    exact torusElement_mem_monomialGroup _ _

theorem twistC_mem_monomialGroup {m : adjointGroup t.tag K} (hm : m ∈ monomialGroup t.tag K) :
    twistC t K σ m ∈ monomialGroup t.tag K :=
  monomialGroup_le_comap_twistC t K σ hm

theorem map_twistC_monomialGroup (hσ : Function.Surjective σ) :
    (monomialGroup t.tag K).map (twistC t K σ) = monomialGroup t.tag K := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 (monomialGroup_le_comap_twistC t K σ)) ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨⟨j, u⟩, rfl⟩)
  · refine ⟨weylElement t.tag K (t.perm.symm j), weylElement_mem_monomialGroup _, ?_⟩
    rw [twistC_weylElement, Equiv.apply_symm_apply]
  · obtain ⟨c, hc⟩ := hσ u
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact u.ne_zero hc.symm
    refine ⟨torusElement t.tag K (t.perm.symm j) (Units.mk0 c hc0),
      torusElement_mem_monomialGroup _ _, ?_⟩
    rw [twistC_torusElement, Equiv.apply_symm_apply]
    congr 1
    exact Units.ext (by simpa using hc)

@[expose] noncomputable def twistN : monomialGroup t.tag K →* monomialGroup t.tag K where
  toFun m := ⟨twistC t K σ m, twistC_mem_monomialGroup t K σ m.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

variable [Finite K]

theorem weylHom_twistN (m : monomialGroup t.tag K) :
    weylHom t.tag K (twistN t K σ m) = weylTwist t (weylHom t.tag K m) := by
  suffices h : (weylHom t.tag K).comp (twistN t K σ) =
      (weylTwist t).toMonoidHom.comp (weylHom t.tag K) from DFunLike.congr_fun h m
  have hgen : Subgroup.closure (((↑) : monomialGroup t.tag K → adjointGroup t.tag K) ⁻¹'
      (Set.range (weylElement t.tag K) ∪
        Set.range fun x : Fin t.tag.rank × Kˣ => torusElement t.tag K x.1 x.2)) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  refine MonoidHom.eq_of_eqOn_dense hgen ?_
  rintro m (⟨i, hi⟩ | ⟨⟨i, u⟩, hi⟩)
  · have hm : m = ⟨weylElement t.tag K i, weylElement_mem_monomialGroup i⟩ := Subtype.ext hi.symm
    subst hm
    have h' : twistN t K σ ⟨weylElement t.tag K i, weylElement_mem_monomialGroup i⟩ =
        ⟨weylElement t.tag K (t.perm i), weylElement_mem_monomialGroup _⟩ :=
      Subtype.ext (twistC_weylElement t K σ i)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h', weylHom_weylElement,
      weylTwist_simple]
  · have hm : m = ⟨torusElement t.tag K i u, torusElement_mem_monomialGroup i u⟩ :=
      Subtype.ext hi.symm
    subst hm
    have h' : twistN t K σ ⟨torusElement t.tag K i u, torusElement_mem_monomialGroup i u⟩ =
        ⟨torusElement t.tag K (t.perm i) (Units.map σ.toMonoidHom u),
          torusElement_mem_monomialGroup _ _⟩ :=
      Subtype.ext (twistC_torusElement t K σ i u)
    simp only [MonoidHom.comp_apply, h', weylHom_torusElement, map_one]

theorem twistC_mem_U {u : adjointGroup t.tag K} (hu : u ∈ (nativeData t.tag K).U) :
    twistC t K σ u ∈ (nativeData t.tag K).U := by
  have hle : (nativeData t.tag K).U ≤ (nativeData t.tag K).U.comap (twistC t K σ) :=
    iSup₂_le fun α hα x hx => (nativeData t.tag K).X_le_U (α := rootTwist t α)
      (by rw [rootCombinatorics_pos, height_rootTwist]; exact hα)
      (twistC_mem_nativeRootSubgroups t K σ hx)
  exact hle hu

theorem map_twistC_U (hσ : Function.Surjective σ) :
    (nativeData t.tag K).U.map (twistC t K σ) = (nativeData t.tag K).U := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun u hu => twistC_mem_U t K σ hu) ?_
  refine iSup₂_le fun β hβ => ?_
  obtain ⟨α, rfl⟩ := (rootTwist t).surjective β
  change (nativeRootSubgroups t.tag K).X (rootTwist t α) ≤ _
  rw [← map_twistC_nativeRootSubgroups t K σ hσ]
  refine Subgroup.map_mono ((nativeData t.tag K).X_le_U (α := α) ?_)
  rw [rootCombinatorics_pos] at hβ ⊢
  rwa [height_rootTwist] at hβ

theorem twistC_mem_H {h : adjointGroup t.tag K} (hh : h ∈ (nativeData t.tag K).H) :
    twistC t K σ h ∈ (nativeData t.tag K).H := by
  obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := RootGroupData.mem_H_iff.1 hh
  have hkN' : k ∈ monomialGroup t.tag K := hkN
  have hk' : weylHom t.tag K ⟨k, hkN'⟩ = 1 := hk
  refine RootGroupData.mem_H_iff.2
    ⟨⟨twistC t K σ k, twistC_mem_monomialGroup t K σ hkN'⟩, ?_, rfl⟩
  change weylHom t.tag K (twistN t K σ ⟨k, hkN'⟩) = 1
  rw [weylHom_twistN, hk', map_one]

theorem map_twistC_H (hσ : Function.Surjective σ) :
    (nativeData t.tag K).H.map (twistC t K σ) = (nativeData t.tag K).H := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.2 fun h hh => twistC_mem_H t K σ hh)
    fun h hh => ?_
  obtain ⟨⟨k, hkN⟩, hk, rfl⟩ := RootGroupData.mem_H_iff.1 hh
  have hkN' : k ∈ monomialGroup t.tag K := hkN
  have hk' : weylHom t.tag K ⟨k, hkN'⟩ = 1 := hk
  rw [← map_twistC_monomialGroup t K σ hσ] at hkN'
  obtain ⟨m, hm, rfl⟩ := hkN'
  refine ⟨m, RootGroupData.mem_H_iff.2 ⟨⟨m, hm⟩, ?_, rfl⟩, rfl⟩
  change weylHom t.tag K ⟨m, hm⟩ = 1
  change weylHom t.tag K (twistN t K σ ⟨m, hm⟩) = 1 at hk'
  rwa [weylHom_twistN, map_eq_one_iff _ (weylTwist t).injective] at hk'

theorem twistC_mem_B {b : adjointGroup t.tag K} (hb : b ∈ (nativeData t.tag K).B) :
    twistC t K σ b ∈ (nativeData t.tag K).B := by
  have hle : (nativeData t.tag K).B ≤ (nativeData t.tag K).B.comap (twistC t K σ) :=
    sup_le (fun h hh => (nativeData t.tag K).H_le_B (twistC_mem_H t K σ hh))
      (fun u hu => (nativeData t.tag K).U_le_B (twistC_mem_U t K σ hu))
  exact hle hb

theorem map_twistC_B (hσ : Function.Surjective σ) :
    (nativeData t.tag K).B.map (twistC t K σ) = (nativeData t.tag K).B := by
  change ((nativeData t.tag K).H ⊔ (nativeData t.tag K).U).map (twistC t K σ) = _
  rw [Subgroup.map_sup, map_twistC_H t K σ hσ, map_twistC_U t K σ hσ]
  rfl

end Borel

section FixedBruhat

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K) (hσ : Function.Surjective σ)

theorem twistEquiv_mem_B [Finite K] :
    ∀ b ∈ (nativeData t.tag K).B, twistEquiv t K σ hσ b ∈ (nativeData t.tag K).B :=
  fun _ hb => twistC_mem_B t K σ hb

theorem twistEquiv_mem_monomialGroup :
    ∀ m : monomialGroup t.tag K, twistEquiv t K σ hσ m ∈ monomialGroup t.tag K :=
  fun m => twistC_mem_monomialGroup t K σ m.2

theorem weylHom_twistEquiv [Finite K] : ∀ m : monomialGroup t.tag K,
    weylHom t.tag K ⟨twistEquiv t K σ hσ m, twistEquiv_mem_monomialGroup t K σ hσ m⟩ =
      weylTwist t (weylHom t.tag K m) :=
  weylHom_twistN t K σ

theorem twistEquiv_mem_Uminus : ∀ w, ∀ u ∈ (Uminus t.tag K w : Set (adjointGroup t.tag K)),
    twistEquiv t K σ hσ u ∈ (Uminus t.tag K (weylTwist t w) : Set (adjointGroup t.tag K)) :=
  fun _ _ hu => twistC_mem_Uminus t K σ hu

theorem twistEquiv_nrep : ∀ w, weylTwist t w = w →
    twistEquiv t K σ hσ (nrep t.tag K w) = nrep t.tag K w := fun w hw => by
  rw [twistEquiv_apply, twistC_nrep, hw]

theorem exists_twistEquiv_fixed_mul [Finite K]
    (hcover : ∀ g : adjointGroup t.tag K, ∃ m : monomialGroup t.tag K,
      ∃ b₁ ∈ (nativeData t.tag K).B, ∃ b₂ ∈ (nativeData t.tag K).B,
        g = b₁ * (m : adjointGroup t.tag K) * b₂)
    (hdisj : ∀ m m' : monomialGroup t.tag K, ∀ b₁ ∈ (nativeData t.tag K).B,
      ∀ b₂ ∈ (nativeData t.tag K).B, ∀ b₃ ∈ (nativeData t.tag K).B,
      ∀ b₄ ∈ (nativeData t.tag K).B,
      b₁ * (m : adjointGroup t.tag K) * b₂ = b₃ * (m' : adjointGroup t.tag K) * b₄ →
        weylHom t.tag K m = weylHom t.tag K m')
    (hexists : ∀ m : monomialGroup t.tag K, ∀ b₁ ∈ (nativeData t.tag K).B,
      ∀ b₂ ∈ (nativeData t.tag K).B, ∃ b ∈ (nativeData t.tag K).B,
      ∃ u ∈ (Uminus t.tag K (weylHom t.tag K m) : Set (adjointGroup t.tag K)),
        b₁ * (m : adjointGroup t.tag K) * b₂ = b * nrep t.tag K (weylHom t.tag K m) * u)
    (hunique : ∀ w, ∀ b ∈ (nativeData t.tag K).B, ∀ b' ∈ (nativeData t.tag K).B,
      ∀ u ∈ (Uminus t.tag K w : Set (adjointGroup t.tag K)),
      ∀ u' ∈ (Uminus t.tag K w : Set (adjointGroup t.tag K)),
      b * nrep t.tag K w * u = b' * nrep t.tag K w * u' → b = b' ∧ u = u')
    {g : adjointGroup t.tag K} (hg : twistEquiv t K σ hσ g = g) :
    ∃ w, weylTwist t w = w ∧ ∃ b ∈ (nativeData t.tag K).B, twistEquiv t K σ hσ b = b ∧
      ∃ u ∈ (Uminus t.tag K w : Set (adjointGroup t.tag K)), twistEquiv t K σ hσ u = u ∧
        g = b * nrep t.tag K w * u :=
  exists_fixed_mul_of_fixed (nativeData t.tag K).B (monomialGroup t.tag K) (weylHom t.tag K)
    (nrep t.tag K) (fun w => (Uminus t.tag K w : Set (adjointGroup t.tag K)))
    (twistEquiv t K σ hσ) (weylTwist t) hcover hdisj hexists hunique
    (twistEquiv_mem_B t K σ hσ) (twistEquiv_mem_monomialGroup t K σ hσ)
    (weylHom_twistEquiv t K σ hσ) (twistEquiv_mem_Uminus t K σ hσ) (twistEquiv_nrep t K σ hσ) hg

end FixedBruhat

end CFSG.LieType.Chevalley
