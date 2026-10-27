module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationSimpleParam
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ClassicalInvolution.ModelFacts (subgroupOf_rootSubgroup_sup_eq)
open CFSG.LieType.Steinberg.Adjoint
  (xPar rootGroup f4Datum f4Par xPar_of_isRoot xPar_injective xPar_zero)

section Generic

variable {τ : Tag} {K : Type} [Field K]

theorem fixedGroup_rootDiagAut (a : Fin τ.rank → Kˣ) :
    fixedGroup (rootDiagAut τ K a) =
      (toralCentralizer τ K a).subgroupOf (adjointGroup τ K) := by
  ext g
  rw [mem_fixedGroup, Subgroup.mem_subgroupOf, mem_toralCentralizer]
  constructor
  · intro h
    exact ⟨g.2, by simpa [coe_rootDiagAut] using congrArg Subtype.val h⟩
  · rintro ⟨-, h⟩
    exact Subtype.ext (by simpa [coe_rootDiagAut] using h)

end Generic

section Component

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem isQuasisimple_componentRootSpan_of_five (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ) (i : KernelComponent χ) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  induction i using Quotient.inductionOn with
  | h a =>
  obtain ⟨α, hα⟩ := a
  have hΨ := isRootComponent_componentRoots (χ := χ) ⟦⟨α, hα⟩⟧
  have hαΨ : α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ := ⟨hα, rfl⟩
  by_cases h2 : 2 < (componentRoots χ ⟦⟨α, hα⟩⟧).ncard
  · exact (odd_sign_root_component_quasisimple τ K χ _).2.2 hK h2
  · have hsub : ({α, -α} : Set (Fin τ.rank → ℤ)) ⊆ componentRoots χ ⟦⟨α, hα⟩⟧ :=
      Set.insert_subset hαΨ (Set.singleton_subset_iff.2 (hΨ.neg_mem α hαΨ))
    have hfin : (componentRoots χ ⟦⟨α, hα⟩⟧).Finite :=
      (finite_setOf_isRoot τ).subset fun β hβ => hΨ.isRoot β hβ
    have hne : α ≠ -α := fun h => (hΨ.isRoot α hαΨ).ne_zero (funext fun j => by
      have := congrFun h j
      simp only [Pi.neg_apply] at this
      simp only [Pi.zero_apply]
      omega)
    have hcard : ({α, -α} : Set (Fin τ.rank → ℤ)).ncard = 2 := Set.ncard_pair hne
    have heq : componentRoots χ ⟦⟨α, hα⟩⟧ = {α, -α} :=
      (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard]; omega) hfin).symm
    have hS : componentRootSpan K χ ⟦⟨α, hα⟩⟧ = rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
      change rootSpan τ K (componentRoots χ ⟦⟨α, hα⟩⟧) = _
      rw [heq, OddToralFixed.rootSpan_pair]
    obtain ⟨-, -, -, hfinK⟩ := odd_arbitrary_root_pair_SL2_p_components τ K hK
      (hΨ.isRoot α hαΨ)
    obtain ⟨-, h5'⟩ := @hfinK inferInstance
    rw [hS]
    exact (h5' h5).1

theorem exists_isComponentOf_rankOne_fixedGroup (hK : ringChar K ≠ 2) (h5 : 5 ≤ Nat.card K)
    (a : Fin τ.rank → Kˣ) (ha : ∀ i, a i = 1 ∨ a i = -1) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hχ : rootChar a γ = 1) :
    ∃ Q₀ : Subgroup ↥(adjointGroup τ K),
      (rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)).subgroupOf (adjointGroup τ K) ≤ Q₀ ∧
        IsComponentOf Q₀ (fixedGroup (rootDiagAut τ K a)) := by
  set χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ := maskChar (signTupleBits a) with hχdef
  have hker : rootCharKernel a = kernelRoots χ := rootCharKernel_eq_kernelRoots hK ha
  have hγk : γ ∈ kernelRoots χ := by rw [← hker]; exact ⟨hγ, hχ⟩
  set i : KernelComponent χ := ⟦⟨γ, hγk⟩⟧ with hi
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hγΨ : γ ∈ componentRoots χ i := ⟨hγk, rfl⟩
  have hγΨ' : -γ ∈ componentRoots χ i := hΨ.neg_mem γ hγΨ
  set SΨ : Subgroup (ModGL τ K) := componentRootSpan K χ i with hSΨ
  set S : Subgroup (ModGL τ K) := rootSpan τ K (kernelRoots χ) with hS
  set X : Subgroup (ModGL τ K) := toralCentralizer τ K a with hX
  have hSΨS : SΨ ≤ S := componentRootSpan_le K i
  have hSX : S ≤ X := by
    rw [hS, ← hker]
    exact rootSpan_rootCharKernel_le_toralCentralizer a
  have hSΨadj : SΨ ≤ adjointGroup τ K := hSΨS.trans (hSX.trans inf_le_left)
  have hSadj : S ≤ adjointGroup τ K := hSX.trans inf_le_left
  have hrank : rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ≤ SΨ :=
    sup_le (le_iSup₂_of_le γ hγΨ le_rfl) (le_iSup₂_of_le (-γ) hγΨ' le_rfl)
  refine ⟨SΨ.subgroupOf (adjointGroup τ K), Subgroup.subgroupOf_mono _ hrank, ?_⟩
  rw [fixedGroup_rootDiagAut]
  have hle1 : SΨ.subgroupOf (adjointGroup τ K) ≤ S.subgroupOf (adjointGroup τ K) :=
    Subgroup.subgroupOf_mono _ hSΨS
  have hle2 : S.subgroupOf (adjointGroup τ K) ≤ X.subgroupOf (adjointGroup τ K) :=
    Subgroup.subgroupOf_mono _ hSX
  have hn1 : ((SΨ.subgroupOf (adjointGroup τ K)).subgroupOf
      (S.subgroupOf (adjointGroup τ K))).Normal := by
    obtain ⟨-, -, -, hnorm, -, -⟩ := root_character_kernel_orthogonal_central_product τ K χ
    have h := (Subgroup.normal_subgroupOf_iff hSΨS).1 (hnorm i).2
    rw [Subgroup.normal_subgroupOf_iff hle1]
    intro x k hx hk
    exact h x k hx hk
  have hn2 : ((S.subgroupOf (adjointGroup τ K)).subgroupOf
      (X.subgroupOf (adjointGroup τ K))).Normal := by
    have hSX' : rootSpan τ K (rootCharKernel a) ≤ toralCentralizer τ K a :=
      rootSpan_rootCharKernel_le_toralCentralizer a
    have h := (Subgroup.normal_subgroupOf_iff hSX').1 (rootSpan_rootCharKernel_normal (K := K) a)
    rw [Subgroup.normal_subgroupOf_iff hle2]
    intro x k hx hk
    have hx' : (x : ModGL τ K) ∈ rootSpan τ K (rootCharKernel a) := by
      rw [hker]
      exact hx
    have := h x k hx' hk
    rw [hker] at this
    exact this
  refine ⟨hle1.trans hle2, isSubnormal_trans (isSubnormal_of_normal_subgroupOf hle1 hn1)
    (isSubnormal_of_normal_subgroupOf hle2 hn2), ?_⟩
  have hq : CFSG.IsQuasisimple ↥SΨ := isQuasisimple_componentRootSpan_of_five hK h5 χ i
  exact (AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    ((isQuasisimple_congr (Subgroup.subgroupOfEquivOfLe hSΨadj)).2 hq)

end Component

section F4

variable {τ : Tag} {K : Type} [Field K]

theorem coe_xPar_eq_pinnedX {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    ((xPar (rootOperatorFamily τ) γ c : adjointGroup τ K) : ModGL τ K) =
      pinnedX τ K γ (((rootOperatorFamily τ).pinnedFamilySign γ : ℤ) * c) := by
  have h := (rootOperatorFamily τ).pinnedX_eq_eltUnit K hγ
    (((rootOperatorFamily τ).pinnedFamilySign γ : K) * c)
  rw [← mul_assoc, (rootOperatorFamily τ).pinnedFamilySign_mul_self K γ, one_mul] at h
  rw [xPar_of_isRoot hγ, h]
  rfl

theorem rootDiagAut_xPar (a : Fin τ.rank → Kˣ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (c : K) :
    rootDiagAut τ K a (xPar (rootOperatorFamily τ) γ c) =
      xPar (rootOperatorFamily τ) γ ((rootChar a γ : K) * c) := by
  apply Subtype.ext
  rw [coe_rootDiagAut, coe_xPar_eq_pinnedX hγ, coe_xPar_eq_pinnedX hγ,
    rootDiagUnit_conj_pinnedX a hγ]
  congr 1
  ring

theorem rootChar_single_eq (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  have := rootChar_nsmul_single a i 1
  rwa [one_smul, pow_one] at this

theorem rootChar_neg_eq_inv (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← rootChar_add, add_neg_cancel, rootChar_zero]

theorem shortRootModelFact_adjoint {p e : ℕ} [Fact p.Prime] (τ : Tag) (hp2 : p ≠ 2)
    (h5 : 5 ≤ p ^ e) :
    ShortRootModelFact (CFSG.LieType.Steinberg.Adjoint.adjDatum (rootOperatorFamily τ)
      (GaloisField p e)) (xPar (rootOperatorFamily τ)) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hK : ringChar (GaloisField p e) ≠ 2 := by
    rw [ringChar.eq (GaloisField p e) p]
    exact hp2
  intro b hb
  refine ⟨rootDiagAut τ (GaloisField p e) b, fun i c => ?_, fun i c => ?_, fun i hbi => ?_⟩
  · rw [rootDiagAut_xPar b (isRoot_single τ i) c, rootChar_single_eq]
  · rw [rootDiagAut_xPar b (isRoot_neg_single τ i) c, rootChar_neg_eq_inv, rootChar_single_eq]
  · have hγ : rootChar b (Pi.single i 1 : Fin τ.rank → ℤ) = 1 := by
      rw [rootChar_single_eq]
      exact hbi
    obtain ⟨Q₀, hQ₀, hQ⟩ := exists_isComponentOf_rankOne_fixedGroup (τ := τ)
      (K := GaloisField p e) hK (by rw [hcard]; exact h5) b hb (isRoot_single τ i) hγ
    refine ⟨Q₀, le_trans (le_of_eq ?_) hQ₀, hQ⟩
    exact (subgroupOf_rootSubgroup_sup_eq (K := GaloisField p e) (rootOperatorFamily τ)
      (isRoot_single τ i)).symm

theorem shortRootModelFact_f4 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) :
    ShortRootModelFact (f4Datum (GaloisField p e)) (f4Par (GaloisField p e)) :=
  shortRootModelFact_adjoint .F4 hp2 h5

theorem shortRootModelFact_g2 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) :
    ShortRootModelFact (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e))
      (xPar (rootOperatorFamily .G2)) :=
  shortRootModelFact_adjoint .G2 hp2 h5

end F4

section Param

variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem simpleParam_adjoint (τ : Tag) (K : Type) [Field K] [Finite K] :
    SimpleParam (CFSG.LieType.Steinberg.Adjoint.adjDatum (rootOperatorFamily τ) K) K
      (xPar (rootOperatorFamily τ)) := by
  refine ⟨CFSG.LieType.Steinberg.Adjoint.adjDatum_isParametrization (F := rootOperatorFamily τ)
    (K := K) _ (CFSG.LieType.Steinberg.Adjoint.adjDatum_roots _ K), ?_⟩
  intro X _ ψ hker g i c h
  have hz : g * xPar (rootOperatorFamily τ) (Pi.single i 1) c * g⁻¹ ∈
      Subgroup.center ↥(adjointGroup τ K) := hker (MonoidHom.mem_ker.mpr h)
  rw [center_adjointGroup_eq_bot, Subgroup.mem_bot] at hz
  have h1 : xPar (rootOperatorFamily τ) (Pi.single i 1) c = 1 := by
    have := congrArg (fun y => g⁻¹ * y * g) hz
    simpa [mul_assoc] using this
  exact xPar_injective (isRoot_single τ i) (h1.trans (xPar_zero _).symm)

end Param

end CFSG.ClassicalInvolution.Balance
