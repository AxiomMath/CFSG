module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofF4B4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofRootComponentGen
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofExcLayerShape
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofToralConj

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.RouteD.Exotic (ChainOK)
open scoped MatrixGroups

@[expose] def f4BitsB4 : Fin (Tag.rank .F4) → Bool := listMask [false, false, false, true]

theorem f4BitsB4_eq_false : ∀ j : Fin (Tag.rank .F4), j ≠ f4Node 3 → f4BitsB4 j = false := by
  decide

theorem maskPairing_f4BitsB4 (α : Fin (Tag.rank .F4) → ℤ) :
    maskPairing f4BitsB4 α = α (f4Node 3) := by
  rw [maskPairing, Finset.sum_eq_single (f4Node 3)]
  · simp [show f4BitsB4 (f4Node 3) = true from by decide]
  · intro j _ hj
    simp [f4BitsB4_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def b4Chain_ch : List ℕ :=
  [0, 1, 4, 5, 6, 7, 8, 12, 13, 14, 15, 16, 18, 20, 22, 23, 26, 29, 39, 42, 43, 46, 2, 9, 21, 28,
    30, 34, 35, 38, 44, 47]

@[expose] def b4Chain_par : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 10, 10]

theorem b4Chain_ok : ChainOK f4Certificate b4Chain_ch b4Chain_par := by
  decide +kernel

theorem b4Chain_ker : ∀ i < b4Chain_ch.length,
    Even (maskPairing f4BitsB4 (f4Certificate.root (b4Chain_ch.getD i 0))) ∧
      b4Chain_ch.getD i 0 < f4Certificate.roots.length := by
  decide +kernel

theorem b4Chain_cover : ∀ p < f4Certificate.roots.length,
    Even (maskPairing f4BitsB4 (f4Certificate.root p)) →
      ∃ i < b4Chain_ch.length, b4Chain_ch.getD i 0 = p := by
  decide +kernel

theorem isRootComponent_f4KerB4
    :
    IsRootComponent (kernelRoots (maskChar (τ := .F4) f4BitsB4)) := by
  classical
  have hC := Tag.rootCertificate_check .F4
  have hker : ∀ i < b4Chain_ch.length,
      f4Certificate.root (b4Chain_ch.getD i 0) ∈ kernelRoots (maskChar (τ := .F4) f4BitsB4) :=
    fun i hi => mem_kernelRoots_maskChar.2
      ⟨RootCertificate.isRoot_root hC _ (b4Chain_ker i hi).2, (b4Chain_ker i hi).1⟩
  have h0 : 0 < b4Chain_ch.length := by decide
  have hcl := ChainOK.class_eq b4Chain_ok hker h0
  set i₀ : KernelComponent (maskChar (τ := .F4) f4BitsB4) :=
    ⟦⟨f4Certificate.root (b4Chain_ch.getD 0 0), hker 0 h0⟩⟧ with hi₀
  have heq : componentRoots (maskChar (τ := .F4) f4BitsB4) i₀ =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    refine Set.Subset.antisymm (fun α ⟨h, _⟩ => h) fun α hα => ⟨hα, ?_⟩
    obtain ⟨hr, hev⟩ := mem_kernelRoots_maskChar.1 hα
    obtain ⟨p, hp, rfl⟩ := (RootCertificate.isRoot_iff hC).1 hr
    obtain ⟨i, hi, hip⟩ := b4Chain_cover p hp hev
    have := hcl i hi
    simp only [hip] at this
    exact this
  rw [← heq]
  exact isRootComponent_componentRoots i₀

@[expose] def b4Simple : Finset (Fin (Tag.rank .F4) → ℤ) :=
  {Pi.single (f4Node 2) 1, Pi.single (f4Node 1) 1, b4Root, Pi.single (f4Node 0) 1}

theorem mem_posRoots_f4KerB4
    {β : Fin (Tag.rank .F4) → ℤ} :
    β ∈ posRoots (kernelRoots (maskChar (τ := .F4) f4BitsB4)) ↔
      β ∈ rootFinset .F4 ∧ Even (β (f4Node 3)) ∧ 0 < height β := by
  rw [posRoots, Set.mem_ofPred_eq, mem_kernelRoots_maskChar, maskPairing_f4BitsB4,
    mem_rootFinset, and_assoc]

theorem b4Simple_sub : ∀ β ∈ b4Simple, β ∈ rootFinset .F4 := by decide +kernel

theorem b4Simple_check : ∀ β ∈ rootFinset .F4,
    ((Even (β (f4Node 3)) ∧ 0 < height β) ∧ ∀ γ ∈ rootFinset .F4, ∀ δ ∈ rootFinset .F4,
      (Even (γ (f4Node 3)) ∧ 0 < height γ) → (Even (δ (f4Node 3)) ∧ 0 < height δ) →
        β ≠ γ + δ) ↔ β ∈ b4Simple := by
  decide +kernel

theorem simpleRoots_f4KerB4
    :
    simpleRoots (kernelRoots (maskChar (τ := .F4) f4BitsB4)) = b4Simple := by
  ext β
  rw [mem_simpleRoots]
  constructor
  · rintro ⟨hr, hpos, hsum⟩
    have hβ : β ∈ rootFinset .F4 := mem_rootFinset.2 hr
    exact (b4Simple_check β hβ).1 ⟨(mem_posRoots_f4KerB4.1 hpos).2,
      fun γ hγ δ hδ hγc hδc => hsum γ (mem_posRoots_f4KerB4.2 ⟨hγ, hγc⟩) δ
        (mem_posRoots_f4KerB4.2 ⟨hδ, hδc⟩)⟩
  · intro hβ
    have hβr := b4Simple_sub β hβ
    obtain ⟨hc, hsum⟩ := (b4Simple_check β hβr).2 hβ
    refine ⟨mem_rootFinset.1 hβr, mem_posRoots_f4KerB4.2 ⟨hβr, hc⟩, fun γ hγ δ hδ => ?_⟩
    obtain ⟨hγr, hγc⟩ := mem_posRoots_f4KerB4.1 hγ
    obtain ⟨hδr, hδc⟩ := mem_posRoots_f4KerB4.1 hδ
    exact hsum γ hγr δ hδr hγc hδc

theorem b4Chain_map_subtype
    {K : Type} [Field K] (k : Fin 4) :
    (b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSubgroup .F4 K (![b4Root, Pi.single (f4Node 0) 1, Pi.single (f4Node 1) 1,
        Pi.single (f4Node 2) 1] k) ⊔ rootSubgroup .F4 K (-(![b4Root, Pi.single (f4Node 0) 1,
          Pi.single (f4Node 1) 1, Pi.single (f4Node 2) 1] k)) := by
  have key : ∀ γ : Fin (Tag.rank .F4) → ℤ, IsRoot .F4 γ →
      ((f4Datum K).rootGroup γ ⊔ (f4Datum K).rootGroup (-γ)).map
        (adjointGroup .F4 K).subtype = rootSubgroup .F4 K γ ⊔ rootSubgroup .F4 K (-γ) :=
    fun γ hγ => by
      rw [Subgroup.map_sup]
      exact congrArg₂ (· ⊔ ·) (map_subtype_rootGroup _ hγ)
        (map_subtype_rootGroup _ (IsRoot.neg hγ))
  fin_cases k
  · exact key _ isRoot_b4Root
  · exact key _ (isRoot_single _ _)
  · exact key _ (isRoot_single _ _)
  · exact key _ (isRoot_single _ _)

theorem mem_b4Simple_iff {β : Fin (Tag.rank .F4) → ℤ} :
    β ∈ b4Simple ↔ ∃ k : Fin 4, ![b4Root, Pi.single (f4Node 0) 1, Pi.single (f4Node 1) 1,
      Pi.single (f4Node 2) 1] k = β := by
  constructor
  · intro h
    simp only [b4Simple, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨3, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp [b4Simple]

theorem map_subtype_iSup_b4Chain
    {K : Type} [Field K] :
    (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (kernelRoots (maskChar (τ := .F4) f4BitsB4)) := by
  rw [rootSpan_eq_iSup_simpleRoots isRootComponent_f4KerB4, simpleRoots_f4KerB4,
    Subgroup.map_iSup]
  simp only [b4Chain_map_subtype]
  refine le_antisymm (iSup_le fun k => ?_) (iSup₂_le fun β hβ => ?_)
  · exact le_iSup₂_of_le _ (mem_b4Simple_iff.2 ⟨k, rfl⟩) le_rfl
  · obtain ⟨k, rfl⟩ := mem_b4Simple_iff.1 hβ
    exact le_iSup_of_le k le_rfl

theorem f4_toral_B4_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (h5 : 5 ≤ Nat.card K)
    {M : Subgroup (toralCentralizer .F4 K (bitsTuple f4BitsB4))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  have hq4 : 4 ≤ Nat.card K := by omega
  have hadm : StatedLieAdmissible .POmegaOdd 4 p f := ⟨hp, hf, by norm_num, hp2⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .F4 K hK2 _
      (bitsTuple_mem (K := K) f4BitsB4)
  have hker : rootCharKernel (bitsTuple (K := K) f4BitsB4) =
      kernelRoots (maskChar (τ := .F4) f4BitsB4) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  obtain ⟨-, -, -, hqs, hlie⟩ := exists_psi_B4_F4 hp hp2 hK hq4 h2
  have hSim : (⨆ k, b4Chain K k).map (adjointGroup .F4 K).subtype =
      rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) := by
    rw [map_subtype_iSup_b4Chain, hker]
  let e₁ : ↥(⨆ k, b4Chain K k) ≃* rootSpan .F4 K (rootCharKernel (bitsTuple (K := K) f4BitsB4)) :=
    ((⨆ k, b4Chain K k).equivMapOfInjective _ (adjointGroup .F4 K).subtype_injective).trans
      (MulEquiv.subgroupCongr hSim)
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* ↥(⨆ k, b4Chain K k) := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁.symm)
  exact ⟨.POmegaOdd, 4, f, hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

end CFSG.ComponentClassification.CatLeafProof
