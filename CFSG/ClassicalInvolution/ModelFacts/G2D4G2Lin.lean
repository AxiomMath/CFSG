module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Lin
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Cent

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

section Chart

variable {τ : Tag} {K : Type} [Field K]

@[expose] def rootChart (τ : Tag) (K : Type) [Field K] (w : WeylGroup τ) (i : Fin τ.rank) :
    SL2 K →* ModGL τ K :=
  (MulAut.conj (canonicalRep (coxeterSystem τ) K w)).toMonoidHom.comp (simpleRootSL2 τ K i)

theorem rootChart_apply (w : WeylGroup τ) (i : Fin τ.rank) (A : SL2 K) :
    rootChart τ K w i A = canonicalRep (coxeterSystem τ) K w * simpleRootSL2 τ K i A *
      (canonicalRep (coxeterSystem τ) K w)⁻¹ := rfl

theorem rootChart_uSL (w : WeylGroup τ) (i : Fin τ.rank) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K, rootChart τ K w i (uSL c) =
      pinnedX τ K (w • (Pi.single i 1 : Fin τ.rank → ℤ)) (ε * c) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_single τ i)
  exact ⟨ε, hε, fun c => by
    rw [rootChart_apply, simpleRootSL2_uSL, ← pinnedX_single, h]⟩

theorem rootChart_vSL (w : WeylGroup τ) (i : Fin τ.rank) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K, rootChart τ K w i (vSL c) =
      pinnedX τ K (-(w • (Pi.single i 1 : Fin τ.rank → ℤ))) (ε * c) := by
  obtain ⟨ε, hε, h⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w (isRoot_neg_single τ i)
  exact ⟨ε, hε, fun c => by
    rw [rootChart_apply, simpleRootSL2_vSL, ← pinnedX_neg_single, h, smul_neg]⟩

theorem rootChart_injective (hK : ringChar K ≠ 2) (w : WeylGroup τ) (i : Fin τ.rank) :
    Function.Injective (rootChart τ K w i) :=
  (MulAut.conj _).injective.comp (simpleRootSL2_injective hK i)

end Chart

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem rootChar_neg_inv (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← zero_sub, rootChar_sub, rootChar_zero, one_mul]

theorem linAct_rootDiagUnit (w : WeylGroup τ) (i : Fin τ.rank) (b : Fin τ.rank → Kˣ) :
    LinAct (rootChart τ K w i) (rootDiagUnit τ b) := by
  obtain ⟨ε, hε, hu⟩ := rootChart_uSL (K := K) w i
  obtain ⟨ε', hε', hv⟩ := rootChart_vSL (K := K) w i
  have hγ : IsRoot τ (w • (Pi.single i 1 : Fin τ.rank → ℤ)) :=
    IsRoot.smul (isRoot_single τ i) w
  refine linAct_diag (rootChar b (w • (Pi.single i 1 : Fin τ.rank → ℤ))) (fun c => ?_)
    (fun c => ?_)
  · rw [hu, hu, rootDiagUnit_conj_pinnedX b hγ]
    congr 1
    ring
  · rw [hv, hv, rootDiagUnit_conj_pinnedX b (IsRoot.neg hγ), rootChar_neg_inv]
    congr 1
    ring

end Torus

section Chart2

variable {K : Type} [Field K]

theorem rootChart_range {τ : Tag} {w : WeylGroup τ} {i : Fin τ.rank} {γ : Fin τ.rank → ℤ}
    (hw : w • (Pi.single i 1 : Fin τ.rank → ℤ) = γ) :
    (rootChart τ K w i).range = rootPair τ K γ := by
  rw [rootChart, MonoidHom.range_comp, range_simpleRootSL2,
    map_conj_canonicalRep_closure_xUnit_yUnit hw]
  rfl

theorem rootChart_neg_one [Finite K] (hK : Odd (Nat.card K)) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hne : a ≠ 1) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ rootCharKernel a) {w : WeylGroup Tag.G2} {i : Fin Tag.G2.rank}
    (hw : w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = γ) :
    rootChart Tag.G2 K w i (-1) = rootDiagUnit Tag.G2 a := by
  rw [rootChart_apply, neg_one_eq_HSL, simpleRootSL2_HSL]
  exact torusElt_neg_one_conj_eq_rootDiagUnit hK ha hne hγ hw

end Chart2

section Main

variable {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem sup_le_linActSubgroup_of_commute {G : Type*} [Group G] {Φ : SL2 K →* G} {P : Subgroup G}
    (hP : ∀ p ∈ P, ∀ A, p * Φ A = Φ A * p) : Φ.range ⊔ P ≤ linActSubgroup Φ :=
  sup_le (fun _ hx => linAct_of_mem_range hx) (fun p hp => linAct_of_commutes (hP p hp))

theorem toralCentralizer_le_linActSubgroup (hK : Odd (Nat.card K)) {a : Fin Tag.G2.rank → Kˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (hne : a ≠ 1) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : γ ∈ rootCharKernel a) {w : WeylGroup Tag.G2} {i : Fin Tag.G2.rank}
    (hw : w • (Pi.single i 1 : Fin Tag.G2.rank → ℤ) = γ) :
    toralCentralizer Tag.G2 K a ≤ linActSubgroup (rootChart Tag.G2 K w i) := by
  have hK2 : ringChar K ≠ 2 := ringChar_ne_two_of_odd_nat_card hK
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK2
  obtain ⟨α, β, hcases, hker, hspan, hcomm, -⟩ := g2_toral_data hK ha hne
  have hlen := iform_ne_g2 (K := K) hcases
  have hγmem : γ = α ∨ γ = -α ∨ γ = β ∨ γ = -β := by
    have := hγ
    rw [hker] at this
    simpa using this
  have hneg := rootChart_neg_one hK ha hne hγ hw
  have hinj := rootChart_injective hK2 w i
  have hrange : (rootChart Tag.G2 K w i).range = rootPair Tag.G2 K γ := rootChart_range hw
  have hXeq := (Chevalley_toral_centralizer_Bruhat_factors Tag.G2 K a).2.2.2
  have hcommP : ∀ P Q : Subgroup (ModGL Tag.G2 K), ⁅Q, P⁆ = ⊥ → Q = (rootChart Tag.G2 K w i).range →
      ∀ p ∈ P, ∀ A, p * rootChart Tag.G2 K w i A = rootChart Tag.G2 K w i A * p := by
    intro P Q hQP hQ p hp A
    have hmem : rootChart Tag.G2 K w i A ∈ Q := hQ ▸ ⟨A, rfl⟩
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQP hmem
    exact Subgroup.mem_centralizer_iff.mp this p hp
  have hcomm' : ⁅rootPair Tag.G2 K α, rootPair Tag.G2 K β⁆ = ⊥ := hcomm
  have hcomm'' : ⁅rootPair Tag.G2 K β, rootPair Tag.G2 K α⁆ = ⊥ := by
    rw [← Subgroup.commutator_comm]
    exact hcomm'
  rw [hXeq]
  refine sup_le (sup_le ?_ ?_) ?_
  · intro t ht
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    exact linAct_rootDiagUnit w i b
  · rw [hspan]
    have hsp : (rootSubgroup Tag.G2 K α ⊔ rootSubgroup Tag.G2 K (-α)) ⊔
        (rootSubgroup Tag.G2 K β ⊔ rootSubgroup Tag.G2 K (-β)) =
        rootPair Tag.G2 K α ⊔ rootPair Tag.G2 K β := rfl
    rw [hsp]
    rcases hγmem with rfl | rfl | rfl | rfl
    · rw [← hrange]
      exact sup_le_linActSubgroup_of_commute (hcommP _ _ hcomm' hrange.symm)
    · rw [rootPair_neg] at hrange
      rw [← hrange]
      exact sup_le_linActSubgroup_of_commute (hcommP _ _ hcomm' hrange.symm)
    · rw [sup_comm, ← hrange]
      exact sup_le_linActSubgroup_of_commute (hcommP _ _ hcomm'' hrange.symm)
    · rw [rootPair_neg] at hrange
      rw [sup_comm, ← hrange]
      exact sup_le_linActSubgroup_of_commute (hcommP _ _ hcomm'' hrange.symm)
  · rw [Subgroup.closure_le]
    rintro _ ⟨w', hw', rfl⟩
    have hxX : canonicalRep (coxeterSystem Tag.G2) K w' ∈ toralCentralizer Tag.G2 K a := by
      rw [hXeq]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨w', hw', rfl⟩)
    have hx := (mem_toralCentralizer.mp hxX).2
    have hxd : canonicalRep (coxeterSystem Tag.G2) K w' * rootDiagUnit Tag.G2 a *
        (canonicalRep (coxeterSystem Tag.G2) K w')⁻¹ = rootDiagUnit Tag.G2 a := by
      have hc := hx
      rw [mul_inv_eq_iff_eq_mul] at hc
      exact mul_inv_eq_iff_eq_mul.mpr hc.symm
    have hxneg : canonicalRep (coxeterSystem Tag.G2) K w' * rootChart Tag.G2 K w i (-1) *
        (canonicalRep (coxeterSystem Tag.G2) K w')⁻¹ = rootChart Tag.G2 K w i (-1) := by
      rw [hneg]
      exact hxd
    have hγroot : IsRoot Tag.G2 γ := hγ.1
    have hwγ : w' • γ ∈ rootCharKernel a := ⟨IsRoot.smul hγ.1 w', by rw [hw' γ]; exact hγ.2⟩
    have hwγ' : w' • γ = α ∨ w' • γ = -α ∨ w' • γ = β ∨ w' • γ = -β := by
      have := hwγ
      rw [hker] at this
      simpa using this
    have hiw : iform (w' • γ) (w' • γ) = iform γ γ := iform_smul w' γ γ
    have hcase := eq_or_eq_neg_of_iform_eq hlen hγmem hwγ' hiw
    obtain ⟨ε₀, hε₀, hu⟩ := rootChart_uSL (K := K) (τ := Tag.G2) w i
    obtain ⟨ε₀', hε₀', hv⟩ := rootChart_vSL (K := K) (τ := Tag.G2) w i
    rw [hw] at hu hv
    obtain ⟨ε₁, hε₁, h1⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w' hγroot
    obtain ⟨ε₂, hε₂, h2'⟩ := exists_canonicalRep_mul_pinnedX_mul_inv K w' (IsRoot.neg hγroot)
    rcases hcase with hc | hc
    · refine linAct_of_signs_diag hinj h2 hxneg (s := ε₁) (s' := ε₂) (fun c => ?_) (fun c => ?_)
      · rw [hu, h1, hc, hu]
        congr 1
        ring
      · rw [hv, h2', smul_neg, hc, hv]
        congr 1
        ring
    · refine linAct_of_signs_anti hinj h2 hxneg (κ := ε₀' * ε₁ * ε₀) (κ' := ε₀ * ε₂ * ε₀')
        (fun c => ?_) (fun c => ?_)
      · rw [hu, h1, hc, hv]
        congr 1
        linear_combination (-(ε₁ * ε₀ * c)) * hε₀'
      · rw [hv, h2', smul_neg, hc, neg_neg, hu]
        congr 1
        linear_combination (-(ε₂ * ε₀' * c)) * hε₀

end Main

end CFSG.ClassicalInvolution.G2D4Models
