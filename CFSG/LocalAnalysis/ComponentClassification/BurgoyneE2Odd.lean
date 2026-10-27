module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2Diag
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2E7Row

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2

open CFSG Subgroup CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.Timmesfeld
open CFSG.ComponentClassification.CatLeafProof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootChar
  root_diagonal_conjugation)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LieType.HighestRoot (rankOneGroup rankOneGroup_adjDatum)
open CFSG.RankThree.Chevalley (conjGL baseChangeGL_simpleRootSL2)
open scoped MatrixGroups

variable {τ : Tag}

theorem exists_innerDiag_of_odd_fix_rankOne (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {β : MulAut (adjointGroup τ K)} (hβ : Odd (orderOf β))
    (k : Fin τ.rank)
    (hfix : ∀ x ∈ rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup k, β x = x) :
    ∃ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ), ∀ h : adjointGroup τ K,
      (β h : ModGL τ K) =
        (g : ModGL τ K) * rootDiagUnit τ a * h * (rootDiagUnit τ a)⁻¹ * (g : ModGL τ K)⁻¹ := by
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form τ hτ K
  obtain ⟨Θ, -, hΘ, -, -, -⟩ := ordinary_E_field_graph_quotient_and_involutions τ hτ K
  obtain ⟨g, a, σ, ε, hexpr⟩ := hNF β
  have hU : ∀ B : SL2 K, 1 * simpleRootSL2 τ K k (conjGL 1
      (Matrix.SpecialLinearGroup.map (algebraMap K K) B)) * 1⁻¹ ∈
        (adjointGroup τ K).map (baseChangeGL (algebraMap K K)) := by
    intro B
    refine ⟨simpleRootSL2 τ K k B, simpleRootSL2_mem_adjointGroup _ B, ?_⟩
    rw [baseChangeGL_simpleRootSL2, conjGL_one', one_mul, inv_one, mul_one]
  have hZ : ∀ η ∈ zpowers β, ∀ (u : adjointGroup τ K) (B : SL2 K),
      baseChangeGL (algebraMap K K) (u : ModGL τ K) = 1 * simpleRootSL2 τ K k
        (conjGL 1 (Matrix.SpecialLinearGroup.map (algebraMap K K) B)) * 1⁻¹ → η u = u := by
    intro η hη u B hu
    rw [conjGL_one', one_mul, inv_one, mul_one, ← baseChangeGL_simpleRootSL2] at hu
    have hu' : (u : ModGL τ K) = simpleRootSL2 τ K k B :=
      baseChangeGL_injective (algebraMap K K) hu
    have huL : u ∈ rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup k := by
      change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single k 1)
      rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf, hu',
        ← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2]
      exact ⟨B, rfl⟩
    have hβu : β ∈ MulAction.stabilizer (MulAut (adjointGroup τ K)) u := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hfix u huL
    have h := (zpowers_le.2 hβu) hη
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h
  obtain ⟨hfield, -, -, -⟩ :=
    RankThree.PartOne.KE.ordinary_E_descended_root_SL2_pointwise_automorphisms_field_free τ hτ
      K K k 1 1 hU (zpowers β) hZ
  have hσ : σ = 1 := hfield β (mem_zpowers β) g a σ ε hexpr
  subst hσ
  have hε : exactQ τ K (ε : ℕ) = 1 := by
    have h := congrArg Prod.snd (map_pow Θ β (orderOf β))
    rw [pow_orderOf_eq_one, map_one, hΘ β g a 1 ε hexpr, Prod.snd_one, Prod.pow_snd,
      ← ofAdd_nsmul] at h
    have h0 : orderOf β • ((ε : ℕ) : ZMod (exactE τ)) = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa using this.symm
    rcases hτ with rfl | rfl | rfl
    · change orderOf β • ((ε : ℕ) : ZMod 2) = 0 at h0
      rw [nsmul_eq_mul, (ZMod.natCast_eq_one_iff_odd).2 hβ, one_mul] at h0
      have hε0 : (ε : ℕ) = 0 := by
        have hlt : (ε : ℕ) < 2 := ε.2
        rw [ZMod.natCast_eq_zero_iff] at h0
        omega
      rw [hε0]
      exact exactQ_zero _ K
    · rfl
    · rfl
  have h1 : ∀ x : ModGL τ K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  refine ⟨g, a, fun h => ?_⟩
  rw [hexpr h, hε, mul_one, inv_one, mul_one, h1]

theorem exists_eq_rootDiagAut_of_odd_fix (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] (hK : ringChar K ≠ 2) {β : MulAut (adjointGroup τ K)}
    (hβ : Odd (orderOf β)) (k : Fin τ.rank)
    (hk : ∀ x ∈ rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup k, β x = x)
    (Γ : List ((Fin τ.rank → ℤ) × ℤ)) (hΓ : ∀ y ∈ Γ, IsRoot τ y.1)
    (hfix : ∀ y ∈ Γ, ∀ u : adjointGroup τ K,
      (u : ModGL τ K) ∈ rootSubgroup τ K y.1 ⊔ rootSubgroup τ K (-y.1) → β u = u)
    (B : ℕ) (hreg : ∀ α : Fin τ.rank → ℤ, IsRoot τ α →
      (∑ j, regCoweight Γ j * α j) ≠ 0 ∧ (∑ j, regCoweight Γ j * α j).natAbs < B) :
    ∃ e : Fin τ.rank → Kˣ, β = rootDiagAut τ K e := by
  obtain ⟨g, a, hga⟩ := exists_innerDiag_of_odd_fix_rankOne hτ hβ k hk
  exact exists_eq_rootDiagAut_of_fix_rootPairs hτ hK hga Γ hΓ hfix B hreg

theorem rootChar_eq_one_of_fix_pinnedX {K : Type} [Field K] {e : Fin τ.rank → Kˣ}
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (h : rootDiagAut τ K e ⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup γ 1⟩ =
      ⟨pinnedX τ K γ 1, pinnedX_mem_adjointGroup γ 1⟩) : rootChar e γ = 1 := by
  have h1 := congrArg Subtype.val h
  rw [coe_rootDiagAut, rootDiagUnit_conj_pinnedX e hγ, mul_one] at h1
  have h2 := pinnedX_injective τ K γ h1
  exact Units.ext h2

theorem rootPair_le_fixedSubgroup {K : Type} [Field K] {b : Fin τ.rank → Kˣ}
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ rootCharKernel b) {u : adjointGroup τ K}
    (hu : (u : ModGL τ K) ∈ rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ)) :
    rootDiagAut τ K b u = u := by
  have hγ' : -γ ∈ rootCharKernel b :=
    ⟨IsRoot.neg hγ.1, by rw [rootChar_neg', hγ.2, inv_one]⟩
  have hle : rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) ≤ toralCentralizer τ K b :=
    le_trans (sup_le (le_iSup₂ (f := fun β (_ : β ∈ rootCharKernel b) => rootSubgroup τ K β)
      γ hγ) (le_iSup₂ (f := fun β (_ : β ∈ rootCharKernel b) => rootSubgroup τ K β) (-γ) hγ'))
      (rootSpan_rootCharKernel_le_toralCentralizer b)
  exact mem_fixedSubgroup_rootDiagAut.2 (hle hu)

theorem rankOne_le_fixedSubgroup_rootDiagAut' {K : Type} [Field K] {b : Fin τ.rank → Kˣ}
    {k : Fin τ.rank} (hk : b k = 1) :
    rankOne (adjDatum (rootOperatorFamily τ) K).rootGroup k ≤
      fixedSubgroup (rootDiagAut τ K b) := by
  intro x hx
  change _ ∈ rankOneGroup (adjDatum (rootOperatorFamily τ) K) (Pi.single k 1) at hx
  rw [rankOneGroup_adjDatum _ (isRoot_single _ _), mem_subgroupOf] at hx
  refine rootPair_le_fixedSubgroup ⟨isRoot_single τ k, ?_⟩ hx
  rw [rootChar_single', hk]

theorem rootDiagAut_eq_one_of_rootChar {K : Type} [Field K] {e : Fin τ.rank → Kˣ}
    (h : ∀ j, rootChar e (Pi.single j 1) = 1) : rootDiagAut τ K e = 1 := by
  have he : e = 1 := funext fun j => by rw [← rootChar_single' e j, h j]; rfl
  rw [he]
  exact (rootDiagAutHom τ K).map_one

end CFSG.ComponentClassification.Burgoyne.E2
