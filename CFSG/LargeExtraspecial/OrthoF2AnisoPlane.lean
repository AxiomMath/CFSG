module

public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.OrthoF2EichlerThree
public import CFSG.GroupTheory.PrimeSqDvdCard
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.SeitzGeneration.OrthLift
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.RankThree.PartOne.Assembly
public import CFSG.RankThree.PartOne.CTP.SeitzOrthModel
public import CFSG.RankThree.PartOne.CTP.SeitzThree
public import CFSG.RankThree.PartOne.CTP.SeitzTransfer
public import CFSG.RankThree.PartOne.CTP.StrongPFinal
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mem_orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {W : Submodule (ZMod 2) V}

namespace OrthoF2

local notation "orthW" => LinearMap.BilinForm.orthogonal q.polarBilin W

private lemma inf_perpW_eq_bot (hW2 : finrank (ZMod 2) W = 2)
    (hWq : ∀ w ∈ W, w ≠ 0 → q w = 1) : W ⊓ orthW = ⊥ := by
  obtain ⟨w1, w2, hli, hspan⟩ := exists_pair_of_finrank_eq_two hW2
  have hw1W : w1 ∈ W := by rw [← hspan]; exact Submodule.subset_span (by simp)
  have hw2W : w2 ∈ W := by rw [← hspan]; exact Submodule.subset_span (by simp)
  obtain ⟨hw10, hw20, hw12⟩ := linearIndependent_pair_iff.mp hli
  have hq1 : q w1 = 1 := hWq w1 hw1W hw10
  have hq2 : q w2 = 1 := hWq w2 hw2W hw20
  have hq12 : q (w1 + w2) = 1 := by
    refine hWq (w1 + w2) (Submodule.add_mem _ hw1W hw2W) fun h => hw12 ?_
    rw [add_eq_zero_iff_eq_neg, vec_neg] at h
    exact h
  have hf : polar q w1 w2 = 1 := by
    have h := hq12
    rw [map_add_eq, hq1, hq2, show (1 : ZMod 2) + 1 = 0 from by decide, zero_add] at h
    exact h
  rw [eq_bot_iff]
  rintro x ⟨hxW, hxU⟩
  rw [← hspan] at hxW
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hxW
  rw [← hαβ] at hxU ⊢
  change α • w1 + β • w2 ∈ LinearMap.BilinForm.orthogonal q.polarBilin W at hxU
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hxU
  have h1 : polar q w1 (α • w1 + β • w2) = 0 := hxU w1 hw1W
  have h2 : polar q w2 (α • w1 + β • w2) = 0 := hxU w2 hw2W
  have hfw21 : polar q w2 w1 = 1 := by rw [polar_comm q w2 w1, hf]
  have hβ : β = 0 := by
    rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self_eq_zero, hf] at h1
    simpa using h1
  have hα : α = 0 := by
    rw [polar_add_right, polar_smul_right, polar_smul_right, hfw21, polar_self_eq_zero] at h2
    simpa using h2
  rw [hα, hβ, zero_smul, zero_smul, add_zero]
  exact Submodule.zero_mem _

private lemma finrank_perpW (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    (hW2 : finrank (ZMod 2) W = 2) : finrank (ZMod 2) orthW = 4 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hq, hV, hW2]

private lemma sup_perpW_eq_top (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    (hW2 : finrank (ZMod 2) W = 2) (hWq : ∀ w ∈ W, w ≠ 0 → q w = 1) : W ⊔ orthW = ⊤ := by
  have hinf : W ⊓ orthW = ⊥ := inf_perpW_eq_bot hW2 hWq
  have hd : Disjoint W orthW := disjoint_iff_inf_le.mpr (le_of_eq hinf)
  refine Submodule.eq_top_of_disjoint W orthW ?_ hd
  rw [hV, hW2, finrank_perpW hq hV hW2]

private lemma mem_perpW_of_mem {H : Subgroup (orthogonalGroup q)}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W) {h : H} {u : V} (hu : u ∈ orthW) :
    ((h : orthogonalGroup q) : V ≃ₗ[ZMod 2] V) u ∈ orthW := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu ⊢
  intro w hw
  rw [polarBilin_apply_apply]
  have hw' : ((h : V ≃ₗ[ZMod 2] V))⁻¹ w ∈ W := by
    have h1 := hHW (h⁻¹) (H.inv_mem h.2) w hw
    simpa using h1
  conv_lhs => rw [show w = (h : V ≃ₗ[ZMod 2] V) (((h : V ≃ₗ[ZMod 2] V))⁻¹ w) from
    ((LinearEquiv.apply_symm_apply _ _).symm)]
  rw [TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup (h : orthogonalGroup q).2]
  exact hu _ hw'

private lemma perm_cube_eq_one_of_fixed {S : Type*} [Fintype S] (hS : Fintype.card S = 3)
    {σ : Equiv.Perm S} (h3 : σ ^ 3 = 1) {s : S} (hs : σ s = s) : σ = 1 := by
  classical
  let e : S ≃ Fin 3 := Fintype.equivFinOfCardEq hS
  have key : ∀ τ : Equiv.Perm (Fin 3), τ ^ 3 = 1 → (∃ i, τ i = i) → τ = 1 := by decide
  have h3' : e.permCongrHom σ ^ 3 = 1 := by rw [← map_pow, h3, map_one]
  have hfix' : ∃ i : Fin 3, e.permCongrHom σ i = i := by
    refine ⟨e s, ?_⟩
    show e.permCongr σ (e s) = e s
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hs]
  have h := key (e.permCongrHom σ) h3' hfix'
  refine e.permCongrHom.injective ?_
  rw [show e.permCongrHom σ = 1 from h, map_one]

private lemma perm_cube_eq_one_of_fpf {S : Type*} [Fintype S] (hS : Fintype.card S = 3)
    {σ : Equiv.Perm S} (h : ∀ s, σ s ≠ s) : σ ^ 3 = 1 := by
  classical
  let e : S ≃ Fin 3 := Fintype.equivFinOfCardEq hS
  have key : ∀ τ : Equiv.Perm (Fin 3), (∀ i, τ i ≠ i) → τ ^ 3 = 1 := by decide
  have hne : ∀ i : Fin 3, e.permCongrHom σ i ≠ i := by
    intro i
    obtain ⟨s, rfl⟩ := e.surjective i
    change e.permCongr σ (e s) ≠ e s
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    intro hh
    exact h s (e.injective hh)
  have h3 : e.permCongrHom σ ^ 3 = 1 := key _ hne
  have h4 : e.permCongrHom (σ ^ 3) = 1 := by rw [map_pow]; exact h3
  exact e.permCongrHom.injective (by rw [h4, map_one])

private lemma perm_three_dichotomy {S : Type*} [Fintype S] (hS : Fintype.card S = 3)
    (K : Subgroup (Equiv.Perm S)) :
    (∃ σ ∈ K, ∀ s : S, σ s ≠ s) ∨ (∃ s : S, ∀ σ ∈ K, σ s = s) := by
  classical
  have hKdvd : Nat.card K ∣ 6 := by
    have h1 := K.card_subgroup_dvd_card
    simp only [Nat.card_eq_fintype_card, Fintype.card_perm, hS] at h1
    norm_num at h1
    rwa [Nat.card_eq_fintype_card]
  by_cases h3 : 3 ∣ Nat.card K
  · left
    have h3' : 3 ∣ Fintype.card K := by rwa [Nat.card_eq_fintype_card] at h3
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card 3 h3'
    refine ⟨(σ : Equiv.Perm S), σ.2, fun s hs => ?_⟩
    have hσ3 : (σ : Equiv.Perm S) ^ 3 = 1 := by
      have h := pow_orderOf_eq_one σ
      rw [hσ] at h
      have h' := congrArg (K.subtype) h
      simpa using h'
    have h1 : (σ : Equiv.Perm S) = 1 := perm_cube_eq_one_of_fixed hS hσ3 hs
    have hσ1 : σ = 1 := Subtype.ext h1
    rw [hσ1] at hσ
    exact absurd hσ (by simp)
  · right
    have h2 : Nat.card K ∣ 2 := by
      have hcop : Nat.Coprime (Nat.card K) 3 :=
        ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
      exact hcop.dvd_mul_right.mp (by simpa using hKdvd)
    have hp : IsPGroup 2 K := IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by simpa using h2)
    letI : MulAction K S :=
      { smul := fun k s => (k : Equiv.Perm S) s
        one_smul := fun s => rfl
        mul_smul := fun k l s => rfl }
    obtain ⟨s, hs⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card S
      (p := 2) (by rw [Nat.card_eq_fintype_card, hS]; norm_num)
    exact ⟨s, fun σ hσ => hs ⟨σ, hσ⟩⟩

private def fixW {H : Subgroup (orthogonalGroup q)}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W) : Subgroup H where
  carrier := {h | ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w = w}
  one_mem' := fun w _ => rfl
  mul_mem' := by
    intro s t hs ht w hw
    show ((s * t : H) : V ≃ₗ[ZMod 2] V) w = w
    change ((s : V ≃ₗ[ZMod 2] V) * (t : V ≃ₗ[ZMod 2] V)) w = w
    rw [LinearEquiv.mul_apply, ht w hw, hs w hw]
  inv_mem' := by
    intro s hs w hw
    have hmem : ((s⁻¹ : H) : V ≃ₗ[ZMod 2] V) w ∈ W := hHW (s⁻¹) (H.inv_mem s.2) w hw
    have h2 : (s : V ≃ₗ[ZMod 2] V) (((s⁻¹ : H) : V ≃ₗ[ZMod 2] V) w) = w := by
      rw [← LinearEquiv.mul_apply]
      have h3 : (s : V ≃ₗ[ZMod 2] V) * ((s⁻¹ : H) : V ≃ₗ[ZMod 2] V) = 1 := by
        rw [← Subgroup.coe_mul]
        simp
      rw [h3]
      rfl
    exact (hs _ hmem).symm.trans h2

private lemma exists_no_fixed_on_W {H : Subgroup (orthogonalGroup q)}
    (hW2 : finrank (ZMod 2) W = 2)
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    (hfix : ∀ v : V, (∀ h : H, (h : V ≃ₗ[ZMod 2] V) v = v) → v = 0) :
    ∃ h₀ : H, (∀ w ∈ W, w ≠ 0 → (h₀ : V ≃ₗ[ZMod 2] V) w ≠ w) ∧
      h₀ ^ 3 ∈ fixW hHW := by
  classical
  haveI : Fintype V := Fintype.ofEquiv (Basis.ofVectorSpaceIndex (ZMod 2) V → ZMod 2)
    (Basis.ofVectorSpace (ZMod 2) V).equivFun.symm.toEquiv
  let S := {v : V // v ∈ W ∧ v ≠ 0}
  haveI : Fintype S := Subtype.fintype _
  have hScard : Fintype.card S = 3 := by
    have hWcard : Nat.card W = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hW2, Nat.card_zmod]
      norm_num
    have he : S ≃ {v : W // v ≠ 0} :=
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, fun hv => x.2.2 (congrArg Subtype.val hv)⟩
        invFun := fun y => ⟨y.1.1, y.1.2, fun hv => y.2 (Subtype.ext hv)⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
    rw [Fintype.card_congr he]
    change Fintype.card {v : W // ¬ v = 0} = 3
    have hcompl := Fintype.card_subtype_compl (α := W) (fun v : W => v = 0)
    have h1 : Fintype.card {v : W // v = 0} = 1 := by
      rw [Fintype.card_eq_one_iff]
      exact ⟨⟨0, rfl⟩, fun x => Subtype.ext (by simpa using x.2)⟩
    have hW4 : Fintype.card W = 4 := by rwa [Nat.card_eq_fintype_card] at hWcard
    rw [hcompl, h1, hW4]
  letI : MulAction H S :=
    { smul := fun h v => ⟨(h : V ≃ₗ[ZMod 2] V) v.1, hHW h h.2 v.1 v.2.1,
        fun hv => v.2.2 ((h : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp hv)⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun h h' v => Subtype.ext rfl }
  let φ : H →* Equiv.Perm S := MulAction.toPermHom H S
  have hsmul : ∀ (h : H) (v : S), ((h • v : S) : V) = (h : V ≃ₗ[ZMod 2] V) v.1 :=
    fun h v => rfl
  rcases perm_three_dichotomy hScard φ.range with ⟨σ, hσ, hσ'⟩ | ⟨s, hs⟩
  · obtain ⟨h₀, hh₀⟩ := hσ
    have hne : ∀ t : S, (φ h₀) t ≠ t := by
      intro t ht
      exact hσ' t (by rwa [← hh₀])
    have hcube : h₀ ^ 3 ∈ fixW hHW := by
      have h3 : (φ h₀) ^ 3 = 1 := perm_cube_eq_one_of_fpf hScard hne
      have h4 : φ (h₀ ^ 3) = 1 := by rw [map_pow, h3]
      intro w hwW
      by_cases hw0 : w = 0
      · subst hw0; simp
      · have h6 : (h₀ ^ 3 • (⟨w, hwW, hw0⟩ : S)) = ⟨w, hwW, hw0⟩ := by
          have h5 : (φ (h₀ ^ 3)) ⟨w, hwW, hw0⟩ = ⟨w, hwW, hw0⟩ := by rw [h4]; rfl
          simpa only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply] using h5
        have h7 := congrArg Subtype.val h6
        simpa only [hsmul] using h7
    refine ⟨h₀, fun w hwW hw0 hw => hσ' ⟨w, hwW, hw0⟩ ?_, hcube⟩
    rw [← hh₀]
    exact Subtype.ext hw
  · exfalso
    have h1 : ∀ h : H, (h : V ≃ₗ[ZMod 2] V) s.1 = s.1 := by
      intro h
      exact congrArg Subtype.val (hs (φ h) ⟨h, rfl⟩)
    exact s.2.2 (hfix s.1 h1)

private lemma eichler_mem_fixW {H : Subgroup (orthogonalGroup q)}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    {a u : V} (ha : q a = 0) (hau : polar q a u = 0) (haU : a ∈ orthW) (huU : u ∈ orthW)
    (hH : (⟨eichler q a u, eichler_mem_orthogonalGroup q a u⟩ : orthogonalGroup q) ∈ H) :
    (⟨⟨eichler q a u, eichler_mem_orthogonalGroup q a u⟩, hH⟩ : H) ∈ fixW hHW := by
  intro w hw
  show eichler q a u w = w
  rw [eichler_apply_zmod2 ha hau]
  have h1 : polar q w a = 0 := by
    rw [← polarBilin_apply_apply]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp haU w hw
  have h2 : polar q w u = 0 := by
    rw [← polarBilin_apply_apply]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp huU w hw
  rw [h1, h2]
  simp

private lemma natCard_dvd_factorial_of_injective {G S : Type*} [Group G] [Finite G] [Fintype S]
    (φ : G →* Equiv.Perm S) (hφ : Function.Injective φ) :
    Nat.card G ∣ Nat.factorial (Fintype.card S) := by
  have hcardrange : Nat.card φ.range = Nat.card G :=
    (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
  have h := φ.range.card_subgroup_dvd_card
  have hS : Nat.card S = Fintype.card S := Nat.card_eq_fintype_card
  rw [hcardrange, Nat.card_perm, hS] at h
  exact h

private lemma fixW_normal {H : Subgroup (orthogonalGroup q)}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W) : (fixW hHW).Normal := by
  refine ⟨fun x hx h => ?_⟩
  intro w hw
  have h1 : ((h⁻¹ : H) : V ≃ₗ[ZMod 2] V) w ∈ W := hHW (h⁻¹) (H.inv_mem h.2) w hw
  have h2 : ((x : H) : V ≃ₗ[ZMod 2] V) (((h⁻¹ : H) : V ≃ₗ[ZMod 2] V) w) =
      ((h⁻¹ : H) : V ≃ₗ[ZMod 2] V) w := hx _ h1
  have h3 : ((h : H) : V ≃ₗ[ZMod 2] V) (((h⁻¹ : H) : V ≃ₗ[ZMod 2] V) w) = w := by
    simp only [Subgroup.coe_inv]
    exact LinearEquiv.apply_symm_apply _ _
  have hcoe : (((h * x * h⁻¹ : H)) : V ≃ₗ[ZMod 2] V) =
      (h : V ≃ₗ[ZMod 2] V) * ((x : H) : V ≃ₗ[ZMod 2] V) * ((h⁻¹ : H) : V ≃ₗ[ZMod 2] V) := rfl
  rw [hcoe, LinearEquiv.mul_apply, LinearEquiv.mul_apply, h2, h3]

private lemma three_mul_card_fixW_dvd {H : Subgroup (orthogonalGroup q)}
    (hW2 : finrank (ZMod 2) W = 2)
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    (hfix : ∀ v : V, (∀ h : H, (h : V ≃ₗ[ZMod 2] V) v = v) → v = 0) :
    3 * Nat.card (fixW hHW) ∣ Nat.card H := by
  classical
  haveI := fixW_normal hHW
  obtain ⟨h₀, hfix0, h03⟩ := exists_no_fixed_on_W hW2 hHW hfix
  have h0not : h₀ ∉ fixW hHW := by
    obtain ⟨w1, w2, hli, hspan⟩ := exists_pair_of_finrank_eq_two hW2
    have hw1 : w1 ∈ W := by rw [← hspan]; exact Submodule.subset_span (by simp)
    have hw10 : w1 ≠ 0 := (linearIndependent_pair_iff.mp hli).1
    exact fun hmem => hfix0 w1 hw1 hw10 (hmem w1 hw1)
  have h3 : orderOf (QuotientGroup.mk' (fixW hHW) h₀) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      show ((h₀ ^ 3 : H) : H ⧸ fixW hHW) = 1
      rw [QuotientGroup.eq_one_iff]
      exact h03
    · intro h1
      exact h0not ((QuotientGroup.eq_one_iff h₀).mp h1)
  have hdvd : 3 ∣ Nat.card (H ⧸ fixW hHW) := by
    rw [← h3]
    exact orderOf_dvd_natCard _
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (fixW hHW)
  obtain ⟨k, hk⟩ := hdvd
  rw [hcard, hk]
  exact Dvd.intro k (by ring)

private lemma span_le_orthogonal_self {s : Set V}
    (h : ∀ x ∈ s, ∀ y ∈ s, polar q x y = 0) :
    Submodule.span (ZMod 2) s ≤
      LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) s) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  refine Submodule.span_induction₂ (s := s) (t := s) (p := fun x y _ _ => polar q y x = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro u v hu hv
    rw [polar_comm]
    exact h u hu v hv
  · intro y hy
    simp
  · intro x hx
    simp
  · intro u v z hu hv hz h1 h2
    rw [polar_add_right, h1, h2, add_zero]
  · intro u v z hu hv hz h1 h2
    rw [polar_add_left, h1, h2, add_zero]
  · intro r u v hu hv h1
    rw [polar_smul_right, h1, smul_zero]
  · intro r u v hu hv h1
    rw [polar_smul_left, h1, smul_zero]

private lemma q_eq_zero_of_mem_span {s : Set V} (hq0 : ∀ x ∈ s, q x = 0)
    (h : ∀ x ∈ s, ∀ y ∈ s, polar q x y = 0) {x : V}
    (hx : x ∈ Submodule.span (ZMod 2) s) : q x = 0 := by
  have horth := span_le_orthogonal_self h
  refine Submodule.span_induction (p := fun x _ => q x = 0) ?_ ?_ ?_ ?_ hx
  · exact hq0
  · exact map_zero q
  · intro u v hu hv hu0 hv0
    rw [map_add_eq, hu0, hv0, zero_add, zero_add, polar_comm]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp (horth hu) v hv
  · intro c u hu hu0
    rw [map_smul_zmod2, hu0, mul_zero]

private lemma le_orthogonal_self_of_q_eq_zero {T : Submodule (ZMod 2) V}
    (hT : ∀ x ∈ T, q x = 0) : T ≤ LinearMap.BilinForm.orthogonal q.polarBilin T := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  have h1 := hT (x + y) (T.add_mem hx hy)
  rw [map_add_eq, hT x hx, hT y hy, zero_add, zero_add] at h1
  rw [polarBilin_apply_apply, polar_comm]
  exact h1

private lemma finrank_le_two_of_q_eq_zero_of_le_perpW (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (hW2 : finrank (ZMod 2) W = 2)
    (hWq : ∀ w ∈ W, w ≠ 0 → q w = 1) {T : Submodule (ZMod 2) V}
    (hTU : T ≤ orthW) (hT : ∀ x ∈ T, q x = 0) : finrank (ZMod 2) T ≤ 2 := by
  have hTorth : T ≤ LinearMap.BilinForm.orthogonal q.polarBilin T := le_orthogonal_self_of_q_eq_zero hT
  have hWle : W ≤ LinearMap.BilinForm.orthogonal q.polarBilin T := by
    intro w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro t ht
    rw [polarBilin_apply_apply, polar_comm]
    exact LinearMap.BilinForm.mem_orthogonal_iff.mp (hTU ht) w hw
  have hsup : W ⊔ T ≤ LinearMap.BilinForm.orthogonal q.polarBilin T := sup_le hWle hTorth
  have hle := Submodule.finrank_mono hsup
  rw [LinearMap.BilinForm.finrank_orthogonal hq, hV] at hle
  have hinf : W ⊓ T = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx1 : x ∈ W ⊓ orthW := ⟨hx.1, hTU hx.2⟩
    rwa [inf_perpW_eq_bot hW2 hWq] at hx1
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W T
  rw [hinf, finrank_bot, hW2] at hsum
  omega

private lemma false_of_pairwise_orthogonal
    (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 6)
    (hW2 : finrank (ZMod 2) W = 2) (hWq : ∀ w ∈ W, w ≠ 0 → q w = 1)
    {H : Subgroup (orthogonalGroup q)}
    (hO2 : ∀ N : Subgroup (orthogonalGroup q), N ≤ H →
      H ≤ Subgroup.normalizer (N : Set _) → IsPGroup 2 N → N = ⊥)
    (hfix : ∀ v : V, (∀ h ∈ H, (h : V ≃ₗ[ZMod 2] V) v = v) → v = 0)
    {D : Set V} (hD : D.Nonempty) (hDU : D ⊆ orthW)
    (hDq : ∀ a ∈ D, a ≠ 0 ∧ q a = 0)
    (hDH : ∀ h ∈ H, ∀ a ∈ D, (h : V ≃ₗ[ZMod 2] V) a ∈ D)
    (hE : ∀ a ∈ D, ∀ u ∈ orthW, polar q a u = 0 →
      (⟨eichler q a u, eichler_mem_orthogonalGroup q a u⟩ : orthogonalGroup q) ∈ H)
    (hP : ∀ a ∈ D, ∀ b ∈ D, polar q a b = 0) : False := by
  classical
  by_cases hsingle : ∀ a ∈ D, ∀ b ∈ D, a = b
  · obtain ⟨a, ha⟩ := hD
    have hfixa : ∀ h ∈ H, (h : V ≃ₗ[ZMod 2] V) a = a := by
      intro h hh
      exact hsingle _ (hDH h hh a ha) _ ha
    exact (hDq a ha).1 (hfix a hfixa)
  · have hsingle' : ∃ a ∈ D, ∃ b ∈ D, a ≠ b := by
      by_contra h
      exact hsingle (fun a ha b hb => by
        by_contra hne
        exact h ⟨a, ha, b, hb, hne⟩)
    obtain ⟨a, ha, b, hb, hab_ne⟩ := hsingle'
    obtain ⟨ha0, hqa⟩ := hDq a ha
    obtain ⟨hb0, hqb⟩ := hDq b hb
    have hab : polar q a b = 0 := hP a ha b hb
    have hli : LinearIndependent (ZMod 2) ![a, b] :=
      linearIndependent_pair_iff.mpr ⟨ha0, hb0, hab_ne⟩
    let T : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {a, b}
    have hT2 : finrank (ZMod 2) T = 2 := finrank_span_pair hli
    have hTq : ∀ x ∈ T, q x = 0 := fun x hx => map_eq_zero_of_mem_span_pair hqa hqb hab hx
    have hmemT : ∀ c ∈ D, c ∈ T := by
      intro c hc
      have hmemD : ∀ x ∈ ({a, b, c} : Set V), x ∈ D := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact ha
        · exact hb
        · exact hc
      have hzero : ∀ x ∈ ({a, b, c} : Set V), q x = 0 :=
        fun x hx => (hDq x (hmemD x hx)).2
      have hpair : ∀ x ∈ ({a, b, c} : Set V), ∀ y ∈ ({a, b, c} : Set V), polar q x y = 0 :=
        fun x hx y hy => hP x (hmemD x hx) y (hmemD y hy)
      have hT'q : ∀ x ∈ Submodule.span (ZMod 2) ({a, b, c} : Set V), q x = 0 :=
        fun x hx => q_eq_zero_of_mem_span hzero hpair hx
      have hleU : Submodule.span (ZMod 2) ({a, b, c} : Set V) ≤ orthW := by
        rw [Submodule.span_le]
        exact fun x hx => hDU (hmemD x hx)
      have hfr := finrank_le_two_of_q_eq_zero_of_le_perpW hq hV hW2 hWq hleU hT'q
      have hTle : T ≤ Submodule.span (ZMod 2) ({a, b, c} : Set V) := by
        rw [Submodule.span_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact Submodule.subset_span (by simp)
        · exact Submodule.subset_span (by simp)
      have hfr2 : finrank (ZMod 2) (Submodule.span (ZMod 2) ({a, b, c} : Set V)) = 2 := by
        have h1 := Submodule.finrank_mono hTle
        rw [hT2] at h1
        omega
      have heq : T = Submodule.span (ZMod 2) ({a, b, c} : Set V) :=
        Submodule.eq_of_le_of_finrank_eq hTle (by rw [hT2, hfr2])
      rw [heq]
      exact Submodule.subset_span (by simp)
    have hEeq : ∀ h ∈ H, eichler q ((h : V ≃ₗ[ZMod 2] V) a) ((h : V ≃ₗ[ZMod 2] V) b) =
        eichler q a b := by
      intro h hh
      have hqa' : q ((h : V ≃ₗ[ZMod 2] V) a) = 0 := by
        rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem h.2, hqa]
      have hqb' : q ((h : V ≃ₗ[ZMod 2] V) b) = 0 := by
        rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem h.2, hqb]
      have hab' : polar q ((h : V ≃ₗ[ZMod 2] V) a) ((h : V ≃ₗ[ZMod 2] V) b) = 0 := by
        rw [CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem h.2, hab]
      have hha0 : (h : V ≃ₗ[ZMod 2] V) a ≠ 0 := by
        intro h0
        exact ha0 ((h : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
      have hhb0 : (h : V ≃ₗ[ZMod 2] V) b ≠ 0 := by
        intro h0
        exact hb0 ((h : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h0)
      have hne : (h : V ≃ₗ[ZMod 2] V) a ≠ (h : V ≃ₗ[ZMod 2] V) b := by
        intro h0
        exact hab_ne ((h : V ≃ₗ[ZMod 2] V).injective h0)
      have hli' : LinearIndependent (ZMod 2) ![(h : V ≃ₗ[ZMod 2] V) a,
          (h : V ≃ₗ[ZMod 2] V) b] := linearIndependent_pair_iff.mpr ⟨hha0, hhb0, hne⟩
      have hspan' : Submodule.span (ZMod 2) {((h : V ≃ₗ[ZMod 2] V) a),
          ((h : V ≃ₗ[ZMod 2] V) b)} = T := by
        refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
        · rw [Submodule.span_le]
          intro x hx
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact hmemT _ (hDH h hh a ha)
          · exact hmemT _ (hDH h hh b hb)
        · rw [finrank_span_pair hli', hT2]
      obtain ⟨hA', hc', hfixE'⟩ := eichler_of_totallySingular hq hli' hqa' hqb' hab'
      obtain ⟨hA, hc, hfixE⟩ := eichler_of_totallySingular hq hli hqa hqb hab
      obtain ⟨w, hw, huniqw⟩ := existsUnique_of_totallySingular_finrank_two hq hTq hT2
      have hPE : eichler q a b ∈ orthogonalGroup q ∧ eichler q a b ≠ 1 ∧
          commSpace (eichler q a b) ≤ T ∧
          ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin T, eichler q a b x = x := by
        refine ⟨eichler_mem_orthogonalGroup q a b, hA.2.1, ?_, ?_⟩
        · rw [hc]
        · intro x hx
          obtain ⟨h1, h2⟩ := mem_orthogonal_span_pair_iff.mp hx
          exact hfixE x h1 h2
      have hPE' : eichler q ((h : V ≃ₗ[ZMod 2] V) a) ((h : V ≃ₗ[ZMod 2] V) b) ∈
            orthogonalGroup q ∧
          eichler q ((h : V ≃ₗ[ZMod 2] V) a) ((h : V ≃ₗ[ZMod 2] V) b) ≠ 1 ∧
          commSpace (eichler q ((h : V ≃ₗ[ZMod 2] V) a) ((h : V ≃ₗ[ZMod 2] V) b)) ≤ T ∧
          ∀ x ∈ LinearMap.BilinForm.orthogonal q.polarBilin T,
            eichler q ((h : V ≃ₗ[ZMod 2] V) a) ((h : V ≃ₗ[ZMod 2] V) b) x = x := by
        refine ⟨eichler_mem_orthogonalGroup q _ _, hA'.2.1, ?_, ?_⟩
        · rw [hc', hspan']
        · intro x hx
          rw [← hspan'] at hx
          obtain ⟨h1, h2⟩ := mem_orthogonal_span_pair_iff.mp hx
          exact hfixE' x h1 h2
      rw [huniqw _ hPE', huniqw _ hPE]
    set E : orthogonalGroup q := ⟨eichler q a b, eichler_mem_orthogonalGroup q a b⟩ with hEdef
    have hEH : E ∈ H := hE a ha b (hDU hb) hab
    have hE1 : E ≠ 1 := by
      intro h1
      have h2 : (E : V ≃ₗ[ZMod 2] V) = 1 := congrArg Subtype.val h1
      exact eichler_ne_one hq hqa hab hli h2
    have hE2 : E ^ 2 = 1 := by
      rw [pow_two]
      exact Subtype.ext (eichler_mul_self hab)
    have hconj : ∀ h ∈ H, h * E * h⁻¹ = E := by
      intro h hh
      apply Subtype.ext
      show (h : V ≃ₗ[ZMod 2] V) * (E : V ≃ₗ[ZMod 2] V) * (h : V ≃ₗ[ZMod 2] V)⁻¹ =
        (E : V ≃ₗ[ZMod 2] V)
      rw [hEdef]
      show (h : V ≃ₗ[ZMod 2] V) * eichler q a b * (h : V ≃ₗ[ZMod 2] V)⁻¹ = eichler q a b
      rw [CFSG.ClassicalGroups.Orthogonal.eichler_conj h.2 a b, hEeq h hh]
    let N : Subgroup (orthogonalGroup q) := Subgroup.zpowers E
    have hNH : N ≤ H := by
      change Subgroup.zpowers E ≤ H
      rw [Subgroup.zpowers_le]
      exact hEH
    have hconjN : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N := by
      intro h hh n hn
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
      rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hconj h hh]
      exact Subgroup.zpow_mem N (Subgroup.mem_zpowers E) k
    have hHN : H ≤ Subgroup.normalizer (N : Set _) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · exact hconjN h hh n
      · intro hn
        have h2 := hconjN h⁻¹ (H.inv_mem hh) (h * n * h⁻¹) hn
        have h3 : h⁻¹ * (h * n * h⁻¹) * (h⁻¹)⁻¹ = n := by group
        rwa [h3] at h2
    have hP2 : IsPGroup 2 N := by
      have h1 : orderOf E = 2 := orderOf_eq_prime hE2 hE1
      change IsPGroup 2 (Subgroup.zpowers E)
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, h1]
      norm_num
    have hNbot : N = ⊥ := hO2 N hNH hHN hP2
    have hNne : N ≠ ⊥ := by
      change Subgroup.zpowers E ≠ ⊥
      intro h1
      exact hE1 ((Subgroup.zpowers_eq_bot).mp h1)
    exact hNne hNbot

private def V0 (q : QuadraticForm (ZMod 2) V) (W : Submodule (ZMod 2) V) (a b : V) :
    Submodule (ZMod 2) V :=
  LinearMap.BilinForm.orthogonal q.polarBilin W ⊓
    LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {a, b})

private lemma mem_V0_iff {a b x : V} :
    x ∈ V0 q W a b ↔ x ∈ orthW ∧ polar q a x = 0 ∧ polar q b x = 0 := by
  rw [V0, Submodule.mem_inf, mem_orthogonal_span_pair_iff]

private lemma decomp_mem_V0 {a b x : V} (hab : polar q a b = 1) (hx : x ∈ orthW)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    x + polar q x b • a + polar q x a • b ∈ V0 q W a b := by
  rw [mem_V0_iff]
  refine ⟨?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.add_mem _ hx (Submodule.smul_mem _ _ haU))
      (Submodule.smul_mem _ _ hbU)
  · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
      polar_self_eq_zero, smul_zero, add_zero, smul_eq_mul, hab, mul_one, polar_comm q a x]
    exact zmod2_add_self _
  · rw [polar_add_right, polar_add_right, polar_smul_right, polar_smul_right,
      polar_self_eq_zero, smul_zero, add_zero, smul_eq_mul, polar_comm q b a, hab, mul_one,
      polar_comm q b x]
    exact zmod2_add_self _

private lemma eq_smul_add_smul_add_decomp {a b x : V} (hab : polar q a b = 1) (hx : x ∈ orthW)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    polar q x b • a + polar q x a • b + (x + polar q x b • a + polar q x a • b) = x := by
  rw [show polar q x b • a + polar q x a • b + (x + polar q x b • a + polar q x a • b) =
    x + (polar q x b • a + polar q x b • a) + (polar q x a • b + polar q x a • b) from by abel]
  rw [vec_add_self, vec_add_self, add_zero, add_zero]

private lemma orthW_eq_sup_span_pair_V0 {a b : V} (hab : polar q a b = 1)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    orthW = Submodule.span (ZMod 2) {a, b} ⊔ V0 q W a b := by
  have hspan : ∀ s t : ZMod 2, s • a + t • b ∈ Submodule.span (ZMod 2) {a, b} := by
    intro s t
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  refine le_antisymm ?_ (sup_le ?_ inf_le_left)
  · intro x hx
    have hdec := eq_smul_add_smul_add_decomp (q := q) (W := W) hab hx haU hbU
    rw [← hdec]
    exact Submodule.mem_sup.mpr
      ⟨_, hspan _ _, _, decomp_mem_V0 (q := q) (W := W) hab hx haU hbU, rfl⟩
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · exact haU
    · exact hbU

private lemma inf_span_pair_V0 {a b : V} (hab : polar q a b = 1) :
    Submodule.span (ZMod 2) {a, b} ⊓ V0 q W a b = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hy1, hy2, hy3⟩ := mem_V0_iff.mp hy.2
  rw [Submodule.mem_bot]
  have hy' : y ∈ Submodule.span (ZMod 2) {a, b} := hy.1
  obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hy'
  have h1 : polar q a (s • a + t • b) = 0 := hy2
  have h2 : polar q b (s • a + t • b) = 0 := hy3
  have ht : t = 0 := by
    have h := h1
    simp only [polar_add_right, polar_smul_right, polar_self_eq_zero, hab, smul_zero, add_zero,
      zero_add, smul_eq_mul, mul_one, mul_zero] at h
    exact h
  have hs : s = 0 := by
    have h := h2
    simp only [polar_add_right, polar_smul_right, polar_self_eq_zero, polar_comm q b a, hab,
      smul_zero, add_zero, zero_add, smul_eq_mul, mul_one, mul_zero] at h
    exact h
  rw [hs, ht, zero_smul, zero_smul, add_zero]

private lemma finrank_V0 {a b : V} (hab : polar q a b = 1) (hV : finrank (ZMod 2) V = 6)
    (hq : q.polarBilin.Nondegenerate) (hW2 : finrank (ZMod 2) W = 2)
    (hWq : ∀ w ∈ W, w ≠ 0 → q w = 1) (haU : a ∈ orthW) (hbU : b ∈ orthW)
    (hli : LinearIndependent (ZMod 2) ![a, b]) : finrank (ZMod 2) (V0 q W a b) = 2 := by
  have hsup : orthW = Submodule.span (ZMod 2) {a, b} ⊔ V0 q W a b :=
    orthW_eq_sup_span_pair_V0 hab haU hbU
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span (ZMod 2) {a, b}) (V0 q W a b)
  rw [← hsup, inf_span_pair_V0 hab, finrank_span_pair hli, finrank_bot,
    finrank_perpW hq hV hW2] at hsum
  omega

private lemma orthW_eq_span_four {a b c d : V} (hab : polar q a b = 1)
    (haU : a ∈ orthW) (hbU : b ∈ orthW)
    (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b) :
    orthW = Submodule.span (ZMod 2) ({a, b, c, d} : Set V) := by
  rw [orthW_eq_sup_span_pair_V0 hab haU hbU, ← hV0, ← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private lemma q_add_add (x y z : V) :
    q (x + y + z) = q x + q y + q z + polar q x y + polar q x z + polar q y z := by
  rw [show x + y + z = x + (y + z) from by abel]
  rw [map_add_eq, map_add_eq, polar_add_right]
  ring

private lemma q_add_add_add (w x y z : V) :
    q (w + x + y + z) = q w + q x + q y + q z + polar q w x + polar q w y + polar q w z +
      polar q x y + polar q x z + polar q y z := by
  rw [show w + x + y + z = w + x + (y + z) from by abel]
  rw [q_add_add, map_add_eq, polar_add_right, polar_add_right]
  ring

private lemma q_combination_aniso {a b c d : V} (hqa : q a = 0) (hqb : q b = 0)
    (hqc : q c = 1) (hqd : q d = 1) (hcd : polar q c d = 1) (hab : polar q a b = 1)
    (hac : polar q a c = 0) (had : polar q a d = 0) (hbc : polar q b c = 0)
    (hbd : polar q b d = 0) (α β s t : ZMod 2) :
    q (α • a + β • b + s • c + t • d) = α * β + s + t + s * t := by
  rw [q_add_add_add]
  simp only [map_smul_zmod2, polar_smul_left, polar_smul_right, smul_eq_mul, hqa, hqb, hqc, hqd,
    hab, hac, had, hbc, hbd, hcd, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  ring

private lemma q_combination_hyp {a b c d : V} (hqa : q a = 0) (hqb : q b = 0)
    (hqc : q c = 0) (hqd : q d = 0) (hcd : polar q c d = 1) (hab : polar q a b = 1)
    (hac : polar q a c = 0) (had : polar q a d = 0) (hbc : polar q b c = 0)
    (hbd : polar q b d = 0) (α β s t : ZMod 2) :
    q (α • a + β • b + s • c + t • d) = α * β + s * t := by
  rw [q_add_add_add]
  simp only [map_smul_zmod2, polar_smul_left, polar_smul_right, smul_eq_mul, hqa, hqb, hqc, hqd,
    hab, hac, had, hbc, hbd, hcd, mul_one, mul_zero, zero_mul, add_zero, zero_add]
  ring

private lemma zmod2_add_add_mul_eq_zero {s t : ZMod 2} (h : s + t + s * t = 0) :
    s = 0 ∧ t = 0 := by
  revert h
  revert s t
  decide

private lemma zmod2_add_add_mul_eq_one {s t : ZMod 2} (h : s + t + s * t = 1) :
    (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 1) := by
  revert h
  revert s t
  decide

private lemma zmod2_mul_eq_one {s t : ZMod 2} (h : s * t = 1) : s = 1 ∧ t = 1 := by
  revert h
  revert s t
  decide

private lemma zmod2_one_add_eq_zero {x : ZMod 2} (h : 1 + x = 0) : x = 1 := by
  revert h
  revert x
  decide

private lemma zmod2_one_add_eq_one {x : ZMod 2} (h : 1 + x = 1) : x = 0 := by
  revert h
  revert x
  decide

private lemma mem_cover_singular_aniso {a b c d x : V} (hqa : q a = 0) (hqb : q b = 0)
    (hqc : q c = 1) (hqd : q d = 1) (hcd : polar q c d = 1) (hab : polar q a b = 1)
    (hac : polar q a c = 0) (had : polar q a d = 0) (hbc : polar q b c = 0)
    (hbd : polar q b d = 0) (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) (hx : x ∈ orthW) (hx0 : x ≠ 0)
    (hxq : q x = 0) :
    x ∈ ({a, b, a + b + c, a + b + d, a + b + c + d} : Set V) := by
  have hdec := eq_smul_add_smul_add_decomp (q := q) (W := W) hab hx haU hbU
  have hv : x + polar q x b • a + polar q x a • b ∈ V0 q W a b :=
    decomp_mem_V0 (q := q) (W := W) hab hx haU hbU
  rw [← hV0] at hv
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hv
  have hx4 : x = polar q x b • a + polar q x a • b + s • c + t • d := by
    calc x = polar q x b • a + polar q x a • b +
          (x + polar q x b • a + polar q x a • b) := hdec.symm
      _ = polar q x b • a + polar q x a • b + (s • c + t • d) := by rw [← hst]
      _ = polar q x b • a + polar q x a • b + s • c + t • d := by abel
  have hqx : q (polar q x b • a + polar q x a • b + s • c + t • d) =
      polar q x b * polar q x a + s + t + s * t :=
    q_combination_aniso hqa hqb hqc hqd hcd hab hac had hbc hbd _ _ s t
  have hq0 : polar q x b * polar q x a + s + t + s * t = 0 := by
    rw [← hqx, ← hx4, hxq]
  rcases zmod2_eq_zero_or_eq_one (polar q x b) with hα | hα <;>
    rcases zmod2_eq_zero_or_eq_one (polar q x a) with hβ | hβ
  · have hst0 : s + t + s * t = 0 := by simpa [hα, hβ] using hq0
    obtain ⟨hs, ht⟩ := zmod2_add_add_mul_eq_zero hst0
    rw [hα, hβ, hs, ht] at hx4
    simp only [zero_smul, add_zero] at hx4
    exact absurd hx4 hx0
  · have hst0 : s + t + s * t = 0 := by simpa [hα, hβ] using hq0
    obtain ⟨hs, ht⟩ := zmod2_add_add_mul_eq_zero hst0
    rw [hα, hβ, hs, ht] at hx4
    simp only [zero_smul, one_smul, add_zero] at hx4
    rw [hx4]
    simp
  · have hst0 : s + t + s * t = 0 := by simpa [hα, hβ] using hq0
    obtain ⟨hs, ht⟩ := zmod2_add_add_mul_eq_zero hst0
    rw [hα, hβ, hs, ht] at hx4
    simp only [zero_smul, one_smul, add_zero] at hx4
    rw [hx4]
    simp
  · have hst1 : s + t + s * t = 1 := by
      have h := hq0
      rw [hα, hβ, mul_one] at h
      exact zmod2_one_add_eq_zero (by simpa only [add_assoc] using h)
    rcases zmod2_add_add_mul_eq_one hst1 with ⟨hs, ht⟩ | ⟨hs, ht⟩ | ⟨hs, ht⟩
    · rw [hα, hβ, hs, ht] at hx4
      simp only [one_smul, zero_smul, add_zero] at hx4
      rw [hx4]
      simp
    · rw [hα, hβ, hs, ht] at hx4
      simp only [one_smul, zero_smul, add_zero] at hx4
      rw [hx4]
      simp
    · rw [hα, hβ, hs, ht] at hx4
      simp only [one_smul, zero_smul, add_zero] at hx4
      rw [hx4]
      simp

private lemma mem_cover_nonsingular_hyp {a b c d x : V} (hqa : q a = 0) (hqb : q b = 0)
    (hqc : q c = 0) (hqd : q d = 0) (hcd : polar q c d = 1) (hab : polar q a b = 1)
    (hac : polar q a c = 0) (had : polar q a d = 0) (hbc : polar q b c = 0)
    (hbd : polar q b d = 0) (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) (hx : x ∈ orthW) (hxq : q x = 1) :
    x ∈ ({c + d, a + c + d, b + c + d, a + b, a + b + c, a + b + d} : Set V) := by
  have hdec := eq_smul_add_smul_add_decomp (q := q) (W := W) hab hx haU hbU
  have hv : x + polar q x b • a + polar q x a • b ∈ V0 q W a b :=
    decomp_mem_V0 (q := q) (W := W) hab hx haU hbU
  rw [← hV0] at hv
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.mp hv
  have hx4 : x = polar q x b • a + polar q x a • b + s • c + t • d := by
    calc x = polar q x b • a + polar q x a • b +
          (x + polar q x b • a + polar q x a • b) := hdec.symm
      _ = polar q x b • a + polar q x a • b + (s • c + t • d) := by rw [← hst]
      _ = polar q x b • a + polar q x a • b + s • c + t • d := by abel
  have hqx : q (polar q x b • a + polar q x a • b + s • c + t • d) =
      polar q x b * polar q x a + s * t :=
    q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd _ _ s t
  have hq1 : polar q x b * polar q x a + s * t = 1 := by
    rw [← hqx, ← hx4, hxq]
  rcases zmod2_eq_zero_or_eq_one (polar q x b) with hα | hα <;>
    rcases zmod2_eq_zero_or_eq_one (polar q x a) with hβ | hβ
  · have hst1 : s * t = 1 := by simpa [hα, hβ] using hq1
    obtain ⟨hs, ht⟩ := zmod2_mul_eq_one hst1
    rw [hα, hβ, hs, ht] at hx4
    simp only [zero_smul, one_smul, add_zero] at hx4
    rw [hx4]
    simp
  · have hst1 : s * t = 1 := by simpa [hα, hβ] using hq1
    obtain ⟨hs, ht⟩ := zmod2_mul_eq_one hst1
    rw [hα, hβ, hs, ht] at hx4
    simp only [zero_smul, one_smul, add_zero] at hx4
    rw [hx4]
    simp
  · have hst1 : s * t = 1 := by simpa [hα, hβ] using hq1
    obtain ⟨hs, ht⟩ := zmod2_mul_eq_one hst1
    rw [hα, hβ, hs, ht] at hx4
    simp only [zero_smul, one_smul, add_zero] at hx4
    rw [hx4]
    simp
  · have hst0 : s * t = 0 := by
      have h := hq1
      rw [hα, hβ, mul_one] at h
      exact zmod2_one_add_eq_one h
    rcases zmod2_eq_zero_or_eq_one s with hs | hs <;>
      rcases zmod2_eq_zero_or_eq_one t with ht | ht
    · rw [hα, hβ, hs, ht] at hx4
      simp only [one_smul, zero_smul, mul_zero, add_zero] at hx4
      rw [hx4]
      simp
    · rw [hα, hβ, hs, ht] at hx4
      simp only [one_smul, zero_smul, mul_zero, add_zero] at hx4
      rw [hx4]
      simp
    · rw [hα, hβ, hs, ht] at hx4
      simp only [one_smul, zero_smul, mul_zero, add_zero] at hx4
      rw [hx4]
      simp
    · rw [hs, ht, mul_one] at hst0
      exact absurd hst0 (by decide)

private lemma eq_one_of_fixes_singular_aniso {H : Subgroup (orthogonalGroup q)}
    {a b c d : V} {h : H}
    (hY : ∀ h : H, (∀ u ∈ orthW, (h : V ≃ₗ[ZMod 2] V) u = u) → h = 1)
    (hfix : ∀ x ∈ orthW, x ≠ 0 → q x = 0 → (h : V ≃ₗ[ZMod 2] V) x = x)
    (hqa : q a = 0) (hqb : q b = 0) (hqc : q c = 1) (hqd : q d = 1)
    (hcd : polar q c d = 1) (hab : polar q a b = 1) (hac : polar q a c = 0)
    (had : polar q a d = 0) (hbc : polar q b c = 0) (hbd : polar q b d = 0)
    (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    h = 1 := by
  have hcU : c ∈ orthW := (mem_V0_iff.mp (by rw [← hV0]; exact Submodule.subset_span (by simp))).1
  have hdU : d ∈ orthW := (mem_V0_iff.mp (by rw [← hV0]; exact Submodule.subset_span (by simp))).1
  have hqabc : q (a + b + c) = 0 := by
    have h := q_combination_aniso hqa hqb hqc hqd hcd hab hac had hbc hbd
      (1 : ZMod 2) (1 : ZMod 2) (1 : ZMod 2) (0 : ZMod 2)
    have h' : q (a + b + c) = 1 + 1 := by simpa using h
    rw [h']
    decide
  have hqabd : q (a + b + d) = 0 := by
    have h := q_combination_aniso hqa hqb hqc hqd hcd hab hac had hbc hbd
      (1 : ZMod 2) (1 : ZMod 2) (0 : ZMod 2) (1 : ZMod 2)
    have h' : q (a + b + d) = 1 + 1 := by simpa using h
    rw [h']
    decide
  have hfa : (h : V ≃ₗ[ZMod 2] V) a = a := by
    by_cases h0 : a = 0
    · rw [h0]; simp
    · exact hfix a haU h0 hqa
  have hfb : (h : V ≃ₗ[ZMod 2] V) b = b := by
    by_cases h0 : b = 0
    · rw [h0]; simp
    · exact hfix b hbU h0 hqb
  have hfabc : (h : V ≃ₗ[ZMod 2] V) (a + b + c) = a + b + c := by
    by_cases h0 : a + b + c = 0
    · rw [h0]; simp
    · exact hfix _ (Submodule.add_mem _ (Submodule.add_mem _ haU hbU) hcU) h0 hqabc
  have hfabd : (h : V ≃ₗ[ZMod 2] V) (a + b + d) = a + b + d := by
    by_cases h0 : a + b + d = 0
    · rw [h0]; simp
    · exact hfix _ (Submodule.add_mem _ (Submodule.add_mem _ haU hbU) hdU) h0 hqabd
  have hc : (h : V ≃ₗ[ZMod 2] V) c = c := by
    have h1 : (h : V ≃ₗ[ZMod 2] V) (a + b + c) = (h : V ≃ₗ[ZMod 2] V) a +
        (h : V ≃ₗ[ZMod 2] V) b + (h : V ≃ₗ[ZMod 2] V) c := by rw [map_add, map_add]
    rw [hfa, hfb, hfabc] at h1
    have h1' : a + b + c = a + b + (h : V ≃ₗ[ZMod 2] V) c := h1
    have h2 : b + c = b + (h : V ≃ₗ[ZMod 2] V) c := by
      apply add_left_cancel (a := a)
      rw [← add_assoc, ← add_assoc]
      exact h1'
    exact (add_left_cancel h2).symm
  have hd : (h : V ≃ₗ[ZMod 2] V) d = d := by
    have h1 : (h : V ≃ₗ[ZMod 2] V) (a + b + d) = (h : V ≃ₗ[ZMod 2] V) a +
        (h : V ≃ₗ[ZMod 2] V) b + (h : V ≃ₗ[ZMod 2] V) d := by rw [map_add, map_add]
    rw [hfa, hfb, hfabd] at h1
    have h1' : a + b + d = a + b + (h : V ≃ₗ[ZMod 2] V) d := h1
    have h2 : b + d = b + (h : V ≃ₗ[ZMod 2] V) d := by
      apply add_left_cancel (a := a)
      rw [← add_assoc, ← add_assoc]
      exact h1'
    exact (add_left_cancel h2).symm
  apply hY h
  intro u hu
  rw [orthW_eq_span_four hab haU hbU hV0] at hu
  refine Submodule.span_induction (p := fun u _ => (h : V ≃ₗ[ZMod 2] V) u = u) ?_ ?_ ?_ ?_ hu
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hfa
    · exact hfb
    · exact hc
    · exact hd
  · simp
  · intro u v hu hv hu' hv'
    rw [map_add, hu', hv']
  · intro r u hu hu'
    rw [map_smul, hu']

private lemma eq_one_of_fixes_nonsingular_hyp {H : Subgroup (orthogonalGroup q)}
    {a b c d : V} {h : H}
    (hY : ∀ h : H, (∀ u ∈ orthW, (h : V ≃ₗ[ZMod 2] V) u = u) → h = 1)
    (hfix : ∀ x ∈ orthW, q x = 1 → (h : V ≃ₗ[ZMod 2] V) x = x)
    (hqa : q a = 0) (hqb : q b = 0) (hqc : q c = 0) (hqd : q d = 0)
    (hcd : polar q c d = 1) (hab : polar q a b = 1) (hac : polar q a c = 0)
    (had : polar q a d = 0) (hbc : polar q b c = 0) (hbd : polar q b d = 0)
    (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    h = 1 := by
  have hcU : c ∈ orthW := (mem_V0_iff.mp (by rw [← hV0]; exact Submodule.subset_span (by simp))).1
  have hdU : d ∈ orthW := (mem_V0_iff.mp (by rw [← hV0]; exact Submodule.subset_span (by simp))).1
  have hqcd : q (c + d) = 1 := by
    have h := q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd
      (0 : ZMod 2) (0 : ZMod 2) (1 : ZMod 2) (1 : ZMod 2)
    have h' : q (c + d) = 1 := by simpa using h
    exact h'
  have hqacd : q (a + c + d) = 1 := by
    have h := q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd
      (1 : ZMod 2) (0 : ZMod 2) (1 : ZMod 2) (1 : ZMod 2)
    have h' : q (a + c + d) = 1 := by simpa using h
    exact h'
  have hqbcd : q (b + c + d) = 1 := by
    have h := q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd
      (0 : ZMod 2) (1 : ZMod 2) (1 : ZMod 2) (1 : ZMod 2)
    have h' : q (b + c + d) = 1 := by simpa using h
    exact h'
  have hqab : q (a + b) = 1 := by
    have h := q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd
      (1 : ZMod 2) (1 : ZMod 2) (0 : ZMod 2) (0 : ZMod 2)
    have h' : q (a + b) = 1 := by simpa using h
    exact h'
  have hqabc : q (a + b + c) = 1 := by
    have h := q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd
      (1 : ZMod 2) (1 : ZMod 2) (1 : ZMod 2) (0 : ZMod 2)
    have h' : q (a + b + c) = 1 := by simpa using h
    exact h'
  have hqabd : q (a + b + d) = 1 := by
    have h := q_combination_hyp hqa hqb hqc hqd hcd hab hac had hbc hbd
      (1 : ZMod 2) (1 : ZMod 2) (0 : ZMod 2) (1 : ZMod 2)
    have h' : q (a + b + d) = 1 := by simpa using h
    exact h'
  have hmem : ∀ x : V, x ∈ ({c + d, a + c + d, b + c + d, a + b, a + b + c, a + b + d} : Set V) →
      x ∈ orthW := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Submodule.add_mem _ hcU hdU
    · exact Submodule.add_mem _ (Submodule.add_mem _ haU hcU) hdU
    · exact Submodule.add_mem _ (Submodule.add_mem _ hbU hcU) hdU
    · exact Submodule.add_mem _ haU hbU
    · exact Submodule.add_mem _ (Submodule.add_mem _ haU hbU) hcU
    · exact Submodule.add_mem _ (Submodule.add_mem _ haU hbU) hdU
  have hf : ∀ x ∈ ({c + d, a + c + d, b + c + d, a + b, a + b + c, a + b + d} : Set V),
      (h : V ≃ₗ[ZMod 2] V) x = x := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfix _ (hmem _ (by simp)) hqcd
    · exact hfix _ (hmem _ (by simp)) hqacd
    · exact hfix _ (hmem _ (by simp)) hqbcd
    · exact hfix _ (hmem _ (by simp)) hqab
    · exact hfix _ (hmem _ (by simp)) hqabc
    · exact hfix _ (hmem _ (by simp)) hqabd
  have hc : (h : V ≃ₗ[ZMod 2] V) c = c := by
    have h1 : (h : V ≃ₗ[ZMod 2] V) ((a + b + c) + (a + b)) = (a + b + c) + (a + b) := by
      rw [map_add, hf _ (by simp), hf _ (by simp)]
    rw [show (a + b + c) + (a + b) = c from by
      rw [show (a + b + c) + (a + b) = c + ((a + b) + (a + b)) from by abel]
      rw [vec_add_self, add_zero]] at h1
    exact h1
  have hd : (h : V ≃ₗ[ZMod 2] V) d = d := by
    have h1 : (h : V ≃ₗ[ZMod 2] V) ((a + b + d) + (a + b)) = (a + b + d) + (a + b) := by
      rw [map_add, hf _ (by simp), hf _ (by simp)]
    rw [show (a + b + d) + (a + b) = d from by
      rw [show (a + b + d) + (a + b) = d + ((a + b) + (a + b)) from by abel]
      rw [vec_add_self, add_zero]] at h1
    exact h1
  have ha : (h : V ≃ₗ[ZMod 2] V) a = a := by
    have h1 : (h : V ≃ₗ[ZMod 2] V) ((a + c + d) + (c + d)) = (a + c + d) + (c + d) := by
      rw [map_add, hf _ (by simp), hf _ (by simp)]
    rw [show (a + c + d) + (c + d) = a from by
      rw [show (a + c + d) + (c + d) = a + ((c + d) + (c + d)) from by abel]
      rw [vec_add_self, add_zero]] at h1
    exact h1
  have hb : (h : V ≃ₗ[ZMod 2] V) b = b := by
    have h1 : (h : V ≃ₗ[ZMod 2] V) ((b + c + d) + (c + d)) = (b + c + d) + (c + d) := by
      rw [map_add, hf _ (by simp), hf _ (by simp)]
    rw [show (b + c + d) + (c + d) = b from by
      rw [show (b + c + d) + (c + d) = b + ((c + d) + (c + d)) from by abel]
      rw [vec_add_self, add_zero]] at h1
    exact h1
  apply hY h
  intro u hu
  rw [orthW_eq_span_four hab haU hbU hV0] at hu
  refine Submodule.span_induction (p := fun u _ => (h : V ≃ₗ[ZMod 2] V) u = u) ?_ ?_ ?_ ?_ hu
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  · simp
  · intro u v hu hv hu' hv'
    rw [map_add, hu', hv']
  · intro r u hu hu'
    rw [map_smul, hu']

private lemma card_dvd_120_aniso {H : Subgroup (orthogonalGroup q)} {a b c d : V}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    (hY : ∀ h : H, (∀ u ∈ orthW, (h : V ≃ₗ[ZMod 2] V) u = u) → h = 1)
    (hqa : q a = 0) (hqb : q b = 0) (hqc : q c = 1) (hqd : q d = 1)
    (hcd : polar q c d = 1) (hab : polar q a b = 1) (hac : polar q a c = 0)
    (had : polar q a d = 0) (hbc : polar q b c = 0) (hbd : polar q b d = 0)
    (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    Nat.card H ∣ Nat.factorial 5 := by
  classical
  haveI : Fintype V := Fintype.ofEquiv (Basis.ofVectorSpaceIndex (ZMod 2) V → ZMod 2)
    (Basis.ofVectorSpace (ZMod 2) V).equivFun.symm.toEquiv
  haveI : Fintype (V → V) := inferInstance
  haveI : Fintype (V ≃ₗ[ZMod 2] V) :=
    Fintype.ofInjective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun x => congrFun h x))
  haveI : Fintype (orthogonalGroup q) := Subtype.fintype _
  haveI : Fintype H := Subtype.fintype _
  let S := {x : V // x ∈ orthW ∧ x ≠ 0 ∧ q x = 0}
  haveI : Fintype S := Subtype.fintype _
  letI : MulAction H S :=
    { smul := fun h v => ⟨(h : V ≃ₗ[ZMod 2] V) v.1,
        mem_perpW_of_mem hHW v.2.1,
        fun hv => v.2.2.1 ((h : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp hv),
        by rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem (h : orthogonalGroup q).2, v.2.2.2]⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun h h' v => Subtype.ext rfl }
  have hsmul : ∀ (h : H) (v : S), ((h • v : S) : V) = (h : V ≃ₗ[ZMod 2] V) v.1 :=
    fun h v => rfl
  let φ : H →* Equiv.Perm S := MulAction.toPermHom H S
  have hφ1 : ∀ h : H, φ h = 1 → h = 1 := by
    intro h hh
    refine eq_one_of_fixes_singular_aniso (H := H) (h := h) hY ?_ hqa hqb hqc hqd hcd hab hac had
      hbc hbd hV0 haU hbU
    intro x hxU hx0 hxq
    have h2 := congrArg (fun τ : Equiv.Perm S => ((τ ⟨x, hxU, hx0, hxq⟩ : S) : V)) hh
    simpa only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, hsmul, Equiv.Perm.coe_one,
      id] using h2
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : x * y⁻¹ = 1 := hφ1 _ h1
    exact mul_inv_eq_one.mp h2
  have h1 : Nat.card H ∣ Nat.factorial (Fintype.card S) := natCard_dvd_factorial_of_injective φ hφ
  have h2 : Fintype.card S ≤ 5 := by
    have hsub : (Finset.univ.filter (fun x : V => x ∈ orthW ∧ x ≠ 0 ∧ q x = 0)) ⊆
        (Finset.univ : Finset (Fin 5)).image
          (fun i => ![a, b, a + b + c, a + b + d, a + b + c + d] i) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨-, hxU, hx0, hxq⟩ := hx
      have hcov := mem_cover_singular_aniso (q := q) (W := W) hqa hqb hqc hqd hcd hab hac had hbc
        hbd hV0 haU hbU hxU hx0 hxq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcov
      rw [Finset.mem_image]
      rcases hcov with rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, Finset.mem_univ _, by simp⟩
      · exact ⟨1, Finset.mem_univ _, by simp⟩
      · exact ⟨2, Finset.mem_univ _, by simp⟩
      · exact ⟨3, Finset.mem_univ _, by simp⟩
      · exact ⟨4, Finset.mem_univ _, by simp⟩
    calc Fintype.card S
        = (Finset.univ.filter (fun x : V => x ∈ orthW ∧ x ≠ 0 ∧ q x = 0)).card :=
          Fintype.card_subtype _
      _ ≤ ((Finset.univ : Finset (Fin 5)).image
            (fun i => ![a, b, a + b + c, a + b + d, a + b + c + d] i)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin 5)).card := Finset.card_image_le
      _ = 5 := by simp
  exact dvd_trans h1 (Nat.factorial_dvd_factorial h2)

private lemma card_dvd_720_hyp {H : Subgroup (orthogonalGroup q)} {a b c d : V}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    (hY : ∀ h : H, (∀ u ∈ orthW, (h : V ≃ₗ[ZMod 2] V) u = u) → h = 1)
    (hqa : q a = 0) (hqb : q b = 0) (hqc : q c = 0) (hqd : q d = 0)
    (hcd : polar q c d = 1) (hab : polar q a b = 1) (hac : polar q a c = 0)
    (had : polar q a d = 0) (hbc : polar q b c = 0) (hbd : polar q b d = 0)
    (hV0 : Submodule.span (ZMod 2) {c, d} = V0 q W a b)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) :
    Nat.card H ∣ Nat.factorial 6 := by
  classical
  haveI : Fintype V := Fintype.ofEquiv (Basis.ofVectorSpaceIndex (ZMod 2) V → ZMod 2)
    (Basis.ofVectorSpace (ZMod 2) V).equivFun.symm.toEquiv
  haveI : Fintype (V → V) := inferInstance
  haveI : Fintype (V ≃ₗ[ZMod 2] V) :=
    Fintype.ofInjective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun x => congrFun h x))
  haveI : Fintype (orthogonalGroup q) := Subtype.fintype _
  haveI : Fintype H := Subtype.fintype _
  let S := {x : V // x ∈ orthW ∧ q x = 1}
  haveI : Fintype S := Subtype.fintype _
  letI : MulAction H S :=
    { smul := fun h v => ⟨(h : V ≃ₗ[ZMod 2] V) v.1, mem_perpW_of_mem hHW v.2.1,
        by rw [CFSG.ClassicalGroups.Orthogonal.map_of_mem (h : orthogonalGroup q).2, v.2.2]⟩
      one_smul := fun v => Subtype.ext rfl
      mul_smul := fun h h' v => Subtype.ext rfl }
  have hsmul : ∀ (h : H) (v : S), ((h • v : S) : V) = (h : V ≃ₗ[ZMod 2] V) v.1 :=
    fun h v => rfl
  let φ : H →* Equiv.Perm S := MulAction.toPermHom H S
  have hφ1 : ∀ h : H, φ h = 1 → h = 1 := by
    intro h hh
    refine eq_one_of_fixes_nonsingular_hyp (H := H) (h := h) hY ?_ hqa hqb hqc hqd hcd hab hac
      had hbc hbd hV0 haU hbU
    intro x hxU hxq
    have h2 := congrArg (fun τ : Equiv.Perm S => ((τ ⟨x, hxU, hxq⟩ : S) : V)) hh
    simpa only [φ, MulAction.toPermHom_apply, MulAction.toPerm_apply, hsmul, Equiv.Perm.coe_one,
      id] using h2
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : φ (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy, mul_inv_cancel]
    have h2 : x * y⁻¹ = 1 := hφ1 _ h1
    exact mul_inv_eq_one.mp h2
  have h1 : Nat.card H ∣ Nat.factorial (Fintype.card S) := natCard_dvd_factorial_of_injective φ hφ
  have h2 : Fintype.card S ≤ 6 := by
    have hsub : (Finset.univ.filter (fun x : V => x ∈ orthW ∧ q x = 1)) ⊆
        (Finset.univ : Finset (Fin 6)).image
          (fun i => ![c + d, a + c + d, b + c + d, a + b, a + b + c, a + b + d] i) := by
      intro x hx
      rw [Finset.mem_filter] at hx
      obtain ⟨-, hxU, hxq⟩ := hx
      have hcov := mem_cover_nonsingular_hyp (q := q) (W := W) hqa hqb hqc hqd hcd hab hac had hbc
        hbd hV0 haU hbU hxU hxq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcov
      rw [Finset.mem_image]
      rcases hcov with rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨0, Finset.mem_univ _, by simp⟩
      · exact ⟨1, Finset.mem_univ _, by simp⟩
      · exact ⟨2, Finset.mem_univ _, by simp⟩
      · exact ⟨3, Finset.mem_univ _, by simp⟩
      · exact ⟨4, Finset.mem_univ _, by simp⟩
      · exact ⟨5, Finset.mem_univ _, by simp⟩
    calc Fintype.card S
        = (Finset.univ.filter (fun x : V => x ∈ orthW ∧ q x = 1)).card :=
          Fintype.card_subtype _
      _ ≤ ((Finset.univ : Finset (Fin 6)).image
            (fun i => ![c + d, a + c + d, b + c + d, a + b, a + b + c, a + b + d] i)).card :=
          Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_image_le
      _ = 6 := by simp
  exact dvd_trans h1 (Nat.factorial_dvd_factorial h2)

private lemma three_dvd_card_fixW_of_eichler_nonsingular {H : Subgroup (orthogonalGroup q)}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    {a b c : V} (hqa : q a = 0) (hqb : q b = 0) (hab : polar q a b = 1)
    (hac : polar q a c = 0) (hbc : polar q b c = 0) (hqc : q c = 1)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) (hcU : c ∈ orthW)
    (hEac : (⟨eichler q a c, eichler_mem_orthogonalGroup q a c⟩ : orthogonalGroup q) ∈ H)
    (hEbc : (⟨eichler q b c, eichler_mem_orthogonalGroup q b c⟩ : orthogonalGroup q) ∈ H) :
    3 ∣ Nat.card (fixW hHW) := by
  classical
  have hσorth : eichler q a c * eichler q b c ∈ orthogonalGroup q :=
    mul_mem (eichler_mem_orthogonalGroup q a c) (eichler_mem_orthogonalGroup q b c)
  have hσH : (⟨eichler q a c * eichler q b c, hσorth⟩ : orthogonalGroup q) ∈ H :=
    H.mul_mem hEac hEbc
  have hσX : (⟨⟨eichler q a c * eichler q b c, hσorth⟩, hσH⟩ : H) ∈ fixW hHW :=
    (fixW hHW).mul_mem (eichler_mem_fixW hHW hqa hac haU hcU hEac)
      (eichler_mem_fixW hHW hqb hbc hbU hcU hEbc)
  have hord : orderOf (⟨⟨⟨eichler q a c * eichler q b c, hσorth⟩, hσH⟩, hσX⟩ :
      fixW hHW) = 3 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eichler_mul_eichler_of_nonsingular hqa hqb hab hac hbc hqc
  rw [← hord]
  exact orderOf_dvd_natCard _

private lemma nine_dvd_card_fixW_of_eichler_hyperbolic {H : Subgroup (orthogonalGroup q)}
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    {a b c d : V} (hqa : q a = 0) (hqb : q b = 0) (hqc : q c = 0) (hqd : q d = 0)
    (hab : polar q a b = 1) (hcd : polar q c d = 1) (hac : polar q a c = 0)
    (had : polar q a d = 0) (hbc : polar q b c = 0) (hbd : polar q b d = 0)
    (haU : a ∈ orthW) (hbU : b ∈ orthW) (hcU : c ∈ orthW) (hdU : d ∈ orthW)
    (hEac : (⟨eichler q a c, eichler_mem_orthogonalGroup q a c⟩ : orthogonalGroup q) ∈ H)
    (hEbd : (⟨eichler q b d, eichler_mem_orthogonalGroup q b d⟩ : orthogonalGroup q) ∈ H)
    (hEad : (⟨eichler q a d, eichler_mem_orthogonalGroup q a d⟩ : orthogonalGroup q) ∈ H)
    (hEbc : (⟨eichler q b c, eichler_mem_orthogonalGroup q b c⟩ : orthogonalGroup q) ∈ H) :
    9 ∣ Nat.card (fixW hHW) := by
  classical
  haveI : Fintype V := Fintype.ofEquiv (Basis.ofVectorSpaceIndex (ZMod 2) V → ZMod 2)
    (Basis.ofVectorSpace (ZMod 2) V).equivFun.symm.toEquiv
  haveI : Fintype (V → V) := inferInstance
  haveI : Fintype (V ≃ₗ[ZMod 2] V) :=
    Fintype.ofInjective (fun e : V ≃ₗ[ZMod 2] V => (e : V → V))
      (fun e1 e2 h => LinearEquiv.ext (fun x => congrFun h x))
  haveI : Fintype (orthogonalGroup q) := Subtype.fintype _
  haveI : Fintype H := Subtype.fintype _
  haveI : Fintype (fixW hHW) := Subtype.fintype _
  have hτorth : eichler q a c * eichler q b d ∈ orthogonalGroup q :=
    mul_mem (eichler_mem_orthogonalGroup q a c) (eichler_mem_orthogonalGroup q b d)
  have hρorth : eichler q a d * eichler q b c ∈ orthogonalGroup q :=
    mul_mem (eichler_mem_orthogonalGroup q a d) (eichler_mem_orthogonalGroup q b c)
  have hτH : (⟨eichler q a c * eichler q b d, hτorth⟩ : orthogonalGroup q) ∈ H :=
    H.mul_mem hEac hEbd
  have hρH : (⟨eichler q a d * eichler q b c, hρorth⟩ : orthogonalGroup q) ∈ H :=
    H.mul_mem hEad hEbc
  have hτX : (⟨⟨eichler q a c * eichler q b d, hτorth⟩, hτH⟩ : H) ∈ fixW hHW :=
    (fixW hHW).mul_mem (eichler_mem_fixW hHW hqa hac haU hcU hEac)
      (eichler_mem_fixW hHW hqb hbd hbU hdU hEbd)
  have hρX : (⟨⟨eichler q a d * eichler q b c, hρorth⟩, hρH⟩ : H) ∈ fixW hHW :=
    (fixW hHW).mul_mem (eichler_mem_fixW hHW hqa had haU hdU hEad)
      (eichler_mem_fixW hHW hqb hbc hbU hcU hEbc)
  set τX : fixW hHW := ⟨⟨⟨eichler q a c * eichler q b d, hτorth⟩, hτH⟩, hτX⟩ with hτXdef
  set ρX : fixW hHW := ⟨⟨⟨eichler q a d * eichler q b c, hρorth⟩, hρH⟩, hρX⟩ with hρXdef
  have hτord : orderOf τX = 3 := by
    rw [hτXdef, Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eichler_mul_eichler_of_hyperbolic hqa hqb hqc hqd hab hcd hac had hbc hbd
  have hρord : orderOf ρX = 3 := by
    rw [hρXdef, Subgroup.orderOf_mk, Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact orderOf_eichler_mul_eichler_of_hyperbolic_swap hqa hqb hqc hqd hab hcd hac had hbc hbd
  have hcomm : Commute τX ρX := by
    have hlin : Commute (eichler q a c * eichler q b d) (eichler q a d * eichler q b c) :=
      commute_eichler_mul_eichler_of_hyperbolic hqa hqb hqc hqd hab hcd hac had hbc hbd
    show τX * ρX = ρX * τX
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact hlin.eq
  have hnot : ρX ∉ Subgroup.zpowers τX := by
    have hlin : eichler q a d * eichler q b c ∉
        Subgroup.zpowers (eichler q a c * eichler q b d) :=
      eichler_mul_eichler_not_mem_zpowers_of_hyperbolic hqa hqb hqc hqd hab hcd hac had hbc hbd
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hlin
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨k, ?_⟩
    have h2 : ((τX ^ k : fixW hHW) : V ≃ₗ[ZMod 2] V) = ((ρX : fixW hHW) : V ≃ₗ[ZMod 2] V) := by
      rw [hk]
    simpa using h2
  have h9 : 3 ^ 2 ∣ Nat.card (fixW hHW) :=
    CFSG.GroupTheory.sq_dvd_natCard_of_commute hτord hρord hcomm hnot
  simpa using h9

theorem false_of_anisotropicPlane (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 6) (hW2 : finrank (ZMod 2) W = 2)
    (hWq : ∀ w ∈ W, w ≠ 0 → q w = 1)
    (H : Subgroup (orthogonalGroup q))
    (hHW : ∀ h ∈ H, ∀ w ∈ W, (h : V ≃ₗ[ZMod 2] V) w ∈ W)
    (hO2 : ∀ N : Subgroup (orthogonalGroup q), N ≤ H →
      H ≤ Subgroup.normalizer (N : Set _) → IsPGroup 2 N → N = ⊥)
    (hfix : ∀ v : V, (∀ h ∈ H, (h : V ≃ₗ[ZMod 2] V) v = v) → v = 0)
    (D : Set V) (hD : D.Nonempty) (hDU : D ⊆ orthW)
    (hDq : ∀ a ∈ D, a ≠ 0 ∧ q a = 0)
    (hDH : ∀ h ∈ H, ∀ a ∈ D, (h : V ≃ₗ[ZMod 2] V) a ∈ D)
    (hE : ∀ a ∈ D, ∀ u ∈ orthW, polar q a u = 0 →
      (⟨eichler q a u, eichler_mem_orthogonalGroup q a u⟩ : orthogonalGroup q) ∈ H)
    (hY : ∀ h ∈ H, (∀ u ∈ orthW, (h : V ≃ₗ[ZMod 2] V) u = u) → h = 1) : False := by
  classical
  have hfix' : ∀ v : V, (∀ h : H, (h : V ≃ₗ[ZMod 2] V) v = v) → v = 0 :=
    fun v hv => hfix v (fun h hh => hv ⟨h, hh⟩)
  have hY' : ∀ h : H, (∀ u ∈ orthW, (h : V ≃ₗ[ZMod 2] V) u = u) → h = 1 := by
    intro h hu
    exact Subtype.ext (hY (h : orthogonalGroup q) h.2 hu)
  by_cases hN : ∃ a ∈ D, ∃ b ∈ D, polar q a b ≠ 0
  · obtain ⟨a, haD, b, hbD, habne⟩ := hN
    have hab : polar q a b = 1 := zmod2_eq_one_of_ne_zero habne
    obtain ⟨ha0, hqa⟩ := hDq a haD
    obtain ⟨hb0, hqb⟩ := hDq b hbD
    have haU : a ∈ orthW := hDU haD
    have hbU : b ∈ orthW := hDU hbD
    have hab_ne : a ≠ b := by
      intro h
      rw [h, polar_self_eq_zero] at habne
      exact habne rfl
    have hli : LinearIndependent (ZMod 2) ![a, b] :=
      linearIndependent_pair_iff.mpr ⟨ha0, hb0, hab_ne⟩
    have hV0fr : finrank (ZMod 2) (V0 q W a b) = 2 :=
      finrank_V0 hab hV hq hW2 hWq haU hbU hli
    by_cases hsing : ∃ c ∈ V0 q W a b, c ≠ 0 ∧ q c = 0
    ·
      obtain ⟨c, hcV0, hc0, hcq⟩ := hsing
      have hcU : c ∈ orthW := (mem_V0_iff.mp hcV0).1
      have hca : polar q a c = 0 := (mem_V0_iff.mp hcV0).2.1
      have hcb : polar q b c = 0 := (mem_V0_iff.mp hcV0).2.2
      have hex : ∃ d ∈ V0 q W a b, polar q c d ≠ 0 := by
        by_contra h
        have hzero : ∀ d ∈ V0 q W a b, polar q c d = 0 := by
          intro d hd
          by_contra hne
          exact h ⟨d, hd, hne⟩
        refine hc0 (hq.1 c ?_)
        intro y
        have hy : y ∈ W ⊔ orthW := by rw [sup_perpW_eq_top hq hV hW2 hWq]; trivial
        obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hy
        have h1 : polar q c w = 0 := by
          rw [polar_comm]
          exact LinearMap.BilinForm.mem_orthogonal_iff.mp hcU w hw
        have h2 : polar q c u = 0 := by
          have hdec := eq_smul_add_smul_add_decomp (q := q) (W := W) hab hu haU hbU
          rw [← hdec, polar_add_right, polar_add_right, polar_smul_right, polar_smul_right]
          have hca' : polar q c a = 0 := by rwa [polar_comm]
          have hcb' : polar q c b = 0 := by rwa [polar_comm]
          rw [hca', hcb', hzero _ (decomp_mem_V0 (q := q) (W := W) hab hu haU hbU)]
          simp
        rw [polarBilin_apply_apply, polar_add_right, h1, h2, add_zero]
      obtain ⟨d, hdV0, hcdne⟩ := hex
      have hcd1 : polar q c d = 1 := zmod2_eq_one_of_ne_zero hcdne
      have hd'V0 : (if q d = 0 then d else d + c) ∈ V0 q W a b := by
        by_cases hq0 : q d = 0
        · rw [if_pos hq0]; exact hdV0
        · rw [if_neg hq0]; exact Submodule.add_mem _ hdV0 hcV0
      have hd'q : q (if q d = 0 then d else d + c) = 0 := by
        by_cases hq0 : q d = 0
        · rw [if_pos hq0]; exact hq0
        · have hqd1 : q d = 1 := by
            rcases zmod2_eq_zero_or_eq_one (q d) with h | h
            · exact absurd h hq0
            · exact h
          rw [if_neg hq0, map_add_eq, hqd1, hcq, polar_comm q d c, hcd1]
          decide
      have hcd'1 : polar q c (if q d = 0 then d else d + c) = 1 := by
        by_cases hq0 : q d = 0
        · rw [if_pos hq0]; exact hcd1
        · rw [if_neg hq0, polar_add_right, hcd1, polar_self_eq_zero, add_zero]
      have hd'U : (if q d = 0 then d else d + c) ∈ orthW := (mem_V0_iff.mp hd'V0).1
      have hd'a : polar q a (if q d = 0 then d else d + c) = 0 := (mem_V0_iff.mp hd'V0).2.1
      have hd'b : polar q b (if q d = 0 then d else d + c) = 0 := (mem_V0_iff.mp hd'V0).2.2
      have hli' : LinearIndependent (ZMod 2) ![c, (if q d = 0 then d else d + c)] := by
        refine linearIndependent_pair_iff.mpr ⟨hc0, ?_, ?_⟩
        · intro h0
          rw [h0] at hcd'1
          simp at hcd'1
        · intro h0
          rw [← h0, polar_self_eq_zero] at hcd'1
          exact zero_ne_one hcd'1
      have hspan' : Submodule.span (ZMod 2) {c, (if q d = 0 then d else d + c)} = V0 q W a b := by
        refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
        · rw [Submodule.span_le]
          rintro x (rfl | rfl)
          · exact hcV0
          · exact hd'V0
        · rw [finrank_span_pair hli', hV0fr]
      have h720 : Nat.card H ∣ 720 := by
        have h := card_dvd_720_hyp (q := q) (W := W) (H := H) hHW hY'
          hqa hqb hcq hd'q hcd'1 hab hca hd'a hcb hd'b hspan' haU hbU
        rw [show Nat.factorial 6 = 720 from by norm_num] at h
        exact h
      have hX9 : 9 ∣ Nat.card (fixW hHW) :=
        nine_dvd_card_fixW_of_eichler_hyperbolic hHW hqa hqb hcq hd'q hab hcd'1 hca hd'a hcb hd'b
          haU hbU hcU hd'U (hE a haD c hcU hca) (hE b hbD (if q d = 0 then d else d + c) hd'U hd'b)
          (hE a haD (if q d = 0 then d else d + c) hd'U hd'a) (hE b hbD c hcU hcb)
      have h3X : 3 * Nat.card (fixW hHW) ∣ Nat.card H :=
        three_mul_card_fixW_dvd (q := q) (W := W) (H := H) hW2 hHW hfix'
      have h27H : 27 ∣ Nat.card H := by
        obtain ⟨k, hk⟩ := hX9
        rw [hk] at h3X
        exact dvd_trans ⟨k, by ring⟩ h3X
      exact absurd (dvd_trans h27H h720) (by norm_num)
    ·
      have haniso : ∀ v ∈ V0 q W a b, v ≠ 0 → q v = 1 := by
        intro v hv hv0
        rcases zmod2_eq_zero_or_eq_one (q v) with h | h
        · exact absurd ⟨v, hv, hv0, h⟩ hsing
        · exact h
      obtain ⟨c, d, hli, hspan⟩ := exists_pair_of_finrank_eq_two hV0fr
      have hcV0 : c ∈ V0 q W a b := by
        rw [← hspan]; exact Submodule.subset_span (by simp)
      have hdV0 : d ∈ V0 q W a b := by
        rw [← hspan]; exact Submodule.subset_span (by simp)
      have hcU : c ∈ orthW := (mem_V0_iff.mp hcV0).1
      have hdU : d ∈ orthW := (mem_V0_iff.mp hdV0).1
      have hac : polar q a c = 0 := (mem_V0_iff.mp hcV0).2.1
      have had : polar q a d = 0 := (mem_V0_iff.mp hdV0).2.1
      have hbc : polar q b c = 0 := (mem_V0_iff.mp hcV0).2.2
      have hbd : polar q b d = 0 := (mem_V0_iff.mp hdV0).2.2
      obtain ⟨hc0, hd0, hcdne⟩ := linearIndependent_pair_iff.mp hli
      have hqc : q c = 1 := haniso c hcV0 hc0
      have hqd : q d = 1 := haniso d hdV0 hd0
      have hqcd : q (c + d) = 1 := by
        refine haniso (c + d) (Submodule.add_mem _ hcV0 hdV0) ?_
        intro h0
        exact hcdne (by rwa [add_eq_zero_iff_eq_neg, vec_neg] at h0)
      have hcd : polar q c d = 1 := by
        have h := hqcd
        rw [map_add_eq, hqc, hqd] at h
        have h2 : (1 : ZMod 2) + 1 = 0 := by decide
        rw [h2, zero_add] at h
        exact h
      have h120 : Nat.card H ∣ 120 := by
        have h := card_dvd_120_aniso (q := q) (W := W) (H := H) hHW hY'
          hqa hqb hqc hqd hcd hab hac had hbc hbd hspan haU hbU
        rw [show Nat.factorial 5 = 120 from by norm_num] at h
        exact h
      have hX3 : 3 ∣ Nat.card (fixW hHW) :=
        three_dvd_card_fixW_of_eichler_nonsingular hHW hqa hqb hab hac hbc hqc haU hbU hcU
          (hE a haD c hcU hac) (hE b hbD c hcU hbc)
      have h3X : 3 * Nat.card (fixW hHW) ∣ Nat.card H :=
        three_mul_card_fixW_dvd (q := q) (W := W) (H := H) hW2 hHW hfix'
      have h9H : 9 ∣ Nat.card H := by
        obtain ⟨k, hk⟩ := hX3
        rw [hk] at h3X
        exact dvd_trans ⟨k, by ring⟩ h3X
      exact absurd (dvd_trans h9H h120) (by norm_num)
  · exact false_of_pairwise_orthogonal (q := q) (W := W) hq hV hW2 hWq hO2 hfix hD hDU hDq hDH
      hE (fun a ha b hb => by
        by_contra h
        exact hN ⟨a, ha, b, hb, h⟩)

end OrthoF2

end CFSG.LargeExtraspecial
