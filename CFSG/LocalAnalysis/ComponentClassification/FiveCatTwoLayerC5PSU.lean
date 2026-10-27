module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatTwoLayerC5Basic
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5PSU

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.TwoL5

open CFSG Subgroup Matrix CFSG.Open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.ComponentClassification.CatLeafProof.X10Lin
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm idForm_isSymm idForm_separatingLeft)

namespace PSU2

@[expose] def TwoLayerShape (n f : ℕ) (G : Type) [Group G] : Prop :=
  ∀ L₁ L₂ : Subgroup G, LitLayer L₁ → LitLayer L₂ → L₁ ≠ L₂ → n = 4 ∧ f = 1

theorem TwoLayerShape.of_mulEquiv {n f : ℕ} {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (h : TwoLayerShape n f H) : TwoLayerShape n f G := by
  intro L₁ L₂ h₁ h₂ hne
  refine h (L₁.map e.toMonoidHom) (L₂.map e.toMonoidHom) (h₁.map e) (h₂.map e) fun heq => hne ?_
  exact Subgroup.map_injective (f := e.toMonoidHom) e.injective heq

theorem commutingUnitary_components_eq_three {p f : ℕ} {E V : Type} [Field E] [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (h : UnitaryFieldData p f E) (hp2 : p ≠ 2)
    (hK3 : p ^ f ≠ 3) (hn : Module.finrank E V = 3) {B : V →ₛₗ[h.bar] V →ₗ[E] E}
    (hB : B.IsSymm) (hBl : B.SeparatingLeft) (τ₀ : V →ₛₗ[h.bar] V)
    (hτ₀ : Function.Bijective τ₀) (hτ₀B : ∀ v w, B (τ₀ v) (τ₀ w) = h.bar (B v w)) (μ : Eˣ)
    (hμ : ∀ v, τ₀ (τ₀ v) = (μ : E) • v) {L₁ L₂ : Subgroup (commutingUnitary B τ₀)}
    (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) : L₁ = L₂ := by
  have hodd : Odd p := h.prime.odd_of_ne_two hp2
  have : Finite E := h.finite
  obtain ⟨hμ1, ⟨b, hb⟩, ⟨t, ht⟩, hall⟩ := odd_unitary_conjugate_semilinear_involution_descent h
    hodd (by omega) hB hBl τ₀ hτ₀ hτ₀B μ hμ
  obtain ⟨-, hfinW, -, hB1, hB2⟩ := hall b t hb ht
  have : Module.Finite h.fixedField (conjFixed h ((b : E) • τ₀)) := finite_conjFixed
  have hkc : Nat.card h.fixedField = p ^ f := h.card_fixedField
  rcases hμ1 with hμ1 | hμ1
  · obtain ⟨B', -, hsym, hnd, Φ, -⟩ := hB1 hμ1
    have h2 : (2 : h.fixedField) ≠ 0 := fun h0 => by
      have h1 := congrArg h.fixedField.subtype h0
      rw [map_ofNat, map_zero] at h1
      exact UnitaryHigher.two_ne_zero_of_odd h hp2 h1
    have hQ : (CatalogueBOrthogonalDescent.originalQuadratic B').polarBilin.Nondegenerate := by
      rw [CatalogueBOrthogonalDescent.originalQuadratic_polarBilin B' hsym h2]
      exact hnd
    let Φ' := Φ.trans (MulEquiv.subgroupCongr
      (CatalogueBUnitaryB.isometryGroup_eq_orthogonalGroup B' hsym h2))
    have hdim : Module.finrank h.fixedField (conjFixed h ((b : E) • τ₀)) = 3 := hfinW.trans hn
    have hodd' : Odd (Nat.card h.fixedField) := by
      rw [hkc]
      exact hodd.pow
    have hK3' : Nat.card h.fixedField ≠ 3 := by
      rw [hkc]
      exact hK3
    obtain ⟨-, -, -, -, -, -, hq, -⟩ := orthogonal_three_derived hodd' hK3'
      (CatalogueBOrthogonalDescent.originalQuadratic B') hQ hdim
    have e₁ := CatLeafProof.eq_commutator_of_isComponent hq
      (LocalCores.isComponent_map_mulEquiv Φ' hL₁)
    have e₂ := CatLeafProof.eq_commutator_of_isComponent hq
      (LocalCores.isComponent_map_mulEquiv Φ' hL₂)
    exact Subgroup.map_injective (f := Φ'.toMonoidHom) Φ'.injective (e₁.trans e₂.symm)
  · obtain ⟨B', -, -, -, hev, -, -⟩ := hB2 hμ1
    rw [hn] at hev
    exact absurd hev (by decide)

theorem exists_component_preimage {P S : Type} [Group P] [Group S] [Finite P] {π : P →* S}
    (hπ : Function.Surjective π) (hK : π.ker ≤ center P) {a : MulAut P} {α : MulAut S}
    (ha : ∀ x, a (a x) = x) (hα : ∀ s, α (α s) = s) (hcomm : ∀ x, π (a x) = α (π x))
    {L : Subgroup (fixedSubgroup α)} (hL : IsComponent L) :
    ∃ Q : Subgroup P, Assembly.IsComponentOf Q (fixedSubgroup a) ∧
      Q.map π = L.map (fixedSubgroup α).subtype := by
  obtain ⟨-, -, hbij, -⟩ :=
    full_central_kernel_involution_fixed_component_correspondence hπ hK ha hα hcomm
  have hR : Assembly.IsComponentOf (L.map (fixedSubgroup α).subtype) (fixedSubgroup α) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : (L.map (fixedSubgroup α).subtype).subgroupOf (fixedSubgroup α) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨Q, hQ, hQR⟩ := hbij.surjOn hR
  exact ⟨Q, hQ, hQR⟩

theorem exists_psuGraph_lift {n : ℕ} {K : Type} [Field K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hn : 3 ≤ n) (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2)
    {L : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hL : IsComponent L) :
    ∃ Q : Subgroup (gramSU h (idGram K n)),
      Assembly.IsComponentOf Q (fixedSubgroup (C5PSU.psiLift h A φ)) ∧
      Q.map (QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n)) =
        L.map (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)).subtype := by
  have : Finite K := h.finite
  obtain ⟨c, hAA, -⟩ := C5PSU.psu_graph_scalar h hn A φ hφ hA
  have hZc : normOneScalars h (gramSU h (idGram K n)) n ≤ center (gramSU h (idGram K n)) := by
    rintro z ⟨c', -, -, hz⟩
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz]
    exact (commute_scalar c' _).eq
  refine exists_component_preimage
    (π := QuotientGroup.mk' (normOneScalars h (gramSU h (idGram K n)) n))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact hZc)
    (C5PSU.psiLift_involutive h A φ hφ hAA) (fun s => ?_) (fun x => ?_) hL
  · rw [← MulAut.mul_apply, ← pow_two, ← hA, pow_orderOf_eq_one, MulAut.one_apply]
  · rw [C5PSU.primeFormPsi_eq_onQuotient h A φ]
    exact CatalogueBFixedCentralQuotient.onQuotient_mk _ _ (C5PSU.psiLift_inv h A φ) _

theorem psuGraph_components_eq_three {K : Type} [Field K] {f : ℕ} (h : UnitaryFieldData 5 f K)
    (A : primeFormUnitary h (idGram K 3)) (φ : K ≃+* K) (hφ : ∀ x, φ x = h.bar x)
    (hA : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2)
    {L₁ L₂ : Subgroup (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩))}
    (hL₁ : IsComponent L₁) (hL₂ : IsComponent L₂) : L₁ = L₂ := by
  have : Finite K := h.finite
  have hf1 : 1 ≤ f := h.one_le
  obtain ⟨Q₁, hQ₁, hQR₁⟩ := exists_psuGraph_lift h (by norm_num) A φ hφ hA hL₁
  obtain ⟨Q₂, hQ₂, hQR₂⟩ := exists_psuGraph_lift h (by norm_num) A φ hφ hA hL₂
  obtain ⟨c, -, hAc⟩ := C5PSU.psu_graph_scalar h (by norm_num) A φ hφ hA
  have hτ₀ : Function.Bijective
      (semilinearMatrixMap h ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :=
    OddInner.semilinearMatrixMap_bijective_of h c.ne_zero hAc
  have hτ₀B := OddInner.idForm_semilinearMatrixMap h A.2
  have hμ := OddInner.semilinearMatrixMap_sq_of h hAc
  have h5 : 5 ≤ 5 ^ f := Nat.le_self_pow (by omega) 5
  have hG := commutingUnitary_components_eq_three h (by norm_num) (by omega)
    (Module.finrank_fin_fun K) (idForm_isSymm h 3) (idForm_separatingLeft h 3) _ hτ₀ hτ₀B c hμ
    (C5PSU.psu_graph_component_G h A φ hφ hQ₁) (C5PSU.psu_graph_component_G h A φ hφ hQ₂)
  have hle₁ := C5PSU.psu_graph_map_le h A φ hφ hQ₁
  have hle₂ := C5PSU.psu_graph_map_le h A φ hφ hQ₂
  have hQ : Q₁ = Q₂ := by
    have h1 := (Subgroup.subgroupOf_inj).1 hG
    rw [inf_eq_left.2 hle₁, inf_eq_left.2 hle₂] at h1
    exact Subgroup.map_injective (C5PSU.suToLin_injective h) h1
  have hRR : L₁.map (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)).subtype =
      L₂.map (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)).subtype := by
    rw [← hQR₁, ← hQR₂, hQ]
  exact Subgroup.map_injective (subtype_injective _) hRR

theorem noLitLayer_inner {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 5 f K)
    (hadm : StatedLieAdmissible .PSU n 5 f) (A : primeFormUnitary h (idGram K n))
    (hord : orderOf (primeFormConjHom h (idGram K n) A) = 2) :
    NoLitLayer (fixedSubgroup (primeFormConjHom h (idGram K n) A)) := by
  rintro L ⟨hL, hA5, hz⟩
  rcases inner_psu_component_cases h (by norm_num) hadm A hord hL with
    ⟨z, hzL, hzc, hzz, hz1⟩ | ⟨t, m, e, hT, hadm', hm'⟩
  · exact hz1 (hz z hzL hzc hzz)
  · obtain ⟨rfl, rfl, rfl⟩ := C5PSL.eq_psl_two_one_of_a5
      (C5PSU.isClassicalTag_of_mem_linUInnerTuples hT) hadm' hm' hA5
    exact C5PSU.not_mem_linUInnerTuples hT

theorem twoLayerShape_graph {n f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 5 f K)
    (hadm : StatedLieAdmissible .PSU n 5 f) (A : primeFormUnitary h (idGram K n)) (φ : K ≃+* K)
    (hφ : ∀ x, φ x = h.bar x)
    (hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2) :
    TwoLayerShape n f (fixedSubgroup (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩)) := by
  rintro L₁ L₂ ⟨hL₁, hA5, -⟩ ⟨hL₂, -, -⟩ hne
  obtain ⟨t, m, e, hT, hadm', hm'⟩ := graph_psu_component_models h (by norm_num : (5 : ℕ) ≠ 2)
    hadm A φ hφ hord hL₁
  obtain ⟨rfl, rfl, rfl⟩ := C5PSL.eq_psl_two_one_of_a5 (isClassicalTag_of_mem_graphTuples hT)
    hadm' hm' hA5
  rcases C5PSL.mem_graphTuples_psl_two_one hT with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (hne (psuGraph_components_eq_three h A φ hφ hord hL₁ hL₂)).elim
  · exact ⟨rfl, rfl⟩

theorem twoLayerShape_psu {J : Type} [Group J] {n f : ℕ} (hadm : StatedLieAdmissible .PSU n 5 f)
    (hm : Blueprint.LieModel J .PSU n 5 f) {α : MulAut J} (hα : orderOf α = 2) :
    TwoLayerShape n f (fixedSubgroup α) := by
  obtain ⟨K, _, h, ⟨ψ⟩⟩ := nonempty_mulEquiv_primeFormP_of_lieModel' hadm hm
  have hn : 3 ≤ n := hadm.2.2.1
  have hq : ¬(n = 3 ∧ 5 ^ f = 2) := fun h3 => hadm.2.2.2 (by rw [h3.1, h3.2])
  have hC : IsPrimeFormGram (1 : GL (Fin n) K) := isPrimeFormGram_one
  have hβ : orderOf (MulAut.congr ψ α) = 2 :=
    (orderOf_injective (MulAut.congr ψ).toMonoidHom (MulAut.congr ψ).injective α).trans hα
  obtain ⟨⟨A, φ⟩, hAφ⟩ := primeFormPsi_surjective h hC hn hq (MulAut.congr ψ α)
  have hff : primeFormFieldFactor h hC hn hq (MulAut.congr ψ α) = φ := by
    rw [← hAφ, primeFormFieldFactor_psi]
  have hφ2 : φ * φ = 1 := by
    rw [← hff, ← map_mul, ← pow_two]
    have h1 := pow_orderOf_eq_one (MulAut.congr ψ α)
    rw [hβ] at h1
    rw [h1, map_one]
  refine TwoLayerShape.of_mulEquiv (fixedSubgroupCongrEquiv ψ α) ?_
  rcases ringEquiv_eq_refl_or_bar h hφ2 with hφ | hφ
  · have hAα : MulAut.congr ψ α = primeFormConjHom h _ A := by
      rw [← hAφ, primeFormPsi_apply, hφ]
      rw [show RingEquiv.refl K = 1 from rfl, map_one, mul_one]
    have hord : orderOf (primeFormConjHom h _ A) = 2 := hAα ▸ hβ
    exact TwoLayerShape.of_mulEquiv (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAα))
      fun L₁ _ h₁ _ _ => (noLitLayer_inner h hadm A hord L₁ h₁).elim
  · have hord : orderOf (primeFormPsi h isPrimeFormGram_one ⟨A, φ⟩) = 2 := hAφ ▸ hβ
    exact TwoLayerShape.of_mulEquiv
      (MulEquiv.subgroupCongr (congrArg fixedSubgroup hAφ.symm))
      (twoLayerShape_graph h hadm A φ hφ hord)

end PSU2

theorem fiveTwoLayer_char5_PSU : FiveTwoLayerCharFiveClause .PSU := by
  intro S _ _ hs hna ⟨n, f, hm⟩ σ P₁ P₂ h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  haveI := hs
  have hadm : StatedLieAdmissible .PSU n 5 f := hm.admissible
  have hσ1 : σ ≠ 1 := h₁.ne_one
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h₁.1 y
  have hσ2 : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσσ) hσ1
  have hq : ∀ α : MulAut S, α * α = 1 → α ≠ 1 →
      ∀ L : Subgroup (fixedSubgroup α), IsPComponent 2 L → IsQuasisimple L :=
    fixedTwoComponentsQuasisimple_lin (by norm_num : (5 : ℕ) ≠ 2) (Or.inr rfl) hadm hm
  obtain ⟨L₁, L₂, hl₁, hl₂, hne', -⟩ :=
    twoLayers_of_clause hq h₁ h₂ hne hZ₁ hZ₂ e₁ e₂ huniq
  obtain ⟨rfl, rfl⟩ := PSU2.twoLayerShape_psu hadm hm hσ2 L₁ L₂ hl₁ hl₂ hne'
  exact Or.inr hm

end CFSG.ComponentClassification.SolMax.FiveCat.TwoL5
