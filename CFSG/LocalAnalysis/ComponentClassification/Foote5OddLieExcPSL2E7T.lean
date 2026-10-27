module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieExcPSL2E6All
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneX10TwMain

public noncomputable section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatLeaf
  CFSG.ComponentClassification.CatLeafProof
open CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open scoped MatrixGroups
open CFSG Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.Burgoyne.X10

theorem noPSL2Odd_family_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ α : MulAut B, orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L)
    (α : MulAut A) (hα : orderOf α = 2) (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) :
    NoPSL2Odd L := by
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact noPSL2Odd_of_component_equiv (fixedSubgroupCongrEquiv e α) (h _ hβ) hL

theorem noPSL2Odd_psl_field (hO : LieOrderFormulasInput) {n : ℕ} (hn68 : n = 6 ∨ n = 8)
    {K : Type} [Field K] [Finite K]
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hsq : CatalogueBLinearSemilinear.semilinearAction n K A σ ^ 2 = 1) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBLinearSemilinear.semilinearAction n K A σ))
    {L : Subgroup X} (hL : IsComponent L) : NoPSL2Odd L := by
  have hn : 2 ≤ n := by omega
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hf2 := two_le_of_ringEquiv_ne_one hp hf hK hσ
  have hpar : 3 ≤ n ∨ 5 ≤ Nat.card K := by
    right
    rw [hK]
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left (by have := hp.two_le; omega) 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  obtain ⟨heven, hσc, H, hα⟩ := CatalogueBLinearSemilinear.odd_linear_field_involution_conjugacy
    n K p f hp hpodd hf hK hn hpar A σ hσ hsq
  have hσ2 : σ ^ 2 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    refine RingEquiv.ext fun x => ?_
    rw [sq, RingAut.mul_apply, hσc, hσc, ← pow_mul, ← sq, ← pow_mul,
      Nat.div_mul_cancel (even_iff_two_dvd.1 heven), ← hK, Nat.card_eq_fintype_card,
      FiniteField.pow_card]
    rfl
  have hc : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction n K H)
      (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) =
      CatalogueBLinearSemilinear.semilinearAction n K A σ :=
    (MulEquiv.ext fun _ => rfl : MulAut.congr (CatalogueBHigherLinearAction.innerDiagonalAction
      n K H) (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) = _).trans hα.symm
  let Ψ' : X ≃* fixedSubgroup (CatalogueBHigherLinearField.pslFieldAut (Fin n) K σ) :=
    Ψ.trans ((MulEquiv.subgroupCongr (congrArg fixedSubgroup hc)).symm.trans
      (fixedSubgroupCongrEquiv _ _).symm)
  have hL' : IsComponent (L.map Ψ'.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψ' hL
  have hL2 := isPComponent_two_of_isComponent hL'
  obtain ⟨hcard, -, hsmall, hiso⟩ :=
    CatalogueBHigherLinearField.linear_field_involution_fixed_p_components n hn K σ hσ2 hσ
  have hcardk : Nat.card (CatalogueBHigherLinearField.fixedField K σ) = p ^ (f / 2) := by
    have h2 : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 heven), hK]
    rw [hcard] at h2
    exact Nat.pow_left_injective two_ne_zero h2
  by_cases hex : n = 2 ∧ (Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 2 ∨
      Nat.card (CatalogueBHigherLinearField.fixedField K σ) = 3)
  · exact absurd hL2 (hsmall hex 2 Nat.prime_two _)
  obtain ⟨E⟩ := hiso hex 2 Nat.prime_two _ hL2
  have he : 1 ≤ f / 2 := by omega
  have hadm : StatedLieAdmissible .PSL n p (f / 2) := by
    refine ⟨hp, he, hn, fun h => ?_, fun h => ?_⟩
    · have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
      have hodd : Odd (p ^ (f / 2)) := hpodd.pow
      rw [h1] at hodd
      exact absurd hodd (by decide)
    · exact hex ⟨(Prod.mk.inj h).1, Or.inr (hcardk.trans (Prod.mk.inj h).2)⟩
  have hstated : StatedClassicalModel (ProjectiveSpecialLinearGroup (Fin n)
      (CatalogueBHigherLinearField.fixedField K σ)) .PSL n p (f / 2) :=
    ⟨hadm, CatalogueBHigherLinearField.fixedField K σ, inferInstance, inferInstance, hcardk,
      ⟨projectiveSpecialLinearGroupEquivStatedProj n _⟩⟩
  have := (LieType.Simplicity.fam_PSL_simplicity _ n p (f / 2) hstated).2
  exact noPSL2Odd_of_simple_model hO (exists_mul_ne_of_isQuasisimple hL'.1 E)
    ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans E) hp2
    (Or.inl ⟨rfl, Or.inr hn68⟩)
    (fun h => by rcases hn68 with rfl | rfl <;> exact absurd h.2 (by norm_num))
    hadm (Or.inl ⟨by decide, hstated⟩)

theorem noPSL2Odd_psl_graphField (hO : LieOrderFormulasInput) {n : ℕ} (hn68 : n = 6 ∨ n = 8)
    {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1)
    (hord : orderOf (CatalogueBGraphField.graphFieldAction n K A σ) = 2) {X : Type} [Group X]
    (Ψ : X ≃* fixedSubgroup (CatalogueBGraphField.graphFieldAction n K A σ)) {L : Subgroup X}
    (hL : IsComponent L) : NoPSL2Odd L := by
  have hn : 3 ≤ n := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.eq_two_or_odd'.resolve_left hp2
  have hsq : CatalogueBGraphField.graphFieldAction n K A σ ^ 2 = 1 :=
    hord ▸ pow_orderOf_eq_one _
  have hne1 : CatalogueBGraphField.graphFieldAction n K A σ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hord
    exact absurd hord (by decide)
  obtain ⟨-, hhalf, hunitary, -, -, -, hcomp⟩ :=
    CatalogueBGraphField.odd_linear_graph_field_involution_fixed_p_components_native n K p f
      hpodd hf hK hn A σ hσ hne1 hsq
  let Ψt : X ≃* CatalogueBGraphField.twistedFixedPSL n K A σ := Ψ
  have hL' : IsComponent (L.map Ψt.toMonoidHom) := LocalCores.isComponent_map_mulEquiv Ψt hL
  obtain ⟨-, ⟨E⟩⟩ := hcomp 2 Nat.prime_two _ (isPComponent_two_of_isComponent hL')
  obtain ⟨eQ⟩ := nonempty_projectiveSpecialUnitary_equiv_statedProj (n := n) hunitary
  have hadm : StatedLieAdmissible .PSU n p (f / 2) := by
    refine ⟨hp, hhalf, hn, fun h => ?_⟩
    have h1 : p ^ (f / 2) = 2 := (Prod.mk.inj h).2
    have hodd : Odd (p ^ (f / 2)) := hpodd.pow
    rw [h1] at hodd
    exact absurd hodd (by decide)
  have hstated : StatedClassicalModel (StatedProj (StatedSU n (p ^ (f / 2)) K)) .PSU n p (f / 2) :=
    ⟨hadm, K, inferInstance, inferInstance, hunitary, ⟨MulEquiv.refl _⟩⟩
  have := (ClassicalGroups.Unitary.fam_PSU_simplicity _ n p (f / 2) hstated).2
  exact noPSL2Odd_of_simple_model hO (exists_mul_ne_of_isQuasisimple hL'.1 (E.trans eQ))
    (((L.equivMapOfInjective Ψt.toMonoidHom Ψt.injective).trans E).trans eQ) hp2
    (Or.inr (Or.inl ⟨rfl, hn68⟩)) (fun h => absurd h.1 (by decide)) hadm
    (Or.inl ⟨by decide, hstated⟩)

theorem noPSL2Odd_of_projectiveSL_involution (hO : LieOrderFormulasInput) {n : ℕ}
    (hn68 : n = 6 ∨ n = 8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {α : MulAut (LinearFlag.projectiveSL n K)} (hα2 : α ^ 2 = 1)
    (hα1 : α ≠ 1) (A : GL (Fin n) K) (σ : K ≃+* K) (hσ : σ ≠ 1) (ε : ℕ) (hε : ε ≤ 1)
    (hαe : α = LinearFlag.conjAut n K A * LinearFlag.fieldAut n K σ * LinearFlag.dualAut n K ^ ε)
    (L : Subgroup (fixedSubgroup α)) (hL : IsComponent L) : NoPSL2Odd L := by
  set e := CatalogueBLinearHigherB.nativeEquiv n K with he
  have hord : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans
      (orderOf_eq_prime hα2 hα1)
  have hsq : MulAut.congr e α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
  interval_cases ε
  · rw [pow_zero, mul_one] at hαe
    have hβ : MulAut.congr e α = CatalogueBLinearSemilinear.semilinearAction n K A σ := by
      rw [hαe, he, CatalogueBLinearHigherB.congr_semilinear]
    exact noPSL2Odd_psl_field hO hn68 hp hp2 hf hK A σ hσ (hβ ▸ hsq)
      ((fixedSubgroupCongrEquiv e α).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ)))
      hL
  · rw [pow_one] at hαe
    have hβ : MulAut.congr e α = CatalogueBGraphField.graphFieldAction n K A σ := by
      rw [hαe, he, CatalogueBLinearHigherB.congr_graphField]
    exact noPSL2Odd_psl_graphField hO hn68 hp hp2 hf hK A σ hσ (hβ ▸ hord)
      ((fixedSubgroupCongrEquiv e α).trans (MulEquiv.subgroupCongr (congrArg fixedSubgroup hβ)))
      hL

section Descent

variable {τ : Tag} {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem noPSL2Odd_orbitGroup_of_quadGroup
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2)
    (hnc : ∃ y ∈ quadGens D, ∃ x ∈ quadGens D, ¬ Commute (D.F y * y⁻¹) x)
    (hq : IsQuasisimple D.orbitGroup)
    (hfam : ∀ α : MulAut (↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)), orderOf α = 2 →
      ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L) :
    NoPSL2Odd D.orbitGroup := by
  have := finite_quadGroup D
  let Y := quadGroup D
  let σ := quadAut D hθ2
  have hσσ : ∀ y, σ (σ y) = y := fun y => Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  let π := QuotientGroup.mk' (Subgroup.center Y)
  let σ' : MulAut (Y ⧸ Subgroup.center Y) :=
    QuotientGroup.congr (Subgroup.center Y) (Subgroup.center Y) σ (Subgroup.map_center_eq σ)
  have hcomm : ∀ y, π (σ y) = σ' (π y) := fun y => rfl
  have hσ'2 : σ' ^ 2 = 1 := by
    ext z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center Y) z
    rw [sq, MulAut.mul_apply, ← hcomm, ← hcomm, hσσ]
    rfl
  have hσ'1 : σ' ≠ 1 := by
    obtain ⟨y, hy, x, hx, hyx⟩ := hnc
    intro h
    have hyY : y ∈ Y := Subgroup.subset_closure hy
    have hxY : x ∈ Y := Subgroup.subset_closure hx
    have h1 : π (σ ⟨y, hyY⟩) = π ⟨y, hyY⟩ := by rw [hcomm, h]; rfl
    have hz : (σ ⟨y, hyY⟩)⁻¹ * ⟨y, hyY⟩ ∈ Subgroup.center Y := QuotientGroup.eq.1 h1
    have hzc := Subgroup.mem_center_iff.1 (inv_mem hz)
    have he : σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹ = ((σ ⟨y, hyY⟩)⁻¹ * ⟨y, hyY⟩)⁻¹ := by
      have h2 := hzc (σ ⟨y, hyY⟩)
      rw [_root_.mul_inv_rev, inv_inv] at h2 ⊢
      calc σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹ =
          σ ⟨y, hyY⟩ * ((⟨y, hyY⟩ : Y)⁻¹ * σ ⟨y, hyY⟩) * (σ ⟨y, hyY⟩)⁻¹ := by group
        _ = (⟨y, hyY⟩ : Y)⁻¹ * σ ⟨y, hyY⟩ := by rw [h2]; group
    apply hyx
    have hc : Commute (σ ⟨y, hyY⟩ * (⟨y, hyY⟩ : Y)⁻¹) ⟨x, hxY⟩ := by
      rw [he]
      exact (hzc ⟨x, hxY⟩).symm
    exact hc.map Y.subtype
  have hord : orderOf σ' = 2 := orderOf_eq_prime hσ'2 hσ'1
  have hCY : D.orbitGroupC ≤ Y := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := orbitGroup_le_map_quadGroup D hcard (Subgroup.mem_subgroupOf.1 hx)
    rwa [← Subtype.ext hyx]
  let C₁ : Subgroup Y := D.orbitGroupC.subgroupOf Y
  let eC : C₁ ≃* D.orbitGroup := (Subgroup.subgroupOfEquivOfLe hCY).trans
    (Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup)
  have hq₁ : IsQuasisimple C₁ := LocalCores.isQuasisimple_of_mulEquiv eC.symm hq
  have hC₁fix : C₁ ≤ fixedSubgroup σ := fun c hc =>
    Subtype.ext (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup hc)).2
  have hYfix : ∀ g : Y, σ g = g → (g : adjointGroup τ k) ∈ D.fixedGroup := fun g hg =>
    D.mem_fixedGroup.2 ⟨Subgroup.mem_subgroupOf.1 (quadGroup_le_rootSpanJ D g.2),
      congrArg Subtype.val hg⟩
  have hN : (C₁.subgroupOf (fixedSubgroup σ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnor := D.orbitGroupC_normal
    have hn' : (⟨(n : Y), hYfix _ n.2⟩ : D.fixedGroup) ∈ D.orbitGroupC.subgroupOf D.fixedGroup :=
      Subgroup.mem_subgroupOf.2 hn
    have := hnor.conj_mem _ hn' ⟨((g : Y) : adjointGroup τ k), hYfix _ g.2⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hC₁comp : Assembly.IsComponentOf C₁ (fixedSubgroup σ) :=
    ⟨hC₁fix, Assembly.IsSubnormal.step hC₁fix hN (Assembly.IsSubnormal.refl _),
      (AssemblyBPredicates.isQuasisimple_iff_native C₁).2 hq₁⟩
  have hmap := LocalAnalysis.ComponentInitial.isComponentOf_map_fixed (π := π)
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hσσ hcomm hC₁comp
  have hK := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hmap.1).1 hmap
  have hPK : NoPSL2Odd ↥(C₁.map π) :=
    NoPSL2Odd.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hmap.1).symm (hfam σ' hord _ hK)
  have hker : (π.subgroupMap C₁).ker ≤ Subgroup.center C₁ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_center_iff.2 fun w =>
      Subtype.ext (Subgroup.mem_center_iff.1 hx1 (w : Y))
  exact NoPSL2Odd.of_mulEquiv eC.symm (NoPSL2Odd.of_central hq₁ (π.subgroupMap C₁)
    (π.subgroupMap_surjective C₁)
    hker hPK)

theorem noPSL2Odd_orbitGroup_of_quadGroup_at
    (D : OrthogonalSemilinearFixedRootDatum τ p k)
    (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2)
    (hq : IsQuasisimple D.orbitGroup)
    (hfam : ∀ L : Subgroup (fixedSubgroup (quadAutBar D hθ2)), IsComponent L → NoPSL2Odd L) :
    NoPSL2Odd D.orbitGroup := by
  have := finite_quadGroup D
  let Y := quadGroup D
  let σ := quadAut D hθ2
  have hσσ : ∀ y, σ (σ y) = y := fun y => Subtype.ext (F_mem_quadGroup D hθ2 y.2).2
  let π := QuotientGroup.mk' (Subgroup.center Y)
  let σ' : MulAut (Y ⧸ Subgroup.center Y) := quadAutBar D hθ2
  have hcomm : ∀ y, π (σ y) = σ' (π y) := fun y => rfl
  have hCY : D.orbitGroupC ≤ Y := fun x hx => by
    obtain ⟨y, hy, hyx⟩ := orbitGroup_le_map_quadGroup D hcard (Subgroup.mem_subgroupOf.1 hx)
    rwa [← Subtype.ext hyx]
  let C₁ : Subgroup Y := D.orbitGroupC.subgroupOf Y
  let eC : C₁ ≃* D.orbitGroup := (Subgroup.subgroupOfEquivOfLe hCY).trans
    (Subgroup.subgroupOfEquivOfLe D.orbitGroup_le_adjointGroup)
  have hq₁ : IsQuasisimple C₁ := LocalCores.isQuasisimple_of_mulEquiv eC.symm hq
  have hC₁fix : C₁ ≤ fixedSubgroup σ := fun c hc =>
    Subtype.ext (D.mem_fixedGroup.1 (D.orbitGroupC_le_fixedGroup hc)).2
  have hYfix : ∀ g : Y, σ g = g → (g : adjointGroup τ k) ∈ D.fixedGroup := fun g hg =>
    D.mem_fixedGroup.2 ⟨Subgroup.mem_subgroupOf.1 (quadGroup_le_rootSpanJ D g.2),
      congrArg Subtype.val hg⟩
  have hN : (C₁.subgroupOf (fixedSubgroup σ)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hnor := D.orbitGroupC_normal
    have hn' : (⟨(n : Y), hYfix _ n.2⟩ : D.fixedGroup) ∈ D.orbitGroupC.subgroupOf D.fixedGroup :=
      Subgroup.mem_subgroupOf.2 hn
    have := hnor.conj_mem _ hn' ⟨((g : Y) : adjointGroup τ k), hYfix _ g.2⟩
    exact Subgroup.mem_subgroupOf.1 this
  have hC₁comp : Assembly.IsComponentOf C₁ (fixedSubgroup σ) :=
    ⟨hC₁fix, Assembly.IsSubnormal.step hC₁fix hN (Assembly.IsSubnormal.refl _),
      (AssemblyBPredicates.isQuasisimple_iff_native C₁).2 hq₁⟩
  have hmap := LocalAnalysis.ComponentInitial.isComponentOf_map_fixed (π := π)
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) hσσ hcomm hC₁comp
  have hK := (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hmap.1).1 hmap
  have hPK : NoPSL2Odd ↥(C₁.map π) :=
    NoPSL2Odd.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hmap.1).symm (hfam _ hK)
  have hker : (π.subgroupMap C₁).ker ≤ Subgroup.center C₁ := by
    intro x hx
    have hx1 : π (x : Y) = 1 := congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
    exact Subgroup.mem_center_iff.2 fun w =>
      Subtype.ext (Subgroup.mem_center_iff.1 hx1 (w : Y))
  exact NoPSL2Odd.of_mulEquiv eC.symm (NoPSL2Odd.of_central hq₁ (π.subgroupMap C₁)
    (π.subgroupMap_surjective C₁)
    hker hPK)

theorem noPSL2Odd_of_projectiveSL_root_fixed (hO : LieOrderFormulasInput) {m : ℕ}
    (hm68 : m + 1 = 6 ∨ m + 1 = 8) {K : Type}
    [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (α : MulAut (LinearFlag.projectiveSL (m + 1) K)) (hα2 : α ^ 2 = 1)
    {N : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hN2 : N * N = 0) (hN : N ≠ 0)
    (r : K → SL(m + 1, K))
    (hr : ∀ c, ((r c : SL(m + 1, K)) : Matrix (Fin (m + 1)) (Fin (m + 1)) K) = 1 + c • N)
    (w : K → LinearFlag.projectiveSL (m + 1) K) (φ₀ : K → K)
    (hinto : ∀ c, ∃ c', w c = LinearFlag.proj (m + 1) K (r c'))
    (honto : ∀ c', ∃ c, w c = LinearFlag.proj (m + 1) K (r c'))
    (hact : ∀ c, α (w c) = w (φ₀ c)) (h1 : Nat.card {c : K // φ₀ c = c} ≠ 1)
    (hKc : Nat.card {c : K // φ₀ c = c} ≠ Nat.card K) (L : Subgroup (fixedSubgroup α))
    (hL : IsComponent L) : NoPSL2Odd L := by
  have hα1 : α ≠ 1 := by
    intro h1'
    have hdec : α = LinearFlag.conjAut (m + 1) K 1 * LinearFlag.fieldAut (m + 1) K 1 *
        LinearFlag.dualAut (m + 1) K ^ 0 := by
      rw [h1', map_one, map_one, pow_zero, mul_one, mul_one]
    exact ringEquiv_ne_one_of_root_action (by omega) hN2 hN r hr 1 1 0 (by omega) w φ₀ hinto
      honto (fun c => by rw [← hdec]; exact hact c) h1 hKc rfl
  have h3 : 3 ≤ m + 1 := by omega
  obtain ⟨A, σ, ε, hε, hαe⟩ := (LinearFlag.automorphism_generation (K := K) h3).2 α
  have hσ : σ ≠ 1 := ringEquiv_ne_one_of_root_action (by omega) hN2 hN r hr A σ ε hε w φ₀ hinto
    honto (fun c => by rw [← hαe]; exact hact c) h1 hKc
  exact noPSL2Odd_of_projectiveSL_involution hO hm68 hp hp2 hf hK hα2 hα1 A σ hσ ε hε hαe L hL

theorem noPSL2Odd_orbitGroup_of_slFrame
    (hO : LieOrderFormulasInput) (D : OrthogonalSemilinearFixedRootDatum τ p k)
    {S : Set (Fin τ.rank → ℤ)}
    (hJS : D.simpleRootsJ = S) (hθ2 : ∀ β ∈ D.simpleRootsJ, D.θ (D.θ (toReal β)) = toReal β)
    (hcard : ∀ O ∈ D.orbits, orbitCard O = 1 ∨ orbitCard O = 2) (hq : IsQuasisimple D.orbitGroup)
    {m : ℕ} (hm68 : m + 1 = 6 ∨ m + 1 = 8) {β₀ : Fin τ.rank → ℤ} (hβ₀ : IsRoot τ β₀)
    (hβS : β₀ ∈ S) (hθβ₀ : D.θ (toReal β₀) = toReal β₀) (k₀ : Fin m)
    (hframe : ∃ Ψ : SL(m + 1, frobeniusFixedField k p (D.e * 2)) →*
        adjointGroup τ (frobeniusFixedField k p (D.e * 2)),
      Ψ.ker ≤ Subgroup.center _ ∧
      Ψ.range.map (adjointGroup τ _).subtype = pairSpan τ (frobeniusFixedField k p (D.e * 2)) S ∧
      (CurtisTits.rankOne (SpecialLinear.rootDatum m (frobeniusFixedField k p (D.e * 2))).rootGroup
        k₀).map Ψ =
        (adjDatum (rootOperatorFamily τ) (frobeniusFixedField k p (D.e * 2))).rootGroup β₀ ⊔
          (adjDatum (rootOperatorFamily τ) (frobeniusFixedField k p (D.e * 2))).rootGroup
            (-β₀)) :
    NoPSL2Odd D.orbitGroup := by
  have hp : p.Prime := Fact.out
  have he : 1 ≤ D.e := D.one_le_e
  refine noPSL2Odd_orbitGroup_of_quadGroup_at D hθ2 hcard hq fun L hL => ?_
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨eY, heY⟩ := exists_quadGroup_equiv_pairSpan D hJS
  obtain ⟨Ψ, hker, hrange, hrk⟩ := hframe
  obtain ⟨θ, hθs, hθk, N, r, hN2, hN0, hr, hR1, hR2⟩ :=
    exists_pairSpan_projectiveSL_of_frame hp D.odd hK₂ (by omega) hβ₀ hβS k₀ Ψ hker hrange hrk
  let Φ : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D) ≃*
      LinearFlag.projectiveSL (m + 1) (frobeniusFixedField k p (D.e * 2)) :=
    (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY)).trans
      ((QuotientGroup.quotientMulEquivOfEq hθk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθs))
  have hΦ : ∀ y : quadGroup D,
      Φ (y : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) = θ (eY y) := fun y => rfl
  have hβJ : β₀ ∈ D.simpleRootsJ := hJS ▸ hβS
  let y : frobeniusFixedField k p (D.e * 2) → quadGroup D := fun c =>
    ⟨⟨rootSL2 τ k β₀ (uSL (c : k)), rootSL2_mem_adjointGroup hβ₀ _⟩,
      Subgroup.subset_closure ⟨_, hβJ, (c : k), c.2, Or.inl rfl⟩⟩
  have heYy : ∀ c, eY (y c) = ⟨rootSL2 τ _ β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ := by
    intro c
    apply Subtype.ext
    apply baseChangeGL_injective (frobeniusFixedField k p (D.e * 2)).subtype
    rw [heY, baseChangeGL_rootSL2_of_field, CFSG.LieType.Chevalley.map_uSL]
    rfl
  have hσy : ∀ c, quadAut D hθ2 (y c) = y (c ^ p ^ D.e) := by
    intro c
    apply Subtype.ext
    apply Subtype.ext
    have h := D.map_rootSL2 _ hβJ.1 _ hθβ₀ (uSL (c : k)) (y c).1 rfl
    change (D.F (y c).1 : ModGL τ k) = _
    rw [h, CFSG.LieType.Chevalley.map_uSL]
    change rootSL2 τ k _ (uSL (iterateFrobenius k p D.e (c : k))) =
      rootSL2 τ k _ (uSL ((c ^ p ^ D.e : frobeniusFixedField k p (D.e * 2)) : k))
    rw [iterateFrobenius_def, SubmonoidClass.coe_pow]
  set α := MulAut.congr Φ (quadAutBar D hθ2) with hα
  set w : frobeniusFixedField k p (D.e * 2) →
      LinearFlag.projectiveSL (m + 1) (frobeniusFixedField k p (D.e * 2)) :=
    fun c => θ ⟨rootSL2 τ _ β₀ (uSL c), rootSL2_uSL_mem_pairSpan hβS c⟩ with hw
  have hwy : ∀ c, w c = Φ (y c : ↥(quadGroup D) ⧸ Subgroup.center ↥(quadGroup D)) := fun c => by
    rw [hΦ, heYy]
  have hact : ∀ c, α (w c) = w (c ^ p ^ D.e) := by
    intro c
    rw [hwy, hwy, hα, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, quadAutBar_mk, hσy]
  have hα2 : α ^ 2 = 1 := by
    rw [hα, ← map_pow, quadAutBar_sq, map_one]
  have hfix := card_pow_fixed_frobeniusFixedField (k := k) (p := p) he
  have h1 : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠ 1 := by
    rw [hfix]
    exact (Nat.one_lt_pow (by omega) hp.one_lt).ne'
  have hKc : Nat.card {c : frobeniusFixedField k p (D.e * 2) // c ^ p ^ D.e = c} ≠
      Nat.card (frobeniusFixedField k p (D.e * 2)) := by
    rw [hfix, hK₂]
    intro h
    have := Nat.pow_right_injective hp.two_le h
    omega
  refine noPSL2Odd_of_component_equiv (fixedSubgroupCongrEquiv Φ _) (fun M hM => ?_) hL
  exact noPSL2Odd_of_projectiveSL_root_fixed hO hm68 hp D.odd (by omega) hK₂ α hα2 hN2 hN0 r hr w
    (fun c => c ^ p ^ D.e) hR1 hR2 hact h1 hKc M hM

end Descent

section Datum

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [IsAlgClosed k]

theorem noPSL2Odd_e7_twisted_orbitGroup
    (D : OrthogonalSemilinearFixedRootDatum .E7 p k) {m : ℕ} (hm : m = 2 ∨ m = 3)
    (hχ : D.χ = signMaskChar .E7 m)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup)
    {S : Set (Fin (Tag.rank .E7) → ℤ)} (hS : simpleUnion (signMaskChar .E7 m) = S)
    (hcls : ∀ {χ : Multiplicative (Fin (Tag.rank .E7) → ℤ) →* ℤˣ}, χ = signMaskChar .E7 m →
      ∀ i : KernelComponent χ, simpleUnion χ ∩ componentRoots χ i = ∅ ∨
        simpleUnion χ ∩ componentRoots χ i = S)
    (hα₃ : Pi.single (e7Node 2) 1 ∈ S)
    (hfam : ∀ (K₂ : Type) [Field K₂] [Finite K₂], Nat.card K₂ = p ^ (D.e * 2) →
      ∀ α : MulAut (↥(pairSpan .E7 K₂ S) ⧸ Subgroup.center ↥(pairSpan .E7 K₂ S)),
        orderOf α = 2 → ∀ L : Subgroup (fixedSubgroup α), IsComponent L → NoPSL2Odd L) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  have hΔ : simpleUnion (D.withOrbit J').χ = S := by
    change simpleUnion D.χ = S
    rw [hχ]
    exact hS
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (hcls hχ) with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  have hθ2 : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ ((D.withOrbit J').θ (toReal β)) = toReal β := by
    intro β hβ
    rw [hJS, ← hS] at hβ
    change D.θ (D.θ (toReal β)) = toReal β
    rw [hθ β, hθ, thetaMap_e7Word2_1_twice hm hβ]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties 1 2 (D.withOrbit J').χ (ToralSign.wordElt .E7 e7Word2_1) := by
    change ThetaProperties 1 2 D.χ _
    rw [hχ]
    rcases hm with rfl | rfl
    · exact h7.theta ⟨2, 36, 2, e7OmegaWords2⟩ (by simp [e7SignDiagramReps]) e7Word2_1
        (by simp [e7OmegaWords2])
    · exact h7.theta ⟨3, 28, 2, e7OmegaWords3⟩ (by simp [e7SignDiagramReps]) e7Word3_1
        (by simp [e7OmegaWords3])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  have hα₃J : Pi.single (e7Node 2) 1 ∈ (D.withOrbit J').simpleRootsJ := hJS ▸ hα₃
  have hr3 : IsRoot .E7 (Pi.single (e7Node 2) 1) := isRoot_single _ _
  have hr7 : IsRoot .E7 (Pi.single (e7Node 6) 1) := isRoot_single _ _
  set y : adjointGroup .E7 k :=
    ⟨rootSL2 .E7 k (Pi.single (e7Node 2) 1) (uSL 1), rootSL2_mem_adjointGroup hr3 _⟩ with hy
  set x : adjointGroup .E7 k :=
    ⟨rootSL2 .E7 k (Pi.single (e7Node 2) 1) (vSL 1), rootSL2_mem_adjointGroup hr3 _⟩ with hx
  have hFy : ((D.withOrbit J').F y : ModGL .E7 k) =
      rootSL2 .E7 k (Pi.single (e7Node 6) 1) (uSL 1) := by
    have h := (D.withOrbit J').map_rootSL2 _ hα₃J.1 (Pi.single (e7Node 6) 1)
      (by change D.θ _ = _; rw [hθ, thetaMap_e7Word2_1_alpha3]) (uSL 1) y rfl
    rw [h, LieType.Chevalley.map_uSL, map_one]
  have hnc : ∃ y ∈ quadGens (D.withOrbit J'), ∃ x ∈ quadGens (D.withOrbit J'),
      ¬ Commute ((D.withOrbit J').F y * y⁻¹) x := by
    refine ⟨y, ⟨_, hα₃J, 1, one_mem _, Or.inl rfl⟩, x, ⟨_, hα₃J, 1, one_mem _, Or.inr rfl⟩,
      fun hc => ?_⟩
    have hc' := hc.map (adjointGroup .E7 k).subtype
    simp only [map_mul, map_inv, Subgroup.coe_subtype] at hc'
    rw [hFy] at hc'
    have ha : Commute (rootSL2 .E7 k (Pi.single (e7Node 6) 1) (uSL 1)) (x : ModGL .E7 k) := by
      have hmem7 : rootSL2 .E7 k (Pi.single (e7Node 6) 1) (uSL 1) ∈
          rootSubgroup .E7 k (Pi.single (e7Node 6) 1) := by
        rw [rootSL2_uSL_eq]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      obtain ⟨ε, -, hε⟩ := exists_rootSL2_vSL_eq (K := k) hr3
      have hmem3 : (x : ModGL .E7 k) ∈ rootSubgroup .E7 k (-Pi.single (e7Node 2) 1) := by
        change rootSL2 .E7 k _ (vSL 1) ∈ _
        rw [hε]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      exact (simply_laced_orthogonal_root_commutation .E7 (Or.inr (Or.inr (Or.inl rfl)))).2 k
        _ _ hr7 (IsRoot.neg hr3) (by decide) _ hmem7 _ hmem3
    have hb : Commute (y : ModGL .E7 k) (x : ModGL .E7 k) := by
      have h1 := ha.inv_left.mul_left hc'
      rw [← mul_assoc, inv_mul_cancel, one_mul] at h1
      simpa using h1.inv_left
    have hAB : rootSL2 .E7 k (Pi.single (e7Node 2) 1) (uSL 1 * vSL 1) =
        rootSL2 .E7 k (Pi.single (e7Node 2) 1) (vSL 1 * uSL 1) := by
      rw [map_mul, map_mul]
      exact hb.eq
    have h2 : ((uSL (1 : k) * vSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 =
        ((vSL (1 : k) * uSL 1 : SL2 k) : Matrix (Fin 2) (Fin 2) k) 0 0 :=
      congrArg (fun A : SL2 k => (A : Matrix (Fin 2) (Fin 2) k) 0 0)
        (rootSL2_injective_of_field (Pi.single (e7Node 2) 1) hAB)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    simp [uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two] at h2
  have hK₂ : Nat.card (frobeniusFixedField k p (D.e * 2)) = p ^ (D.e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; omega)
  have : Finite (frobeniusFixedField k p (D.e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  let eY : quadGroup (D.withOrbit J') ≃* pairSpan .E7 (frobeniusFixedField k p (D.e * 2)) S :=
    (((quadGroup (D.withOrbit J')).equivMapOfInjective _
      (adjointGroup .E7 k).subtype_injective).trans
        (MulEquiv.subgroupCongr (map_subtype_quadGroup (D.withOrbit J')))).trans
      (((pairSpan .E7 _ _).equivMapOfInjective _ (baseChangeGL_injective _)).symm.trans
        (MulEquiv.subgroupCongr (congrArg (pairSpan .E7 _) hJS)))
  exact noPSL2Odd_orbitGroup_of_quadGroup (D.withOrbit J') hθ2 hcard hnc hq
    (noPSL2Odd_family_of_mulEquiv (QuotientGroup.congr _ _ eY (Subgroup.map_center_eq eY))
      (hfam _ hK₂))

theorem noPSL2Odd_e7_twisted_E6_orbitGroup
    (hO : LieOrderFormulasInput) (D : OrthogonalSemilinearFixedRootDatum .E7 p k)
    (hχ : D.χ = signMaskChar .E7 3)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E6 0 p (D.e * 2) := ⟨hp, by have := D.one_le_e; omega, rfl⟩
  exact noPSL2Odd_e7_twisted_orbitGroup D (Or.inr rfl) hχ hθ J' hq
    simpleUnion_e7_three (fun hχ' i => e7_simple_inter_three hχ' i) ⟨0, by decide⟩
    fun K₂ _ _ hK₂ _ hα _ hL => noPSL2Odd_of_E6_involution hO hp D.odd hadm
      (lieModel_pairSpan_E6 hp D.odd hK₂) hα hL

end Datum

theorem noPSL2Odd_e7TwistedA7
    (hO : LieOrderFormulasInput) {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [IsAlgClosed k] (D : OrthogonalSemilinearFixedRootDatum .E7 p k)
    (hχ : D.χ = signMaskChar .E7 2)
    (hθ : ∀ γ, D.θ (toReal γ) = toReal (thetaMap (ToralSign.wordElt .E7 e7Word2_1) 1 γ))
    (J' : Set.range D.classOrbit) (hq : IsQuasisimple (D.withOrbit J').orbitGroup) :
    NoPSL2Odd (D.withOrbit J').orbitGroup := by
  have hp : p.Prime := Fact.out
  have hΔ : simpleUnion (D.withOrbit J').χ = Set.range e7A7Root := by
    change simpleUnion D.χ = _
    rw [hχ]
    exact simpleUnion_e7_two
  rcases simpleRootsJ_eq_empty_or_eq (D.withOrbit J') hΔ (e7_simple_inter_two hχ) with h0 | hJS
  · exact absurd (orbitGroup_eq_bot_of_simpleRootsJ_eq_empty _ h0)
      ((Subgroup.nontrivial_iff_ne_bot _).1 (CFSG.LocalCores.isQuasisimple_nontrivial hq))
  have hθ2 : ∀ β ∈ (D.withOrbit J').simpleRootsJ,
      (D.withOrbit J').θ ((D.withOrbit J').θ (toReal β)) = toReal β := by
    intro β hβ
    rw [hJS, ← simpleUnion_e7_two] at hβ
    change D.θ (D.θ (toReal β)) = toReal β
    rw [hθ β, hθ, thetaMap_e7Word2_1_twice (Or.inl rfl) hβ]
  obtain ⟨h7, -, -⟩ := rational_toral_sign_diagram_arithmetic
  have hθp : ThetaProperties 1 2 (D.withOrbit J').χ (ToralSign.wordElt .E7 e7Word2_1) := by
    change ThetaProperties 1 2 D.χ _
    rw [hχ]
    exact h7.theta ⟨2, 36, 2, e7OmegaWords2⟩ (by simp [e7SignDiagramReps]) e7Word2_1
      (by simp [e7OmegaWords2])
  have hcard : ∀ O ∈ (D.withOrbit J').orbits, orbitCard O = 1 ∨ orbitCard O = 2 := fun O hO =>
    ClassicalInvolution.ModelFacts.orbitCard_eq_of_thetaProperties (D.withOrbit J') hθp hθ hO
  have h3 : e7A7Root 3 = Pi.single (e7Node 4) 1 := by
    simp [e7A7Root, e7A7Node]
  have hθα₅ : (D.withOrbit J').θ (toReal (e7A7Root 3)) = toReal (e7A7Root 3) := by
    rw [h3]
    change D.θ _ = _
    rw [hθ]
    exact congrArg toReal thetaMap_e7Word2_1_alpha5
  have hK₂ : Nat.card (frobeniusFixedField k p ((D.withOrbit J').e * 2)) =
      p ^ ((D.withOrbit J').e * 2) :=
    card_frobeniusFixedField (by have := D.one_le_e; change 0 < D.e * 2; omega)
  have : Finite (frobeniusFixedField k p ((D.withOrbit J').e * 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hK₂]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_A7_E7_rankOne hp D.odd hK₂
  exact noPSL2Odd_orbitGroup_of_slFrame hO (D.withOrbit J') hJS hθ2 hcard hq (m := 7)
    (Or.inr rfl) (by rw [h3]; exact isRoot_single _ _) ⟨3, rfl⟩ hθα₅ 3 ⟨Ψ, hker, hrange, hrk 3⟩

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
