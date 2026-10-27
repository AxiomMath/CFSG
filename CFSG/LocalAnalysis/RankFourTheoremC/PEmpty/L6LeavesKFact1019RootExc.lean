module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019Reduce
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootAbs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCover
public import CFSG.ClassicalInvolution.ModelFacts.FundNoncentralMain
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main
public import CFSG.LieType.HighestRoot.GenModels
public import CFSG.LieType.HighestRoot.ModelCenter
public import CFSG.Adapters.TauCetiExceptional.B1Exceptional
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootChk
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact1019RootD4
public import CFSG.LieType.Catalog.Realization

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open scoped MatrixGroups

section Check

open CFSG.AGLEmbedding.P1Lie

theorem linIndepPair_symm' {r : ℕ} {x y : Fin r → ℤ} (h : LinIndepPair x y) :
    LinIndepPair y x := fun a b hab => (h b a (by rw [add_comm]; exact hab)).symm

theorem linIndepPair_neg_left {r : ℕ} {x y : Fin r → ℤ} (h : LinIndepPair x y) :
    LinIndepPair (-x) y := by
  intro a b hab
  have := h (-a) b (by rw [neg_smul, ← smul_neg]; simpa using hab)
  exact ⟨by omega, this.2⟩

theorem openCone_comm' {r : ℕ} (Φ : Set (Fin r → ℤ)) (x y : Fin r → ℤ) :
    openCone Φ x y = openCone Φ y x := by
  ext ε
  constructor <;> rintro ⟨hε, a, c, ha, hc, rfl⟩ <;> exact ⟨hε, c, a, hc, ha, add_comm _ _⟩

theorem commRoots_symm {K : Type*} [Group K] {D : UniversalRootDatum K} {x y : Fin D.rank → ℤ}
    (h : CommRoots D x y) : CommRoots D y x :=
  ⟨linIndepPair_symm' h.1, by rw [openCone_comm']; exact h.2⟩

theorem openCone_neg_single_eq_empty {K : Type*} [Group K] (D : UniversalRootDatum K)
    {i : Fin D.rank} (hAii : D.cartan i i = 2) {β : Fin D.rank → ℤ}
    (hβ : ∑ k, D.cartan i k * β k = 0) (h : openCone D.roots (Pi.single i 1) β = ∅) :
    openCone D.roots (-Pi.single i 1) β = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro ε ⟨hε, a, c, ha, hc, rfl⟩
  have hrefl := (RootSystem.ofCartan D.isFiniteType D.divisible).refl_mem i _ hε
  have e : (RootSystem.ofCartan D.isFiniteType D.divisible).refl i
      (a • (-Pi.single i 1) + c • β) = a • Pi.single i 1 + c • β := by
    rw [RootSystem.ofCartan_refl_apply, map_add, map_nsmul, map_nsmul, map_neg,
      reflection_single_self hAii, reflection_apply, hβ, zero_smul, sub_zero, neg_neg]
  rw [e] at hrefl
  exact (Set.eq_empty_iff_forall_notMem.1 h) _ ⟨hrefl, a, c, ha, hc, rfl⟩

theorem four_roots_of_check {K : Type*} [Group K] (D : UniversalRootDatum K)
    (R : Finset (Fin D.rank → ℤ)) (hR : ∀ ε, ε ∈ D.roots ↔ ε ∈ R) {i : Fin D.rank}
    {b : Fin 3 → (Fin D.rank → ℤ)} (h : FourCheck D.cartan R i b) :
    ∃ S : Finset (Fin D.rank → ℤ), (Pi.single i 1 : Fin D.rank → ℤ) ∈ S ∧ S.card = 4 ∧
      (∀ δ ∈ S, δ ∈ D.roots ∧ 0 < ht δ ∧ ∀ ε ∈ D.roots, δ ≠ 2 • ε) ∧
      (∀ δ ∈ S, ∀ δ' ∈ S, δ ≠ δ' → CommRoots D δ δ') ∧
      (∀ δ ∈ S, δ ≠ Pi.single i 1 → CommRoots D (-Pi.single i 1) δ) := by
  obtain ⟨hAii, hαR, hαind, hb, h01, h02, h12, hbα, hcα, hc01, hc02, hc12⟩ := h
  classical
  set α : Fin D.rank → ℤ := Pi.single i 1 with hα
  have hαpos : 0 < ht α := by simp [hα, ht]
  have hind' : ∀ δ, (∀ ε ∈ R, δ ≠ 2 • ε) → ∀ ε ∈ D.roots, δ ≠ 2 • ε :=
    fun δ hδ ε hε => hδ ε ((hR ε).1 hε)
  have hposroots : ∀ δ ∈ ({α, b 0, b 1, b 2} : Finset _), δ ∈ D.roots ∧ 0 < ht δ ∧
      ∀ ε ∈ D.roots, δ ≠ 2 • ε := by
    intro δ hδ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hδ
    rcases hδ with rfl | rfl | rfl | rfl
    · exact ⟨(hR _).2 hαR, hαpos, hind' _ hαind⟩
    · exact ⟨(hR _).2 (hb 0).1, (hb 0).2.1, hind' _ (hb 0).2.2.2⟩
    · exact ⟨(hR _).2 (hb 1).1, (hb 1).2.1, hind' _ (hb 1).2.2.2⟩
    · exact ⟨(hR _).2 (hb 2).1, (hb 2).2.1, hind' _ (hb 2).2.2.2⟩
  have hcomm : ∀ x y, x ∈ ({α, b 0, b 1, b 2} : Finset _) → y ∈ ({α, b 0, b 1, b 2} : Finset _) →
      x ≠ y → NoCone R x y → CommRoots D x y := by
    intro x y hx hy hxy hnc
    obtain ⟨hxr, hxp, hxi⟩ := hposroots x hx
    obtain ⟨hyr, hyp, hyi⟩ := hposroots y hy
    refine ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).linIndepPair_of_mem_pos
      ⟨hxr, hxp⟩ hxi ⟨hyr, hyp⟩ hyi hxy, openCone_eq_empty_of_noCone _ R hR hxp hyp hnc⟩
  have hcα' : ∀ j, CommRoots D α (b j) := fun j =>
    hcomm α (b j) (by fin_cases j <;> simp) (by fin_cases j <;> simp) (hbα j).symm (hcα j)
  refine ⟨{α, b 0, b 1, b 2}, by simp, ?_, hposroots, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using h12
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨(hbα 0).symm, (hbα 1).symm, (hbα 2).symm⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact hcα' _
      | exact commRoots_symm (hcα' _)
      | exact hcomm _ _ (by simp) (by simp) hxy hc01
      | exact hcomm _ _ (by simp) (by simp) hxy hc02
      | exact hcomm _ _ (by simp) (by simp) hxy hc12
      | exact commRoots_symm (hcomm _ _ (by simp) (by simp) (Ne.symm hxy) hc01)
      | exact commRoots_symm (hcomm _ _ (by simp) (by simp) (Ne.symm hxy) hc02)
      | exact commRoots_symm (hcomm _ _ (by simp) (by simp) (Ne.symm hxy) hc12)
  · intro δ hδ hδα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hδ
    rcases hδ with rfl | rfl | rfl | rfl
    · exact absurd rfl hδα
    all_goals
      first
      | exact ⟨linIndepPair_neg_left (hcα' 0).1, openCone_neg_single_eq_empty D hAii (hb 0).2.2.1
          (hcα' 0).2⟩
      | exact ⟨linIndepPair_neg_left (hcα' 1).1, openCone_neg_single_eq_empty D hAii (hb 1).2.2.1
          (hcα' 1).2⟩
      | exact ⟨linIndepPair_neg_left (hcα' 2).1, openCone_neg_single_eq_empty D hAii (hb 2).2.2.1
          (hcα' 2).2⟩

theorem two_roots_of_check {K : Type*} [Group K] (D : UniversalRootDatum K)
    (R : Finset (Fin D.rank → ℤ)) (hR : ∀ ε, ε ∈ D.roots ↔ ε ∈ R) {i : Fin D.rank}
    {b : Fin D.rank → ℤ} (h : TwoCheck D.cartan R i b) :
    ∃ S : Finset (Fin D.rank → ℤ), (∀ δ, δ ∈ S ↔ δ = Pi.single i 1 ∨ δ = b) ∧
      (Pi.single i 1 : Fin D.rank → ℤ) ≠ b ∧
      (∀ w : (Fin D.rank → ℤ) → ℕ, ∑ δ ∈ S, w δ = w (Pi.single i 1) + w b) ∧
      (∀ δ ∈ S, δ ∈ D.roots ∧ 0 < ht δ ∧ ∀ ε ∈ D.roots, δ ≠ 2 • ε) ∧
      (∀ δ ∈ S, ∀ δ' ∈ S, δ ≠ δ' → CommRoots D δ δ') ∧
      (∀ δ ∈ S, δ ≠ Pi.single i 1 → CommRoots D (-Pi.single i 1) δ) := by
  obtain ⟨hAii, hαR, hαind, hbR, hbpos, hbo, hbind, hbα, hc⟩ := h
  classical
  set α : Fin D.rank → ℤ := Pi.single i 1 with hα
  have hαpos : 0 < ht α := by simp [hα, ht]
  have hind' : ∀ δ, (∀ ε ∈ R, δ ≠ 2 • ε) → ∀ ε ∈ D.roots, δ ≠ 2 • ε :=
    fun δ hδ ε hε => hδ ε ((hR ε).1 hε)
  have hposroots : ∀ δ ∈ ({α, b} : Finset _), δ ∈ D.roots ∧ 0 < ht δ ∧
      ∀ ε ∈ D.roots, δ ≠ 2 • ε := by
    intro δ hδ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hδ
    rcases hδ with rfl | rfl
    · exact ⟨(hR _).2 hαR, hαpos, hind' _ hαind⟩
    · exact ⟨(hR _).2 hbR, hbpos, hind' _ hbind⟩
  have hcαb : CommRoots D α b := by
    refine ⟨(RootSystem.ofCartan D.isFiniteType D.divisible).linIndepPair_of_mem_pos
      ⟨(hposroots α (by simp)).1, hαpos⟩ (hposroots α (by simp)).2.2
      ⟨(hposroots b (by simp)).1, hbpos⟩ (hposroots b (by simp)).2.2 hbα.symm,
      openCone_eq_empty_of_noCone _ R hR hαpos hbpos hc⟩
  refine ⟨{α, b}, fun δ => by simp, hbα.symm, fun w => Finset.sum_pair hbα.symm, hposroots, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact hcαb
      | exact commRoots_symm hcαb
  · intro δ hδ hδα
    simp only [Finset.mem_insert, Finset.mem_singleton] at hδ
    rcases hδ with rfl | rfl
    · exact absurd rfl hδα
    · exact ⟨linIndepPair_neg_left hcαb.1, openCone_neg_single_eq_empty D hAii hbo hcαb.2⟩

end Check

section Certified


open CFSG.ClassicalInvolution.ModelFacts in
theorem exists_fund_involution {t : StatedLieTag} {n p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p f)
    (h1 : ¬ (t = .PSL ∧ n = 2))
    {γ : Fin (modelUniv t n p f Fact.out).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv t n p f Fact.out).D γ) :
    ∃ z : (modelUniv t n p f Fact.out).K,
      z ∈ (modelUniv t n p f Fact.out).D.rootGroup γ ⊔
        (modelUniv t n p f Fact.out).D.rootGroup (-γ) ∧ z ^ 2 = 1 ∧
      (∀ r ∈ (modelUniv t n p f Fact.out).D.rootGroup γ ⊔
        (modelUniv t n p f Fact.out).D.rootGroup (-γ), z * r = r * z) ∧
      ¬ ∀ y : (modelUniv t n p f Fact.out).K,
        z * y * z⁻¹ * y⁻¹ ∈ Subgroup.center (modelUniv t n p f Fact.out).K := by
  have hfund' : IsFundTag t := by cases t <;> trivial
  have hSL2 := fundamentalSL2_of_isFundTag hp2 hfund hadm
  have hf : 1 ≤ f := hadm.2.1
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f (by omega)]
    exact (((Fact.out : p.Prime).eq_two_or_odd').resolve_left hp2).pow
  have hSL2' := hSL2 (1 : (CFSG.ClassicalInvolution.Generic.modelUniv t n p f Fact.out).K) γ hγ
  obtain ⟨e⟩ := hSL2'
  set R1 := ((modelUniv t n p f Fact.out).D.rootGroup γ ⊔
    (modelUniv t n p f Fact.out).D.rootGroup (-γ)).map
      (MulAut.conj (1 : (modelUniv t n p f Fact.out).K)).toMonoidHom with hR1def
  have hR1 : R1 = (modelUniv t n p f Fact.out).D.rootGroup γ ⊔
      (modelUniv t n p f Fact.out).D.rootGroup (-γ) :=
    CFSG.ClassicalInvolution.ModelFacts.map_conj_one _
  let e' : R1 ≃* SL(2, GaloisField p f) := e
  let z : R1 := e'.symm (-1)
  have hz2 : orderOf z = 2 :=
    (CFSG.ClassicalInvolution.orderOf_eq_two_iff_of_equiv_sl2 hodd e' z).2 rfl
  have hzsq : (z : (modelUniv t n p f Fact.out).K) ^ 2 = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2] at this
    exact congrArg Subtype.val this
  have hz1 : (z : (modelUniv t n p f Fact.out).K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz2
    omega
  refine ⟨z, hR1 ▸ z.2, hzsq, ?_, ?_⟩
  · intro r hr
    have hr1 : r ∈ R1 := by rw [hR1]; exact hr
    have hcen : (-1 : SL(2, GaloisField p f)) ∈ Subgroup.center SL(2, GaloisField p f) :=
      (CFSG.ClassicalInvolution.mem_center_sl2_iff _).2 (Or.inr rfl)
    have h := e'.injective (show e' (z * ⟨r, hr1⟩) = e' (⟨r, hr1⟩ * z) by
      rw [map_mul, map_mul]
      simp only [z, MulEquiv.apply_symm_apply]
      exact (Subgroup.mem_center_iff.1 hcen (e' ⟨r, hr1⟩)).symm)
    exact congrArg Subtype.val h
  · intro hcentral
    exact hz1 (fundNoncentral_core t n p f hfund' hadm h1 R1 ⟨1, γ, Or.inl hγ, rfl⟩ z z.2
      hcentral)

open CFSG.ClassicalInvolution.ModelFacts CFSG.AGLEmbedding.P1Lie in
theorem exists_involution_of_lieModel {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (h1 : ¬ (t = .PSL ∧ n = 2)) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Blueprint.LieModel X t n p f)
    {γ : Fin (modelUniv t n p f hp).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv t n p f hp).D γ)
    (S : Finset (Fin (modelUniv t n p f hp).D.rank → ℤ)) (hγS : γ ∈ S) (hcard : S.card = 4)
    (hS : ∀ δ ∈ S, δ ∈ (modelUniv t n p f hp).D.roots ∧ 0 < ht δ ∧
      ∀ ε ∈ (modelUniv t n p f hp).D.roots, δ ≠ 2 • ε)
    (hcomm : ∀ δ ∈ S, ∀ δ' ∈ S, δ ≠ δ' → CommRoots (modelUniv t n p f hp).D δ δ')
    (hneg : ∀ δ ∈ S, δ ≠ γ → CommRoots (modelUniv t n p f hp).D (-γ) δ) :
    ∃ t' : X, orderOf t' = 2 ∧ ∃ E : Subgroup X, E ≤ Subgroup.centralizer {t'} ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfund' : IsFundTag t := by cases t <;> trivial
  have : Finite (CFSG.ClassicalInvolution.Generic.modelUniv t n p f hp).K :=
    finite_modelUniv hp2 hp hfund hadm
  have : Finite (modelUniv t n p f hp).K := finite_modelUniv hp2 hp hfund hadm
  obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Catalog.lieModel_finite_simple X t n p f hX
  haveI : IsSimpleGroup X := hsimple
  obtain ⟨ψ, -, hψk⟩ :=
    CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t n p f hp hp2 hfund hadm X hX
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum t n p f hp hfund' hadm
  have hXp := CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv t n p f hp hfund' hadm
  have hcen := CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t n p f hp hp2
    hfund hadm
  obtain ⟨z, hzR, hz2, hzc, hznc⟩ := exists_fund_involution (p := p) hp2 hfund hadm h1 hγ
  have htc : ∀ δ ∈ S, ∀ x ∈ (modelUniv t n p f hp).D.rootGroup δ, z * x = x * z := by
    intro δ hδ x hx
    by_cases hδγ : δ = γ
    · subst hδγ
      exact hzc x (Subgroup.mem_sup_left hx)
    · have hle : (modelUniv t n p f hp).D.rootGroup γ ⊔
          (modelUniv t n p f hp).D.rootGroup (-γ) ≤
          Subgroup.centralizer ((modelUniv t n p f hp).D.rootGroup δ : Set _) := by
        refine sup_le (fun r hr => ?_) (fun r hr => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (commute_of_commRoots hext (hS γ hγS).1 (hS δ hδ).1
            (hcomm γ hγS δ hδ (Ne.symm hδγ)) hr hy).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hneg' := hneg δ hδ hδγ
          exact (commute_of_commRoots hext
            (by have := (RootSystem.ofCartan (modelUniv t n p f hp).D.isFiniteType
                (modelUniv t n p f hp).D.divisible).neg_mem γ (hS γ hγS).1; exact this)
            (hS δ hδ).1 hneg' hr hy).symm
      exact (Subgroup.mem_centralizer_iff.1 (hle hzR) x hx).symm
  obtain ⟨E, hEc, hEa, hEcard⟩ := exists_elemAbelian_of_four_roots hext hp hXp z S hcard hS hcomm
    htc
  refine exists_involution_of_central_cover hp hcen ψ hψk hz2 ?_ hEc hEa hEcard
  intro h
  apply hznc
  intro y
  have hz : z ∈ Subgroup.center (modelUniv t n p f hp).K := hψk (MonoidHom.mem_ker.2 h)
  rw [Subgroup.mem_center_iff] at hz
  rw [show z * y * z⁻¹ * y⁻¹ = 1 by rw [← hz y]; group]
  exact one_mem _

open CFSG.ClassicalInvolution.ModelFacts CFSG.AGLEmbedding.P1Lie in
theorem exists_involution_of_lieModel_weighted {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) (h1 : ¬ (t = .PSL ∧ n = 2)) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Blueprint.LieModel X t n p f)
    {γ : Fin (modelUniv t n p f hp).D.rank → ℤ}
    (hγ : IsLongestRoot (modelUniv t n p f hp).D γ)
    (S : Finset (Fin (modelUniv t n p f hp).D.rank → ℤ)) (hγS : γ ∈ S)
    (hS : ∀ δ ∈ S, δ ∈ (modelUniv t n p f hp).D.roots ∧ 0 < ht δ ∧
      ∀ ε ∈ (modelUniv t n p f hp).D.roots, δ ≠ 2 • ε)
    (hcomm : ∀ δ ∈ S, ∀ δ' ∈ S, δ ≠ δ' → CommRoots (modelUniv t n p f hp).D δ δ')
    (hneg : ∀ δ ∈ S, δ ≠ γ → CommRoots (modelUniv t n p f hp).D (-γ) δ)
    (w : (Fin (modelUniv t n p f hp).D.rank → ℤ) → ℕ)
    (hroot : ∀ δ ∈ S, ∃ E ≤ (modelUniv t n p f hp).D.rootGroup δ, IsElemAbelian p E ∧
      p ^ w δ ≤ Nat.card E)
    (hw : 4 ≤ ∑ δ ∈ S, w δ) :
    ∃ t' : X, orderOf t' = 2 ∧ ∃ E : Subgroup X, E ≤ Subgroup.centralizer {t'} ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hfund' : IsFundTag t := by cases t <;> trivial
  have : Finite (CFSG.ClassicalInvolution.Generic.modelUniv t n p f hp).K :=
    finite_modelUniv hp2 hp hfund hadm
  have : Finite (modelUniv t n p f hp).K := finite_modelUniv hp2 hp hfund hadm
  obtain ⟨-, -, hsimple⟩ := CFSG.LieType.Catalog.lieModel_finite_simple X t n p f hX
  haveI : IsSimpleGroup X := hsimple
  obtain ⟨ψ, -, hψk⟩ :=
    CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover t n p f hp hp2 hfund hadm X hX
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum t n p f hp hfund' hadm
  have hcen := CFSG.ComponentClassification.RankTwoOddLie.modelCenterPPrime t n p f hp hp2
    hfund hadm
  obtain ⟨z, hzR, hz2, hzc, hznc⟩ := exists_fund_involution (p := p) hp2 hfund hadm h1 hγ
  have htc : ∀ δ ∈ S, ∀ x ∈ (modelUniv t n p f hp).D.rootGroup δ, z * x = x * z := by
    intro δ hδ x hx
    by_cases hδγ : δ = γ
    · subst hδγ
      exact hzc x (Subgroup.mem_sup_left hx)
    · have hle : (modelUniv t n p f hp).D.rootGroup γ ⊔
          (modelUniv t n p f hp).D.rootGroup (-γ) ≤
          Subgroup.centralizer ((modelUniv t n p f hp).D.rootGroup δ : Set _) := by
        refine sup_le (fun r hr => ?_) (fun r hr => ?_)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (commute_of_commRoots hext (hS γ hγS).1 (hS δ hδ).1
            (hcomm γ hγS δ hδ (Ne.symm hδγ)) hr hy).symm
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hneg' := hneg δ hδ hδγ
          exact (commute_of_commRoots hext
            (by have := (RootSystem.ofCartan (modelUniv t n p f hp).D.isFiniteType
                (modelUniv t n p f hp).D.divisible).neg_mem γ (hS γ hγS).1; exact this)
            (hS δ hδ).1 hneg' hr hy).symm
      exact (Subgroup.mem_centralizer_iff.1 (hle hzR) x hx).symm
  obtain ⟨E, hEc, hEa, hEcard⟩ := exists_elemAbelian_of_weighted_roots hext hp z w S hS hcomm htc
    hroot hw
  refine exists_involution_of_central_cover hp hcen ψ hψk hz2 ?_ hEc hEa hEcard
  intro h
  apply hznc
  intro y
  have hz : z ∈ Subgroup.center (modelUniv t n p f hp).K := hψk (MonoidHom.mem_ker.2 h)
  rw [Subgroup.mem_center_iff] at hz
  rw [show z * y * z⁻¹ * y⁻¹ = 1 by rw [← hz y]; group]
  exact one_mem _

open CFSG.ClassicalInvolution.ModelFacts in
theorem exists_involution_of_fourCheck {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t 0 p f) (h1 : ¬ (t = .PSL ∧ 0 = 2)) {X : Type} [Group X]
    [Finite X] (hX : CFSG.Blueprint.LieModel X t 0 p f)
    (i : Fin (modelUniv t 0 p f hp).D.rank) (hlong : IsLongNode t 0 i.val)
    (R : Finset (Fin (modelUniv t 0 p f hp).D.rank → ℤ))
    (hR : ∀ ε, ε ∈ (modelUniv t 0 p f hp).D.roots ↔ ε ∈ R)
    (b : Fin 3 → (Fin (modelUniv t 0 p f hp).D.rank → ℤ))
    (hcheck : FourCheck (modelUniv t 0 p f hp).D.cartan R i b) :
    ∃ t' : X, orderOf t' = 2 ∧ ∃ E : Subgroup X, E ≤ Subgroup.centralizer {t'} ∧
      IsElemAbelian p E ∧ Nat.card E = p ^ 4 := by
  obtain ⟨S, hαS, hcard, hS, hcomm, hneg⟩ := four_roots_of_check _ R hR hcheck
  exact exists_involution_of_lieModel hp hp2 hfund hadm h1 hX
    (isLongestRoot_single t 0 p f hp (by cases t <;> trivial) hadm i hlong) S hαS hcard hS hcomm
    hneg

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.ModelFacts in
theorem involution_typeE8 : InvolutionAt FamE8 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨q, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.E8 q := hdq
  subst hdq'
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E8 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hX : CFSG.Blueprint.LieModel K .E8 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.e8 q hv hp2 e⟩⟩)
  exact exists_involution_of_fourCheck (t := .E8) q.prime_p hp2 trivial hadm
    (fun h => absurd h.2 (by decide)) hX ⟨7, show 7 < 8 by omega⟩ trivial (rootFinset .E8)
    (fun ε => Adjoint.mem_adjDatum_roots.trans mem_rootFinset.symm) _ tagCheck_E8

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.ModelFacts in
theorem involution_typeE7 : InvolutionAt FamE7 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨q, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.E7 q := hdq
  subst hdq'
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E7 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hX : CFSG.Blueprint.LieModel K .E7 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.e7 q hv hp2 e⟩⟩)
  exact exists_involution_of_fourCheck (t := .E7) q.prime_p hp2 trivial hadm
    (fun h => absurd h.2 (by decide)) hX ⟨0, show 0 < 7 by omega⟩ trivial (rootFinset .E7)
    (fun ε => Minuscule.MinData.Valid.mem_minDatum_roots _ _ _ |>.trans mem_rootFinset.symm) _
    tagCheck_E7

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.ModelFacts in
theorem involution_typeE6 : InvolutionAt FamE6 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨q, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.E6 q := hdq
  subst hdq'
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .E6 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hX : CFSG.Blueprint.LieModel K .E6 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.e6 q hv hp2 e⟩⟩)
  exact exists_involution_of_fourCheck (t := .E6) q.prime_p hp2 trivial hadm
    (fun h => absurd h.2 (by decide)) hX ⟨0, show 0 < 6 by omega⟩ trivial (rootFinset .E6)
    (fun ε => Minuscule.MinData.Valid.mem_minDatum_roots _ _ _ |>.trans mem_rootFinset.symm) _
    tagCheck_E6

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.ModelFacts in
theorem involution_typeF4 : InvolutionAt FamF4 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨q, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.F4 q := hdq
  subst hdq'
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .F4 0 q.p q.exponent := ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hX : CFSG.Blueprint.LieModel K .F4 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, CFSG.TauCetiBridge.untwistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.f4 q hv hp2 e⟩⟩)
  exact exists_involution_of_fourCheck (t := .F4) q.prime_p hp2 trivial hadm
    (fun h => absurd h.2 (by decide)) hX ⟨0, show 0 < 4 by omega⟩ (show 0 < 2 by omega)
    (rootFinset .F4) (fun ε => Adjoint.mem_adjDatum_roots.trans mem_rootFinset.symm) _ tagCheck_F4

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.ModelFacts in
theorem involution_typeTwistedE6 : InvolutionAt FamTwistedE6 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨q, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.twistedE6 q := hdq
  subst hdq'
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hadm : StatedLieAdmissible .twistedE6 0 q.p q.exponent :=
    ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hX : CFSG.Blueprint.LieModel K .twistedE6 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.twistedE6 q hv hp2 (by decide) e⟩⟩)
  exact exists_involution_of_fourCheck (t := .twistedE6) q.prime_p hp2 trivial hadm
    (fun h => absurd h.2 (by decide)) hX ⟨0, show 0 < 4 by omega⟩ (show 0 < 2 by omega)
    (rootFinset .F4)
    (fun ε => (Set.ext_iff.1 (TwistedE6.twistedDatum_roots
      (k := GaloisField q.p (2 * q.exponent)) (θ := Exceptional.frobQ q.p q.exponent)) ε).trans
        mem_rootFinset.symm) _ tagCheck_F4

open CFSG.Blueprint.Chevalley CFSG.ClassicalInvolution.ModelFacts in
theorem involution_typeTrialityD4 : InvolutionAt FamTrialityD4 := by
  intro K _ _ d hd ⟨e⟩ p hp hp2 hchar
  obtain ⟨q, hdq⟩ := hd
  obtain ⟨dd, hv⟩ := d
  have hdq' : dd = TauCeti.LieTypeIndex.trialityD4 q := hdq
  subst hdq'
  have hpq : p = q.p := by simpa using hchar
  subst hpq
  haveI : Fact q.p.Prime := ⟨hp⟩
  have hf : 1 ≤ q.exponent := q.exponent_pos
  have hadm : StatedLieAdmissible .trialityD4 0 q.p q.exponent :=
    ⟨q.prime_p, q.exponent_pos, rfl⟩
  have hX : CFSG.Blueprint.LieModel K .trialityD4 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by decide, ⟨hadm, CFSG.TauCetiBridge.twistedModel_of_bridge
      CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp2 (by decide) e⟩⟩)
  obtain ⟨nn, H, hct, hext⟩ := hasBruhatDatum .trialityD4 0 q.p q.exponent q.prime_p
    (by trivial) hadm
  have hXp := CFSG.LieType.HighestRoot.isPGroup_rootGroup_modelUniv .trialityD4 0 q.p q.exponent
    q.prime_p (by trivial) hadm
  set σ := iterateFrobenius (GaloisField q.p (3 * q.exponent)) q.p q.exponent with hσdef
  have hR : ∀ ε, ε ∈ (modelUniv .trialityD4 0 q.p q.exponent q.prime_p).D.roots ↔
      ε ∈ rootFinset .G2 := fun ε =>
    (Set.ext_iff.1 (TwistedD4.twistedDatum_roots σ) ε).trans mem_rootFinset.symm
  set i₀ : Fin (modelUniv .trialityD4 0 q.p q.exponent q.prime_p).D.rank :=
    ⟨0, by show 0 < 2; omega⟩ with hi₀
  set i₁ : Fin (modelUniv .trialityD4 0 q.p q.exponent q.prime_p).D.rank :=
    ⟨1, by show 1 < 2; omega⟩ with hi₁
  set b : Fin (modelUniv .trialityD4 0 q.p q.exponent q.prime_p).D.rank → ℤ :=
    Pi.single i₀ 1 + 2 • Pi.single i₁ 1 with hb
  obtain ⟨S, hmemS, hαb, hsum, hS, hcomm, hneg⟩ := two_roots_of_check
    (modelUniv .trialityD4 0 q.p q.exponent q.prime_p).D (rootFinset .G2) hR (i := i₀) (b := b)
    tagCheck_G2
  have hcardK : Nat.card (GaloisField q.p (3 * q.exponent)) = (q.p ^ q.exponent) ^ 3 := by
    rw [GaloisField.card q.p (3 * q.exponent) (by omega), ← pow_mul, mul_comm]
  have hσ3 : ∀ c, σ (σ (σ c)) = c := TwistedD4.sigma_three_of_card hcardK
    (fun c => iterateFrobenius_def q.p q.exponent c)
  classical
  haveI : Finite (modelUniv .trialityD4 0 q.p q.exponent q.prime_p).K :=
    finite_modelUniv (t := .trialityD4) hp2 q.prime_p trivial hadm
  refine exists_involution_of_lieModel_weighted (t := .trialityD4) q.prime_p hp2 trivial hadm
    (fun h => absurd h.2 (by decide)) hX
    (isLongestRoot_single .trialityD4 0 q.p q.exponent q.prime_p (by trivial) hadm i₀ rfl) S
    ((hmemS _).2 (Or.inl rfl)) hS hcomm hneg (fun δ => if δ = b then 3 else 1) ?_ ?_
  · intro δ hδ
    rcases (hmemS δ).1 hδ with rfl | rfl
    · rw [if_neg hαb]
      exact exists_isElemAbelian_of_isPGroup q.prime_p (hXp _ (hS _ hδ).1)
        (hext.ne_bot _ (hS _ hδ).1)
    · rw [if_pos rfl]
      exact exists_isElemAbelian_twistedRootGroup (K := GaloisField q.p (3 * q.exponent))
        (p := q.p) (σ := σ) hσ3 (k := 3 * q.exponent) (by omega)
        (by rw [GaloisField.card q.p _ (by omega)])
  · rw [hsum, if_neg hαb, if_pos rfl]

end Certified

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Fact1019
