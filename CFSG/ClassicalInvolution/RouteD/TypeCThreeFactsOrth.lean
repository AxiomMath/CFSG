module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinModel
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomy

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Generic (Commutes conjSub conjSub_mul)
open CFSG.ClassicalInvolution.ModelFacts (lenSq IsIrreducible IsLongestRoot longestFundamental
  exists_map_conj_rankOne_of_isLongest exists_map_conj_rankOne_of_lenSq_eq lenSq_of_mem_roots
  lenSq_weylAction lenSq_single lenSq_two_nsmul mem_roots_of_mem_fundamentalSubgroups)
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped commutatorElement

section Solvable

variable {K : Type*} [Group K]

theorem not_solvable_centralizer_of_commuting {R R' : Subgroup K} (hc : Commutes R R')
    (hperf : R' ≤ ⁅R', R'⁆) (hne : R' ≠ ⊥) :
    ¬ Group.IsSolvable ↥(Subgroup.centralizer (R : Set K)) := by
  intro hsolv
  have hle : R' ≤ Subgroup.centralizer (R : Set K) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun r hr => hc r hr x hx
  have : Group.IsSolvable ↥R' :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  have : Nontrivial ↥R' := (Subgroup.nontrivial_iff_ne_bot R').mpr hne
  have hcomm : ⁅R', R'⁆ = R' := le_antisymm
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact R'.mul_mem (R'.mul_mem (R'.mul_mem ha hb) (R'.inv_mem ha)) (R'.inv_mem hb)) hperf
  have hP : Group.IsPerfect ↥R' := Subgroup.isPerfect_iff.mpr hcomm
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥R'
  rw [Group.IsPerfect.commutator_eq_top] at h1
  exact lt_irrefl _ h1

end Solvable

section Abstract

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem commutingPartner_of_pair
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {γ₀ δ₀ : Fin D.rank → ℤ} (hγ₀ : IsLongestRoot D γ₀) (hδ₀ : IsLongestRoot D δ₀)
    (horth : form D.isFiniteType (toRat γ₀) (toRat δ₀) = 0) :
    ∀ R ∈ longestFundamental D, ∃ R' ∈ longestFundamental D, Commutes R R' := by
  rintro R ⟨g, γ, hγ, rfl⟩
  obtain ⟨g₁, h1, h2⟩ := exists_map_conj_rankOne_of_isLongest hct hirr hD hγ₀ hγ
  have hAB := CFSG.ClassicalInvolution.RouteD.commutes_fund_of_orthogonal_of_longest D hext
    hγ₀.1 hδ₀.1 hγ₀.2 horth
  have hR : D.rootGroup γ ⊔ D.rootGroup (-γ) = conjSub g₁ (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀)) := by
    unfold conjSub
    rw [Subgroup.map_sup, h1, h2]
  refine ⟨conjSub (g * g₁) (D.rootGroup δ₀ ⊔ D.rootGroup (-δ₀)), ⟨g * g₁, δ₀, hδ₀, rfl⟩, ?_⟩
  have : (D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj g).toMonoidHom =
      conjSub (g * g₁) (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀)) := by
    rw [hR, conjSub_mul]
    rfl
  rw [this]
  exact hAB.conjSub (g * g₁)

theorem commutingPartner_of_pair_two_lengths {t : StatedLieTag} (ht : t = .G2 ∨ t = .trialityD4)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {γ₀ δ₀ : Fin D.rank → ℤ} (hγ₀ : IsLongestRoot D γ₀) (hδ₀ : δ₀ ∈ D.roots)
    (horth : form D.isFiniteType (toRat γ₀) (toRat δ₀) = 0)
    (hlen : ∀ γ ∈ D.roots, lenSq D.isFiniteType γ = lenSq D.isFiniteType γ₀ ∨
      lenSq D.isFiniteType γ = lenSq D.isFiniteType δ₀) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D, Commutes R R' := by
  have hroots : ∀ {ε : Fin D.rank → ℤ}, ε ∈ D.roots → ε ∈ roots D.isFiniteType ∅ := by
    intro ε hε
    have : D.roots = roots D.isFiniteType ∅ := by
      show roots D.isFiniteType D.divisible = _
      rw [hdiv]
    rwa [this] at hε
  have hA : Commutes (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀)) (D.rootGroup δ₀ ⊔ D.rootGroup (-δ₀)) :=
    CFSG.ClassicalInvolution.RouteD.commutes_fund_of_orthogonal_of_longest D hext hγ₀.1 hδ₀
      hγ₀.2 horth
  have hmemA : ∀ g : K, conjSub g (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀)) ∈
      CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D := fun g =>
    ⟨g, γ₀, Or.inl hγ₀, rfl⟩
  have hmemB : ∀ g : K, conjSub g (D.rootGroup δ₀ ⊔ D.rootGroup (-δ₀)) ∈
      CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D := fun g => by
    rcases ht with rfl | rfl
    · exact ⟨g, δ₀, Or.inr (Or.inl ⟨rfl, hδ₀⟩), rfl⟩
    · exact ⟨g, δ₀, Or.inr (Or.inr ⟨rfl, hδ₀⟩), rfl⟩
  rintro R ⟨g, γ, hγ, rfl⟩
  have hγr : γ ∈ D.roots := by
    rcases hγ with h | ⟨-, h⟩ | ⟨-, h⟩
    · exact h.1
    · exact h
    · exact h
  rcases hlen γ hγr with hl | hl
  · obtain ⟨g₁, h1, h2⟩ := exists_map_conj_rankOne_of_lenSq_eq hct hirr (hroots hγ₀.1)
      (hroots hγr) hl.symm
    have hX : D.rootGroup γ ⊔ D.rootGroup (-γ) =
        conjSub g₁ (D.rootGroup γ₀ ⊔ D.rootGroup (-γ₀)) := by
      unfold conjSub
      rw [Subgroup.map_sup, h1, h2]
    rw [hX, ← conjSub_mul]
    exact ⟨_, hmemB (g * g₁), hA.conjSub (g * g₁)⟩
  · obtain ⟨g₁, h1, h2⟩ := exists_map_conj_rankOne_of_lenSq_eq hct hirr (hroots hδ₀)
      (hroots hγr) hl.symm
    have hX : D.rootGroup γ ⊔ D.rootGroup (-γ) =
        conjSub g₁ (D.rootGroup δ₀ ⊔ D.rootGroup (-δ₀)) := by
      unfold conjSub
      rw [Subgroup.map_sup, h1, h2]
    rw [hX, ← conjSub_mul]
    exact ⟨_, hmemA (g * g₁), hA.symm.conjSub (g * g₁)⟩

end Abstract

section Bonds

variable {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A)

theorem coroot_reflection_single_eq_zero {k j : I} (hkk : A k k = 2) (hprod : A k j * A j k = 2) :
    coroot A k (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple j) (Pi.single k 1)) =
      0 := by
  simp only [weylAction_simple, reflection_apply_coroot, map_sub, map_zsmul, coroot_single,
    smul_eq_mul]
  rw [hkk]
  linear_combination (-1 : ℤ) * hprod

theorem coroot_triple_eq_zero {k j : I} (hkk : A k k = 2) (hjj : A j j = 2) (hkj : A k j = -1)
    (hjk : A j k = -3) :
    coroot A k (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple j)
      (weylAction hA ((coxeterMatrix hA).toCoxeterSystem.simple k) (Pi.single j 1))) = 0 := by
  simp only [weylAction_simple, reflection_apply_coroot, map_sub, map_zsmul, coroot_single,
    smul_eq_mul]
  rw [hkk, hjj, hkj, hjk]
  norm_num

end Bonds

section Patterns

variable {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem form_single_eq_zero_of_coroot (k : Fin D.rank) (θ : Fin D.rank → ℤ)
    (h : coroot D.cartan k θ = 0) :
    form D.isFiniteType (toRat (Pi.single k 1 : Fin D.rank → ℤ)) (toRat θ) = 0 := by
  rw [form_comm]
  exact CFSG.ClassicalInvolution.RouteD.form_toRat_single_eq_zero D k θ h

theorem commutingPartner_nonadjacent
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {k j : Fin D.rank} (hkj : D.cartan k j = 0)
    (hk : IsLongestRoot D (Pi.single k 1)) (hj : IsLongestRoot D (Pi.single j 1)) :
    ∀ R ∈ longestFundamental D, ∃ R' ∈ longestFundamental D, Commutes R R' :=
  commutingPartner_of_pair hct hext hirr hD hk hj
    (form_single_eq_zero_of_coroot k _ (by rw [coroot_single, hkj]))

theorem commutingPartner_double
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {k j : Fin D.rank} (hkk : D.cartan k k = 2) (hprod : D.cartan k j * D.cartan j k = 2)
    (hk : IsLongestRoot D (Pi.single k 1)) :
    ∀ R ∈ longestFundamental D, ∃ R' ∈ longestFundamental D, Commutes R R' := by
  set δ := weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)
    (Pi.single k 1) with hδ
  have hδL : IsLongestRoot D δ := by
    refine ⟨CFSG.LieType.RootSystem.weylAction_mem_roots D.isFiniteType _ hk.1, fun ε hε => ?_⟩
    have := hk.2 ε hε
    rwa [← lenSq_weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)
      (Pi.single k 1)] at this
  exact commutingPartner_of_pair hct hext hirr hD hk hδL
    (form_single_eq_zero_of_coroot k δ (coroot_reflection_single_eq_zero D.isFiniteType hkk hprod))

theorem commutingPartner_double_two
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan)
    (hD : ∀ i ∈ D.divisible, ∀ j,
      symmetrizer D.isFiniteType j < 4 * symmetrizer D.isFiniteType i)
    {k j : Fin D.rank} (hkd : k ∈ D.divisible) (hkk : D.cartan k k = 2)
    (hprod : D.cartan k j * D.cartan j k = 2) (hk : IsLongestRoot D (2 • Pi.single k 1)) :
    ∀ R ∈ longestFundamental D, ∃ R' ∈ longestFundamental D, Commutes R R' := by
  set δ := weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)
    (Pi.single k 1) with hδ
  have hlen : lenSq D.isFiniteType (2 • δ) = lenSq D.isFiniteType (2 • (Pi.single k 1 :
      Fin D.rank → ℤ)) := by
    rw [lenSq_two_nsmul, lenSq_two_nsmul, hδ, lenSq_weylAction]
  have hδL : IsLongestRoot D (2 • δ) := by
    refine ⟨Or.inr ⟨_, k, hkd, rfl⟩, fun ε hε => ?_⟩
    rw [hlen]
    exact hk.2 ε hε
  refine commutingPartner_of_pair hct hext hirr hD hk hδL ?_
  have h0 := form_single_eq_zero_of_coroot k δ
    (coroot_reflection_single_eq_zero D.isFiniteType hkk hprod)
  have e : form D.isFiniteType (toRat (2 • (Pi.single k 1 : Fin D.rank → ℤ))) (toRat (2 • δ)) =
      4 * form D.isFiniteType (toRat (Pi.single k 1 : Fin D.rank → ℤ)) (toRat δ) := by
    simp only [two_nsmul, map_add, LinearMap.add_apply]
    ring
  rw [e, h0, mul_zero]

theorem commutingPartner_triple {t : StatedLieTag} (ht : t = .G2 ∨ t = .trialityD4)
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hirr : IsIrreducible D.cartan) (hdiv : D.divisible = ∅)
    {k j : Fin D.rank} (hrank : ∀ i : Fin D.rank, i = k ∨ i = j) (hkk : D.cartan k k = 2)
    (hjj : D.cartan j j = 2) (hkj : D.cartan k j = -1) (hjk : D.cartan j k = -3)
    (hk : IsLongestRoot D (Pi.single k 1)) :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D, Commutes R R' := by
  set sk := (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple k with hsk
  set sj := (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j with hsj
  set δ := weylAction D.isFiniteType sj (weylAction D.isFiniteType sk (Pi.single j 1)) with hδ
  have hjroot : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := Or.inl ⟨1, j, by simp⟩
  have hδroot : δ ∈ D.roots :=
    CFSG.LieType.RootSystem.weylAction_mem_roots D.isFiniteType _
      (CFSG.LieType.RootSystem.weylAction_mem_roots D.isFiniteType _ hjroot)
  refine commutingPartner_of_pair_two_lengths ht hct hext hirr hdiv hk hδroot
    (form_single_eq_zero_of_coroot k δ (coroot_triple_eq_zero D.isFiniteType hkk hjj hkj hjk)) ?_
  intro γ hγ
  have hγ' : γ ∈ roots D.isFiniteType ∅ := by
    have : D.roots = roots D.isFiniteType ∅ := by
      show roots D.isFiniteType D.divisible = _
      rw [hdiv]
    rwa [this] at hγ
  rcases lenSq_of_mem_roots D.isFiniteType hγ' with ⟨i, hi⟩ | ⟨i, hi, -⟩
  · rcases hrank i with rfl | rfl
    · left
      rw [hi, lenSq_single]
    · right
      rw [hi, hδ, lenSq_weylAction, lenSq_weylAction, lenSq_single]
  · exact absurd hi (Set.notMem_empty i)

theorem partner_fund_of_longest {t : StatedLieTag} (ht₁ : t ≠ .G2) (ht₂ : t ≠ .trialityD4)
    (h : ∀ R ∈ longestFundamental D, ∃ R' ∈ longestFundamental D, Commutes R R') :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t D, Commutes R R' := by
  intro R hR
  obtain ⟨R', hR', hc⟩ := h R
    (CFSG.ClassicalInvolution.ModelFacts.fundamentalSubgroups_subset_longest ht₁ ht₂ D hR)
  exact ⟨R', CFSG.ClassicalInvolution.ModelFacts.longestFundamental_subset t D hR', hc⟩

end Patterns

section Glue

variable {p : ℕ} [Fact p.Prime]

theorem not_solvable_of_partner (hp2 : p ≠ 2) {t : StatedLieTag} {n e : ℕ}
    (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (h4 : 4 ≤ p ^ e)
    (hP : ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).D,
      ∃ R' ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).D, Commutes R R') :
    ∀ R ∈ CFSG.ClassicalInvolution.Generic.fundamentalSubgroups t
        (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).D,
      ¬ Group.IsSolvable ↥(Subgroup.centralizer
        (R : Set (CFSG.ClassicalInvolution.Generic.modelUniv t n p e Fact.out).K)) := by
  have hfund' : CFSG.ClassicalInvolution.ModelFacts.IsFundTag t := by
    cases t <;> trivial
  obtain ⟨nn, H, hct, hext⟩ := CFSG.ClassicalInvolution.ModelFacts.hasBruhatDatum t n p e Fact.out
    hfund' hadm
  intro R hR
  obtain ⟨R', hR', hc⟩ := hP R hR
  have hperf := CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p e hp2 hfund' hadm h4 R'
    hR'
  have hne : R' ≠ ⊥ := by
    obtain ⟨g, δ, hδ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR'
    intro hbot
    have hbot' := (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj g).injective).mp hbot
    exact hext.ne_bot δ hδ (le_bot_iff.mp (le_trans le_sup_left hbot'.le))
  exact not_solvable_centralizer_of_commuting hc hperf hne

end Glue

end CFSG.ClassicalInvolution.RouteD.LieBridge
