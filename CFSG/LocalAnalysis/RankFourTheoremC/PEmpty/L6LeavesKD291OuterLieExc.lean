module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieTransfer
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
import CFSG.LocalAnalysis.SectionRank.ExceptionalModels
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.TableGeneric
import CFSG.Blueprint.LieModelAPI
public import CFSG.LieType.Chevalley.OddF4CosetDescent
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291OuterLieDefs

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section


theorem pRank_adjoint_le_fixed_entrywise {p : ℕ} (hp1 : 1 < p) (τ : Tag) {M : Type} [Field M]
    [Finite M] (hM : ringChar M ≠ 2) (σ : M ≃+* M) :
    CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ (fixSubfield σ))) ≤
      CFSG.Open.pRank p (fixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  obtain ⟨-, -, -, hJΓ, -⟩ := Chevalley_coordinate_field_fixed_structure τ M hM σ
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ M := hJΓ.trans inf_le_left
  set J : Subgroup ↥(adjointGroup τ M) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ M)
    with hJ
  have hmemJ : ∀ x : ↥(adjointGroup τ M), x ∈ J ↔ (x : ModGL τ M) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixedSubgroup (entrywiseAdjointAut τ σ) := fun x hx => by
    refine Subtype.ext ?_
    change ((entrywiseAdjointAut τ σ x : ↥(adjointGroup τ M)) : ModGL τ M) = (x : ModGL τ M)
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  have h1 : CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ (fixSubfield σ))) =
      CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp1 eJ).symm
  have h2 : CFSG.Open.pRank p J = CFSG.Open.pRank p (⊤ : Subgroup ↥J) :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.open_pRank_eq_pRank_top J
  have h3 := CFSG.SectionRank.pRank_mono (p := p) hp1 hJC
  omega

theorem two_le_pRank_adjoint {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f₀ : ℕ} [Fact p.Prime]
    (hf₀ : 1 ≤ f₀) {k : Type} [Field k] [Finite k] (hk : Nat.card k = p ^ f₀) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (adjointGroup τ k)) := by
  have hmodel : UntwistedChevalleyModel (adjointGroup τ k) τ (p ^ f₀) :=
    ⟨k, inferInstance, inferInstance, hk,
      ⟨((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot).symm⟩⟩
  rcases hτ with rfl | hτ'
  · have := CFSG.SectionRank.three_mul_le_pRank_of_G2Model (p := p) hmodel
    omega
  · have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (p := p) (by tauto) hmodel
    omega

theorem two_le_pRank_fixed_entrywise {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p f : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] (hK : Nat.card K = p ^ f)
    (σ : K ≃+* K) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup (entrywiseAdjointAut τ σ)) := by
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp.out hf hK
  have hM : ringChar K ≠ 2 := by rw [ringChar.eq K p]; omega
  obtain ⟨hdvd, hcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hp.out hf hK σ
  have hf0 : 1 ≤ f / orderOf σ :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) (Nat.pos_of_dvd_of_pos hdvd (by omega))
  have h1 := two_le_pRank_adjoint hτ (p := p) hf0 hcard
  have h2 := pRank_adjoint_le_fixed_entrywise hp.out.one_lt τ hM σ
  omega

theorem two_le_pRank_fixed_of_model {τ : Tag} {S : Type} [Group S] [Finite S] {q p : ℕ}
    (hp1 : 1 < p) (hmodel : UntwistedChevalleyModel S τ q)
    (hdesc : ∀ (M : Type) [Field M] [Finite M], Nat.card M = q →
      ∀ β : MulAut (adjointGroup τ M), β ^ p = 1 → β ∉ inner (adjointGroup τ M) →
        2 ≤ CFSG.Open.pRank p (fixedSubgroup β))
    (α : MulAut S) (hαp : α ^ p = 1) (hαin : α ∉ inner S) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup α) := by
  obtain ⟨M, _, _, hM, ⟨e⟩⟩ := hmodel
  let θ : S ≃* adjointGroup τ M := e.trans
    ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
      QuotientGroup.quotientBot)
  have hβp : MulAut.congr θ α ^ p = 1 := by rw [← map_pow, hαp, map_one]
  have hβin : MulAut.congr θ α ∉ inner (adjointGroup τ M) := fun hin =>
    hαin ((CFSG.HardMathSupport.Lang.Coordinator.congr_mem_inner_iff θ α).mp hin)
  have h1 := hdesc M hM (MulAut.congr θ α) hβp hβin
  have h2 : CFSG.Open.pRank p (fixedSubgroup (MulAut.congr θ α)) ≤
      CFSG.Open.pRank p (fixedSubgroup α) :=
    pRank_fixed_le_of_intertwine hp1 θ α (MulAut.congr θ α) fun x => by
      simp [MulAut.congr_apply]
  omega

open CFSG.HardMathSupport.Lang.E6Descent (G2_form_odd exists_conj_eq_entrywiseAdjointAut_of_form
  exists_conj_entrywise_of_not_innerDiag prime_dvd_of_diag_noninner)

theorem intertwine_of_conj {G : Type*} [Group G] {α β δ : MulAut G} (h : δ * α * δ⁻¹ = β)
    (x : G) : β (δ x) = δ (α x) := by
  rw [← h]
  simp [MulAut.mul_apply]

theorem two_le_pRank_fixed_adjoint_G2 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hpℓ : p = ℓ) (hp5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.G2 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.G2 K)) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup α) := by
  subst hpℓ
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.G2 K)).one_mem)
  obtain ⟨x, σ, hσp, hασ⟩ := G2_form_odd hℓ (by omega) (by omega) hf K hK hp α hαord hα
  obtain ⟨δ, hδ⟩ := exists_conj_eq_entrywiseAdjointAut_of_form Tag.G2 hℓ hf K hK hp α hαord x σ
    hσp hασ
  have h1 := two_le_pRank_fixed_entrywise (Or.inl rfl) (p := p) hp5 hf hK σ
  have h2 := pRank_fixed_le_of_intertwine hp.one_lt δ α (entrywiseAdjointAut Tag.G2 σ)
    (intertwine_of_conj hδ)
  omega

theorem two_le_pRank_fixed_adjoint_F4 {ℓ f p : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime)
    (hpℓ : p = ℓ) (hp5 : 5 ≤ p) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (α : MulAut (adjointGroup Tag.F4 K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup Tag.F4 K)) :
    2 ≤ CFSG.Open.pRank p (fixedSubgroup α) := by
  subst hpℓ
  have : Fact p.Prime := ⟨hp⟩
  have hαord : orderOf α = p :=
    orderOf_eq_prime hαp fun h1 => hα (h1 ▸ (inner (adjointGroup Tag.F4 K)).one_mem)
  obtain ⟨x, σ, δ, -, -, hδ, -, -⟩ := odd_F4_prime_field_coset_descent hℓ (by omega) hf K hK hp α
    hαord hα
  have h1 := two_le_pRank_fixed_entrywise (Or.inr (Or.inl rfl)) (p := p) hp5 hf hK σ
  have h2 := pRank_fixed_le_of_intertwine hp.one_lt δ α (entrywiseAdjointAut Tag.F4 σ)
    (intertwine_of_conj hδ)
  omega

theorem fixedSubgroup_le_pow {G : Type*} [Group G] (β : MulAut G) (n : ℕ) :
    fixedSubgroup β ≤ fixedSubgroup (β ^ n) := by
  intro x hx
  have hx' : β x = x := hx
  change (β ^ n) x = x
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx']; exact ih

theorem two_le_pRank_fixed_adjoint_E {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {ℓ f p : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hp : p.Prime) (hpℓ : p = ℓ) (hp5 : 5 ≤ p) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup τ K)) (hαp : α ^ p = 1)
    (hα : α ∉ inner (adjointGroup τ K)) : 2 ≤ CFSG.Open.pRank p (fixedSubgroup α) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      α ≠ MulAut.conj g * rootDiagAut τ K a := by
    intro g a h
    have hdvd := (prime_dvd_of_diag_noninner τ hτ K hp g a α h hαp hα).2
    rw [hK] at hdvd
    have h1 : p ∣ ℓ ^ f := by
      rw [hpℓ]
      exact dvd_pow_self ℓ (by omega)
    have h2 : p ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub h1 hdvd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hp.one_lt.ne' (Nat.dvd_one.1 h2)
  obtain ⟨d, T, r, j, ψ, -, -, -, -, -, hαβ, hψ⟩ :=
    exists_conj_entrywise_of_not_innerDiag τ hτ hf K hK hp (by omega) α hαp hnd
  have hp' : Fact p.Prime := ⟨hp⟩
  have hK' : Nat.card K = p ^ f := by rw [hK, hpℓ]
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by tauto
  have h1 := two_le_pRank_fixed_entrywise hτ' (p := p) hp5 hf hK' T
  have h2 := pRank_fixed_le_of_intertwine hp.one_lt ψ (α ^ r) (entrywiseAdjointAut τ T)
    (intertwine_of_conj hψ)
  have h3 : fixedSubgroup (α ^ r) ≤ fixedSubgroup α := by
    have := fixedSubgroup_le_pow (α ^ r) j
    rwa [hαβ] at this
  have h4 := CFSG.SectionRank.pRank_mono (p := p) hp.one_lt h3
  omega

theorem outerFixedRankDefAt_G2 : OuterFixedRankDefAt .G2 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨hℓp, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  have hm : UntwistedChevalleyModel K .G2 (ℓ ^ f) := hch.2
  exact Or.inl (two_le_pRank_fixed_of_model hp.one_lt hm
    (fun M _ _ hM β hβp hβin => two_le_pRank_fixed_adjoint_G2 hℓp hf hp rfl hp5 M (hM) β hβp hβin)
    α hαp hαin)

theorem outerFixedRankDefAt_F4 : OuterFixedRankDefAt .F4 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨hℓp, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  have hm : UntwistedChevalleyModel K .F4 (ℓ ^ f) := hch.2
  exact Or.inl (two_le_pRank_fixed_of_model hp.one_lt hm
    (fun M _ _ hM β hβp hβin => two_le_pRank_fixed_adjoint_F4 hℓp hf hp rfl hp5 M (hM) β hβp hβin)
    α hαp hαin)

theorem outerFixedRankDefAt_E6 : OuterFixedRankDefAt .E6 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨hℓp, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  have hm : UntwistedChevalleyModel K .E6 (ℓ ^ f) := hch.2
  exact Or.inl (two_le_pRank_fixed_of_model hp.one_lt hm
    (fun M _ _ hM β hβp hβin => two_le_pRank_fixed_adjoint_E (Or.inl rfl) hℓp hf hp rfl hp5 M
      (hM) β hβp hβin) α hαp hαin)

theorem outerFixedRankDefAt_E7 : OuterFixedRankDefAt .E7 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨hℓp, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  have hm : UntwistedChevalleyModel K .E7 (ℓ ^ f) := hch.2
  exact Or.inl (two_le_pRank_fixed_of_model hp.one_lt hm
    (fun M _ _ hM β hβp hβin => two_le_pRank_fixed_adjoint_E (Or.inr (Or.inl rfl)) hℓp hf hp rfl
      hp5 M (hM) β hβp hβin) α hαp hαin)

theorem outerFixedRankDefAt_E8 : OuterFixedRankDefAt .E8 := by
  intro K _ _ n ℓ f hadm hmodel hT p hp hp5 hℓ α hαp hαin
  subst hℓ
  obtain ⟨hℓp, hf, -⟩ := hadm
  obtain ⟨-, hch⟩ := (CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 hmodel
  have hm : UntwistedChevalleyModel K .E8 (ℓ ^ f) := hch.2
  exact Or.inl (two_le_pRank_fixed_of_model hp.one_lt hm
    (fun M _ _ hM β hβp hβin => two_le_pRank_fixed_adjoint_E (Or.inr (Or.inr rfl)) hℓp hf hp rfl
      hp5 M (hM) β hβp hβin) α hαp hαin)

end

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291OL
