module

public import CFSG.LocalAnalysis.ComponentClassification.FiveCatC5ExcBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormF4
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofSLFormE8

public noncomputable section

namespace CFSG.ComponentClassification.SolMax.FiveCat.C5Exc

open CFSG Subgroup CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.CatLeafProof
open CFSG.Blueprint (chevalleyExceptionalTags ChevalleyExceptionalModel UntwistedChevalleyModel)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

theorem noLitA5_quadratic_field
    (hO : LieOrderFormulasInput) {t : StatedLieTag} {τ : Tag}
    (htτ : t = .G2 ∧ τ = .G2 ∨ t = .F4 ∧ τ = .F4 ∨ t = .E6 ∧ τ = .E6 ∨ t = .E7 ∧ τ = .E7 ∨
      t = .E8 ∧ τ = .E8) {K : Type} [Field K] [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hKe : Nat.card K = (p ^ e) ^ 2) (δ : K ≃+* K) (hδ : ∀ c, δ c = c ^ (p ^ e))
    {α : MulAut (adjointGroup τ K)} {g : adjointGroup τ K} {a : Fin τ.rank → Kˣ}
    (hαg : ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ K) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ K)⁻¹)
    (hα : orderOf α = 2) : NoLitA5 (fixedSubgroup α) := by
  rintro L hL ⟨eA⟩
  exfalso
  have hα2 : α ^ 2 = 1 := hα ▸ pow_orderOf_eq_one α
  obtain ⟨E⟩ := odd_field_component_equiv hp hp2 he hKe δ hδ hαg hα2 (MulEquiv.refl _) hL
  have hk := card_fixSubfield_of_sq_pow hp he hKe δ hδ
  have h3 := three_le_pow_of_odd_prime hp hp2 he
  have hadm : StatedLieAdmissible t 0 p e := by
    rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨hp, he, rfl, h3⟩
    all_goals exact ⟨hp, he, rfl⟩
  have hlie := lieModel_centralQuotient_of_mulEquiv_adjointGroup htτ hadm hk E
  refine (isEmpty_a5_of_lieModel hO (MulEquiv.refl _) hadm hp2 hlie ?_).false eA
  rcases htτ with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide

theorem toralCentralizer_G2_slForm
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) (b : Fin Tag.G2.rank → Kˣ) (hb : ∀ i, b i = 1 ∨ b i = -1)
    (hb1 : b ≠ 1) : SLComponentForm K (toralCentralizer .G2 K b) := by
  intro M hM
  refine Or.inl ?_
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hK2 : Nat.card K ≠ 2 := fun h => absurd (h ▸ hKodd) (by decide)
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  obtain ⟨-, -, hcases, hstruct, hq3⟩ :=
    odd_G2_toral_involution_fixed_p_components K hKodd b hb
  by_cases hK3 : Nat.card K = 3
  · have := (hq3 hK3 hb1).1
    exact (CatLeafProof.not_isComponent_of_isSolvable hM).elim
  obtain ⟨α₀, β₀, hc⟩ : ∃ α₀ β₀ : Fin Tag.G2.rank → ℤ,
      (b = ![-1, 1] ∧ α₀ = ![0, 1] ∧ β₀ = ![2, 3]) ∨
        (b = ![1, -1] ∧ α₀ = ![1, 0] ∧ β₀ = ![1, 2]) ∨
          (b = ![-1, -1] ∧ α₀ = ![1, 1] ∧ β₀ = ![1, 3]) := by
    rcases hcases with h | h | h | h
    · exact absurd h hb1
    · exact ⟨_, _, Or.inl ⟨h, rfl, rfl⟩⟩
    · exact ⟨_, _, Or.inr (Or.inl ⟨h, rfl, rfl⟩)⟩
    · exact ⟨_, _, Or.inr (Or.inr ⟨h, rfl, rfl⟩)⟩
  obtain ⟨-, -, hS, hcomm, -, ⟨eα⟩, ⟨eβ⟩, hSX, hSn, hsolv, -⟩ := hstruct α₀ β₀ hc
  set X := toralCentralizer .G2 K b
  set Qα := rootSubgroup .G2 K α₀ ⊔ rootSubgroup .G2 K (-α₀)
  set Qβ := rootSubgroup .G2 K β₀ ⊔ rootSubgroup .G2 K (-β₀)
  have hQαX : Qα ≤ X := (hS ▸ (le_sup_left : Qα ≤ Qα ⊔ Qβ)).trans hSX
  have hQβX : Qβ ≤ X := (hS ▸ (le_sup_right : Qβ ≤ Qα ⊔ Qβ)).trans hSX
  have hD : (rootSpan .G2 K (rootCharKernel b)).subgroupOf X =
      Qα.subgroupOf X ⊔ Qβ.subgroupOf X := by
    rw [hS]
    exact Subgroup.subgroupOf_sup hQαX hQβX
  have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 K le_rfl (Or.inr hK2)
    (Or.inr hK3)
  let eα' := (Subgroup.subgroupOfEquivOfLe hQαX).trans eα.symm
  let eβ' := (Subgroup.subgroupOfEquivOfLe hQβX).trans eβ.symm
  have hqα : IsQuasisimple (Qα.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eα'.symm hSL
  have hqβ : IsQuasisimple (Qβ.subgroupOf X) := LocalCores.isQuasisimple_of_mulEquiv eβ'.symm hSL
  have hαβ : ∀ x ∈ Qα.subgroupOf X, ∀ y ∈ Qβ.subgroupOf X, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp h1 _ hy).symm)
  have hnα : ((Qα.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    refine sup_le Subgroup.le_normalizer fun y hy => ?_
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      hαβ x hx y hy)
  have hnβ : ((Qβ.subgroupOf X).subgroupOf
      ((rootSpan .G2 K (rootCharKernel b)).subgroupOf X)).Normal := by
    rw [hD, Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
    refine sup_le (fun y hy => ?_) Subgroup.le_normalizer
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (hαβ y hy x hx).symm)
  have hMS := le_of_isComponent_of_solvable_quotient hsolv hM
  rcases CatLeafProof.eq_or_eq_of_isComponent_le_sup hD hqα hqβ hnα hnβ hM hMS with h | h
  · exact ⟨(MulEquiv.subgroupCongr h).trans eα'⟩
  · exact ⟨(MulEquiv.subgroupCongr h).trans eβ'⟩

theorem oddExcInnerDiagSLForm_G2 :
    OddExcInnerDiagSLForm .G2 :=
  oddExcInnerDiagSLForm_of_toral (Or.inl rfl)
    (fun K _ _ hK α hα L hL =>
      odd_G2_F4_E8_all_involution_fixed_p_components .G2 (Or.inl rfl) K hK α hα 2
        Nat.prime_two L hL)
    fun _ _ _ _ _ hp hp2 hKp b hb hb1 => toralCentralizer_G2_slForm hp hp2 hKp b hb hb1

theorem noLitA5_F4_E8_G2_explicit
    (hO : LieOrderFormulasInput) {τ : Tag} (hτ : τ = .F4 ∨ τ = .E8 ∨ τ = .G2)
    (hinner : OddExcInnerDiagSLForm τ) {K : Type} [Field K] [Finite K] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : τ = .G2 → p ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) (β : MulAut (adjointGroup τ K)) (hβ : orderOf β = 2) :
    NoLitA5 (fixedSubgroup β) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hchar := ringChar_eq_of_card hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [hchar]; exact hp2
  have hKodd : Odd (Nat.card K) := by rw [hK]; exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hτ' : τ = .F4 ∨ τ = .E8 ∨ (τ = .G2 ∧ ringChar K ≠ 3) := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨h, hchar ▸ hp3 h⟩)
  have : Finite (ModGL τ K) := finite_modGL
  rcases odd_F4_E8_G2_involution_inner_or_quadratic hτ' hKodd hβ2 with ⟨g, a, hβg⟩ |
    ⟨q, e, hq, he, hKe, δ, hδ, g, a, hβg⟩
  · exact noLitA5_of_slComponentForm hK2 (hinner K p f hp hp2 hK β g a hβg hβ).2
  · have hqp : q = p := by
      have h : q ∣ p ^ f := by
        rw [← hK, hKe]
        exact dvd_pow (dvd_pow_self q (by omega)) two_ne_zero
      exact (Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)
    subst hqp
    have htτ : (StatedLieTag.F4 = .F4 ∧ τ = .F4 ∨ StatedLieTag.E8 = .E8 ∧ τ = .E8) ∨
        τ = .G2 := by
      rcases hτ with h | h | h
      · exact Or.inl (Or.inl ⟨rfl, h⟩)
      · exact Or.inl (Or.inr ⟨rfl, h⟩)
      · exact Or.inr h
    rcases htτ with (⟨-, rfl⟩ | ⟨-, rfl⟩) | rfl
    · exact noLitA5_quadratic_field hO (t := .F4) (Or.inr (Or.inl ⟨rfl, rfl⟩)) hq hp2 he hKe
        δ hδ hβg hβ
    · exact noLitA5_quadratic_field hO (t := .E8)
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))) hq hp2 he hKe δ hδ hβg hβ
    · exact noLitA5_quadratic_field hO (t := .G2) (Or.inl ⟨rfl, rfl⟩) hq hp2 he hKe δ hδ
        hβg hβ

theorem noLitA5_E7_explicit
    (hO : LieOrderFormulasInput) (hinner : OddExcInnerDiagSLForm .E7) {K : Type} [Field K]
    [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = p ^ f)
    (β : MulAut (adjointGroup .E7 K)) (hβ : orderOf β = 2) : NoLitA5 (fixedSubgroup β) := by
  have hβ2 : β ^ 2 = 1 := hβ ▸ pow_orderOf_eq_one β
  have hK2 : ringChar K ≠ 2 := by rw [ringChar_eq_of_card hp hf hK]; exact hp2
  have : Finite (ModGL Tag.E7 K) := finite_modGL
  have h1 : ∀ x : ModGL Tag.E7 K, Units.map (entrywiseHom (1 : K ≃+* K).toRingHom) x = x :=
    fun x => Units.ext (entrywise_id _)
  have hQ : ∀ ε : Fin (exactE Tag.E7), exactQ Tag.E7 K ε = 1 := fun _ => rfl
  obtain ⟨-, -, hNF⟩ := ordinary_E_exact_automorphism_normal_form Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨-, -, -, -, hsq, hquad⟩ :=
    ordinary_E_field_graph_quotient_and_involutions Tag.E7 (Or.inr (Or.inl rfl)) K
  obtain ⟨g, a, σ, ε, hgaσ⟩ := hNF β
  have hσ2 := hsq β g a σ ε hgaσ hβ2
  by_cases hσ1 : σ = 1
  · subst hσ1
    refine noLitA5_of_slComponentForm hK2
      (hinner K p f hp hp2 hK β g a (fun h => ?_) hβ).2
    rw [hgaσ h, hQ, h1, mul_one, inv_one, mul_one]
  · obtain ⟨hev, hσc, -⟩ := hquad p f hp hf hK σ hσ2 hσ1
    have he : 1 ≤ f / 2 := by
      obtain ⟨m, rfl⟩ := hev
      omega
    have hKe : Nat.card K = (p ^ (f / 2)) ^ 2 := by
      rw [← pow_mul, Nat.div_mul_cancel (even_iff_two_dvd.1 hev), hK]
    exact noLitA5_quadratic_field hO (t := .E7) (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
      hp hp2 he hKe σ hσc (g := g) (a := a)
      (fun h => by rw [hgaσ h, hQ, mul_one, inv_one, mul_one]) hβ

theorem oddLieA5For_of_explicit
    {t : StatedLieTag} {τ : Tag} (ht : t ∈ chevalleyExceptionalTags)
    (hmodel : ∀ (J : Type) [Group J] (p f : ℕ), ChevalleyExceptionalModel J t p f →
      UntwistedChevalleyModel J τ (p ^ f))
    (hexp : ∀ (K : Type) [Field K] [Finite K] (p f : ℕ), p.Prime → p ≠ 2 → p ≠ 3 → 1 ≤ f →
      Nat.card K = p ^ f → ∀ β : MulAut (adjointGroup τ K), orderOf β = 2 →
        NoLitA5 (fixedSubgroup β)) :
    OddLieA5For t := by
  intro J _ n p f hp hp2 hp3 hadm hm α hα
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup τ
    (hmodel J p f (GH74.chevalleyExceptionalModel_of_lieModel ht hm))
  have hβ : orderOf (MulAut.congr e α) = 2 :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective α).trans hα
  exact NoLitA5.of_mulEquiv (fixedSubgroupCongrEquiv e α)
    (hexp F p f hp hp2 hp3 hadm.2.1 hF _ hβ)

theorem oddLieA5For_G2
    (hO : LieOrderFormulasInput) : OddLieA5For .G2 :=
  oddLieA5For_of_explicit (τ := .G2) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 hp3 hf hK β hβ =>
      noLitA5_F4_E8_G2_explicit hO (Or.inr (Or.inr rfl)) oddExcInnerDiagSLForm_G2 hp hp2
        (fun _ => hp3) hf hK β hβ

theorem oddLieA5For_F4
    (hO : LieOrderFormulasInput) : OddLieA5For .F4 :=
  oddLieA5For_of_explicit (τ := .F4) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 _ hf hK β hβ =>
      noLitA5_F4_E8_G2_explicit hO (Or.inl rfl) oddExcInnerDiagSLForm_F4 hp hp2
        (fun h => absurd h (by decide)) hf hK β hβ

theorem oddLieA5For_E8
    (hO : LieOrderFormulasInput) : OddLieA5For .E8 :=
  oddLieA5For_of_explicit (τ := .E8) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 _ hf hK β hβ =>
      noLitA5_F4_E8_G2_explicit hO (Or.inr (Or.inl rfl)) oddExcInnerDiagSLForm_E8 hp hp2
        (fun h => absurd h (by decide)) hf hK β hβ

theorem oddLieA5For_E7
    (hO : LieOrderFormulasInput) : OddLieA5For .E7 :=
  oddLieA5For_of_explicit (τ := .E7) (by decide) (fun _ _ _ _ h => h.2)
    fun _ _ _ _ _ hp hp2 _ hf hK β hβ =>
      noLitA5_E7_explicit hO oddExcInnerDiagSLForm_E7 hp hp2 hf hK β hβ

end CFSG.ComponentClassification.SolMax.FiveCat.C5Exc
