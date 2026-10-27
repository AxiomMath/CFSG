module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsKG2
public import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyFacts
public import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2Main

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open scoped MatrixGroups

section Bridge

theorem exists_lift_central_involution {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {K X : Type} [Group K] [Group X] (φ : K →* X)
    (hker : φ.ker ≤ Subgroup.center K) {R : Subgroup K} (e : R ≃* SL(2, F)) {a : X}
    (ha : IsUniqueInvolution (R.map φ) a) :
    ∃ c ∈ R, orderOf c = 2 ∧ (∀ s ∈ R, orderOf s = 2 → s = c) ∧ a = φ c ∧
      (∀ z ∈ R, z ∈ φ.ker → z = 1) ∧ R ≤ ⁅R, R⁆ := by
  have hperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.mp (isPerfect_of_equiv_sl2 h4 e)
  have hacent : ∀ y ∈ R, φ y * a = a * φ y := by
    intro y hy
    have hyR : φ y ∈ R.map φ := ⟨y, hy, rfl⟩
    have hk : φ y * a * (φ y)⁻¹ ∈ R.map φ :=
      (R.map φ).mul_mem ((R.map φ).mul_mem hyR ha.mem) ((R.map φ).inv_mem hyR)
    have hkk : φ y * a * (φ y)⁻¹ * (φ y * a * (φ y)⁻¹) = 1 := by
      calc φ y * a * (φ y)⁻¹ * (φ y * a * (φ y)⁻¹) = φ y * (a * a) * (φ y)⁻¹ := by group
        _ = 1 := by rw [ha.sq]; group
    rcases ha.unique _ hk hkk with h | h
    · exfalso
      apply ha.ne_one
      have := congrArg (fun x => (φ y)⁻¹ * x * φ y) h
      simpa [mul_assoc] using this
    · exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨r, hr, hra⟩ := ha.mem
  have hcomm : ∀ y ∈ R, y * r = r * y := by
    refine commute_of_commutator_central hperf (b := r) (fun y hy => hker ?_)
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, hra, hacent y hy]
    group
  have hrc : (⟨r, hr⟩ : R) ∈ Subgroup.center R :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hcomm g g.2)
  have hrc₀ : r = (e.symm (-1) : R) := by
    rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hrc) with h | h
    · exfalso
      have h1 : (⟨r, hr⟩ : R) = 1 := e.injective (by rw [h, map_one])
      have hr1 : r = 1 := congrArg Subtype.val h1
      exact ha.ne_one (by rw [← hra, hr1, map_one])
    · exact congrArg Subtype.val (e.injective (by rw [h, MulEquiv.apply_symm_apply]) :
        (⟨r, hr⟩ : R) = e.symm (-1))
  refine ⟨(e.symm (-1) : R), (e.symm (-1)).2, ?_, ?_, ?_, ?_, hperf.ge⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, sl2_orderOf_neg_one hodd]
  · intro s hs hord
    have := (orderOf_eq_two_iff_of_equiv_sl2 hodd e ⟨s, hs⟩).mp (by rwa [Subgroup.orderOf_mk])
    exact congrArg Subtype.val this
  · rw [← hra, hrc₀]
  · intro z hz hzk
    have hzc : z ∈ Subgroup.center K := hker hzk
    have hzr : (⟨z, hz⟩ : R) ∈ Subgroup.center R :=
      Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hzc (g : K))
    rcases (mem_center_sl2_iff _).mp ((mem_center_iff_of_equiv_sl2 e _).mp hzr) with h | h
    · have h1 : (⟨z, hz⟩ : R) = 1 := e.injective (by rw [h, map_one])
      exact congrArg Subtype.val h1
    · exfalso
      have h1 : z = (e.symm (-1) : R) :=
        congrArg Subtype.val (e.injective (by rw [h, MulEquiv.apply_symm_apply]) :
          (⟨z, hz⟩ : R) = e.symm (-1))
      have hzr' : z = r := h1.trans hrc₀.symm
      exact ha.ne_one (by rw [← hra, ← hzr']; exact MonoidHom.mem_ker.mp hzk)

variable {p : ℕ} [Fact p.Prime]

theorem stdPair_of_dichotomy {e : ℕ} {t : StatedLieTag} {n : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (hSL2 : ModelFacts.FundamentalSL2 p t n e)
    (hdich : ModelFacts.StandardPairDichotomy p t n e) {X : Type} [Group X]
    (φ : (modelUniv t n p e Fact.out).K →* X) (hker : φ.ker ≤ Subgroup.center _)
    {R₀ Rβ : Subgroup (modelUniv t n p e Fact.out).K}
    (h₀ : R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D)
    (hβ : Rβ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) {a₁ a₂ : X}
    (hN : NormalizedPair (R₀.map φ) (Rβ.map φ) a₁ a₂) :
    StdPairImage p e (R₀.map φ) (Rβ.map φ) := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [hcard]
    omega
  have hl₀ := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ h₀
  have hlβ := ModelFacts.fundamentalSubgroups_subset_longest hG2 hD4 _ hβ
  have hSLR : ∀ R ∈ ModelFacts.longestFundamental (modelUniv t n p e Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField p e)) := by
    rintro R ⟨g, γ, hγ, rfl⟩
    exact hSL2 g γ hγ
  obtain ⟨e₀⟩ := hSLR R₀ hl₀
  obtain ⟨eβ⟩ := hSLR Rβ hlβ
  obtain ⟨c₀, hc₀, hord₀, hu₀, -, hinj₀, -⟩ :=
    exists_lift_central_involution hodd h4 φ hker e₀ hN.uniq₁
  obtain ⟨cβ, hcβ, hordβ, huβ, -, hinjβ, hperfβ⟩ :=
    exists_lift_central_involution hodd h4 φ hker eβ hN.uniq₂
  obtain ⟨-, -, hcomm, -⟩ := lift_normalizedPair hker hperfβ hcβ hordβ hu₀ huβ hinj₀ hinjβ hN
  rcases hdich hp2 hq R₀ hl₀ Rβ hlβ c₀ cβ hc₀ hcβ hord₀ hordβ hcomm with h | h | ⟨W, hW⟩ | ⟨W, hW⟩
  · exfalso
    subst h
    rcases hN.uniq₁.unique a₂ hN.uniq₂.mem hN.uniq₂.sq with h | h
    · exact hN.uniq₂.ne_one h
    · exact hN.ne h.symm
  · exact absurd (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, h x hx y hy]) hN.nc
  · exact Or.inl ⟨_, Balance.linearBlockStandardPair_map_of_ker_le_center hW φ hker⟩
  · exact Or.inr ⟨_, Balance.unitaryBlockStandardPair_map_of_ker_le_center
      (K₀ := GaloisField p (2 * e)) (card_galoisField_two_mul p e (by omega)) hq hW φ hker⟩

theorem pairKG2_of_dichotomy {f : ℕ} (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {X : Type} [Group X]
    {Φ : Set (Subgroup X)} (D : LieSystemData p f X Φ) (i : Fin D.card) (hG2 : D.tag i ≠ .G2)
    (hD4 : D.tag i ≠ .trialityD4)
    (hSL2 : ModelFacts.FundamentalSL2 p (D.tag i) (D.rank i) (D.exp i))
    (hdich : ModelFacts.StandardPairDichotomy p (D.tag i) (D.rank i) (D.exp i)) :
    PairKG2 p f D i := by
  have he : D.exp i = f := by
    rcases D.exp_eq i with h | ⟨h, -⟩
    · exact h
    · exact absurd h hD4
  have key : ∀ (t : StatedLieTag) (n e : ℕ), t ≠ .G2 → t ≠ .trialityD4 → e = f →
      ModelFacts.FundamentalSL2 p t n e → ModelFacts.StandardPairDichotomy p t n e →
      ∀ φ : (modelUniv t n p e Fact.out).K →* X, φ.ker ≤ Subgroup.center _ →
        ∀ R₀ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
        ∀ Rβ ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D, ∀ a₁ a₂ : X,
          NormalizedPair (R₀.map φ) (Rβ.map φ) a₁ a₂ → StdPairImage p f (R₀.map φ) (Rβ.map φ) := by
    intro t n e hG2 hD4 hE hS hd φ hker R₀ h₀ Rβ hβ a₁ a₂ hN
    have hE' : f = e := hE.symm
    subst hE'
    exact stdPair_of_dichotomy hp2 hq hG2 hD4 hS hd φ hker h₀ hβ hN
  intro R₀ hR₀ Rβ hRβ a₁ a₂ hN
  exact key _ _ _ hG2 hD4 he hSL2 hdich (D.hom i) (D.ker_le_center i) R₀ hR₀ Rβ hRβ a₁ a₂ hN

theorem a2ModelKG2_of_dichotomy {f : ℕ} (hFE : ModelFacts.StandardPairDichotomyFE p) :
    A2ModelKG2 p f := by
  intro hp2 hq X _ Φ D i hG2 hD4
  exact pairKG2_of_dichotomy hp2 hq D i hG2 hD4
    (ModelFacts.fundamentalSL2_of_isFundTag hp2 (D.isFundTag i) (D.admissible i))
    (ModelFacts.standardPairDichotomy_of_FE hFE (D.isFundTag i) hG2 hD4 (D.admissible i))

theorem a2LocalStdPairs_of_dichotomy {f : ℕ} (hP1 : A2P1 p f) (hN : A2NoG2D4 p f)
    (hFE : ModelFacts.StandardPairDichotomyFE p) : A2LocalStdPairs p f :=
  a2LocalStdPairs_of_modelKG2 hP1 hN (a2ModelKG2_of_dichotomy hFE)

theorem smallConnectedA2_of_model_facts {f : ℕ} (hD : A2Datum p f) (hP1 : A2P1 p f)
    (hN : A2NoG2D4 p f) (hFE : ModelFacts.StandardPairDichotomyFE p)
    (hI : A2InjectiveCentral p f) (hO : A2OrthEndpoint p f) :
    CoreAssembly.SmallConnectedA2 p f :=
  smallConnectedA2_of_residuals
    { datum := hD
      p1 := hP1
      single := a2SingleClass_of_noG2D4 hN
      localPairs := a2LocalStdPairs_of_dichotomy hP1 hN hFE
      injective := hI
      orth := hO }

end Bridge

end CFSG.ClassicalInvolution.ConnectedA2
