module

public import CFSG.ClassicalInvolution.Q3.Q3EXOrthLarge
public import CFSG.ClassicalInvolution.Q3.Q3EXD4Local
public import CFSG.ClassicalInvolution.RouteD.ExoticD4GenModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W.EX

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Exotic
  CFSG.ClassicalInvolution.ModelFacts.TG3 CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "𝔽₃" => GaloisField 3 1


section Facts

theorem finite_spin_plus_four : Finite (spinGroup (quadPlus 4 𝔽₃)) := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hn3 : 3 ≤ 4 := by norm_num
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hfin : Finite (modelUniv .POmegaPlus 4 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (t := .POmegaPlus) (by norm_num) Nat.prime_three trivial hadm
  rw [hM] at hfin
  exact hfin

instance : Finite (spinGroup (quadPlus 4 𝔽₃)) := finite_spin_plus_four

theorem central3_plus_four :
    Central3 (spinAction (quadPlus 4 𝔽₃)) (fundD4 𝔽₃) (fundSet (quadPlus 4 𝔽₃)) := by
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hn3 : 3 ≤ 4 := by norm_num
  have h3 : (3 : ℕ) ^ 1 = 3 := by norm_num
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hG3 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      ModelFacts.Gen3 R := fun R hR =>
    ModelFacts.gen3_of_mem_longestFundamental3 (t := .POmegaPlus) h3 trivial hadm (by decide)
      (by decide)
      (ModelFacts.fundamentalSubgroups_subset_longest (by decide) (by decide) _ hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => ModelFacts.isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm k trivial
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR
  have hne : (fundamentalSubgroups .POmegaPlus
      (modelUniv .POmegaPlus 4 3 1 Fact.out).D).Nonempty :=
    nonempty_fund_plus (p := 3) (f := 1) (le_refl 4)
  generalize modelUniv .POmegaPlus 4 3 1 Fact.out = M at hM hsingle hG3 hlong hsl2 hne
  subst hM
  have ctx := spinCtx3_plus hn3 (le_refl 4) hsingle hlong hG3 hsl2
  exact central3_of_ctx3 ctx (fun R hR g => conjSub_mem_fundamentalSubgroups hR g)
    (fun R hR R' hR' => hsingle _ hR R' hR') hne

structure D4Facts3 : Prop where
  central : Central3 (spinAction (quadPlus 4 𝔽₃)) (fundD4 𝔽₃) (fundSet (quadPlus 4 𝔽₃))
  single : FundamentalSingleClass .POmegaPlus (plusDatum 4 𝔽₃ (by norm_num))
  long : ∀ k : Fin 4, IsLongestRoot (plusDatum 4 𝔽₃ (by norm_num)) (Pi.single k 1)
  sl2 : ∀ R ∈ fundD4 𝔽₃, Nonempty (R ≃* SL(2, 𝔽₃))
  gen : ∀ x : spinGroup (quadPlus 4 𝔽₃),
    ⨆ k : Fin 4, rankOneRoot (plusDatum 4 𝔽₃ (by norm_num)) x (Pi.single k 1) = ⊤

theorem D4Facts3.of_gf3 : D4Facts3 := by
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 3 1 := ⟨Nat.prime_three, le_rfl, le_rfl⟩
  have hM : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 3 1 Fact.out =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 Fact.out).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D :=
    ModelFacts.fundamentalSingleClass .POmegaPlus 4 3 1 Fact.out trivial hadm (by decide)
      (by decide)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D (Pi.single k 1) :=
    fun k => ModelFacts.isLongestRoot_single .POmegaPlus 4 3 1 Fact.out trivial hadm k trivial
  have hgen : ∀ g : (modelUniv .POmegaPlus 4 3 1 Fact.out).K,
      ⨆ i : Fin (modelUniv .POmegaPlus 4 3 1 Fact.out).D.rank,
        rankOneRoot (modelUniv .POmegaPlus 4 3 1 Fact.out).D g (Pi.single i 1) = ⊤ :=
    iSup_rankOneRoot_simple_eq_top .POmegaPlus 4 3 1 Fact.out trivial hadm
  have hsl2 : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 3 1 Fact.out).D,
      Nonempty (R ≃* SL(2, GaloisField 3 1)) := fun R hR =>
    ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num) (t := .POmegaPlus)
      trivial hadm (by decide) (by decide) hR
  have key : ∀ M : LieUniversal, M =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
      FundamentalSingleClass .POmegaPlus M.D →
      (∀ k : Fin M.D.rank, IsLongestRoot M.D (Pi.single k 1)) →
      (∀ g : M.K, ⨆ i : Fin M.D.rank, rankOneRoot M.D g (Pi.single i 1) = ⊤) →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, Nonempty (R ≃* SL(2, GaloisField 3 1))) →
      D4Facts3 := by
    intro M hM hs hl hg hs2
    subst hM
    exact ⟨central3_plus_four, hs, hl, hs2, hg⟩
  exact key _ hM hsingle hlong hgen hsl2

end Facts

section Central

theorem D4Facts3.eq_of_map_eq (hF : D4Facts3) {R R' : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) (hR' : R' ∈ fundD4 𝔽₃)
    (h : R.map (spinAction (quadPlus 4 𝔽₃)) = R'.map (spinAction (quadPlus 4 𝔽₃))) : R = R' :=
  hF.central.map_inj hR hR' h

theorem D4Facts3.inj (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) {c : spinGroup (quadPlus 4 𝔽₃)} (hc : c ∈ R)
    (h1 : spinAction (quadPlus 4 𝔽₃) c = 1) : c = 1 :=
  hF.central.inj R hR c hc h1

theorem D4Facts3.exists_frame (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) :
    ∃ fr : OFrame (quadPlus 4 𝔽₃), R.map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range :=
  exists_frame_of_mem_fund_plus (by norm_num) hF.single hF.long hR

theorem D4Facts3.theta_central (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) {fr : OFrame (quadPlus 4 𝔽₃)}
    (hfr : R.map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range) {c : spinGroup (quadPlus 4 𝔽₃)}
    (hc : c ∈ R) (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) :
    spinAction (quadPlus 4 𝔽₃) c = fr.La (-1) :=
  (map_central_eq_one_or_neg_one _ R fr hfr hc hz).resolve_left fun h => h1 (hF.inj hR hc h)

theorem D4Facts3.sq_eq_of_central (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) {fr : OFrame (quadPlus 4 𝔽₃)}
    (hfr : R.map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range) {u : spinGroup (quadPlus 4 𝔽₃)}
    (hu : u ∈ R) {A : SL(2, 𝔽₃)} (hθ : spinAction (quadPlus 4 𝔽₃) u = fr.La A)
    (hA : A * A = -1) {c : spinGroup (quadPlus 4 𝔽₃)} (hc : c ∈ R)
    (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) : u * u = c := by
  have hθc := hF.theta_central hR hfr hc hz h1
  have hmem : u * u * c⁻¹ ∈ R := R.mul_mem (R.mul_mem hu hu) (R.inv_mem hc)
  have h0 : spinAction (quadPlus 4 𝔽₃) (u * u * c⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, hθ, hθc, ← map_mul, hA, mul_inv_cancel]
  exact mul_inv_eq_one.mp (hF.inj hR hmem h0)

theorem D4Facts3.not_central_of_sq (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) {u c : spinGroup (quadPlus 4 𝔽₃)} (hu : u ∈ R) (hc : c ∈ R)
    (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) (hsq : u * u = c) :
    ¬ ∀ r ∈ R, u * r = r * u := by
  intro hu'
  obtain ⟨e⟩ := hF.sl2 R hR
  have hcenR : ∀ (g : spinGroup (quadPlus 4 𝔽₃)) (hg : g ∈ R), (∀ r ∈ R, g * r = r * g) →
      e ⟨g, hg⟩ = 1 ∨ e ⟨g, hg⟩ = -1 := by
    intro g hg hgc
    have : (⟨g, hg⟩ : R) ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hgc y y.2).symm
    exact (CFSG.ClassicalInvolution.mem_center_sl2_iff _).mp
      ((CFSG.ClassicalInvolution.mem_center_iff_of_equiv_sl2 e _).mp this)
  have hec : e ⟨c, hc⟩ = -1 := by
    rcases hcenR c hc hz with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm) :
        (⟨c, hc⟩ : R) = 1)) h1
    · exact h
  have hsq' : e ⟨c, hc⟩ = e ⟨u, hu⟩ * e ⟨u, hu⟩ := by
    rw [← map_mul]
    congr 1
    exact Subtype.ext hsq.symm
  rcases hcenR u hu hu' with h | h
  · rw [hec, h, one_mul] at hsq'
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one odd_natCard_galoisField_three hsq'
  · rw [hec, h] at hsq'
    exact CFSG.ClassicalInvolution.sl2_neg_one_ne_one odd_natCard_galoisField_three
      (by simpa using hsq')

theorem D4Facts3.exists_central (hF : D4Facts3) {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))}
    (hR : R ∈ fundD4 𝔽₃) {fr : OFrame (quadPlus 4 𝔽₃)}
    (hfr : R.map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range) :
    ∃ c ∈ R, (∀ r ∈ R, c * r = r * c) ∧ c ≠ 1 ∧
      spinAction (quadPlus 4 𝔽₃) c = fr.La (-1) := by
  have hker := ker_spinAction_le_center (quadPlus 4 𝔽₃)
  obtain ⟨r, hr, hθr⟩ : fr.La (-1) ∈ R.map (spinAction (quadPlus 4 𝔽₃)) := hfr ▸ ⟨-1, rfl⟩
  have hne : fr.La (-1) ≠ 1 := fun h =>
    CFSG.ClassicalInvolution.sl2_neg_one_ne_one odd_natCard_galoisField_three
      (fr.La_injective (by rw [h, map_one]))
  have hrcent : ∀ s ∈ R, s * r = r * s :=
    ModelFacts.commute_of_map_commute_of_gen3 (spinAction (quadPlus 4 𝔽₃)) hker hF.central.k3
      (hF.central.gen R hR) (b := r) (by
        intro s hs
        have hs' : spinAction (quadPlus 4 𝔽₃) s ∈ fr.La.range := hfr ▸ ⟨s, hs, rfl⟩
        obtain ⟨A, hA⟩ := hs'
        rw [hθr, ← hA, ← map_mul, ← map_mul]
        congr 1
        exact (Subgroup.mem_center_iff.mp
          ((CFSG.ClassicalInvolution.mem_center_sl2_iff (-1 : SL(2, 𝔽₃))).mpr (Or.inr rfl)) A))
  refine ⟨r, hr, fun r' hr' => (hrcent r' hr').symm, ?_, hθr⟩
  rintro rfl
  exact hne (hθr.symm.trans (map_one _))

theorem D4Facts3.mul_self_eq_one_of_central (hF : D4Facts3)
    {R : Subgroup (spinGroup (quadPlus 4 𝔽₃))} (hR : R ∈ fundD4 𝔽₃) {fr : OFrame (quadPlus 4 𝔽₃)}
    (hfr : R.map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range) {c : spinGroup (quadPlus 4 𝔽₃)}
    (hc : c ∈ R) (hz : ∀ r ∈ R, c * r = r * c) (h1 : c ≠ 1) : c * c = 1 := by
  have hθc := hF.theta_central hR hfr hc hz h1
  have h0 : spinAction (quadPlus 4 𝔽₃) (c * c) = 1 := by
    rw [map_mul, hθc]
    exact Frame.La_neg_one_mul_self fr
  exact hF.inj hR (R.mul_mem hc hc) h0

theorem D4Facts3.commutes_of_map_commute (hF : D4Facts3)
    {S R : Subgroup (spinGroup (quadPlus 4 𝔽₃))} (hR : R ∈ fundD4 𝔽₃)
    (h : ∀ a ∈ S.map (spinAction (quadPlus 4 𝔽₃)), ∀ b ∈ R.map (spinAction (quadPlus 4 𝔽₃)),
      a * b = b * a) : Commutes S R := by
  intro x hx y hy
  have := ModelFacts.commute_of_map_commute_of_gen3 (spinAction (quadPlus 4 𝔽₃))
    (ker_spinAction_le_center _) hF.central.k3 (hF.central.gen R hR) (b := x)
    (fun a ha => (h _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩).symm) y hy
  exact this.symm

end Central

section Product

theorem D4Facts3.fund_pair_mul_central (hF : D4Facts3)
    {R₁ R₂ : Subgroup (spinGroup (quadPlus 4 𝔽₃))} (hR₁ : R₁ ∈ fundD4 𝔽₃)
    (hR₂ : R₂ ∈ fundD4 𝔽₃) (hc : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a)
    {c₁ c₂ : spinGroup (quadPlus 4 𝔽₃)} (hc₁ : c₁ ∈ R₁) (hc₂ : c₂ ∈ R₂)
    (hz₁ : ∀ r ∈ R₁, c₁ * r = r * c₁) (hz₂ : ∀ r ∈ R₂, c₂ * r = r * c₂)
    (h₁ : c₁ ≠ 1) (h₂ : c₂ ≠ 1) :
    c₁ * c₂ ∈ Subgroup.center (spinGroup (quadPlus 4 𝔽₃)) := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have hker := ker_spinAction_le_center (quadPlus 4 𝔽₃)
  have hdim : Module.finrank 𝔽₃ (Fin 4 ⊕ Fin 4 → 𝔽₃) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have hmemF : ∀ (x : spinGroup (quadPlus 4 𝔽₃)) (k : Fin 4),
      rankOneRoot (plusDatum 4 𝔽₃ hn3) x (Pi.single k 1) ∈ fundD4 𝔽₃ := fun x k =>
    ⟨x, Pi.single k 1, Or.inl (hF.long k), rfl⟩
  have hθ₁ : spinAction (quadPlus 4 𝔽₃) c₁ ≠ 1 := fun h => h₁ (hF.inj hR₁ hc₁ h)
  have hθ₂ : spinAction (quadPlus 4 𝔽₃) c₂ ≠ 1 := fun h => h₂ (hF.inj hR₂ hc₂ h)
  obtain ⟨fr₁, hfr₁⟩ := hF.exists_frame hR₁
  obtain ⟨fr₂, hfr₂⟩ := hF.exists_frame hR₂
  have hi₁ : spinAction (quadPlus 4 𝔽₃) c₁ = fr₁.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₁ fr₁ hfr₁ hc₁ hz₁).resolve_left hθ₁
  have hi₂ : spinAction (quadPlus 4 𝔽₃) c₂ = fr₂.La (-1) :=
    (map_central_eq_one_or_neg_one _ R₂ fr₂ hfr₂ hc₂ hz₂).resolve_left hθ₂
  by_cases hEq : fr₂.La (-1) = fr₁.La (-1)
  · apply hker
    rw [MonoidHom.mem_ker, map_mul, hi₁, hi₂, hEq]
    exact fr₁.La_neg_one_mul_self
  · have hc' : fr₂.La (-1) * fr₁.La (-1) = fr₁.La (-1) * fr₂.La (-1) := by
      rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hc c₁ hc₁ c₂ hc₂]
    have hcent : ∀ A : SL(2, 𝔽₃), fr₂.La (-1) * fr₁.La A = fr₁.La A * fr₂.La (-1) := by
      intro A
      obtain ⟨r, hr, hrA⟩ : fr₁.La A ∈ R₁.map (spinAction (quadPlus 4 𝔽₃)) := hfr₁ ▸ ⟨A, rfl⟩
      rw [← hi₂, ← hrA, ← map_mul, ← map_mul, (hc r hr c₂ hc₂).symm]
    have horth := (Frame.orth_or_eq h2 hc' hcent).resolve_right hEq
    have hneg := La_neg_one_mul_of_orth h2 hdim horth
    have hθ12 : spinAction (quadPlus 4 𝔽₃) (c₁ * c₂) = LinearEquiv.neg 𝔽₃ := by
      rw [map_mul, hi₁, hi₂, hneg]
    have hcent' : ∀ R ∈ fundD4 𝔽₃, ∀ y ∈ R, y * (c₁ * c₂) = (c₁ * c₂) * y := by
      intro R hR y hy
      exact ModelFacts.commute_of_map_commute_of_gen3 (spinAction (quadPlus 4 𝔽₃)) hker
        hF.central.k3 (hF.central.gen R hR) (b := c₁ * c₂) (by
          intro a _
          rw [hθ12]
          ext v
          simp) y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ (⨆ k : Fin 4, rankOneRoot (plusDatum 4 𝔽₃ hn3) 1 (Pi.single k 1)) := by
      rw [hF.gen 1]
      trivial
    have : (⨆ k : Fin 4, rankOneRoot (plusDatum 4 𝔽₃ hn3) 1 (Pi.single k 1)) ≤
        Subgroup.centralizer ({c₁ * c₂} : Set (spinGroup (quadPlus 4 𝔽₃))) :=
      iSup_le fun k y hy => Subgroup.mem_centralizer_singleton_iff.mpr
        (hcent' _ (hmemF 1 k) y hy)
    exact Subgroup.mem_centralizer_singleton_iff.mp (this hg)

end Product

section Generation

theorem D4Facts3.exists_mem_fund (hF : D4Facts3) : ∃ R, R ∈ fundD4 𝔽₃ :=
  ⟨_, 1, Pi.single (⟨0, by norm_num⟩ : Fin 4) 1, Or.inl (hF.long _), rfl⟩

theorem D4Facts3.exists_fund_of_frame (hF : D4Facts3) (fr : OFrame (quadPlus 4 𝔽₃)) :
    ∃ S ∈ fundD4 𝔽₃, S.map (spinAction (quadPlus 4 𝔽₃)) = fr.La.range := by
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hQnd : (polarBilin (quadPlus 4 𝔽₃)).Nondegenerate := nondegenerate_polarBilin_quadPlus 4 𝔽₃
  obtain ⟨R₀, hR₀⟩ := hF.exists_mem_fund
  obtain ⟨fr₀, hfr₀⟩ := hF.exists_frame hR₀
  have hperp : 2 ≤ Module.finrank 𝔽₃ fr₀.perp := by
    rw [finrank_perp_eq_four finrank_quadPlus_four]
    norm_num
  obtain ⟨x₀, hx₀⟩ := ModelFacts.exists_spin_conj odd_natCard_galoisField_three hQnd fr₀ fr hperp
  refine ⟨conjSub x₀ R₀, conjSub_mem_fundamentalSubgroups hR₀ x₀, ?_⟩
  show (R₀.map (MulAut.conj x₀).toMonoidHom).map _ = _
  rw [ModelFacts.map_conj_map, hfr₀]
  exact (ModelFacts.La_range_eq_map_conj hx₀).symm

theorem D4Facts3.generate_of_comm (hF : D4Facts3)
    {R R' : Subgroup (spinGroup (quadPlus 4 𝔽₃))} (hR : R ∈ fundD4 𝔽₃) (hR' : R' ∈ fundD4 𝔽₃)
    (hne : R' ≠ R) (hnc : ¬ Commutes R R') {c c' : spinGroup (quadPlus 4 𝔽₃)} (hc : c ∈ R)
    (hcz : ∀ r ∈ R, c * r = r * c) (hc1 : c ≠ 1) (hc' : c' ∈ R')
    (hcz' : ∀ r ∈ R', c' * r = r * c') (hc1' : c' ≠ 1)
    (hcomm : c * c' * c⁻¹ * c'⁻¹ ∈ Subgroup.center (spinGroup (quadPlus 4 𝔽₃))) :
    (⨆ S ∈ {S : Subgroup (spinGroup (quadPlus 4 𝔽₃)) |
      S ∈ fundD4 𝔽₃ ∧ (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')}, S) = ⊤ := by
  classical
  have h2 : (2 : 𝔽₃) ≠ 0 := two_ne_zero_three
  have : Invertible (2 : 𝔽₃) := invertibleOfNonzero h2
  have hdim := finrank_quadPlus_four (F := 𝔽₃)
  have hn3 : 3 ≤ 4 := by norm_num
  have : Group.IsPerfect (spinGroup (quadPlus 4 𝔽₃)) := isPerfect_spinGroup_quadPlus hn3
  obtain ⟨fr, hfr⟩ := hF.exists_frame hR
  obtain ⟨fr', hfr'⟩ := hF.exists_frame hR'
  obtain ⟨frY, hY⟩ := exists_frame_span_eq_perp odd_natCard_galoisField_three fr
  obtain ⟨R₁, hR₁, hθR₁⟩ := hF.exists_fund_of_frame fr.swap
  obtain ⟨R₂, hR₂, hθR₂⟩ := hF.exists_fund_of_frame frY
  obtain ⟨R₃, hR₃, hθR₃⟩ := hF.exists_fund_of_frame frY.swap
  obtain ⟨R₄, hR₄, hθR₄⟩ := hF.exists_fund_of_frame fr'.swap
  have horth : ∀ X Y, polar (quadPlus 4 𝔽₃) (fr.incl X) (frY.incl Y) = 0 := fun X Y =>
    polar_eq_zero_of_span_eq_perp hY ⟨X, rfl⟩ ⟨Y, rfl⟩
  have horth' : ∀ X Y, polar (quadPlus 4 𝔽₃) (fr.incl X) (frY.swap.incl Y) = 0 := fun X Y => by
    rw [Frame.incl_swap]
    exact horth X _
  have hC₁ : Commutes R₁ R := hF.commutes_of_map_commute hR fun a ha b hb => by
    rw [hθR₁] at ha
    rw [hfr] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_La_swap fr A B).symm
  have hC₂ : Commutes R₂ R := hF.commutes_of_map_commute hR fun a ha b hb => by
    rw [hθR₂] at ha
    rw [hfr] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_of_orth horth A B).symm
  have hC₃ : Commutes R₃ R := hF.commutes_of_map_commute hR fun a ha b hb => by
    rw [hθR₃] at ha
    rw [hfr] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_of_orth horth' A B).symm
  have hC₄ : Commutes R₄ R' := hF.commutes_of_map_commute hR' fun a ha b hb => by
    rw [hθR₄] at ha
    rw [hfr'] at hb
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨A, rfl⟩ := hb
    exact (Frame.La_comm_La_swap fr' A B).symm
  have hθc := hF.theta_central hR hfr hc hcz hc1
  have hθc' := hF.theta_central hR' hfr' hc' hcz' hc1'
  have hcc := hF.mul_self_eq_one_of_central hR hfr hc hcz hc1
  have hcc' := hF.mul_self_eq_one_of_central hR' hfr' hc' hcz' hc1'
  have hw2 := sq_commutator_eq_one hcc hcc' hcomm
  have hθw : spinAction (quadPlus 4 𝔽₃) (c * c' * c⁻¹ * c'⁻¹) =
      fr.La (-1) * fr'.La (-1) * (fr.La (-1))⁻¹ * (fr'.La (-1))⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hθc, hθc']
  have hmemE : spinAction (quadPlus 4 𝔽₃) (c * c' * c⁻¹ * c'⁻¹) ∈
      elementaryGroup (quadPlus 4 𝔽₃) := by
    rw [← range_spinAction_quadPlus (by norm_num)]
    exact ⟨_, rfl⟩
  let zz : ↥(elementaryGroup (quadPlus 4 𝔽₃)) := ⟨_, hmemE⟩
  have hzc : zz ∈ Subgroup.center ↥(elementaryGroup (quadPlus 4 𝔽₃)) := by
    rw [Subgroup.mem_center_iff]
    intro u
    have hu : (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) ∈
        (spinAction (quadPlus 4 𝔽₃)).range := by
      rw [range_spinAction_quadPlus (by norm_num)]
      exact u.2
    obtain ⟨y, hy⟩ := hu
    apply Subtype.ext
    show (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃)) *
      spinAction (quadPlus 4 𝔽₃) (c * c' * c⁻¹ * c'⁻¹) =
        spinAction (quadPlus 4 𝔽₃) (c * c' * c⁻¹ * c'⁻¹) *
          (u : (Fin 4 ⊕ Fin 4 → 𝔽₃) ≃ₗ[𝔽₃] (Fin 4 ⊕ Fin 4 → 𝔽₃))
    rw [← hy, ← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hcomm y)]
  have hz2 : zz * zz = 1 := Subtype.ext (by
    show spinAction (quadPlus 4 𝔽₃) (c * c' * c⁻¹ * c'⁻¹) *
      spinAction (quadPlus 4 𝔽₃) (c * c' * c⁻¹ * c'⁻¹) = 1
    rw [← map_mul, hw2, map_one])
  have hZ := CFSG.ClassicalInvolution.Models.Transfer.centerScalar_quadPlus (K := 𝔽₃)
    (n := 4) (by norm_num)
  have hcomm' : fr.La (-1) * fr'.La (-1) * (fr.La (-1))⁻¹ * (fr'.La (-1))⁻¹ = 1 ∨
      fr.La (-1) * fr'.La (-1) * (fr.La (-1))⁻¹ * (fr'.La (-1))⁻¹ = LinearEquiv.neg 𝔽₃ := by
    rcases CFSG.ClassicalInvolution.Models.Transfer.eq_one_or_eq_neg_of_mem_center hZ hzc hz2 with
      h | h
    · left
      rw [← hθw]
      exact congrArg Subtype.val h
    · right
      rw [← hθw]
      exact h
  have hpos := position_of_commutator_eq (Frame.La_neg_one_mul_self fr)
    (Frame.La_neg_one_mul_self fr') hcomm'
  have hne1 : fr'.span ≠ fr.span := by
    intro hs
    rcases Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hs) with h | h
    · exact hne (hF.eq_of_map_eq hR' hR (hfr'.trans (h.trans hfr.symm)))
    · refine hnc (Commutes.symm (hF.commutes_of_map_commute hR fun a ha b hb => ?_))
      rw [hfr', h] at ha
      rw [hfr] at hb
      obtain ⟨B, rfl⟩ := ha
      obtain ⟨A, rfl⟩ := hb
      exact (Frame.La_comm_La_swap fr A B).symm
  have hne2 : fr'.span ≠ fr.perp := by
    intro hs
    rw [← hY] at hs
    rcases Frame.La_range_eq_or_eq_swap h2 (Frame.La_neg_one_eq_of_span_eq hs) with h | h
    · refine hnc (Commutes.symm (hF.commutes_of_map_commute hR fun a ha b hb => ?_))
      rw [hfr', h] at ha
      rw [hfr] at hb
      obtain ⟨B, rfl⟩ := ha
      obtain ⟨A, rfl⟩ := hb
      exact (Frame.La_comm_of_orth horth A B).symm
    · refine hnc (Commutes.symm (hF.commutes_of_map_commute hR fun a ha b hb => ?_))
      rw [hfr', h] at ha
      rw [hfr] at hb
      obtain ⟨B, rfl⟩ := ha
      obtain ⟨A, rfl⟩ := hb
      exact (Frame.La_comm_of_orth horth' A B).symm
  set T : Subgroup (spinGroup (quadPlus 4 𝔽₃)) :=
    ⨆ S ∈ {S : Subgroup (spinGroup (quadPlus 4 𝔽₃)) |
      S ∈ fundD4 𝔽₃ ∧ (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R')}, S with hT
  have hmemT : ∀ S ∈ fundD4 𝔽₃, (S = R ∨ Commutes S R ∨ S = R' ∨ Commutes S R') → S ≤ T :=
    fun S hS hS' => le_iSup₂_of_le S ⟨hS, hS'⟩ le_rfl
  have hle : ∀ (fr₀ : OFrame (quadPlus 4 𝔽₃)) (S : Subgroup (spinGroup (quadPlus 4 𝔽₃))),
      S.map (spinAction (quadPlus 4 𝔽₃)) = fr₀.La.range → S ≤ T →
      fr₀.La.range ≤ T.map (spinAction (quadPlus 4 𝔽₃)) := fun fr₀ S hS hST =>
    hS ▸ Subgroup.map_mono hST
  have h₁ : omegaGrp fr ≤ T.map (spinAction (quadPlus 4 𝔽₃)) :=
    sup_le (hle fr R hfr (hmemT R hR (Or.inl rfl)))
      (hle fr.swap R₁ hθR₁ (hmemT R₁ hR₁ (Or.inr (Or.inl hC₁))))
  have h₃ : omegaGrp frY ≤ T.map (spinAction (quadPlus 4 𝔽₃)) :=
    sup_le (hle frY R₂ hθR₂ (hmemT R₂ hR₂ (Or.inr (Or.inl hC₂))))
      (hle frY.swap R₃ hθR₃ (hmemT R₃ hR₃ (Or.inr (Or.inl hC₃))))
  have h' : omegaGrp fr' ≤ T.map (spinAction (quadPlus 4 𝔽₃)) :=
    sup_le (hle fr' R' hfr' (hmemT R' hR' (Or.inr (Or.inr (Or.inl rfl)))))
      (hle fr'.swap R₄ hθR₄ (hmemT R₄ hR₄ (Or.inr (Or.inr (Or.inr hC₄)))))
  have hE := elementaryGroup_le_of_position h2 hdim hY h₁ h₃ h' hne1 hne2 hpos
  exact eq_top_of_range_le_map (spinAction (quadPlus 4 𝔽₃)) (ker_spinAction_le_center _)
    ((range_spinAction_quadPlus hn3).le.trans hE)

end Generation

end CFSG.ClassicalInvolution.Q3.Q3W.EX
