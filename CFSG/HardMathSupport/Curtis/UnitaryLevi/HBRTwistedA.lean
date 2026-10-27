module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftedData
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftGroupCount
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.LiftGroupSemilinear
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.BlockRestrictCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

section Real

open Matrix CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {n : ℕ} {Y : Type} [Group Y] {L : Subgroup Y}

theorem real_semilinear_conj (hK : Nat.card K = (2 ^ 1) ^ 2) (ρ : StatedSU n 2 K →* ↥L) {t : Y}
    {φ : K ≃+* K} {At : GL (Fin n) K}
    (hAt : At ∈ isoGroup (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK
      le_rfl) n)
    (hreal : ∀ g : StatedSU n 2 K, ∃ g' : StatedSU n 2 K,
      (g' : GL (Fin n) K) = At * glAut φ (g : GL (Fin n) K) * At⁻¹ ∧
        t * (ρ g : Y) * t⁻¹ = (ρ g' : Y))
    {A : GL (Fin n) K} {u : Y} (hr : Real ρ A u) :
    Real ρ (At * glAut φ A * At⁻¹) (t * u * t⁻¹) := fun g => by
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  let σ := conjSUSemi h φ hAt
  have hσinj : Function.Injective σ := fun g₁ g₂ hg => by
    have h1 := congrArg Subtype.val hg
    simp only [σ, coe_conjSUSemi] at h1
    apply Subtype.ext
    exact (glAut φ).injective (mul_left_cancel (mul_right_cancel h1))
  have hσsurj : Function.Surjective σ := Finite.injective_iff_surjective.mp hσinj
  obtain ⟨g₁, rfl⟩ := hσsurj g
  obtain ⟨g₂, hg₂, hρ₂⟩ := hr g₁
  obtain ⟨g₃, hg₃, hρ₃⟩ := hreal g₂
  obtain ⟨g₄, hg₄, hρ₄⟩ := hreal g₁
  have hg₄' : g₄ = σ g₁ := Subtype.ext hg₄
  refine ⟨g₃, ?_, ?_⟩
  · rw [hg₃, hg₂]
    simp only [σ, coe_conjSUSemi, map_mul, map_inv]
    group
  · rw [← hg₄']
    calc t * u * t⁻¹ * (ρ g₄ : Y) * (t * u * t⁻¹)⁻¹
        = t * (u * (t⁻¹ * (ρ g₄ : Y) * t) * u⁻¹) * t⁻¹ := by group
      _ = (ρ g₃ : Y) := by
        have h5 : t⁻¹ * (ρ g₄ : Y) * t = (ρ g₁ : Y) := by
          rw [← hρ₄]; group
        rw [h5, hρ₂, hρ₃]

theorem herm_semilinear_of_isometry (hK : Nat.card K = (2 ^ 1) ^ 2) (φ : K ≃+* K)
    {At : GL (Fin n) K}
    (hAt : ∀ x y : Fin n → K,
      stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
        ((At : Matrix (Fin n) (Fin n) K) *ᵥ x) ((At : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n x y)
    (x y : Fin n → K) :
    stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
        ((At : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (x i)))
        ((At : Matrix (Fin n) (Fin n) K) *ᵥ (fun i => φ (y i))) =
      φ (stdHermForm (CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl) n
        x y) := by
  set h := CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK le_rfl with hh
  rw [hAt]
  simp only [stdHermForm_apply, map_sum, map_mul, map_bar_comm h]

end Real

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding
open CFSG.AGLEmbedding.UnitaryLevi CFSG.LinearGroups CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped commutatorElement


theorem hBR_twistedA {Y : Type} [Group Y] [Finite Y] {Lb Pb D : Subgroup Y} {x : Y}
    (hcomp : IsComponentOf Lb ⊤) (hodd : Odd (Nat.card (Subgroup.center ↥Lb)))
    (hpar : IsParabolicTwo Lb Pb) (hne : Pb ≠ Lb) (r : ℕ) (hr : 3 ≤ r) (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid) (hd : q.p = 2) (f : ℕ)
    (hfq : q.exponent = f)
    (e : ↥Lb ⧸ Subgroup.center ↥Lb ≃* TauCeti.ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩)
    (hrank3 : CFSG.Open.pRank 3 Pb ≤ 3)
    (hcycY : ∀ V : Subgroup Y, V ≤ Pb → ⁅V, V⁆ = V → ∀ A : Subgroup Y, A ≤ V → IsPGroup 3 A →
      IsCyclic A)
    (hDperf : ⁅D, D⁆ = D) (hDle : D ≤ Pb ⊔ Subgroup.centralizer (Lb : Set Y))
    (hx : x ∈ D) (hx3 : x ^ 3 = 1) (hxC : x ∉ Subgroup.centralizer (Lb : Set Y))
    (hfreeY : ∀ W : Subgroup Y, W ≤ Lb → ⁅W, W⁆ = W →
      W ≤ Subgroup.centralizer ({x} : Set Y) → W = ⊥)
    (E : Subgroup Y) (hEL : E ≤ Subgroup.normalizer (Lb : Set Y))
    (hEP : E ≤ Subgroup.normalizer (Pb : Set Y)) (hED : E ≤ Subgroup.centralizer (D : Set Y))
    (hEab : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 3 ^ 2)
    (t : Y) (ht : t ∈ Subgroup.normalizer (Lb : Set Y))
    (htE : t ∈ Subgroup.normalizer (E : Set Y))
    (htF : ∀ F : Subgroup Y, F ≤ E → Nat.card F = 3 →
      t ∉ Subgroup.normalizer (F : Set Y)) :
    E ⊓ Subgroup.centralizer (Lb : Set Y) ≠ ⊥ := by
  intro hEC
  have hE3 : IsPGroup 3 E := fun g => ⟨1, by
    have := hEab.2 g.1 g.2
    apply Subtype.ext
    simpa using this⟩
  obtain ⟨r', ε, K, hF, hFin, hchar, hε, hr1, hn4, hcard, hf, ρ, e', S₀, Dt, d, hρs, hρe, hρc,
    hNJ, hJ, hDtJ, hDt, hdD, hds, hd3, hfree, hcyc, hrank, hfix⟩ :=
    exists_lifted_data hcomp hodd hpar hne r hr q hv hd f hfq e hrank3 hcycY hDperf hDle hx hx3 hxC
      hfreeY
  obtain ⟨hf1, -⟩ := survivor_analysis hr1 hε hn4 hcard hf _ S₀ hNJ hJ Dt hDtJ hDt d hdD hds hd3
    hfree hcyc
  subst hf1
  have hK : Nat.card K = (2 ^ 1) ^ 2 := hcard
  have hlift27 : Nat.card (liftGroup hK ρ E) = 27 := by
    rw [card_liftGroup hn4 hK ρ hρs e' hρe hρc hEL hE3 hEC, hE9]
    norm_num
  obtain ⟨φ, At, hφ, hAtiso, hreal, hAtE⟩ :=
    exists_semilinear_conj_mem_liftGroup hn4 hK ρ e' hρe ht htE
  have hAtisom := (mem_primeFormUnitary_one_iff_isometry _ At).mp hAtiso
  obtain ⟨Ft, hFtE, hFt9, hFtscal, hFtst⟩ := hBR_core hr1 hε hn4 hK hf _ S₀ hNJ hJ Dt hDtJ hDt d
    hdD hds hd3 hfree hcyc hrank
    (liftGroup hK ρ E) (fun u hu => (mem_liftGroup_iff hK ρ E u).mp hu |>.1)
    (fun u hu => pow_eq_one_of_mem_liftGroup hn4 hK ρ e' hρe hρc hEL hE3 hu)
    (fun u hu y y' hy =>
      mem_liftGroup_real_mem_iff hEP
        (fun y => by rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]) hu y y' hy)
    (fun u hu x hx => real_commutes_scalar ρ hρc
      (fun v hv g hg => hfix v (hEL hv) (hED hv) g hg) hu hx)
    hlift27 (fun c => scalar_mem_liftGroup hK ρ E c) φ At hAtisom
    (herm_semilinear_of_isometry hK φ hAtisom) hAtE
  obtain ⟨π, hπs, hπr, hπk⟩ := exists_liftGroup_hom hn4 hK ρ hρs e' hρe hρc hEL hE3 hEC
  set F0 : Subgroup ↥(liftGroup hK ρ E) := Ft.subgroupOf (liftGroup hK ρ E) with hF0
  have hmemF0 : ∀ A : ↥(liftGroup hK ρ E), A ∈ F0 ↔ A.1 ∈ Ft := fun A => Iff.rfl
  have hF0card : Nat.card F0 = 9 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFtE).toEquiv).trans hFt9
  set ψ : ↥F0 →* ↥E := π.comp F0.subtype with hψ
  have hψker : Nat.card ψ.ker = 3 := by
    rw [← card_units_eq_three hK]
    symm
    refine Nat.card_congr (Equiv.ofBijective
      (fun c : Kˣ => (⟨⟨⟨Matrix.GeneralLinearGroup.scalar (Fin (2 * r' + ε)) c,
        scalar_mem_liftGroup hK ρ E c⟩, hFtscal c⟩,
        (hπk _).mpr ⟨c, rfl⟩⟩ : ψ.ker)) ⟨?_, ?_⟩)
    · intro c c' hcc
      exact scalar_injective' (by omega)
        (congrArg (fun x : ψ.ker => x.1.1.1) hcc)
    · rintro ⟨⟨⟨A, hA⟩, hAF⟩, hAk⟩
      obtain ⟨c, hc⟩ := (hπk ⟨A, hA⟩).mp hAk
      exact ⟨c, Subtype.ext (Subtype.ext (Subtype.ext hc))⟩
  have hFcard3 : Nat.card ψ.range = 3 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [hψker, Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hF0card] at h1
    omega
  let F : Subgroup Y := ψ.range.map E.subtype
  have hFle : F ≤ E := by
    rintro _ ⟨u, -, rfl⟩
    exact u.2
  have hFcard : Nat.card F = 3 := by
    rw [← hFcard3]
    exact Nat.card_congr (Subgroup.equivMapOfInjective ψ.range E.subtype
      E.subtype_injective).toEquiv.symm
  have hmemF : ∀ u : Y, u ∈ F ↔ ∃ A : GL (Fin (2 * r' + ε)) K, ∃ hA : A ∈ liftGroup hK ρ E,
      A ∈ Ft ∧ ∃ hu : u ∈ E, π ⟨A, hA⟩ = ⟨u, hu⟩ := by
    intro u
    constructor
    · rintro ⟨v, ⟨⟨A, hAF⟩, hAv⟩, rfl⟩
      exact ⟨A.1, A.2, hAF, v.2, hAv⟩
    · rintro ⟨A, hA, hAF, hu, hπ⟩
      refine ⟨⟨u, hu⟩, ⟨⟨⟨A, hA⟩, hAF⟩, ?_⟩, rfl⟩
      exact hπ
  have hstab : ∀ u ∈ (F : Set Y), t * u * t⁻¹ ∈ (F : Set Y) := by
    intro u hu
    obtain ⟨A, hA, hAF, huE, hπA⟩ := (hmemF u).mp hu
    have hreal1 : Real ρ A u := by
      have := hπr ⟨A, hA⟩
      rw [hπA] at this
      exact this
    have hreal2 : Real ρ (At * glAut φ A * At⁻¹) (t * u * t⁻¹) :=
      real_semilinear_conj hK ρ hAtiso hreal hreal1
    have hB : At * glAut φ A * At⁻¹ ∈ liftGroup hK ρ E := hAtE A hA
    have htuE : t * u * t⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp htE u).mp huE
    have hπB : π ⟨_, hB⟩ = ⟨t * u * t⁻¹, htuE⟩ := by
      apply Subtype.ext
      exact real_elem_unique hρs hEC hB (π ⟨_, hB⟩).2 htuE (hπr ⟨_, hB⟩) hreal2
    exact (hmemF _).mpr ⟨_, hB, hFtst A hAF, htuE, hπB⟩
  exact htF F hFle hFcard (Subgroup.mem_normalizer_fintype hstab)

end CFSG.HardMathSupport.Curtis.UnitaryLevi
