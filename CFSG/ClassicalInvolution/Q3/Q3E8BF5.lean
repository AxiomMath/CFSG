module

public import CFSG.ClassicalInvolution.Q3.Q3E8BF5Stage
public import CFSG.ClassicalInvolution.Q3.Q3WAE78
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerPsi

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.ModelFacts.E7Model CFSG.LieType.HighestRoot
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


local notation "M₇" => E7sc 3 1
local notation "D₇" => e7Datum (GaloisField 3 1)
local notation "M₁₂" => Generic.modelUniv StatedLieTag.POmegaPlus 6 3 1 Nat.prime_three

section Psi

theorem exists_psi_E7_layer3 :
    ∃ Ψ : (M₁₂).K →* M₇, Ψ.ker ≤ Subgroup.center (M₁₂).K ∧ Ψ.range = HJ 3 1 ∧
      ∀ i, (rankOne (M₁₂).D.rootGroup i).map Ψ =
        rankOne (e7Datum (GaloisField 3 1)).rootGroup (iota7 i) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hadmY : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨hp, le_rfl, by norm_num⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 3 1 hp trivial hadm
  set D := (Generic.modelUniv .E7 0 3 1 Nat.prime_three).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E7 0 3 1 hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 7; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  exact exists_psi_of_chain_plus3 (N := 6) hadmY
    (G := (Generic.modelUniv .E7 0 3 1 Nat.prime_three).K) (fun i => rankOne D.rootGroup (iota7 i))
    (fun i j hij h1 h2 => commutes_rankOne_of_cartan_eq_zero D hext hℓ (iota7_comm i j hij h1 h2))
    (fun i j h => stdPair_adj_E7 (iota7_edge i j h))

theorem fund12_class3 :
    Generic.FundamentalSingleClass .POmegaPlus (M₁₂).D ∧
      (∀ R ∈ Generic.fundamentalSubgroups .POmegaPlus (M₁₂).D, Pow3 R) ∧
      (∀ z ∈ Subgroup.center (M₁₂).K, ¬ 3 ∣ orderOf z) ∧
      rankOne (M₁₂).D.rootGroup (0 : Fin 6) ∈ Generic.fundamentalSubgroups .POmegaPlus (M₁₂).D := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨hp, le_rfl, rfl⟩
  have hadmY : StatedLieAdmissible .POmegaPlus 6 3 1 := ⟨hp, le_rfl, by norm_num⟩
  obtain ⟨M⟩ := nonempty_extModel3_E7 hadm
  exact ⟨ModelFacts.fundamentalSingleClass .POmegaPlus 6 3 1 hp trivial hadmY (by decide)
    (by decide), M.pow_Y, M.cop_Y, rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .POmegaPlus 6 3 1 hp trivial hadmY _ trivial)⟩

theorem commutes_map_iff_pow3 {X Y : Type} [Group X] [Group Y] (Ψ : Y →* X)
    (hker : Ψ.ker ≤ Subgroup.center Y) (hcop : ∀ z ∈ Ψ.ker, ¬ 3 ∣ orderOf z) {R R' : Subgroup Y}
    (hR : Pow3 R) : Commutes (R.map Ψ) (R'.map Ψ) ↔ Commutes R R' := by
  constructor
  · intro h a ha b hb
    have hc : ∀ b' ∈ R', ∀ l ∈ R, Ψ b' * Ψ l = Ψ l * Ψ b' := fun b' hb' l hl =>
      (h (Ψ l) ⟨l, hl, rfl⟩ (Ψ b') ⟨b', hb', rfl⟩).symm
    exact (commutes_of_map_commute_exponent3 Ψ hker hcop (A := R') (L := R) hR hc b hb a ha).symm
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, h x hx y hy]

theorem layer_equiv_of_map3 {X Y : Type} [Group X] [Group Y] (Ψ : Y →* X)
    (hker : Ψ.ker ≤ Subgroup.center Y) (hcop : ∀ z ∈ Ψ.ker, ¬ 3 ∣ orderOf z)
    {FX : Set (Subgroup X)} {FY : Set (Subgroup Y)} {T : Subgroup X}
    (hpow : ∀ R ∈ FY, Pow3 R) (hmem : ∀ R ∈ FY, R.map Ψ ∈ FX)
    (hcomm : ∀ R ∈ FY, Commutes (R.map Ψ) T)
    (hsurj : ∀ A ∈ FX, Commutes A T → ∃ R ∈ FY, R.map Ψ = A) :
    ∃ e : {A : Subgroup X // A ∈ FX ∧ Commutes A T} ≃ {R : Subgroup Y // R ∈ FY},
      ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1 := by
  let φ : {R : Subgroup Y // R ∈ FY} → {A : Subgroup X // A ∈ FX ∧ Commutes A T} :=
    fun R => ⟨R.1.map Ψ, hmem R.1 R.2, hcomm R.1 R.2⟩
  have hinj : Function.Injective φ := by
    intro R R' h
    exact Subtype.ext (eq_of_map_eq_of_pow3 Ψ hker hcop (hpow R.1 R.2) (hpow R'.1 R'.2)
      (congrArg Subtype.val h))
  have hsurj' : Function.Surjective φ := by
    rintro ⟨A, hA, hAT⟩
    obtain ⟨R, hR, rfl⟩ := hsurj A hA hAT
    exact ⟨⟨R, hR⟩, rfl⟩
  have hbij : Function.Bijective φ := ⟨hinj, hsurj'⟩
  refine ⟨(Equiv.ofBijective φ hbij).symm, fun A A' => ?_⟩
  obtain ⟨R, rfl⟩ := hsurj' A
  obtain ⟨R', rfl⟩ := hsurj' A'
  have e1 : (Equiv.ofBijective φ hbij).symm (φ R) = R :=
    (Equiv.ofBijective φ hbij).symm_apply_apply R
  have e2 : (Equiv.ofBijective φ hbij).symm (φ R') = R' :=
    (Equiv.ofBijective φ hbij).symm_apply_apply R'
  rw [e1, e2]
  exact commutes_map_iff_pow3 Ψ hker hcop (hpow R.1 R.2)

theorem e7LayerEquiv_theta3 :
    ∃ e : {A : Subgroup (TypeE8.K7 3 1) //
        A ∈ TypeE8.F7 3 1 ∧ Commutes A (stdRankOne D₇ thetaE7)} ≃ TypeE8.Fund12 3 1,
      ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1 := by
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_E7_layer3
  obtain ⟨hsc12, hpow12, hcop12, hR₀⟩ := fund12_class3
  have hy0 := hrk (y12 3 1)
  have hadm : StatedLieAdmissible .E7 0 3 1 := ⟨Nat.prime_three, le_rfl, rfl⟩
  have hmem : ∀ R ∈ Generic.fundamentalSubgroups StatedLieTag.POmegaPlus (M₁₂).D,
      R.map Ψ ∈ Generic.fundamentalSubgroups .E7 D₇ := by
    intro R hR
    obtain ⟨m, hm⟩ := hsc12 _ hR₀ R hR
    have h1 : R.map Ψ = conjSub (Ψ m) (rankOne (e7Datum (GaloisField 3 1)).rootGroup
        (iota7 (y12 3 1))) := by
      rw [hm, ← hy0]
      exact (Generic.conjSub_map Ψ m _).symm
    rw [h1]
    exact conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamental _
        (ModelFacts.isLongestRoot_single .E7 0 3 1 Nat.prime_three trivial hadm
          (iota7 (y12 3 1)) trivial))
      (Ψ m)
  have hcommθ : ∀ R ∈ Generic.fundamentalSubgroups StatedLieTag.POmegaPlus (M₁₂).D,
      Commutes (R.map Ψ) (stdRankOne D₇ thetaE7) := by
    intro R _ x hx y hy
    have := commutes_HJ_theta3
    rw [← hrange] at this
    exact this x (Subgroup.map_le_range Ψ R hx) y hy
  have hsurj : ∀ A ∈ Generic.fundamentalSubgroups .E7 D₇, Commutes A (stdRankOne D₇ thetaE7) →
      ∃ R ∈ Generic.fundamentalSubgroups StatedLieTag.POmegaPlus (M₁₂).D, R.map Ψ = A := by
    intro A hA hAθ
    obtain ⟨h, hh, hAh⟩ := exists_mem_HJ_conj_of_commutes_theta3 hA hAθ.symm
    rw [← hrange] at hh
    obtain ⟨m, rfl⟩ := hh
    refine ⟨conjSub m (rankOne (M₁₂).D.rootGroup (y12 3 1)),
      conjSub_mem_fundamentalSubgroups hR₀ m, ?_⟩
    have h6 : e7Idx 6 = iota7 (y12 3 1) := rfl
    rw [hAh, h6, ← hy0]
    exact (Generic.conjSub_map Ψ m _).symm
  exact layer_equiv_of_map3 Ψ hker (fun z hz => hcop12 z (hker hz)) hpow12 hmem hcommθ hsurj

theorem e7LayerEquiv3 : TypeE8.E7LayerEquiv 3 1 := by
  intro T hT
  obtain ⟨hsingle, hRθF⟩ := e7_fund_class3
  obtain ⟨g, hg⟩ := hsingle _ hRθF T hT
  obtain ⟨e₀, he₀⟩ := e7LayerEquiv_theta3
  subst hg
  exact layer_equiv_conj (G := TypeE8.K7 3 1) (F := TypeE8.F7 3 1)
    (fun A hA g => conjSub_mem_fundamentalSubgroups hA g)
    (R := fun R R' : TypeE8.Fund12 3 1 => Commutes R.1 R'.1) (stdRankOne D₇ thetaE7) g e₀ he₀

end Psi

end CFSG.ClassicalInvolution.Q3.Q3W
