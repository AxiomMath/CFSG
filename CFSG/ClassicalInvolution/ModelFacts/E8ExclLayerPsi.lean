module

public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerStage
public import CFSG.ClassicalInvolution.ModelFacts.E8ExclLayerStmt
public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import CFSG.ClassicalInvolution.RouteD.TypeEModel
public import CFSG.ClassicalInvolution.RouteD.GapsOrthTransfer
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.ModelFacts.E7Model

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Universal
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.ModelFacts.Levi CFSG.ClassicalInvolution.ModelFacts
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.RouteD CFSG.Timmesfeld

@[expose] def y12 (p f : ℕ) [Fact p.Prime] :
    Fin (modelUniv StatedLieTag.POmegaPlus 6 p f Fact.out).D.rank :=
  ⟨0, by show 0 < 6; decide⟩

section Psi

variable {p f : ℕ} [Fact p.Prime]

local notation "M₇" => E7sc p f
local notation "D₇" => e7Datum (GaloisField p f)
local notation "M₁₂" => modelUniv StatedLieTag.POmegaPlus 6 p f Fact.out

theorem exists_psi_E7 (hq : 4 ≤ p ^ f) :
    ∃ Ψ : (M₁₂).K →* M₇, Ψ.ker ≤ Subgroup.center (M₁₂).K ∧ Ψ.range = HJ p f ∧
      ∀ i, (rankOne (M₁₂).D.rootGroup i).map Ψ =
        rankOne (e7Datum (GaloisField p f)).rootGroup (iota7 i) := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hp : p.Prime := Fact.out
  have hadm : StatedLieAdmissible .E7 0 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), rfl⟩
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), by norm_num⟩
  obtain ⟨nW, H, -, hext⟩ := ModelFacts.hasBruhatDatum .E7 0 p f hp trivial hadm
  set D := (modelUniv .E7 0 p f Fact.out).D with hD
  have hdiv : D.divisible = ∅ := rfl
  have hl : ∀ i, ModelFacts.IsLongestRoot D (Pi.single i 1) := fun i =>
    ModelFacts.isLongestRoot_single .E7 0 p f hp trivial hadm i trivial
  let z0 : Fin D.rank := ⟨0, by show 0 < 7; decide⟩
  have hℓ := lenSq_eq_of_simplyLaced D hdiv hl z0
  exact exists_psi_D6 (p := p) (f := f) hadmY hq
    (X := (modelUniv .E7 0 p f Fact.out).K) (fun i => rankOne D.rootGroup (iota7 i))
    (fun i j hij h1 h2 => commutes_rankOne_of_cartan_eq_zero D hext hℓ (iota7_comm i j hij h1 h2))
    (fun i j h => stdPair_adj_E7 (iota7_edge i j h))

theorem fund12_class (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f) :
    FundamentalSingleClass .POmegaPlus (M₁₂).D ∧
      (∀ R ∈ fundamentalSubgroups .POmegaPlus (M₁₂).D, ⁅R, R⁆ = R) ∧
      rankOne (M₁₂).D.rootGroup (0 : Fin 6) ∈
        fundamentalSubgroups .POmegaPlus (M₁₂).D := by
  have : NeZero f := ⟨by rintro rfl; simp at hq⟩
  have hp : p.Prime := Fact.out
  have hadmY : StatedLieAdmissible .POmegaPlus 6 p f :=
    ⟨hp, Nat.one_le_iff_ne_zero.2 (NeZero.ne f), by norm_num⟩
  refine ⟨fundamentalSingleClass .POmegaPlus 6 p f hp trivial hadmY (by decide) (by decide),
    fun R hR => le_antisymm (commutator_self_le R)
      (fundPerfect_core .POmegaPlus 6 p f hp2 trivial hadmY hq R hR),
    rankOne_mem_fundamental _
      (ModelFacts.isLongestRoot_single .POmegaPlus 6 p f hp trivial hadmY _ trivial)⟩

theorem layer_equiv_of_map {X Y : Type} [Group X] [Group Y] (Ψ : Y →* X)
    (hker : Ψ.ker ≤ Subgroup.center Y) {FX : Set (Subgroup X)} {FY : Set (Subgroup Y)}
    {T : Subgroup X} (hperf : ∀ R ∈ FY, ⁅R, R⁆ = R) (hmem : ∀ R ∈ FY, R.map Ψ ∈ FX)
    (hcomm : ∀ R ∈ FY, Commutes (R.map Ψ) T)
    (hsurj : ∀ A ∈ FX, Commutes A T → ∃ R ∈ FY, R.map Ψ = A) :
    ∃ e : {A : Subgroup X // A ∈ FX ∧ Commutes A T} ≃ {R : Subgroup Y // R ∈ FY},
      ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1 := by
  let φ : {R : Subgroup Y // R ∈ FY} → {A : Subgroup X // A ∈ FX ∧ Commutes A T} :=
    fun R => ⟨R.1.map Ψ, hmem R.1 R.2, hcomm R.1 R.2⟩
  have hinj : Function.Injective φ := by
    intro R R' h
    exact Subtype.ext (Gaps.eq_of_map_eq_of_central Ψ hker (hperf R.1 R.2).ge
      (hperf R'.1 R'.2).ge (congrArg Subtype.val h))
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
  exact Gaps.commutes_map_iff hker (hperf R.1 R.2)

theorem e7LayerEquiv_theta (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    ∃ e : {A : Subgroup (TypeE8.K7 p f) //
        A ∈ TypeE8.F7 p f ∧ Commutes A (stdRankOne D₇ thetaE7)} ≃ TypeE8.Fund12 p f,
      ∀ A A', Commutes A.1 A'.1 ↔ Commutes (e A).1 (e A').1 := by
  obtain ⟨Ψ, hker, hrange, hrk⟩ := exists_psi_E7 (p := p) (f := f) (by omega)
  obtain ⟨hsc12, hperf12, hR₀⟩ := fund12_class (p := p) (f := f) hp2 (by omega)
  have hy0 := hrk (y12 p f)
  have hmem : ∀ R ∈ fundamentalSubgroups StatedLieTag.POmegaPlus (M₁₂).D,
      R.map Ψ ∈ fundamentalSubgroups .E7 D₇ := by
    intro R hR
    obtain ⟨m, hm⟩ := hsc12 _ hR₀ R hR
    have h1 : R.map Ψ = conjSub (Ψ m) (rankOne (e7Datum (GaloisField p f)).rootGroup
        (iota7 (y12 p f))) := by
      rw [hm, ← hy0]
      exact (Generic.conjSub_map Ψ m _).symm
    rw [h1]
    exact conjSub_mem_fundamentalSubgroups
      (rankOne_mem_fundamental _ (ModelFacts.isLongestRoot_single .E7 0 p f Fact.out trivial
        ⟨Fact.out, Nat.one_le_iff_ne_zero.2 (by rintro rfl; simp at hq), rfl⟩
        (iota7 (y12 p f)) trivial))
      (Ψ m)
  have hcommθ : ∀ R ∈ fundamentalSubgroups StatedLieTag.POmegaPlus (M₁₂).D,
      Commutes (R.map Ψ) (stdRankOne D₇ thetaE7) := by
    intro R _ x hx y hy
    have := commutes_HJ_theta hp2 hq
    rw [← hrange] at this
    exact this x (Subgroup.map_le_range Ψ R hx) y hy
  have hsurj : ∀ A ∈ fundamentalSubgroups .E7 D₇, Commutes A (stdRankOne D₇ thetaE7) →
      ∃ R ∈ fundamentalSubgroups StatedLieTag.POmegaPlus (M₁₂).D, R.map Ψ = A := by
    intro A hA hAθ
    obtain ⟨h, hh, hAh⟩ := exists_mem_HJ_conj_of_commutes_theta hp2 hq hA hAθ.symm
    rw [← hrange] at hh
    obtain ⟨m, rfl⟩ := hh
    refine ⟨conjSub m (rankOne (M₁₂).D.rootGroup (y12 p f)),
      conjSub_mem_fundamentalSubgroups hR₀ m, ?_⟩
    have h6 : e7Idx 6 = iota7 (y12 p f) := rfl
    rw [hAh, h6, ← hy0]
    exact (Generic.conjSub_map Ψ m _).symm
  exact layer_equiv_of_map Ψ hker hperf12 hmem hcommθ hsurj

theorem layer_equiv_conj {G : Type} [Group G] {F : Set (Subgroup G)}
    (hF : ∀ A ∈ F, ∀ g : G, conjSub g A ∈ F) {Y : Type} {R : Y → Y → Prop} (S : Subgroup G)
    (g : G) (e₀ : {A : Subgroup G // A ∈ F ∧ Commutes A S} ≃ Y)
    (he₀ : ∀ A A', Commutes A.1 A'.1 ↔ R (e₀ A) (e₀ A')) :
    ∃ e : {A : Subgroup G // A ∈ F ∧ Commutes A (conjSub g S)} ≃ Y,
      ∀ A A', Commutes A.1 A'.1 ↔ R (e A) (e A') := by
  have hconj : ∀ A A' : Subgroup G,
      Commutes A A' ↔ Commutes (conjSub g⁻¹ A) (conjSub g⁻¹ A') := by
    intro A A'
    refine ⟨fun h => h.conjSub g⁻¹, fun h => ?_⟩
    have := h.conjSub g
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
  let c : {A : Subgroup G // A ∈ F ∧ Commutes A (conjSub g S)} ≃
      {A : Subgroup G // A ∈ F ∧ Commutes A S} :=
    { toFun := fun A => ⟨conjSub g⁻¹ A.1, hF _ A.2.1 g⁻¹, by
        have := A.2.2.conjSub g⁻¹
        rwa [conjSub_inv_conjSub] at this⟩
      invFun := fun A => ⟨conjSub g A.1, hF _ A.2.1 g, A.2.2.conjSub g⟩
      left_inv := fun A => Subtype.ext (conjSub_conjSub_inv g A.1)
      right_inv := fun A => Subtype.ext (conjSub_inv_conjSub g A.1) }
  refine ⟨c.trans e₀, fun A A' => ?_⟩
  exact (hconj A.1 A'.1).trans (he₀ (c A) (c A'))

theorem e7LayerEquiv (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) : TypeE8.E7LayerEquiv p f := by
  intro T hT
  obtain ⟨hsingle, hRθF, -⟩ := e7_fund_class hp2 hq
  obtain ⟨g, hg⟩ := hsingle _ hRθF T hT
  obtain ⟨e₀, he₀⟩ := e7LayerEquiv_theta hp2 hq
  subst hg
  exact layer_equiv_conj (G := TypeE8.K7 p f) (F := TypeE8.F7 p f)
    (fun A hA g => conjSub_mem_fundamentalSubgroups hA g)
    (R := fun R R' : TypeE8.Fund12 p f => Commutes R.1 R'.1) (stdRankOne D₇ thetaE7) g e₀ he₀

end Psi

end CFSG.ClassicalInvolution.ModelFacts.E7Model
