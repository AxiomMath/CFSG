module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Core

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open scoped commutatorElement

section Bridge

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem normal_coreHull (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    (coreHull Ω c).Normal :=
  ⟨fun n hn g => by
    have := conj_mem_conjSub (n := g) hn
    rwa [conjSub_coreHull hΩ hc2] at this⟩

theorem mem_oddCore_of_mem_oddCore_coreHull (hΩ : HypOmegaGen Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {n : ↥(coreHull Ω c)}
    (hn : n ∈ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    (n : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) := by
  obtain ⟨m, hm, hmn⟩ := oddCore_coreHull_le hΩ hc2 hn
  have : m = (n : ↥(Subgroup.centralizer ({c} : Set G))) :=
    Subtype.ext hmn
  exact this ▸ hm

variable (Ω c) in
@[expose] noncomputable def secMap (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) →* OddQuot c :=
  QuotientGroup.lift (classicalInvolutionOddCore ↥(coreHull Ω c))
    ((oddQuotMk c).comp (coreHull Ω c).subtype) (fun n hn => by
      rw [MonoidHom.mem_ker]
      exact (QuotientGroup.eq_one_iff _).mpr (mem_oddCore_of_mem_oddCore_coreHull hΩ hc2 hn))

theorem secMap_mk (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (h : ↥(coreHull Ω c)) :
    secMap Ω c hΩ hc2 (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h) =
      oddQuotMk c (h : ↥(Subgroup.centralizer ({c} : Set G))) :=
  rfl

theorem secMap_injective (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    Function.Injective (secMap Ω c hΩ hc2) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  set H : Subgroup ↥(Subgroup.centralizer ({c} : Set G)) := coreHull Ω c with hH
  set O := classicalInvolutionOddCore ↥H with hO
  set T : Subgroup ↥H :=
    (classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G))).comap H.subtype with hT
  have hker : (secMap Ω c hΩ hc2).ker ≤ T.map (QuotientGroup.mk' O) := by
    intro y hy
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective O y
    refine ⟨h, ?_, rfl⟩
    have h1 : oddQuotMk c (h : ↥(Subgroup.centralizer ({c} : Set G))) = 1 := hy
    exact (QuotientGroup.eq_one_iff (N := classicalInvolutionOddCore
      ↥(Subgroup.centralizer ({c} : Set G))) (h : ↥(Subgroup.centralizer ({c} : Set G)))).mp h1
  have hTodd : Odd (Nat.card T) := by
    have h1 : Nat.card T = Nat.card (T.map H.subtype) :=
      (Subgroup.card_map_of_injective H.subtype_injective).symm
    have h2 : T.map H.subtype ≤
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({c} : Set G)) := by
      rintro _ ⟨a, ha, rfl⟩
      exact ha
    rw [h1]
    exact (CFSG.ComponentClassification.OddCore.odd_card
      ↥(Subgroup.centralizer ({c} : Set G))).of_dvd_nat (Subgroup.card_dvd_of_le h2)
  have hKodd : Odd (Nat.card (secMap Ω c hΩ hc2).ker) :=
    hTodd.of_dvd_nat ((Subgroup.card_dvd_of_le hker).trans (Subgroup.card_map_dvd T (QuotientGroup.mk' O)))
  have hle : (secMap Ω c hΩ hc2).ker ≤ classicalInvolutionOddCore (↥H ⧸ O) := by
    show _ ≤ sSup _
    exact le_sSup ⟨inferInstance, hKodd⟩
  have hbot : classicalInvolutionOddCore (↥H ⧸ O) = ⊥ := CFSG.ComponentClassification.OddCore.quotient_corefree ↥H
  have := hle (MonoidHom.mem_ker.mpr hx)
  rwa [hbot, Subgroup.mem_bot] at this

variable (Ω c) in
@[expose] noncomputable def secAut (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) :
    (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) ≃*
      (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :=
  haveI := normal_coreHull hΩ hc2
  QuotientGroup.congr (classicalInvolutionOddCore ↥(coreHull Ω c))
    (classicalInvolutionOddCore ↥(coreHull Ω c)) (MulAut.conjNormal g)
    (CFSG.ComponentClassification.OddCore.equiv_invariant (MulAut.conjNormal g))

theorem secAut_mk (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G))) (h h' : ↥(coreHull Ω c))
    (e : (h' : ↥(Subgroup.centralizer ({c} : Set G))) =
      g * (h : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹) :
    secAut Ω c hΩ hc2 g (QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h) =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥(coreHull Ω c)) h' := by
  haveI := normal_coreHull hΩ hc2
  have : h' = MulAut.conjNormal g h := Subtype.ext (by rw [e, MulAut.conjNormal_apply])
  subst this
  exact QuotientGroup.congr_mk' _ _ _ _ h

theorem secMap_secAut (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G)))
    (y : ↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c)) :
    secMap Ω c hΩ hc2 (secAut Ω c hΩ hc2 g y) =
      oddQuotMk c g * secMap Ω c hΩ hc2 y * (oddQuotMk c g)⁻¹ := by
  haveI := normal_coreHull hΩ hc2
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥(coreHull Ω c)) y
  set h' : ↥(coreHull Ω c) := ⟨g * (h : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹,
    this.conj_mem _ h.2 g⟩ with hh'
  rw [secAut_mk hΩ hc2 g h h' rfl, secMap_mk, secMap_mk]
  show oddQuotMk c (g * (h : ↥(Subgroup.centralizer ({c} : Set G))) * g⁻¹) = _
  rw [map_mul, map_mul, map_inv]

theorem oddQuot_centralizes_of_fix (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    (g : ↥(Subgroup.centralizer ({c} : Set G)))
    {L : Subgroup (↥(coreHull Ω c) ⧸ classicalInvolutionOddCore ↥(coreHull Ω c))}
    (hfix : ∀ l ∈ L, secAut Ω c hΩ hc2 g l = l) {y : ↥(coreHull Ω c) ⧸ _} (hy : y ∈ L) :
    oddQuotMk c g * secMap Ω c hΩ hc2 y = secMap Ω c hΩ hc2 y * oddQuotMk c g := by
  have h1 := secMap_secAut hΩ hc2 g y
  rw [hfix y hy] at h1
  calc oddQuotMk c g * secMap Ω c hΩ hc2 y
      = oddQuotMk c g * secMap Ω c hΩ hc2 y * (oddQuotMk c g)⁻¹ * oddQuotMk c g := by group
    _ = secMap Ω c hΩ hc2 y * oddQuotMk c g := by rw [← h1]

end Bridge

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
