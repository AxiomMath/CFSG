module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36L4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36U4Twin
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7L4EUType

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.HarrisLit.Hin CFSG.ComponentClassification.RestrictedStd
open GrSLit.L34Facts

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

theorem eq_of_psu4 (h : Config G p m τ K) {k : ℕ}
    (hL : Blueprint.LieModel (G ⧸ center G) .PSU 4 p k) : m = 2 * k := by
  classical
  have := h.simple_bar
  have hnab := h.nonabelian_bar
  have := finite_mulAut (Y := G ⧸ center G)
  obtain ⟨eW, hWn, -, -, hWC, -⟩ := autSocle hnab
  have := hWn
  have hZ : center (G ⧸ center G) = ⊥ := CatLeaf.center_eq_bot_of_simple hnab
  have hF := CatLeaf.generalizedFitting_mulAut_eq_range hnab
  have he : 1 ≤ k := (admissible_of_lieModel' hL).2.1
  obtain ⟨-, Kf, _, _, hKf, ⟨φ₀⟩⟩ :=
    LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
  have hud : UnitaryFieldData p k Kf := ⟨h.prime, he, by rw [hKf, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨h.prime⟩
  let φ : ↥(generalizedFitting (MulAut (G ⧸ center G))) ≃* StatedProj (StatedSU 4 (p ^ k) Kf) :=
    eW.symm.trans φ₀
  have hZP : center (StatedProj (StatedSU 4 (p ^ k) Kf)) = ⊥ := by
    rw [← Subgroup.map_center_eq φ₀, hZ, Subgroup.map_bot]
  obtain ⟨ρ, hinj, hρW, -, -⟩ := OutcomeLocal.socle_extension hWC φ hZP
  set σ := quotAut τ with hσ
  set Kb := K.map (QuotientGroup.mk' (center G)) with hKb
  set X := Kb.map (MulAut.conj : G ⧸ center G →* MulAut (G ⧸ center G)) with hX
  have hcj := conj_injective_of_center hZ
  have hKc := h.isTwoComponentIn_bar
  have hconj : ∀ c ∈ fixedPoints σ, ∀ l ∈ Kb, c * l * c⁻¹ ∈ Kb := by
    intro c hc l hl
    have h1 := h.bar_normal.conj_mem ⟨l, hKc.1 hl⟩ (by rw [mem_subgroupOf]; exact hl) ⟨c, hc⟩
    rw [mem_subgroupOf] at h1
    exact h1
  have hXt := isTwoComponentIn_map_conj_of_normal hZ hKc hconj
  have hXF : X ≤ generalizedFitting (MulAut (G ⧸ center G)) := hF ▸ map_le_range _ _
  have hXp : IsPComponent 2 (X.subgroupOf (centralizer ({σ} : Set (MulAut (G ⧸ center G))))) :=
    (isTwoComponentIn_iff hXt.1).mp hXt
  have hXm : Blueprint.LieModel (↥X ⧸ pPrimeCore 2 ↥X) .PSL 2 p m :=
    GSThmB.OddQuot.lieModel_of_equiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (Kb.equivMapOfInjective _ hcj)) h.lieModel_bar
  have h5 : 5 ≤ p ^ m := by have := h.seven_le; omega
  obtain ⟨hcore, hXq, -⟩ := GSThmB.Catalog7L4EU.psu4_component_type hud hWC h.ne_two φ hinj hρW
    hZP h.orderOf_bar hXF hXt.1 hXp h.prime h.ne_two h5 hXm
  have hZodd : Odd (Nat.card (center X)) := by
    rw [← hcore]
    have h' := (pPrimeCore_coprime_card (p := 2) (G := X))
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at h'
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h')
  have hXmZ : Blueprint.LieModel (X ⧸ center X) .PSL 2 p m :=
    LieType.CurtisTits.lieModel_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hcore) hXm
  have hXC : Assembly.IsComponentOf X (centralizer ({σ} : Set (MulAut (G ⧸ center G)))) :=
    ⟨hXt.1, (assembly_isSubnormal_iff hXt.1).mpr hXt.2.1,
      (AssemblyBPredicates.isQuasisimple_iff_native _).mpr hXq⟩
  have hsX : SmallSource X := Or.inl ⟨p, m, h.prime, h.ne_two, h.one_le, h5, hXmZ, hZodd⟩
  obtain ⟨-, -, hCW, hL₁⟩ := OddSelector.socle_images φ hinj hρW hXF hXC
  have hcjP := OddClassSelector.conj_injective hZP
  obtain ⟨hX', hX'map⟩ := OddClassSelector.isComponentOf_comap_conj hcjP hL₁
  let eXX' : X ≃* (X.map ρ).comap MulAut.conj :=
    (X.equivMapOfInjective ρ hinj).trans ((MulEquiv.subgroupCongr hX'map.symm).trans
      (((X.map ρ).comap MulAut.conj).equivMapOfInjective _ hcjP).symm)
  have hsX' : SmallSource ((X.map ρ).comap MulAut.conj) :=
    OddClassSelector.smallSource_of_mulEquiv eXX' hsX
  have hcardrel : ∀ (F₀ : Type) [Field F₀] [Finite F₀], Odd (Nat.card F₀) →
      Nonempty (((X.map ρ).comap MulAut.conj) ⧸ center ((X.map ρ).comap MulAut.conj) ≃*
        GorensteinWalter.PSL2 F₀) → p ^ m = Nat.card F₀ := by
    intro F₀ _ _ hF₀ ⟨eP⟩
    exact GSThmB.Catalog7L4EU.eq_card_of_quotient_psl2 h.prime h.ne_two hXm hF₀
      ((QuotientGroup.quotientMulEquivOfEq hcore).trans
        ((GSThmB.Catalog7L4EU.centerQuotientCongr eXX').trans eP))
  have hsq : ∀ n : ℕ, p ^ m = n → n = (p ^ k) ^ 2 → m = 2 * k := by
    intro n h1 h2
    rw [h2, ← pow_mul, mul_comm] at h1
    exact Nat.pow_right_injective h.prime.two_le h1
  have hα : ∀ y, ρ σ (ρ σ y) = y := by
    intro y
    have hx2 : σ * σ = 1 := by rw [← pow_two, ← h.orderOf_bar, pow_orderOf_eq_one]
    rw [← MulAut.mul_apply, ← map_mul, hx2, map_one, MulAut.one_apply]
  have hρx1 : ρ σ ≠ 1 := by
    intro h1
    have hx1 : σ = 1 := hinj (h1.trans (map_one ρ).symm)
    have h2 := h.orderOf_bar
    rw [← hσ, hx1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have : Finite Kf := hud.finite
  obtain ⟨A, ψ, hAu, hψ, hcase⟩ := GSThmB.Catalog7U4.exists_lift hud h.ne_two (ρ σ) hα
  have hKodd : Odd (Nat.card Kf) := by
    rw [hud.card_eq_sq]
    exact ((h.prime.odd_of_ne_two h.ne_two).pow).pow
  have hk₀odd : Odd (Nat.card hud.fixedField) := by
    rw [hud.card_fixedField]
    exact (h.prime.odd_of_ne_two h.ne_two).pow
  rcases hcase with ⟨hψA, c₀, hAA⟩ | ⟨hψA, z, hAA⟩
  · obtain ⟨⟨eP⟩, -⟩ :=
      GSThmB.Catalog7L4EU.psu4_inner_case hud h.ne_two hρx1 hX' hsX' hAu hψ hψA hAA
    exact hsq _ (hcardrel Kf hKodd ⟨eP⟩) hud.card_eq_sq
  rcases GSThmB.Catalog7L4EU.HarrisN36.psu4_anti_twin hud h.ne_two hX' hsX' hAu hψ hψA hAA with
    ⟨X₂, hX₂, hne, hev⟩ | ⟨E', _, _, hE', ⟨eP⟩⟩
  · exfalso
    have hJ : Assembly.IsComponentOf (X₂.map MulAut.conj)
        (OuterAutomorphisms.inner (StatedProj (StatedSU 4 (p ^ k) Kf)) ⊓ centralizer {ρ σ}) := by
      have h1 := SymmetricLocal.isComponentOf_map_of_injective MulAut.conj hcjP hX₂
      rwa [OddClassSelector.map_conj_fixedSubgroup hcjP] at h1
    refine h.false_of_twin hinj hF hCW hJ (by rw [Subgroup.card_map_of_injective hcjP]; exact hev)
      fun heq => hne (Subgroup.map_injective hcjP ?_)
    rw [heq, hX'map]
  · exact hsq _ (hcardrel E' (by rw [hE']; exact hk₀odd.pow) ⟨eP⟩) (by
      rw [hE', hud.card_fixedField])

end Config

theorem l4U4PartialCoverFact_holds : L4U4PartialCoverFact := by
  intro G _ _ hq hO hns p k hp hp2 hL hM τ hτ m hm h16 K hK hu hLK
  have hc : Config G p m τ K := ⟨hq, hO, hp, hp2, hτ, hm, h16, hK, hu, hLK, hns, hM⟩
  rcases hL with hL | hL
  · exact hc.eq_of_psl4 hL
  · exact hc.eq_of_psu4 hL

end CFSG.ComponentClassification.HarrisLit.N36
