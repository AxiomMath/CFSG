module

public import CFSG.ClassicalInvolution.Q3.TL3GlueJ
public import CFSG.ClassicalInvolution.Q3.TL3GlueLie

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Conj

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem conjClass_conjSub (g : Y) (K : Subgroup Y) :
    CoreAssembly.conjClass (conjSub g K) = CoreAssembly.conjClass K := by
  ext X
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, conjSub_mul h g K⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    show conjSub (h * g⁻¹) (conjSub g K) = conjSub h K
    rw [conjSub_mul, conjSub_inv_conjSub]

omit [Finite Y] in
theorem TightCls.conj (hc : TightCls Y R S t) (g : Y) {S' : Sylow 2 ↥(conjSub g R)}
    (e : (S' : Subgroup ↥(conjSub g R)) ≃* (S : Subgroup R)) :
    TightCls Y (conjSub g R) S' (g * t * g⁻¹) := by
  obtain ⟨⟨e8⟩, hgen, hO⟩ := hc
  refine ⟨⟨e.trans e8⟩, ?_, hO⟩
  have key : (⨆ h : Y, conjSub h (conjSub g (tightCore R))) =
      ⨆ h : Y, conjSub h (tightCore R) := by
    apply le_antisymm
    · refine iSup_le fun h => ?_
      rw [← conjSub_mul]
      exact le_iSup (fun h : Y => conjSub h (tightCore R)) (h * g)
    · refine iSup_le fun h => ?_
      have e1 : conjSub h (tightCore R) = conjSub (h * g⁻¹) (conjSub g (tightCore R)) := by
        rw [conjSub_mul, conjSub_inv_conjSub]
      rw [e1]
      exact le_iSup (fun h : Y => conjSub h (conjSub g (tightCore R))) (h * g⁻¹)
  show (⨆ h : Y, conjSub h (tightCore (conjSub g R))) = ⊤
  rw [← conjSub_tightCore R g, key]
  exact hgen

omit [Finite Y] in
theorem not_tightInO2_conj (h : ¬ TightInO2 t) (g : Y) : ¬ TightInO2 (g * t * g⁻¹) := by
  rintro ⟨P, hPn, hP2, hP⟩
  apply h
  refine ⟨P, hPn, hP2, ?_⟩
  have := hPn.conj_mem _ hP g⁻¹
  simpa [mul_assoc] using this

theorem TightDatum.card_dbar_lt (hd : TightDatum R S t) (hE2 : ¬ TightInO2 t) :
    Nat.card hd.Dbar < Nat.card Y := by
  have h1 : Nat.card hd.Dbar ≤ Nat.card ↥hd.act.ker :=
    Nat.card_le_card_of_surjective hd.toDbar (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥hd.act.ker ≤ Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) :=
    Subgroup.card_le_card_group _
  have h3 : Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) ≤ Nat.card Y :=
    Subgroup.card_le_card_group _
  have hne : Subgroup.centralizer ({t} : Set Y) ≠ ⊤ := by
    intro htop
    apply hE2
    have hcen : ∀ g : Y, g * t = t * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    have htc : t ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr hcen
    have hle : Subgroup.zpowers t ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr htc
    refine ⟨Subgroup.zpowers t, ⟨fun n hn g => ?_⟩, ?_, Subgroup.mem_zpowers t⟩
    · have hgn : g * n = n * g := Subgroup.mem_center_iff.mp (hle hn) g
      rw [hgn, mul_inv_cancel_right]
      exact hn
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order, pow_one])
  have h4 : Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) ≠ Nat.card Y :=
    fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h)
  omega

end Conj

section Cit3


@[expose] def TightEdgeSectionGood (n : ℕ) : Prop :=
  CIT3Below n → TightBelow n → ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y = n →
    ∀ (R : Subgroup Y) (S : Sylow 2 R) (t : Y), TightDatum R S t → TightCls Y R S t →
      ¬ TightInO2 t → TightFStarQuasisimple Y →
        ¬ TwoSubgroupsFourGenerated (genFittingFStar Y) →
          ∀ J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R), ∀ u : Y,
            IsUniqueInvolution J u → ∀ (htu : t ∈ Subgroup.centralizer ({u} : Set Y)),
              GoodThreeElement (R.subgroupOf (Subgroup.centralizer ({u} : Set Y))) (⟨t, htu⟩ : _)

theorem tightLargeLift_of_edgeSection (h : ∀ n, TightEdgeSectionGood n) :
    ∀ n, TightLargeLift n := by
  intro n hA hB Y _ _ hn R S t hd hc hE2 hQ hlarge hedge
  have hΩ := hd.hypOmegaGen
  have huniq := hd.isUniqueInvolution_core
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨J, hJ⟩ := hd.nonempty_omegaNbr_of_not_dEdgeless hedge
  obtain ⟨u, hu⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨-, hu2, hut, htu, huK, T, hTJ, -, hTc, hTD⟩ := hd.edge_involution hJ hu
  have hg1 := h n hA hB Y hn R S t hd hc hE2 hQ hlarge J hJ u hu htu
  obtain ⟨g, hgJ'⟩ := hJ.1
  have hgJ : conjSub g (tightCore R) = J := hgJ'
  have hJcore : tightCore (conjSub g R) = J := by rw [← conjSub_tightCore, hgJ]
  have hgu : g * t * g⁻¹ = u := by
    have h1 := huniq.conj g
    rw [hgJ] at h1
    exact h1.eq hu
  obtain ⟨SJ, hdJ, ⟨eJ⟩⟩ := hd.conj g
  rw [hgu] at hdJ
  have hcJ : TightCls Y (conjSub g R) SJ u := by
    have := hc.conj g eJ
    rwa [hgu] at this
  have hE2J : ¬ TightInO2 u := by
    have := not_tightInO2_conj hE2 g
    rwa [hgu] at this
  have hJΩ : J ∈ CoreAssembly.conjClass (tightCore R) := hJ.1
  have hKJ : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J :=
    Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hK hJΩ hJ
  have hfam : CoreAssembly.conjClass (tightCore (conjSub g R)) =
      CoreAssembly.conjClass (tightCore R) := by
    rw [← conjSub_tightCore, conjClass_conjSub]
  have hKJ' : tightCore R ∈ omegaNbr (CoreAssembly.conjClass (tightCore (conjSub g R)))
      (tightCore (conjSub g R)) := by
    rw [hfam, hJcore]
    exact hKJ
  obtain ⟨-, -, htu', -, -, T', hT'K, -, hT'c, hT'D⟩ := hdJ.edge_involution hKJ' huniq
  have hg2 := h n hA hB Y hn (conjSub g R) SJ u hdJ hcJ hE2J hQ hlarge _ hKJ' t huniq hut
  have hTJ' : IsSylow2In T (tightCore (conjSub g R)) := hJcore ▸ hTJ
  obtain ⟨L, hL⟩ := hd.exists_member_dbar hdJ hut huK hTJ' hTc hTD hT'K hT'c hT'D hg2
  have hcard : Nat.card hd.Dbar + 1 ≤ n := by
    have := hd.card_dbar_lt hE2
    omega
  exact hd.good_of_section_member (CIT3Below.mono hcard hA) hut huK hu2 htu hg1 hL

end Cit3

end CFSG.ClassicalInvolution.Q3
