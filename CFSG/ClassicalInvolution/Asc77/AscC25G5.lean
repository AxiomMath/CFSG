module

public import CFSG.ClassicalInvolution.Asc77.AscC25G1
public import CFSG.ClassicalInvolution.Asc77.AscC25G4
public import CFSG.ClassicalInvolution.Asc77.AscC25V25
public import CFSG.ClassicalInvolution.Asc77.AscC25V38
public import CFSG.ClassicalInvolution.Asc77.AscCX4
public import CFSG.ClassicalInvolution.Asc77.AscS22F
public import CFSG.ClassicalInvolution.Asc77.AscS22G

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25G

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77.C25V
open CFSG.ClassicalInvolution.Asc77.T3
open scoped MatrixGroups commutatorElement

section Proof

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


local notation "Lₐ" => perfectCoreIn K' a

theorem false_of_omega6 (h : T7F2.Hyp25T p f Ω K K' W S R R' z t u₁ u₂ t') (h9 : p ^ f ≠ 9)
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hF' : IsFAut R' a) (hat : a * t' = t' * a)
    {e₀ : ℕ} (h5 : 5 ≤ p ^ e₀) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMember p e₀ (perfectCoreIn K' a) ⟨z, hzA⟩)
    (hO6 : SectionOrthType p e₀ (conjFamily (perfectCoreIn K' a)) (conjGen (perfectCoreIn K' a))
      6 (!piSign p e₀)) : False := by
  classical
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := fs_twinSect0 h h9 haS ha2 hF' hat h5 hzA hL
  obtain ⟨tg, n, hT, D, hcard, i, hi1, hi2⟩ := hO6
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨τ, y, hτz, hτc, hτ2, hy, hτA, -⟩ := twinCent6_proved (p := p) (f := e₀)
    (↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) _ D _ _ _ a₀ b₀ hcard
    ⟨i, by rw [hi1, hi2]; exact hT⟩ T
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ↥(conjGen Lₐ), ζ = ⟨⟨z, hzA⟩, hzX⟩ := ⟨_, rfl⟩
  rw [← hζ] at hy hτc hτz
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := by
    rw [hζ]
    apply Subtype.ext
    apply Subtype.ext
    exact hzz
  obtain ⟨y₀, rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = τ := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hy
  have hcomm : (QuotientGroup.mk (y₀ * ζ * y₀⁻¹) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) * QuotientGroup.mk ζ =
      QuotientGroup.mk ζ * QuotientGroup.mk (y₀ * ζ * y₀⁻¹) := by
    rw [hmk]
    exact hτc
  obtain ⟨g, hgc, hgm⟩ := exists_conj_comm_lift _ hOodd hζ2 y₀ hcomm
  obtain ⟨w, hw⟩ : ∃ w : ↥(conjGen Lₐ), w = g * ζ * g⁻¹ := ⟨_, rfl⟩
  rw [← hw] at hgc hgm
  have hwτ : (QuotientGroup.mk w :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = τ := by
    rw [hgm]
    exact hmk
  let φ : ↥(conjGen Lₐ) →* G :=
    (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjGen Lₐ).subtype
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hφζ : φ ζ = z := by
    rw [hζ]
    rfl
  have hbC : φ w ∈ Subgroup.centralizer ({a} : Set G) :=
    (w : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hba : φ w * a = a * φ w := Subgroup.mem_centralizer_singleton_iff.mp hbC
  have hbc : φ w * z = z * φ w := by
    have := congrArg φ hgc
    rw [map_mul, map_mul, hφζ] at this
    exact this
  have hbg : φ w = φ g * z * (φ g)⁻¹ := by
    rw [hw, map_mul, map_mul, map_inv, hφζ]
  have hbz : φ w ≠ z := by
    intro hbz
    apply hτz
    have hwζ : w = ζ := hφinj (hbz.trans hφζ.symm)
    rw [← hwτ, hwζ]
  have hbK' : conjSub (φ w) K' = K' := by
    rcases cz_conj_K' h hbc with h1 | h1
    · exfalso
      have hc''C : t' * φ w ∈ Subgroup.centralizer ({a} : Set G) :=
        Subgroup.mul_mem _ ht'a hbC
      have hc''K' : conjSub (t' * φ w) K' = K' := by
        rw [conjSub_mul, h1, conjSub_t'_K h]
      have hfix := conjSub_perfectCoreIn_eq (K := K') hc''C
        (mem_normalizer_iff_conjSub_eq.mpr hc''K')
      have e2 : (w : ↥(Subgroup.centralizer ({a} : Set G))) =
          (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨t' * φ w, hc''C⟩ := by
        apply Subtype.ext
        change φ w = t' * (t' * φ w)
        calc φ w = (t' * t') * φ w := by rw [h.ht'2, one_mul]
          _ = t' * (t' * φ w) := by group
      have hbL : conjSub (w : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ =
          conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ := by
        rw [e2, conjSub_mul, hfix]
      have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
      have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
      have h2 := secAct_secImg (conjGen Lₐ) (w : ↥(Subgroup.centralizer ({a} : Set G))) hLX
      rw [hbL] at h2
      have hsecτ : conjSub τ (secImg (conjGen Lₐ) Lₐ) = secImg (conjGen Lₐ)
          (conjSub (⟨t', ht'a⟩ : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ) := by
        rw [← h2, secAct_of_mem (conjGen Lₐ) (w : ↥(conjGen Lₐ)).2, ← hwτ]
        rfl
      exact T.ne (hτA.symm.trans hsecτ)
    · exact h1
  have hbN : φ w ∈ Subgroup.normalizer (K' : Set G) := mem_normalizer_iff_conjSub_eq.mpr hbK'
  exact false_of_conj_normalizer' h haS ha2 hF' hbg hbz hba hbN

theorem g1Omega6_proved : G1Omega6 p f := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ t' h h9 a haS ha2 hF' hat e₀ h5 hzA hL hO6 hp hq e d hdK
    hdz hda hd'
  exact (false_of_omega6 h h9 haS ha2 hF' hat h5 hzA hL hO6).elim

end Proof

end CFSG.ClassicalInvolution.Asc77.C25G
