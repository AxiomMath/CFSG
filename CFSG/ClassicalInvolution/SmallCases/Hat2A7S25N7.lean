module

public import Mathlib
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N5
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25N6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Hat2A7S.N

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.C25V
  CFSG.ClassicalInvolution.Asc77.C25H CFSG.ClassicalInvolution.Asc77.C25J
  CFSG.ClassicalInvolution.Asc77.C25X CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Asc77.C25I CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Asc77.T3
open CFSG.ClassicalInvolution.Hat2A7M.Asc77.T7F2 (Hyp25T)
open scoped MatrixGroups commutatorElement

section Model


@[expose] def W3Three : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25A7 Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 →
      IsFAut R' a → ¬ FixDiv5 K' a → Iso3 K' a

end Model

section Branches

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}


local notation "Lₐ" => crossIn K' a

theorem typed5_data9 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    (ha2 : a * a = 1) (ha1 : a ≠ 1) {e₀ : ℕ} (hp : p ≠ 2) (h3 : 3 ≤ p ^ e₀)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
    (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
    {a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))}
    (T : TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
          (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀)
    (hO5 : SectionOrthTypeU p e₀ (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 5 true) :
    ∃ t₀ y c₁ : G, C25I.IsSwap K K' z t₀ ∧ a * t₀ = t₀ * a ∧
      (∃ c : G, c * a = a * c ∧ c * z * c⁻¹ = t₀) ∧ c₁ * a = a * c₁ ∧ y ∈ conjSub c₁ K' ∧
      orderOf y = 4 ∧ y * a = a * y ∧ y * (z * t₀) = (z * t₀) * y ∧
      ∀ c : G, c * a = a * c → a * (z * t₀) ≠ c * z * c⁻¹ := by
  classical
  obtain ⟨tg, n, hT, D, hC⟩ := hO5
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨⟨sw, hsw2, hs1, hs2, hs3, ⟨xq, hsx⟩, ⟨x', yq, hyq, hyq4, hyqc⟩⟩, hcen⟩ :=
    twinSwapQ5U hp h3 D hT hC T
  let w : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨t', ht'a⟩
  let ζ : ↥(conjGen Lₐ) := ⟨⟨z, hzA⟩, hzX⟩
  have hLmem : Lₐ ∈ conjFamily Lₐ := ⟨1, conjSub_one _⟩
  have hLX : Lₐ ≤ conjGen Lₐ := le_conjGen hLmem
  have hL'mem : conjSub w Lₐ ∈ conjFamily Lₐ := ⟨w, rfl⟩
  have hL'X : conjSub w Lₐ ≤ conjGen Lₐ := le_conjGen hL'mem
  have hzz : z * z = 1 := h.hz.sq
  have hζ2 : ζ * ζ = 1 := Subtype.ext (Subtype.ext hzz)
  obtain ⟨t₀, ht₀s, ht₀2, ht₀z⟩ :=
    C25I.exists_involution_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hζ2 hsw2 hs1
  obtain ⟨c, hc⟩ := C25I.exists_conj_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hζ2 ht₀2
    (x := xq) (by rw [ht₀s]; exact hsx)
  let φ : ↥(conjGen Lₐ) →* G :=
    (Subgroup.centralizer ({a} : Set G)).subtype.comp (conjGen Lₐ).subtype
  have hφinj : Function.Injective φ :=
    (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  have hφζ : φ ζ = z := rfl
  have hCa : ∀ x : ↥(conjGen Lₐ), φ x * a = a * φ x := fun x =>
    Subgroup.mem_centralizer_singleton_iff.mp (x : ↥(Subgroup.centralizer ({a} : Set G))).2
  obtain ⟨t₀G, ht₀G⟩ : ∃ g : G, g = φ t₀ := ⟨_, rfl⟩
  have ht₀G2 : t₀G * t₀G = 1 := by rw [ht₀G, ← map_mul, ht₀2, map_one]
  have ht₀Gz : t₀G * z = z * t₀G := by rw [ht₀G, ← hφζ, ← map_mul, ← map_mul, ht₀z]
  have hcG : φ c * z * (φ c)⁻¹ = t₀G := by
    rw [ht₀G, ← hc, ← hφζ, map_mul, map_mul, map_inv]
  have hat₀ : a * t₀G = t₀G * a := by rw [ht₀G]; exact (hCa t₀).symm
  have ht₀G' : t₀G = (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) :=
    ht₀G
  have hsw1 : (QuotientGroup.mk t₀ :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = sw := ht₀s
  have ht₀C : t₀G ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [ht₀G]
    exact ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))).2
  have hnotN : conjSub t₀G K ≠ K := by
    intro hN
    have ht'K : conjSub t' K = K' := conjSub_t'_K h
    have hc1 : conjSub (t' * t₀G * t') K' = K' := by
      rw [conjSub_mul, conjSub_mul, conjSub_t'_K' h, hN, ht'K]
    have hcC : t' * t₀G * t' ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ht'a ht₀C) ht'a
    have hfix := conjSub_crossIn_eq (K := K') hcC (mem_normalizer_iff_conjSub_eq.mpr hc1)
    have h1 : conjSub ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
        (conjSub w Lₐ) = conjSub w Lₐ := by
      have e2 : ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) * w =
          w * (⟨t' * t₀G * t', hcC⟩ : ↥(Subgroup.centralizer ({a} : Set G))) := by
        apply Subtype.ext
        change (((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) : G) * t' =
          t' * (t' * t₀G * t')
        rw [← ht₀G']
        calc t₀G * t' = (t' * t') * t₀G * t' := by rw [h.ht'2]; group
          _ = t' * (t' * t₀G * t') := by group
      rw [← conjSub_mul, e2, conjSub_mul, hfix]
    have hsecw : conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ)) =
        secImg (conjGen Lₐ) (conjSub w Lₐ) := by
      have h2 := secAct_secImg (conjGen Lₐ)
        ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) hL'X
      rw [h1] at h2
      calc conjSub sw (secImg (conjGen Lₐ) (conjSub w Lₐ))
          = (secImg (conjGen Lₐ) (conjSub w Lₐ)).map (secAct (conjGen Lₐ)
              ((t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))).toMonoidHom := by
            rw [secAct_of_mem (conjGen Lₐ) (t₀ : ↥(conjGen Lₐ)).2, ← hsw1]
            rfl
        _ = secImg (conjGen Lₐ) (conjSub w Lₐ) := h2
    rw [hsecw] at hs3
    exact T.ne hs3.symm
  have hsw' : conjSub (t₀G * t') K = K := by
    rcases cz_cover h ht₀Gz with h1 | h1
    · exact absurd h1 hnotN
    · exact h1
  have hswK : conjSub t₀G K = K' := by
    have e1 : conjSub t₀G K' = K := by
      have := hsw'
      rwa [conjSub_mul, conjSub_t'_K h] at this
    calc conjSub t₀G K = conjSub t₀G (conjSub t₀G K') := by rw [e1]
      _ = conjSub (t₀G * t₀G) K' := by rw [conjSub_mul]
      _ = K' := by rw [ht₀G2, conjSub_one]
  have hIS : IsSwap K K' z t₀G := ⟨ht₀G2, ht₀Gz, hswK⟩
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk_surjective x'
  have hx₂2 : (ζ * t₀) * (ζ * t₀) = 1 := by
    have h1 := (show Commute ζ t₀ from ht₀z.symm).mul_pow 2
    rw [pow_two, pow_two, pow_two, hζ2, ht₀2, mul_one] at h1
    exact h1
  let M : Subgroup ↥(conjGen Lₐ) :=
    (conjSub ((x₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G))) Lₐ).subgroupOf
      (conjGen Lₐ)
  have hM : ∃ m ∈ M, (QuotientGroup.mk m :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) = yq := by
    rw [← hx₀, C25I.conjSub_mk_secImg (conjGen Lₐ) x₀ hLX] at hyq
    obtain ⟨m, hm, hmy⟩ := hyq
    exact ⟨m, hm, hmy⟩
  have hc' : yq * (QuotientGroup.mk (ζ * t₀) :
      ↥(conjGen Lₐ) ⧸ classicalInvolutionOddCore ↥(conjGen Lₐ)) =
      QuotientGroup.mk (ζ * t₀) * yq := by
    rw [QuotientGroup.mk_mul, ht₀s]
    exact hyqc
  obtain ⟨h₁, y, ⟨m, hmM, hym⟩, hy4, hyx⟩ :=
    C25I.exists_order_four_lift (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hx₂2 M hyq4 hc' hM
  have hmK' : (φ x₀)⁻¹ * φ m * φ x₀ ∈ K' := by
    have h2 := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hmM)
    exact (Subgroup.mem_subgroupOf.mp h2).1
  obtain ⟨c₁G, hc₁G⟩ : ∃ g : G, g = φ h₁ * φ x₀ := ⟨_, rfl⟩
  have hyG : φ y = c₁G * ((φ x₀)⁻¹ * φ m * φ x₀) * c₁G⁻¹ := by
    rw [hym, map_mul, map_mul, map_inv, hc₁G, mul_inv_rev]
    group
  have hyK : φ y ∈ conjSub c₁G K' := by
    rw [hyG]
    exact conj_mem_conjSub hmK'
  have hc₁a : c₁G * a = a * c₁G := by
    rw [hc₁G, mul_assoc, hCa x₀, ← mul_assoc, hCa h₁, mul_assoc]
  have hy4G : orderOf (φ y) = 4 := by rw [orderOf_injective φ hφinj y]; exact hy4
  have hyxG : φ y * (z * t₀G) = (z * t₀G) * φ y := by
    have := congrArg φ hyx
    simp only [map_mul, hφζ] at this
    rw [← ht₀G] at this
    exact this
  have hlast : ∀ c : G, c * a = a * c → a * (z * t₀G) ≠ c * z * c⁻¹ := by
    intro c hca heq
    have hcC : c ∈ Subgroup.centralizer ({a} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hca
    let cY : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨c, hcC⟩
    let aY : ↥(Subgroup.centralizer ({a} : Set G)) :=
      ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    let ζY : ↥(Subgroup.centralizer ({a} : Set G)) := ⟨z, hzA⟩
    let x₂Y : ↥(Subgroup.centralizer ({a} : Set G)) :=
      ((ζ * t₀ : ↥(conjGen Lₐ)) : ↥(Subgroup.centralizer ({a} : Set G)))
    have hrel : aY * x₂Y = cY * ζY * cY⁻¹ := by
      apply Subtype.ext
      change a * φ (ζ * t₀) = c * z * c⁻¹
      rw [map_mul, hφζ, ← ht₀G]
      exact heq
    have hx₂Ymem : x₂Y ∈ conjGen Lₐ := (ζ * t₀ : ↥(conjGen Lₐ)).2
    have haY : aY ∈ conjGen Lₐ := by
      have h1 : aY = (cY * ζY * cY⁻¹) * x₂Y⁻¹ := by
        rw [← hrel]
        group
      rw [h1]
      exact Subgroup.mul_mem _ (hXn.conj_mem _ hzX cY) (Subgroup.inv_mem _ hx₂Ymem)
    let aX : ↥(conjGen Lₐ) := ⟨aY, haY⟩
    have haX1 : aX = 1 :=
      C25I.eq_one_of_central (classicalInvolutionOddCore ↥(conjGen Lₐ)) hOodd hcen
        (fun v => Subtype.ext (Subtype.ext (hCa v))) (Subtype.ext (Subtype.ext ha2))
    apply ha1
    exact congrArg (fun x : ↥(conjGen Lₐ) => ((x : ↥(Subgroup.centralizer ({a} : Set G))) : G))
      haX1
  exact ⟨t₀G, φ y, c₁G, hIS, hat₀, ⟨φ c, hCa c, hcG⟩, hc₁a, hyK, hy4G, hCa y, hyxG, hlast⟩

end Branches

section Branches6

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' a : G}



local notation "Lₐ" => crossIn K' a

theorem false_of_omega6_9 (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t')
    {e₀ : ℕ} (hp : p ≠ 2)
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
    (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
    {a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))}
    (T : TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
          (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀)
    (hO6 : SectionOrthTypeU p e₀ (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 6
      (!piSign p e₀)) : False := by
  classical
  obtain ⟨tg, n, hT, D, hC⟩ := hO6
  have hXn : (conjGen Lₐ).Normal := conjGen_normal _
  have hOodd : Odd (Nat.card (classicalInvolutionOddCore ↥(conjGen Lₐ))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  obtain ⟨τ, y, hτz, hτc, hτ2, hy, hτA, -⟩ := twinCent6U hp D hT hC T
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
  obtain ⟨g, hgc, hgm⟩ := C25G.exists_conj_comm_lift _ hOodd hζ2 y₀ hcomm
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
      have hfix := conjSub_crossIn_eq (K := K') hc''C
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
  exact false_of_conj_normalizer_a7 h hbg hbz hbN

end Branches6

section Typed

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


theorem typed3 (hbelow : Q3.CIT3Below (Nat.card G))
    (h : Hyp25T Ω K K' W S R R' z t u₁ u₂ t') {a : G} (hF' : IsFAut R' a)
    (hat : a * t' = t' * a) (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hL : IsClassicalMemberU (.sl2 3 1) (crossIn K' a) ⟨z, hzA⟩)
    (hlt : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G) :
    ∃ (ht'a : t' ∈ Subgroup.centralizer ({a} : Set G))
      (hzX : (⟨z, hzA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈ conjGen (crossIn K' a))
      (a₀ b₀ : ↥(conjGen (crossIn K' a)) ⧸ classicalInvolutionOddCore ↥(conjGen (crossIn K' a))),
      TwinSect0 (oddQuotientFamily (restrictFamily (conjFamily (crossIn K' a))
          (conjGen (crossIn K' a))))
        (secImg (conjGen (crossIn K' a)) (crossIn K' a))
        (secImg (conjGen (crossIn K' a)) (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) (crossIn K' a)))
        (QuotientGroup.mk ⟨⟨z, hzA⟩, hzX⟩) a₀ b₀ ∧
      (z ∈ zStarOf (Subgroup.centralizer ({a} : Set G)) ∨
        SectionOrthTypeU 3 1 (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 5 true ∨
        SectionOrthTypeU 3 1 (conjFamily (crossIn K' a)) (conjGen (crossIn K' a)) 6
          (!piSign 3 1)) := by
  have hzKa : z ∈ K' ⊓ Subgroup.centralizer ({a} : Set G) := ⟨h.hz'.mem, hzA⟩
  have hΛ : HypOmegaModU (.sl2 3 1) (conjFamily (crossIn K' a)) :=
    crossIn_hypOmegaModU h.hΩ h.hK' h.hz' hzA hL
  obtain ⟨ht'a, hzX, a₀, b₀, T⟩ := crossIn_twinSect0 h hF' hat hzA hΛ
  refine ⟨ht'a, hzX, a₀, b₀, T, ?_⟩
  set L := crossIn K' a with hLdef
  set X := conjGen L with hX
  have hne : (conjFamily L).Nonempty := ⟨L, ⟨1, conjSub_one L⟩⟩
  have hIn : Q3.InClass3 (restrictFamily (conjFamily L) X) := T3CII.inClass3_layer hΛ hne
  have hXC : Nat.card ↥X ≤ Nat.card ↥(Subgroup.centralizer ({a} : Set G)) :=
    Subgroup.card_le_card_group _
  have hquot : Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) ≤ Nat.card ↥X :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
  obtain ⟨ι, -, ⟨D3⟩⟩ := hbelow ↥X (by omega) (restrictFamily (conjFamily L) X) hIn
  have hΦ : HypOmegaModU (.sl2 3 1) (oddQuotientFamily (restrictFamily (conjFamily L) X)) :=
    hypOmegaModU_oddQuotientFamily (hypOmegaModU_restrict hΛ X)
  have hO : classicalInvolutionOddCore (↥X ⧸ classicalInvolutionOddCore ↥X) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥X
  have hA := aEmpty_secFamily hΛ (crossIn_aEmpty h hΛ)
  have h4 : Thm4BelowU 3 1 (Nat.card (↥X ⧸ classicalInvolutionOddCore ↥X) + 1) :=
    thm4BelowU_of_citBelowT ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mpr
      (Q3.CIT3Below.mono (by omega) hbelow))
  rcases classify_sect h4 (Nat.lt_succ_self _) hΦ hO hA (LieSystemDataU.ofQ3 D3) T with
    hall | ⟨D', t₁, k₁, hCI, htags⟩
  · left
    have hu : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        IsUniqueInvolution (conjSub c L) (c * ⟨z, hzA⟩ * c⁻¹) := fun c =>
      crossIn_isUniqueInvolution_conjSub h.hz' hzA hzKa c
    have hconn' : ∀ c : ↥(Subgroup.centralizer ({a} : Set G)),
        secImg X (conjSub c L) = secImg X L ∨
        secImg X (conjSub c L) = secImg X (conjSub (⟨t', ht'a⟩ :
          ↥(Subgroup.centralizer ({a} : Set G))) L) :=
      fun c => hall _ ((mem_secFamily_iff L _).mpr ⟨c, rfl⟩)
    unfold zStarOf
    refine Subgroup.mem_map.mpr ⟨⟨z, hzA⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro g
    obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective g
    exact (central_of_connected L ⟨z, hzA⟩ hu hzX _ T.hzA' hconn' c).symm
  · right
    have hne' : (oddQuotientFamily (restrictFamily (conjFamily L) X)).Nonempty := ⟨_, T.hA⟩
    have hε : (!piSign 3 1) = true := by decide
    rcases htags with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hh | hh | hh | hh
    · left
      exact ⟨.PSp, 2, Or.inl ⟨rfl, rfl, rfl⟩, D', hCI⟩
    · right
      exact ⟨.PSL, 4, Or.inr (Or.inl ⟨rfl, hε, rfl, rfl⟩), D', hCI⟩
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inl hh) (crossIn_nc4_excl h hzA)).elim
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inr (Or.inl hh)) (crossIn_nc4_excl h hzA)).elim
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inr (Or.inr (Or.inl hh)))
        (crossIn_nc4_excl h hzA)).elim
    · exact (false_of_s4_tag hΦ hne' D' hCI (Or.inr (Or.inr (Or.inr hh)))
        (crossIn_nc4_excl h hzA)).elim

end Typed

section Main

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}



theorem a7_false_of_ff3 (h11 : A7C25_11) (hyp : Hyp25A7 Ω K K' W S R R' z t u₁ u₂) {a : G}
    (haS : a ∈ (S : Subgroup G)) (ha2 : a * a = 1) (hFa : IsFAut R a) (hF' : IsFAut R' a)
    (hZ : z ∉ zStarOf (Subgroup.centralizer ({a} : Set G)))
    (hiso : Iso3 K' a) : False := by
  classical
  obtain ⟨t', g, h, hg, hnf, hat⟩ :=
    Hat2A7M.Asc77.C25V.exists_comm_swap_of_ff (Hat2A7S.Eps.c25_11_mirror h11) hyp.toMirror haS ha2
      hFa hF'
  have ha1 : a ≠ 1 := ne_one_of_isFAut_hyp h haS ha2 hF'
  have hp : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : 3 ≤ 3 ^ 1 := by norm_num
  have hzA : z ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (h.hyp.hzS a haS).symm
  have d' := twinCtx'_of_hyp25 h
  have hconj : ∀ y x : G, y ∈ Subgroup.centralizer ({z} : Set G) →
      x ∈ Subgroup.centralizer ({z} : Set G) → conjSub x K' = K' →
        conjSub (y * x * y⁻¹) K' = K' := fun y x hy hx hxK =>
    d'.conj_normalizer (Subgroup.mem_centralizer_singleton_iff.mp hy)
      (Subgroup.mem_centralizer_singleton_iff.mp hx) hxK
  have hL : IsClassicalMemberU (.sl2 3 1) (crossIn K' a) ⟨z, hzA⟩ :=
    crossIn_isClassicalMember h.hz' (C25V.isUniqueInvolution_le_centralizer h.hz') hconj hzA hiso
  have hlt : Nat.card ↥(Subgroup.centralizer ({a} : Set G)) < Nat.card G :=
    fs_card_centralizer_lt (exists_noncomm_of_swap h) ha1
  have hbelow : Q3.CIT3Below (Nat.card G) :=
    (citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp (h.hs.stand.below3 1 (by norm_num))
  obtain ⟨ht'a, hzX, a₀, b₀, T, hcases⟩ := typed3 hbelow h hF' hat hzA hL hlt
  rcases hcases with hz | h5' | h6'
  · exact hZ hz
  · obtain ⟨t₀, y₁, c₁, hsw, hat₀, hcz, hc₁a, hy₁K, hy₁4, hy₁a, hy₁x, hlast⟩ :=
      typed5_data9 h ha2 ha1 hp h3 hzA ht'a hzX T h5'
    exact Hat2A7S.a7_false_of_swap_data h11 h haS ha2 hFa hF' hat hsw hat₀ hcz hc₁a hy₁K hy₁4
      hy₁a hy₁x hlast
  · exact false_of_omega6_9 h hp hzA ht'a hzX T h6'

theorem a7NoFFz3_of_w3 (h11 : A7C25_11) (hW : W3Three) : A7NoFFz3 := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa hFa' hZ hndiv
  exact a7_false_of_ff3 h11 hyp haS ha2 hFa hFa' hZ
    (hW G Ω K K' W S R R' z t u₁ u₂ hyp a haS ha2 hFa' hndiv)

theorem a7NoFFz_of_w3 (h11 : A7C25_11) (h5 : W3Five) (h3 : W3Three) : A7NoFFz :=
  a7NoFFz_of_5_3 (a7NoFFz5_of_w3 h11 h5) (a7NoFFz3_of_w3 h11 h3)

end Main

end CFSG.ClassicalInvolution.Hat2A7S.N
