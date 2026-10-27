module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25X3
public import CFSG.ClassicalInvolution.Asc77.AscCX8E

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X

open CFSG.ClassicalInvolution.Asc77.C25W (InFour mem_zStarOf_centralizer_conj_iff good_of_mem_zpowers
  exists_sq_mem_mod exists_conj_ge_sylow)
open CFSG.ClassicalInvolution.Asc77.C25Y (mem_closure_pair)
open CFSG.Open (classicalInvolutionOddCore fusionStronglyClosed)
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q8P.Asc77.P25R
  CFSG.ClassicalInvolution.Q8P.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
open scoped commutatorElement


section Mixed

variable {G : Type} [Group G] [Finite G] [CoreLike G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ : G}

theorem exists_badCompl_of_bad (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp) {a : G}
    (haA : a ∈ cA S R R') (ha2 : a * a = 1) (ha1 : a ≠ 1) (haz : a ≠ z)
    (hconj : ∀ s ∈ (S : Subgroup G), s * a * s⁻¹ = a ∨ s * a * s⁻¹ = a * z) {y : G}
    (hyA : y ∈ cA S R R') (hya : y * a = a * y) (hy2 : InFour a z (y * y))
    (hyc : ∀ s ∈ (S : Subgroup G), InFour a z (s * y * s⁻¹ * y⁻¹)) (hyV : ¬ InFour a z y) {b : G}
    (hbA : b ∈ cA S R R') (hb1 : b ≠ 1) (hbbad : BadElt z b) :
    ∃ D : Subgroup G, D ≤ cA S R R' ∧ b ∈ D ∧ BadSub z D ∧ ∀ g ∈ cA S R R', g ∈ D ∨ g * z ∈ D := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hz1 : z ≠ 1 := hyp.std.setting.hz.ne_one
  have hD₀A : Subgroup.zpowers b ≤ cA S R R' := Subgroup.zpowers_le.mpr hbA
  have hD₀bad : BadSub z (Subgroup.zpowers b) := (badSub_zpowers_iff z b).mpr hbbad
  have hD₀1 : Subgroup.zpowers b ≠ ⊥ := by
    intro h
    apply hb1
    have : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rwa [h, Subgroup.mem_bot] at this
  have hsmall : Nat.card (Subgroup.zpowers b) < 4 → ∃ x ∈ cA S R R', x ∉ Subgroup.zpowers b ∧
        x * z ∉ Subgroup.zpowers b ∧ (∀ d ∈ Subgroup.zpowers b, x * d = d * x) ∧
        (x * x ∈ Subgroup.zpowers b ∨ x * x * z ∈ Subgroup.zpowers b) := by
    intro hlt
    have hb2 : b * b = 1 := by
      have h2 : IsPGroup 2 (Subgroup.zpowers b) :=
        S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hbA.1)
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      rw [Nat.card_zpowers] at hn hlt
      have hn1 : n ≤ 1 := by
        by_contra h
        push Not at h
        have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
        omega
      have hdvd : orderOf b ∣ 2 ^ 1 := by
        rw [hn]
        exact Nat.pow_dvd_pow 2 hn1
      have h := orderOf_dvd_iff_pow_eq_one.mp hdvd
      rwa [pow_one, pow_two] at h
    obtain ⟨x, hxset, hx1, hxb, hxz1, hxzb, hxbc, hxx⟩ := CX.exists_witness_of_ext hz2 hz1
      hyp.hzS haA.1 ha2 ha1 haz hconj hyA.1 hya hy2 hyc hyV hbA.1 hb2
    have hxA : x ∈ cA S R R' := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxset
      rcases hxset with rfl | rfl | rfl
      · exact haA
      · exact hyA
      · exact Subgroup.mul_mem _ hyA haA
    have hmem : ∀ g ∈ Subgroup.zpowers b, g = 1 ∨ g = b := fun g hg =>
      mem_zpowers_of_sq hb2 hg
    refine ⟨x, hxA, ?_, ?_, ?_, ?_⟩
    · intro h
      rcases hmem x h with h | h
      · exact hx1 h
      · exact hxb h
    · intro h
      rcases hmem _ h with h | h
      · exact hxz1 h
      · exact hxzb h
    · intro d hd
      rcases hmem d hd with rfl | rfl
      · simp
      · exact hxbc
    · rcases hxx with h | h | h | h
      · left
        rw [h]
        exact one_mem _
      · left
        rw [h]
        exact Subgroup.mem_zpowers b
      · right
        rw [h, hz2]
        exact one_mem _
      · right
        rw [h, mul_assoc, hz2, mul_one]
        exact Subgroup.mem_zpowers b
  obtain ⟨D, hDA, hD₀D, hDbad, hcov⟩ := exists_bad_complement hyp hQ hD₀A hD₀bad hD₀1 hsmall
  exact ⟨D, hDA, hD₀D (Subgroup.mem_zpowers b), hDbad, hcov⟩

theorem false_of_stronglyClosed_G (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp)
    {N D₁ : Subgroup G} (hNA : N ≤ cA S R R') (hND₁ : N ≤ D₁) (hD₁A : D₁ ≤ cA S R R')
    (hD₁bad : BadSub z D₁) (hN1 : N ≠ ⊥) (hsc : fusionStronglyClosed (N : Set G) (S : Subgroup G)) :
    False := by
  classical
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hΩ : HypOmegaGen Ω := hyp.std.1.stand.hyp
  have hN2 : IsPGroup 2 N := S.isPGroup'.to_le (hNA.trans inf_le_left)
  obtain ⟨b, hbN, hb1, hb2, hbc⟩ := CX.exists_central_involution (E := N) (B := N) hN2 le_rfl
    Subgroup.le_normalizer hN1
  have hbA : b ∈ cA S R R' := hNA hbN
  have hbbad : BadElt z b := badElt_of_mem hD₁A hyp hD₁bad (hND₁ hbN)
  have hQb := hQ hbA hb2 hb1 hbbad
  have hb2' : IsPGroup 2 (Subgroup.zpowers b) := isPGroup_zpowers_of_sq_eq_one hb2
  have hNb : N ≤ Subgroup.centralizer ({b} : Set G) := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hbc e he)
  have hNY : ∀ e ∈ N, conjSub e (TwinDisc.coreLayer Ω b) = TwinDisc.coreLayer Ω b := fun e he =>
    TwinDisc.conjSub_coreLayer hΩ hb2' (hNb he)
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (MulAut (↥(TwinDisc.coreLayer Ω b) ⧸
      classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b))),
      L = (N.subgroupOf (Subgroup.centralizer ({b} : Set G))).map (actOf hyp hb2) := ⟨_, rfl⟩
  have hmemL : ∀ e (he : e ∈ N), actOf hyp hb2 ⟨e, hNb he⟩ ∈ L := fun e he =>
    hL ▸ Subgroup.mem_map.mpr ⟨⟨e, hNb he⟩, Subgroup.mem_subgroupOf.mpr he, rfl⟩
  have hLle : L ≤ ((cA S R R').subgroupOf (Subgroup.centralizer ({b} : Set G))).map
      (actOf hyp hb2) := by
    rw [hL]
    exact Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hNA (Subgroup.mem_subgroupOf.mp hx)))
  have hzY := hQb.zY
  have hLconj : MulAut.conj (QuotientGroup.mk ⟨z, hzY⟩ :
      ↥(TwinDisc.coreLayer Ω b) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b)) ∉ L := by
    rw [hL]
    rintro ⟨e', he', he'z⟩
    have hm : (e' : G) ∈ N := Subgroup.mem_subgroupOf.mp he'
    apply hD₁bad
    have hzC : z ∈ Subgroup.centralizer (D₁ : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun g hg => hzS g (hD₁A hg).1
    refine mem_zStarOf_of_layerAut_eq_conj (d := (e' : G)) (H := Subgroup.centralizer (D₁ : Set G))
      (fun h hh => TwinDisc.conjSub_coreLayer hΩ hb2'
        (Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hh) b (hND₁ hbN)).symm))
      (fun h hh => ((Subgroup.mem_centralizer_iff.mp hh) (e' : G) (hND₁ hm)).symm) hzC
      (TwinDisc.conjSub_coreLayer hΩ hb2' e'.2) hzY hQb.center ?_
    intro y
    have := congrArg (fun φ => φ y) he'z
    simpa [actOf_apply, MulAut.conj_apply] using this
  have hns := hQb.nonsolv L hLle hLconj
  let f : ↥(TwinDisc.coreLayer Ω b ⊓ Subgroup.centralizer (N : Set G)) →*
      ↥(TwinDisc.coreLayer Ω b) ⧸ classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b) :=
    (QuotientGroup.mk' (classicalInvolutionOddCore ↥(TwinDisc.coreLayer Ω b))).comp
      (Subgroup.inclusion (inf_le_left : TwinDisc.coreLayer Ω b ⊓ Subgroup.centralizer (N : Set G) ≤ TwinDisc.coreLayer Ω b))
  have hfix : fixOf L ≤ f.range := by
    intro x hx
    obtain ⟨y, hy, hyC, hyx⟩ := exists_mem_inf_centralizer_fixed hN2 hNY (x := x)
      (fun e he => hx (actOf hyp hb2 ⟨e, hNb he⟩) (hmemL e he))
    refine ⟨⟨y, hy, hyC⟩, ?_⟩
    exact hyx
  haveI : IsSimpleGroup ↥(genFittingFStar G) := CoreLike.fstar_simple
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer (N : Set G)) :=
    CFSG.ClassicalInvolution.Q3.isSolvable_centralizer_of_stronglyClosed_fstar CoreLike.fstar_nonab CoreLike.oddCore_eq_bot S
      (hNA.trans inf_le_left) hN1 hsc
  have hsolvM : Group.IsSolvable ↥(TwinDisc.coreLayer Ω b ⊓ Subgroup.centralizer (N : Set G)) :=
    solvable_of_solvable_injective (f := Subgroup.inclusion
      (inf_le_right : TwinDisc.coreLayer Ω b ⊓ Subgroup.centralizer (N : Set G) ≤
        Subgroup.centralizer (N : Set G)))
      (Subgroup.inclusion_injective _)
  have hsolvR : Group.IsSolvable ↥f.range := solvable_of_surjective f.rangeRestrict_surjective
  exact hns (solvable_of_solvable_injective (f := Subgroup.inclusion hfix)
    (Subgroup.inclusion_injective _))

theorem false_of_mixedClosed (hyp : Hyp25 Ω K K' W S R R' z t u₁ u₂) (hQ : QTFAt hyp) (hSqL : SqZLAt hyp)
    {N D₁ : Subgroup G} (hNA : N ≤ cA S R R') (hN1 : N ≠ ⊥) (hND₁ : N ≤ D₁) (hD₁A : D₁ ≤ cA S R R')
    (hD₁bad : BadSub z D₁)
    (hsc : ∀ n ∈ N, ∀ c : G, c * z * c⁻¹ = z → c * n * c⁻¹ ∈ (S : Subgroup G) → c * n * c⁻¹ ∈ N)
    (hbad : ∀ n ∈ N, n ≠ 1 → BadElt z n)
    (hgood : ∀ n ∈ N, n ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({n * z} : Set G))) : False := by
  by_cases hG : fusionStronglyClosed (N : Set G) (S : Subgroup G)
  · exact false_of_stronglyClosed_G hyp hQ hNA hND₁ hD₁A hD₁bad hN1 hG
  · unfold fusionStronglyClosed at hG
    push Not at hG
    obtain ⟨a, haN, g, hgS, hgN⟩ := hG
    obtain ⟨e, heN, -, g', htC, htz, hnc⟩ := CX.exists_placed (S := S) hyp.hzS
      hyp.std.setting.hz.sq (hNA.trans inf_le_left) hsc haN (k := g⁻¹)
      (by simpa using hgS) (by simpa using hgN)
    obtain ⟨h, hhC, hh⟩ := goodFusion_of_placed hyp hQ hSqL hNA hsc hbad hgood heN htC htz
    exact hnc h hhC hh

theorem centExtMix_of (hQ : P25X_QTF) (hSqL : P25X_SqZL) : CentExtMix := by
  intro G _ _ _ Ω K K' W S R R' z t u₁ u₂ hyp a haA ha2 ha1 haz hconj hbad y hyA hya hy2 hyc hmix
  have hQ' : QTFAt hyp := hQ G Ω K K' W S R R' z t u₁ u₂ hyp
  have hSqL' : SqZLAt hyp := hSqL G Ω K K' W S R R' z t u₁ u₂ hyp
  by_contra hyV
  obtain ⟨x, hxA, hxz, -, hxgood⟩ := hmix
  have hz2 : z * z = 1 := hyp.std.setting.hz.sq
  have hzS : ∀ s ∈ (S : Subgroup G), s * z = z * s := hyp.hzS
  have hzA : z ∈ cA S R R' := (z_facts hyp).1
  set A : Subgroup G := cA S R R' with hA
  set 𝒟 : Set (Subgroup G) := {D | D ≤ A ∧ BadSub z D ∧ ∀ g ∈ A, g ∈ D ∨ g * z ∈ D} with h𝒟
  set N : Subgroup G := A ⊓ ⨅ D ∈ 𝒟, D with hN
  have hmemN : ∀ g, g ∈ N ↔ g ∈ A ∧ ∀ D ∈ 𝒟, g ∈ D := by
    intro g
    simp only [hN, Subgroup.mem_inf, Subgroup.mem_iInf]
  obtain ⟨D₁, hD₁A, -, hD₁bad, hD₁cov, -⟩ :=
    exists_bad_complement_of_ext hyp hQ' haA ha2 ha1 haz hbad hyA hya hy2 hyV
  have hD₁ : D₁ ∈ 𝒟 := ⟨hD₁A, hD₁bad, hD₁cov⟩
  have hzD : ∀ D ∈ 𝒟, z ∉ D := fun D hD => notMem_of_badSub hD.1 hyp hD.2.1
  have hbadD : ∀ D ∈ 𝒟, ∀ g ∈ D, g ≠ 1 → BadElt z g :=
    fun D hD g hg _ => badElt_of_mem hD.1 hyp hD.2.1 hg
  have hNA : N ≤ A := inf_le_left
  have hND : ∀ D ∈ 𝒟, N ≤ D := fun D hD g hg => ((hmemN g).mp hg).2 D hD
  have hxN : x ∈ N := by
    refine (hmemN x).mpr ⟨hxA, fun D hD => ?_⟩
    rcases hD.2.2 x hxA with h | h
    · exact h
    · exfalso
      by_cases hxz1 : x * z = 1
      · apply hxz
        have : x = z := by
          calc x = x * z * z := by rw [mul_assoc, hz2, mul_one]
            _ = z := by rw [hxz1, one_mul]
        rw [this]
        exact Subgroup.mem_zpowers z
      · exact hbadD D hD _ h hxz1 hxgood
  have hN1 : N ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hxN
    apply hxz
    rw [hxN]
    exact one_mem _
  have hNbad : ∀ n ∈ N, n ≠ 1 → BadElt z n :=
    fun n hn hn1 => hbadD D₁ hD₁ n (hND D₁ hD₁ hn) hn1
  have hNgood : ∀ n ∈ N, n ≠ 1 → z ∈ zStarOf (Subgroup.centralizer ({n * z} : Set G)) := by
    intro n hn hn1
    by_contra hng
    have hnz1 : n * z ≠ 1 := by
      intro h
      apply hzD D₁ hD₁
      have : n = z := by
        calc n = n * z * z := by rw [mul_assoc, hz2, mul_one]
          _ = z := by rw [h, one_mul]
      rw [← this]
      exact hND D₁ hD₁ hn
    obtain ⟨D', hD'A, hnzD', hD'bad, hD'cov⟩ := exists_badCompl_of_bad hyp hQ' haA ha2 ha1 haz
      hconj hyA hya hy2 hyc hyV (A.mul_mem (hNA hn) hzA) hnz1 hng
    have hD' : D' ∈ 𝒟 := ⟨hD'A, hD'bad, hD'cov⟩
    apply hzD D' hD'
    have e1 : z = n⁻¹ * (n * z) := by group
    rw [e1]
    exact D'.mul_mem (D'.inv_mem (hND D' hD' hn)) hnzD'
  have hAsc : ∀ g ∈ A, ∀ c : G, c * z * c⁻¹ = z → c * g * c⁻¹ ∈ (S : Subgroup G) →
      c * g * c⁻¹ ∈ A := by
    intro g hg c hc hcS
    have h1 := mem_trivialOnQuot_of_mem_A hyp hg
    exact conj_mem_Csub hyp h1.1 h1.2 hc hcS
  have hsc := C25W.stronglyClosed_inter_of_good hz2 hAsc 𝒟 (fun D hD => hD.2.2) hzD
    (fun D hD g hg hg1 => hbadD D hD g hg hg1) hNA hND (fun g hg hall => (hmemN g).mpr ⟨hg, hall⟩)
    hNgood
  exact false_of_mixedClosed hyp hQ' hSqL' hNA hN1 (hND D₁ hD₁) hD₁A hD₁bad hsc hNbad hNgood

end Mixed

end CFSG.ClassicalInvolution.Q8P.Asc77.P25S.X
