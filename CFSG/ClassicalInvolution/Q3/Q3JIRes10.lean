module

public import CFSG.ClassicalInvolution.Asc77.AscR10E20
public import CFSG.ClassicalInvolution.Asc77.AscR10E24

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.JI

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3CII
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
  CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups commutatorElement

section Res10



@[expose] def Sec3TypingBelow (m : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], Nat.card Y < m → ∀ (Λ : Set (Subgroup Y)),
    HypOmegaModU (.sl2 3 1) Λ → (∀ M₁ ∈ Λ, ∀ M₂ ∈ omegaNbr Λ M₁, M₂ ∈ twinSet Λ M₁) →
    ∀ (K J : Subgroup Y) (zK zJ : Y), K ∈ Λ → AViol Λ K J zK zJ → SectionG2 Λ K

theorem Sec3TypingBelow.mono {m n : ℕ} (h : m ≤ n) (hn : Sec3TypingBelow n) : Sec3TypingBelow m :=
  fun Y _ _ hY => hn Y (lt_of_lt_of_le hY h)

theorem sec3TypingBelow_of_g2Sec3 {m : ℕ} (hB : Q3.CIT3Below m) (hG : G2Sec3) :
    Sec3TypingBelow m := by
  intro Y _ _ hY Λ hΩ htw K J zK zJ hK hv
  have hLn : (omegaGen Λ).Normal := omegaGen_normal hΩ.conjInvariant
  have hIn := inClass3_layer hΩ ⟨K, hK⟩
  have hlt : Nat.card ↥(omegaGen Λ) < m := lt_of_le_of_lt (Subgroup.card_le_card_group _) hY
  obtain ⟨ι, -, ⟨D⟩⟩ := hB ↥(omegaGen Λ) hlt (restrictFamily Λ (omegaGen Λ)) hIn
  obtain ⟨i, hi, hk⟩ := hG Y Λ hΩ htw K J zK zJ hK hv D
  exact sectionG2_of_single hΩ hK (fun M hM => le_omegaGen hM) D hi hk

section Std

variable {G : Type} [Group G] [Finite G]
  {K K' J : Subgroup G} {S : Sylow 2 G} {R R' W V : Subgroup G} {z t : G}

theorem r9_fusion_below [IsSimpleGroup G] (hT : Sec3TypingBelow (Nat.card G + 1))
    (d : Std20 3 2 K K' J S R R' W V z t) (c7 : Concl20_7 S K K' z)
    (c9 : Concl20_9 S K K' R R' z) (h8 : 8 < Nat.card R) {b : G}
    (hb : FieldInv20 S K K' W z t b) {u : G} {k : ℕ} (hu : Subgroup.zpowers u = K ⊓ W)
    (huo : orderOf u = 2 ^ (k + 1))
    (hact : ∀ x ∈ K ⊓ W, b * x * b⁻¹ = x ^ ((2 : ℤ) ^ k + 1)) {s : G} (hs2 : s * s = 1)
    (hsb : s * b = b * s) (hsN : s ∈ Subgroup.normalizer (K : Set G))
    (hsz : ∃ g : G, s = g * z * g⁻¹) :
    ∃ c : G, c * b = b * c ∧ s = c * z * c⁻¹ := by
  set C : Subgroup G := Subgroup.centralizer ({b} : Set G) with hC
  have hzA : z ∈ C := by
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (d.hSz hb.mem)).symm
  obtain ⟨htA, J_b, hv⟩ := d.t9_aViol c7 c9 h8 hb hu huo hact hzA
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hsb
  have hmem := d.t9_isClassicalMember c9 h8 hb hzA
  have hΛ := d.t9_hypOmegaModU c9 h8 hb hzA
  have htw := d.t9_nbr_twin hzA hΛ hmem
  have hK : crossIn K b ∈ conjFamily (crossIn K b) := ⟨1, conjSub_one _⟩
  have hClt : Nat.card ↥C < Nat.card G + 1 :=
    Nat.lt_succ_of_le (Subgroup.card_le_card_group C)
  let T : Set ↥C := {y | ∃ g : G, (y : G) = g * z * g⁻¹}
  have hTc : ∀ y ∈ T, ∀ e : ↥C, e * y * e⁻¹ ∈ T := by
    rintro y ⟨g, hg⟩ e
    exact ⟨(e : G) * g, by rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hg]; group⟩
  have hZ : ∀ y ∈ T, y * y = 1 → ∀ Q : Subgroup ↥C, Q ≤ crossIn K b → IsPGroup 2 Q →
      (∃ x ∈ Q, ∃ y' ∈ Q, x * y' ≠ y' * x) →
      (∀ q ∈ Q, y⁻¹ * (q * y * q⁻¹) ∈ classicalInvolutionOddCore ↥C) →
      ∃ o ∈ classicalInvolutionOddCore ↥C, y = o * ⟨z, hzA⟩ * o⁻¹ :=
    fun y hy hy2 Q hQK hQ2 hQnc hfix => d.t9_conj_of_centralizes hzA hy2 hy hQ2 hQK hQnc hfix
  have hsK : conjSub (⟨s, hsC⟩ : ↥C) (crossIn K b) = crossIn K b := by
    apply Subgroup.map_injective C.subtype_injective
    have hmap1 : (crossIn K b).map C.subtype = K ⊓ C := by
      have := map_conjSub_crossIn (K := K) (a := b) 1
      rw [conjSub_one, Subgroup.coe_one, conjSub_one] at this
      exact this
    rw [map_conjSub_crossIn, hmap1]
    exact conjSub_eq_of_mem_normalizer (t9_le_normalizer hsN hsC)
  obtain ⟨c, hc⟩ := aft_fusion3 hΛ hv.hzK
    (hT ↥C hClt (conjFamily (crossIn K b)) hΛ htw (crossIn K b) J_b ⟨z, hzA⟩ ⟨t, htA⟩ hK hv) T hTc
    hZ (by obtain ⟨g, hg⟩ := hsz; exact ⟨g, hg⟩) (Subtype.ext hs2) hsK
  exact ⟨(c : G), Subgroup.mem_centralizer_singleton_iff.mp c.2, congrArg Subtype.val hc⟩

end Std

theorem fus9Stmt_of_minimal {n : ℕ} (hT : Sec3TypingBelow (n + 1))
    (hbig : ¬ CITBelowU 3 2 (n + 1)) : Fus9Stmt 3 2 := by
  intro G _ _ _ K K' J S R R' W V z t d c3 c4 c5 c7 c8 c9 h8 b hb hplus s hs2 hsb hsS hsz
  by_cases hle : Nat.card G ≤ n
  · have hT' : Sec3TypingBelow (Nat.card G + 1) := hT.mono (by omega)
    obtain ⟨u, k, -, hu, huo, hact⟩ := hplus
    have hX1 : (1 : G) ∈ sec20X (CoreAssembly.conjClass K) z K K' :=
      (sec20X (CoreAssembly.conjClass K) z K K').one_mem
    have hsN : s ∈ Subgroup.normalizer (K : Set G) :=
      (c9 h8).2.2 s hsS (by rw [hs2]; exact hX1)
    exact r9_fusion_below hT' d c7 c9 h8 hb hu huo hact hs2 hsb hsN hsz
  · exfalso
    exact hbig (CITBelowU.mono 3 2 (by omega) (d.below 2 (by norm_num)))

theorem res10aNoConj9_of_minimal (p f : ℕ) [Fact p.Prime] {n : ℕ} (hB : Q3.CIT3Below (n + 1))
    (hbig : ¬ CITBelowU p f (n + 1)) : p ^ f = 9 → Res10aNoConj p f := by
  intro h9
  obtain ⟨rfl, rfl⟩ := eq_three_two_of_pow_eq_nine p f h9
  have hG : G2Sec3 := g2Sec3_of_g2Comp3 (g2Comp3_of_qv3Comp (qv3Comp_of_qv3ModelV
    (qv3ModelV_of_orth_exc ModelFacts.stdDich3Orth ModelFacts.stdDich3Exc)))
  exact res10aNoConj_of_fus9 3 2 (fus9Stmt_of_minimal (sec3TypingBelow_of_g2Sec3 hB hG) hbig)

end Res10

end CFSG.ClassicalInvolution.Q3.JI
