module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzEightRoot
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BenderCoverCentral
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient
public import Certificates.Certificate113
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.Walter.J1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

open CFSG.ProperTwoGeneratedCore.TheoremC CFSG.ProperTwoGeneratedCore.TheoremC.BenderCover

variable {J : Type} [Group J]

theorem eq_one_or_eq_of_mem_zpowers_two {t g : J} (ht : orderOf t = 2)
    (hg : g ∈ Subgroup.zpowers t) : g = 1 ∨ g = t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, ht]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem normal_of_le_center {N : Subgroup J} (hN : N ≤ Subgroup.center J) : N.Normal :=
  ⟨fun n hn g => by rw [(Subgroup.mem_center_iff.mp (hN hn) g), mul_inv_cancel_right]; exact hn⟩

theorem center_quotient_eq_map (hperf : commutator J = ⊤) {N : Subgroup J} [N.Normal]
    (hN : N ≤ Subgroup.center J) :
    Subgroup.center (J ⧸ N) = (Subgroup.center J).map (QuotientGroup.mk' N) := by
  apply le_antisymm
  · intro s hs
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective N s
    refine ⟨j, Subgroup.mem_center_iff.mpr fun k => ?_, rfl⟩
    have h := eq_conj_of_perfect hperf (MulAut.conj j).toMonoidHom 1 (fun k => by
      have hk := (Subgroup.mem_center_iff.mp hs (QuotientGroup.mk' N k))
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at hk
      have hX := Subgroup.inv_mem _ (hN hk)
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one,
        QuotientGroup.eq]
      have hT : (j * k * j⁻¹)⁻¹ * k = j * ((k * j)⁻¹ * (j * k))⁻¹ * j⁻¹ := by group
      rw [hT, Subgroup.mem_center_iff.mp hX j, mul_inv_cancel_right]
      exact hX) k
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, one_mul, inv_one, mul_one,
      mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  · rintro _ ⟨a, ha, rfl⟩
    refine Subgroup.mem_center_iff.mpr fun s => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N s
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp ha g]

theorem commutator_quotient_eq_top (hperf : commutator J = ⊤) (N : Subgroup J) [N.Normal] :
    commutator (J ⧸ N) = ⊤ := by
  have h := Subgroup.map_commutator (⊤ : Subgroup J) ⊤ (QuotientGroup.mk' N)
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h
  rw [commutator_def, ← h, ← commutator_def, hperf,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

variable [Finite J]

theorem false_of_szModel_of_mem_center (hperf : commutator J = ⊤)
    (hZ2 : IsPGroup 2 (Subgroup.center J)) {c : J} (hc : c ∈ Subgroup.center J)
    (hcc : c * c ≠ 1) (hcccc : c * c * (c * c) = 1)
    (hu : ∀ s ∈ Subgroup.center J, s * s = 1 → s = 1 ∨ s = c * c)
    (e : J ⧸ Subgroup.center J ≃* ↥(CFSG.Theory.Comparator.SzModel 1)) : False := by
  set Z := Subgroup.center J with hZdef
  set u := c * c with hudef
  have huZ : u ∈ Z := Z.mul_mem hc hc
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcccc) hcc
  set N := Subgroup.zpowers u with hNdef
  have hNZ : N ≤ Z := (Subgroup.zpowers_le).mpr huZ
  have : N.Normal := normal_of_le_center hNZ
  have hNmem : ∀ a ∈ N, a = 1 ∨ a = u := fun a ha => eq_one_or_eq_of_mem_zpowers_two hu2 ha
  have hcenter := center_quotient_eq_map hperf hNZ
  have : (Z.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective N)
  let e₁ : (J ⧸ N) ⧸ Subgroup.center (J ⧸ N) ≃* J ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientQuotientEquivQuotient N Z hNZ)
  have hB₁ : CFSG.BenderSuzuki.IsBenderGroup ((J ⧸ N) ⧸ Subgroup.center (J ⧸ N)) :=
    .isSuzuki 1 le_rfl (e₁.trans e)
  have hB : CFSG.BenderSuzuki.IsBenderGroup (J ⧸ Z) := .isSuzuki 1 le_rfl e
  obtain ⟨Q⟩ : Nonempty (Sylow 2 J) := inferInstance
  set R := Q.mapSurjective (QuotientGroup.mk'_surjective Z) with hRdef
  have hRc : (R : Subgroup (J ⧸ Z)) = (Q : Subgroup J).map (QuotientGroup.mk' Z) :=
    Sylow.coe_mapSurjective _ _
  have hBR := benderBorelFactsHold _ hB R
  have hSR := szEightSylowFacts_of_mulEquiv e R
  obtain ⟨w, hwc, hw1⟩ : ∃ w : J ⧸ Z, InCenterOf (R : Subgroup (J ⧸ Z)) w ∧ w ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : Subsingleton {w : J ⧸ Z // InCenterOf (R : Subgroup (J ⧸ Z)) w} :=
      ⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩
    have h1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h4 := hBR.center_card
    omega
  have hwR := hwc.1
  rw [hRc] at hwR
  obtain ⟨ŵ, hŵQ, rfl⟩ := hwR
  have hŵŵ : ŵ * ŵ ∈ Z := by
    have h := hSR.sq_of_comm ⟨_, hwc.1⟩ fun y => Subtype.ext ((hwc.2 y y.2).eq.symm)
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, pow_two, ← map_mul, OneMemClass.coe_one, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h'
    exact h'
  have hcomm : ∀ x ∈ (Q : Subgroup J), x * ŵ * x⁻¹ * ŵ⁻¹ ∈ N := by
    intro x hx
    have haZ : x * ŵ * x⁻¹ * ŵ⁻¹ ∈ Z := by
      have h := (hwc.2 _ (hRc ▸ ⟨x, hx, rfl⟩ : QuotientGroup.mk' Z x ∈ (R : Subgroup _))).eq
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h
      have h2 : x * ŵ * x⁻¹ * ŵ⁻¹ = (x * ŵ) * ((x * ŵ)⁻¹ * (ŵ * x))⁻¹ * (x * ŵ)⁻¹ := by group
      rw [h2, Subgroup.mem_center_iff.mp (Z.inv_mem h) (x * ŵ), mul_inv_cancel_right]
      exact Z.inv_mem h
    set a := x * ŵ * x⁻¹ * ŵ⁻¹ with hadef
    have hac := Subgroup.mem_center_iff.mp haZ
    have hxw : x * ŵ * x⁻¹ = a * ŵ := by rw [hadef]; group
    have hww := Subgroup.mem_center_iff.mp hŵŵ
    have haa : a * a = 1 := by
      have h1 : x * (ŵ * ŵ) * x⁻¹ = ŵ * ŵ := by rw [hww x, mul_inv_cancel_right]
      have h2 : x * (ŵ * ŵ) * x⁻¹ = (x * ŵ * x⁻¹) * (x * ŵ * x⁻¹) := by group
      have h3 : (a * ŵ) * (a * ŵ) = a * a * (ŵ * ŵ) := by
        calc (a * ŵ) * (a * ŵ) = a * (ŵ * a) * ŵ := by group
          _ = a * (a * ŵ) * ŵ := by rw [hac ŵ]
          _ = a * a * (ŵ * ŵ) := by group
      have h4 : a * a * (ŵ * ŵ) = ŵ * ŵ := by rw [← h3, ← hxw, ← h2, h1]
      exact mul_eq_right.mp h4
    rcases hu a haZ haa with h | h
    · rw [h]
      exact N.one_mem
    · rw [h]
      exact Subgroup.mem_zpowers u
  set Q₁ := Q.mapSurjective (QuotientGroup.mk'_surjective N) with hQ₁def
  have hQ₁c : (Q₁ : Subgroup (J ⧸ N)) = (Q : Subgroup J).map (QuotientGroup.mk' N) :=
    Sylow.coe_mapSurjective _ _
  have hw₀Q : QuotientGroup.mk' N ŵ ∈ (Q₁ : Subgroup (J ⧸ N)) := hQ₁c ▸ ⟨ŵ, hŵQ, rfl⟩
  have hw₀c : ∀ q ∈ (Q₁ : Subgroup (J ⧸ N)), Commute q (QuotientGroup.mk' N ŵ) := by
    intro q hq
    rw [hQ₁c] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    have h := hcomm x hx
    change QuotientGroup.mk' N x * QuotientGroup.mk' N ŵ =
      QuotientGroup.mk' N ŵ * QuotientGroup.mk' N x
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    have h2 : (x * ŵ)⁻¹ * (ŵ * x) = (x * ŵ)⁻¹ * (x * ŵ * x⁻¹ * ŵ⁻¹)⁻¹ * (x * ŵ) := by group
    have h3 := Subgroup.mem_center_iff.mp (hNZ (N.inv_mem h))
    rw [h2, h3 (x * ŵ)⁻¹, inv_mul_cancel_right]
    exact N.inv_mem h
  have hw₀Z : QuotientGroup.mk' N ŵ ∉ Subgroup.center (J ⧸ N) := by
    rw [hcenter]
    rintro ⟨a, ha, haw⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at haw
    apply hw1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rw [show ŵ = a * (a⁻¹ * ŵ) by group]
    exact Z.mul_mem ha (hNZ haw)
  have hZ₁2 : IsPGroup 2 (Subgroup.center (J ⧸ N)) := hcenter ▸ hZ2.map _
  have hu₁ : ∀ s ∈ Subgroup.center (J ⧸ N), s * s = 1 → s = 1 ∨ s = QuotientGroup.mk' N c := by
    intro s hs hss
    rw [hcenter] at hs
    obtain ⟨a, ha, rfl⟩ := hs
    rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hss
    have hac := Subgroup.mem_center_iff.mp ha
    rcases hNmem _ hss with h | h
    · left
      rcases hu a ha h with h' | h'
      · rw [h', map_one]
      · rw [h', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_zpowers u
    · right
      have hcc' : (a * c⁻¹) * (a * c⁻¹) = 1 := by
        calc (a * c⁻¹) * (a * c⁻¹) = a * (c⁻¹ * a) * c⁻¹ := by group
          _ = a * (a * c⁻¹) * c⁻¹ := by rw [hac c⁻¹]
          _ = a * a * (c * c)⁻¹ := by group
          _ = 1 := by rw [h, mul_inv_cancel]
      rcases hu _ (Z.mul_mem ha (Z.inv_mem hc)) hcc' with h' | h'
      · rw [mul_inv_eq_one] at h'
        rw [h']
      · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
        have h'' : a⁻¹ * c = (a * c⁻¹)⁻¹ := by
          rw [mul_inv_rev, inv_inv]
          exact (Subgroup.mem_center_iff.mp (Z.inv_mem ha) c).symm
        rw [h'', h']
        exact N.inv_mem (Subgroup.mem_zpowers u)
  have hBF₁ := benderBorelFactsHold _ hB₁
    (Q₁.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center (J ⧸ N))))
  rw [Sylow.coe_mapSurjective] at hBF₁
  have hbot := center_eq_bot_of_borelFacts (commutator_quotient_eq_top hperf N) hZ₁2 hu₁ Q₁ hBF₁
    hw₀Q hw₀c hw₀Z
  have hcN : QuotientGroup.mk' N c ∈ Subgroup.center (J ⧸ N) := hcenter ▸ ⟨c, hc, rfl⟩
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcN
  rcases hNmem c hcN with h | h
  · exact hcc (show c * c = 1 by rw [h, one_mul])
  · exact hcc (show c * c = 1 by rw [h]; exact hcccc)

end CFSG.ProperTwoGeneratedCore.Lemma37
