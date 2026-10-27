module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158GInn3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158Inn

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158G

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T156 CFSG.LocalAnalysis.GLTheoremA.S267 CFSG.LocalAnalysis.GLTheoremA.T158
open scoped commutatorElement

theorem t158g_inn_of_omega {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hΩ : T158GOmega p) {K B : Subgroup G} {x₁ x₂ : G} {L₁ L₂ : Subgroup G}
    (hQ : catalogIs (PSimple p K) t158FamTwo) (hh : I158HypK p (⊤ : Subgroup G) K B x₁ x₂ L₁ L₂) :
    InnDiagOn p (Subgroup.zpowers x₁) K ∧ InnDiagOn p (Subgroup.zpowers x₂) K := by
  obtain ⟨⟨-, hK, hBel, hBX, -, hx1B, hx2B, -, -, hL1, hC1, hL2, hC2⟩, hF12, hF21⟩ := hh
  have hx1X : x₁ ∈ (⊤ : Subgroup G) := hBX hx1B
  have hx2X : x₂ ∈ (⊤ : Subgroup G) := hBX hx2B
  have hN1 : x₁ ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.K156.normalizer_of_normalizes_component hp hK hx1X
      (inf_le_left.trans hK.1) inf_le_left hL2 (t158g_normalizer_of_fgOn hF12)
  have hN2 : x₂ ∈ Subgroup.normalizer (K : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.K156.normalizer_of_normalizes_component hp hK hx2X
      (inf_le_left.trans hK.1) inf_le_left hL1 (t158g_normalizer_of_fgOn hF21)
  set H : Subgroup G := K ⊔ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ with hHdef
  have hK1 : K ≤ K ⊔ Subgroup.zpowers x₁ := le_sup_left
  have hZ1 : Subgroup.zpowers x₁ ≤ K ⊔ Subgroup.zpowers x₁ := le_sup_right
  have hK1H : K ⊔ Subgroup.zpowers x₁ ≤ H := le_sup_left
  have hZ2H : Subgroup.zpowers x₂ ≤ H := le_sup_right
  have hKH : K ≤ H := hK1.trans hK1H
  have hx1H : x₁ ∈ H := hK1H (hZ1 (Subgroup.mem_zpowers x₁))
  have hx2H : x₂ ∈ H := hZ2H (Subgroup.mem_zpowers x₂)
  have hHN : H ≤ Subgroup.normalizer (K : Set G) :=
    sup_le (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hN1)) (Subgroup.zpowers_le.2 hN2)
  set M : Subgroup ↥H := K.subgroupOf H with hMdef
  have hMn : M.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  have hHnorm : ∀ g : ↥H, g ∈ Subgroup.normalizer (M : Set ↥H) := by
    intro g
    rw [Subgroup.normalizer_eq_top_iff.2 hMn]
    exact Subgroup.mem_top g
  have hN0n : (GLAPPrimeCoreOf p M).Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p M
    rw [Subgroup.normalizer_eq_top_iff.2 hMn, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  haveI := hN0n
  set N0 : Subgroup ↥H := GLAPPrimeCoreOf p M with hN0def
  set π : ↥H →* ↥H ⧸ N0 := QuotientGroup.mk' N0 with hπdef
  have hN : ¬ p ∣ Nat.card π.ker := by
    rw [hπdef, QuotientGroup.ker_mk']
    exact not_dvd_card_glaPPrimeCoreOf hp _
  have hMK : M.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  set S : Subgroup (↥H ⧸ N0) := M.map π with hSdef
  have hSn : S.Normal := hMn.map π (QuotientGroup.mk'_surjective N0)
  set eK : PQuot p K ≃* PQuot p S := compIso hp hMK π hN with heKdef
  have hqPS : CFSG.Open.IsQuasisimple (PQuot p S) :=
    (isQuasisimple_pQuot_of_glaPComponent hp hK).of_mulEquiv eK.symm
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 : (GLAPPrimeCoreOf p M).map π = GLAPPrimeCoreOf p S := map_glaPPrimeCoreOf hp π hN M
    have h2 : (GLAPPrimeCoreOf p M).map π = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hπdef, QuotientGroup.ker_mk']
    have h3 : GLAPPrimeCoreOf p S = ⊥ := by rw [← h1, h2]
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h3
  have eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hqS : CFSG.Open.IsQuasisimple ↥S := hqPS.of_mulEquiv eS.symm
  have hQS : catalogIs (PSimple p S) t158FamTwo := catalog_forth hp hKH hN hQ
  set x1H : ↥H := ⟨x₁, hx1H⟩ with hx1Hdef
  set x2H : ↥H := ⟨x₂, hx2H⟩ with hx2Hdef
  have hx1p : x1H ^ p = 1 := Subtype.ext (hBel.2 x₁ hx1B)
  have hx2p : x2H ^ p = 1 := Subtype.ext (hBel.2 x₂ hx2B)
  have hcomm : x1H * x2H = x2H * x1H := by
    apply Subtype.ext
    have hB : (⟨x₁, hx1B⟩ : ↥B) * ⟨x₂, hx2B⟩ = ⟨x₂, hx2B⟩ * ⟨x₁, hx1B⟩ :=
      hBel.1.is_comm.comm _ _
    have hG : x₁ * x₂ = x₂ * x₁ := congrArg Subtype.val hB
    exact hG
  have hy1p : (π x1H) ^ p = 1 := by rw [← map_pow, hx1p, map_one]
  have hy2p : (π x2H) ^ p = 1 := by rw [← map_pow, hx2p, map_one]
  have hcommY : π x1H * π x2H = π x2H * π x1H := by rw [← map_mul, ← map_mul, hcomm]
  have hL1H : L₁ ≤ H := hL1.1.trans (inf_le_left.trans hKH)
  have hL2H : L₂ ≤ H := hL2.1.trans (inf_le_left.trans hKH)
  have hL1Ω := glaPComponent_forth hp hKH hx1H hN1 (hBel.2 x₁ hx1B) hN hL1
  have hL2Ω := glaPComponent_forth hp hKH hx2H hN2 (hBel.2 x₂ hx2B) hN hL2
  have hC1Ω := chev_forth hp hL1H hN hC1
  have hC2Ω := chev_forth hp hL2H hN hC2
  have hF12Ω := fgOn_forth hp hL2H hN hx1H (t158g_normalizer_of_fgOn hF12) hF12
  have hF21Ω := fgOn_forth hp hL1H hN hx2H (t158g_normalizer_of_fgOn hF21) hF21
  have o1 := hΩ (↥H ⧸ N0) S (π x1H) (π x2H) ((L₁.subgroupOf H).map π) ((L₂.subgroupOf H).map π) hSn hqS hSp
    hQS hy1p hy2p hcommY hL1Ω hC1Ω hL2Ω hC2Ω hF12Ω hF21Ω
  have o2 := hΩ (↥H ⧸ N0) S (π x2H) (π x1H) ((L₂.subgroupOf H).map π) ((L₁.subgroupOf H).map π) hSn hqS hSp
    hQS hy2p hy1p hcommY.symm hL2Ω hC2Ω hL1Ω hC1Ω hF21Ω hF12Ω
  exact ⟨innDiagOn_back hp hMK hN hx1H hN1 (hHnorm x1H) o1,
    innDiagOn_back hp hMK hN hx2H hN2 (hHnorm x2H) o2⟩

section Headline


theorem t158InnElemOn_two : T158InnElemOn t158FamTwo := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ hQ hp hp2 hh
  exact t158g_inn_of_omega hp
    (t158gOmega_of_cores t158gU38Core_holds t158gTD4Core_holds t158gD4Core_holds hp hp2) hQ hh

end Headline

end CFSG.LocalAnalysis.GLTheoremA.T158G

end
