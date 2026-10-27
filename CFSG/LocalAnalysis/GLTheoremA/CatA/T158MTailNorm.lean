module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T158MTailRankU6
import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Shape
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullCore
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2FullTransport
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_2_Bar
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T158

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.ComponentBalance
open CFSG.HardMathSupport.Solomon.Coordinator

section Bar

variable {G : Type} [Group G] [Finite G]

private theorem bar_of_kGroup {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X B L : Subgroup G}
    (hXK : CFSG.Open.IsKGroup ↥X) (hB : IsElemAbelian p B) (hBX : B ≤ X)
    (hr : GLATwoLocalRank p ↥X ≤ CFSG.Open.pRank p B) (hL : GLAPComponent p X L)
    (hnL : ¬ B ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.Open.IsKGroup (↥X ⧸ GLAPPrimeCore p ↥X) ∧
      GLAPPrimeCore p (↥X ⧸ GLAPPrimeCore p ↥X) = ⊥ ∧ IsElemAbelian p (barX p X B) ∧
      GLATwoLocalRank p (↥X ⧸ GLAPPrimeCore p ↥X) ≤ CFSG.Open.pRank p (barX p X B) ∧
      GLAPComponent p ⊤ (barX p X L) ∧
      ¬ barX p X B ≤ Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) :
        Set (↥X ⧸ GLAPPrimeCore p ↥X)) := by
  have : Fact p.Prime := ⟨hp⟩
  set N : Subgroup ↥X := GLAPPrimeCore p ↥X with hNdef
  have hNc : ¬ p ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card
  have hBp : IsPGroup p B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  refine ⟨isKGroup_quotient' hXK N, glaPPrimeCore_quotient_eq_bot hp,
    isElemAbelian_barX hB, ?_, i112b_glaPComponent_of_isComponentOf
      (glaPPrimeCore_quotient_eq_bot hp) hL.2.2.1, ?_⟩
  · rw [rank_barX_of_isPGroup hp hBp hBX]
    exact (glaTwoLocalRank_quotient_le hp hp2 N hNc).trans hr
  · intro hle
    apply hnL
    intro b hb
    have h1 : QuotientGroup.mk' N ⟨b, hBX hb⟩ ∈
        Subgroup.normalizer ((barX p X L : Subgroup (↥X ⧸ N)) : Set (↥X ⧸ N)) :=
      hle ⟨⟨b, hBX hb⟩, (Subgroup.mem_subgroupOf).2 hb, rfl⟩
    have h2 : (⟨b, hBX hb⟩ : ↥X) ∈ (Subgroup.normalizer (L : Set G)).subgroupOf X := by
      rw [← i112f_comap_normalizer_barX hL]
      exact h1
    exact (Subgroup.mem_subgroupOf).1 h2

end Bar

private theorem le_pRank_mulAut {Y : Type} [Group Y] [Finite Y] {F : Subgroup Y} (hF : IsElemAbelian 3 F)
    {e : ℕ} (hcard : Nat.card F = 3 ^ e) (hZ : F ⊓ Subgroup.center Y = ⊥) :
    e ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut Y)) := by
  have hinj : Function.Injective ((MulAut.conj : Y →* MulAut Y).comp F.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha
    have hcen : (a : Y) ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h := congrArg (fun φ : MulAut Y => φ z) ha
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      have h' : (a : Y) * z * (a : Y)⁻¹ = z := h
      calc z * (a : Y) = (a : Y) * z * (a : Y)⁻¹ * (a : Y) := by rw [h']
        _ = (a : Y) * z := by group
    have hmem : (a : Y) ∈ F ⊓ Subgroup.center Y := ⟨a.2, hcen⟩
    rw [hZ] at hmem
    exact (Subgroup.mem_bot).2 (Subtype.ext hmem)
  have hr : ((MulAut.conj : Y →* MulAut Y).comp F.subtype).range = F.map MulAut.conj := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardE : Nat.card (F.map (MulAut.conj : Y →* MulAut Y)) = 3 ^ e := by
    rw [← hr, ← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  exact CFSG.SectionRank.le_pRank (by norm_num) le_top (hF.map _) hcardE

theorem t158NormConj_of (T : Tables112) (TL : TableL2) (TT : Tables112Types) (hE : T158RankTE6)
    {Q : TauCeti.CFSGIndex → Prop} : T158NormConj Q := by
  intro X _ _ p K B x₁ x₂ L₁ L₂ _ hh hc g b hb y
  have hc0 := hc
  obtain ⟨hp3, n, hn, hn1, hcase⟩ := hc
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L : Subgroup X := K.map (MulAut.conj g⁻¹).toMonoidHom with hLdef
  have hmemL : ∀ z : X, z ∈ L ↔ g * z * g⁻¹ ∈ K := by
    intro z
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hk
    · intro hz
      refine ⟨g * z * g⁻¹, hz, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  suffices hBL : B ≤ Subgroup.normalizer (L : Set X) by
    have h := Subgroup.mem_normalizer_iff.mp (hBL hb) y
    rw [hmemL, hmemL] at h
    exact h
  by_contra hnL
  have hKc : GLAPComponent 3 (⊤ : Subgroup X) K := hh.hyp.1.2.1
  have hLc : GLAPComponent 3 (⊤ : Subgroup X) L := by
    have h := CFSG.HardMathSupport.Dickson.I271.glaPComponent_map_equiv Nat.prime_three
      (MulAut.conj g⁻¹) hKc
    have htop : (⊤ : Subgroup X).map (MulAut.conj g⁻¹).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective
    rwa [htop] at h
  have hXK : CFSG.Open.IsKGroup ↥(⊤ : Subgroup X) := hh.hyp.1.1
  have hBel : IsElemAbelian 3 B := hh.hyp.1.2.2.1
  have hr : GLATwoLocalRank 3 ↥(⊤ : Subgroup X) ≤ CFSG.Open.pRank 3 B := by
    have h1 : 3 ^ GLATwoLocalRank 3 ↥(⊤ : Subgroup X) ≤ Nat.card B := hh.hyp.1.2.2.2.2.1
    obtain ⟨k, hk⟩ := exists_card_eq_of_isElemAbelian Nat.prime_three hBel
    have h2 : k ≤ CFSG.Open.pRank 3 B := CFSG.SectionRank.le_pRank (by norm_num) le_rfl hBel hk
    rw [hk] at h1
    exact ((Nat.pow_le_pow_iff_right (by norm_num)).mp h1).trans h2
  obtain ⟨hQK, hQcore, hBbar, hrbar, hLbar, hnLbar⟩ :=
    bar_of_kGroup Nat.prime_three (by norm_num) hXK hBel le_top hr hLc hnL
  obtain ⟨-, -, haut, -, -⟩ :=
    i112f_core T TL TT hQK Nat.prime_three (by norm_num) hQcore hBbar hrbar hLbar hnLbar
  let eKL : ↥K ≃* ↥L := (MulAut.conj g⁻¹).subgroupMap K
  let eQ : PQuot 3 K ≃* PQuot 3 L :=
    QuotientGroup.congr (GLAPPrimeCore 3 ↥K) (GLAPPrimeCore 3 ↥L) eKL (CFSG.pPrimeCore_map_iso 3 eKL)
  let eB : PQuot 3 K ≃* ↥(barX 3 (⊤ : Subgroup X) L) :=
    eQ.trans (quotEquivBarX Nat.prime_three hLc.1 hLc.2.1)
  have hqs : CFSG.Open.IsQuasisimple (PQuot 3 K) := isQuasisimple_pQuot_of_glaPComponent hh.prime hKc
  obtain ⟨e, F, hFel, hFcard, hFZ, he⟩ : ∃ e : ℕ, ∃ F : Subgroup (PQuot 3 K), IsElemAbelian 3 F ∧
      Nat.card F = 3 ^ e ∧ F ⊓ Subgroup.center (PQuot 3 K) = ⊥ ∧ 3 ≤ e := by
    rcases hcase with ⟨hKt, -⟩ | ⟨hKt, -⟩
    · obtain ⟨F, hF1, hF2, hF3⟩ := t158RankU6_holds (PQuot 3 K) n hn hn1 hqs hKt
      exact ⟨4, F, hF1, hF2, hF3, by norm_num⟩
    · obtain ⟨F, hF1, hF2, hF3⟩ := hE (PQuot 3 K) n hn hn1 hqs hKt
      exact ⟨5, F, hF1, hF2, hF3, by norm_num⟩
  set F' : Subgroup ↥(barX 3 (⊤ : Subgroup X) L) := F.map eB.toMonoidHom with hF'def
  have hF'el : IsElemAbelian 3 F' := hFel.map _
  have hF'card : Nat.card F' = 3 ^ e := by
    rw [hF'def, ← hFcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective F eB.toMonoidHom eB.injective).toEquiv).symm
  have hF'Z : F' ⊓ Subgroup.center ↥(barX 3 (⊤ : Subgroup X) L) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨f, hf, rfl⟩, hz⟩
    have hfc : f ∈ Subgroup.center (PQuot 3 K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      have h := (Subgroup.mem_center_iff.mp hz) (eB w)
      apply eB.injective
      simpa [map_mul] using h
    have hmem : f ∈ F ⊓ Subgroup.center (PQuot 3 K) := ⟨hf, hfc⟩
    rw [hFZ] at hmem
    rw [Subgroup.mem_bot.1 hmem]
    simp
  have hlow := le_pRank_mulAut hF'el hF'card hF'Z
  omega

end CFSG.LocalAnalysis.GLTheoremA.T158

end
