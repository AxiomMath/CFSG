module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267Amb267
public import CFSG.LocalAnalysis.GLTheoremA.S11.Basic
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

section Main

theorem i267At_of_facts (hgen : S267FactGen) (hp3 : S267FactP3) (hcls : S267FactBadCls)
    (hexc : S267FactBadExc)
    (G : Type) [Group G] [Finite G] (p : ℕ) : I267At G p := by
  classical
  intro hp hp2 q hq hq2 hqp X K B hX hK hChev hBel hBX hm2 hB4 hBC
  haveI : Fact p.Prime := ⟨hp⟩
  have hKX : K ≤ X := hK ▸ P65.glaPLayer_le_self X
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := by
    have := P65.le_normalizer_glaPLayer (p := p) (X := X) (B := X) Subgroup.le_normalizer
    rwa [hK] at this
  set H : Subgroup G := K ⊔ B with hH
  have hKH : K ≤ H := le_sup_left
  have hBH : B ≤ H := le_sup_right
  have hHX : H ≤ X := sup_le hKX hBX
  have hHN : H ≤ Subgroup.normalizer (K : Set G) := hHX.trans hXK
  set K₀ : Subgroup ↥H := K.subgroupOf H with hK₀
  haveI hK₀n : K₀.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).2 hHN
  set N₀ : Subgroup ↥H := GLAPPrimeCoreOf p K₀ with hN₀def
  haveI hN₀n : N₀.Normal := by
    have h := normalizer_le_normalizer_glaPPrimeCoreOf p K₀
    rw [Subgroup.normalizer_eq_top_iff.2 hK₀n, top_le_iff] at h
    exact Subgroup.normalizer_eq_top_iff.1 h
  have hN : ¬ p ∣ Nat.card N₀ := not_dvd_card_glaPPrimeCoreOf hp K₀
  have hNK : N₀ ≤ K₀ := Subgroup.map_subtype_le _
  set π : ↥H →* ↥H ⧸ N₀ := QuotientGroup.mk' N₀ with hπ
  have hker : ¬ p ∣ Nat.card π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hN
  set S : Subgroup (↥H ⧸ N₀) := K₀.map π with hS
  set B₀ : Subgroup ↥H := B.subgroupOf H with hB₀
  set Bb : Subgroup (↥H ⧸ N₀) := B₀.map π with hBb
  have hSn : S.Normal := hK₀n.map π (QuotientGroup.mk'_surjective N₀)
  have hB₀el : IsElemAbelian p B₀ := isElemAbelian_subgroupOf hBel H
  have hBbel : IsElemAbelian p Bb := CFSG.SectionRank.isElemAbelian_map hB₀el π
  have hB₀p : IsPGroup p B₀ := isPGroup_of_isElemAbelian hB₀el
  have hcB₀ : Nat.card B₀ = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBH).toEquiv
  have hcBb : Nat.card Bb = Nat.card B := by
    rw [hBb, card_map_of_isPGroup hp π hker hB₀p, hcB₀]
  obtain ⟨e₂⟩ := nonempty_pQuot_equiv_subgroupOf p hKH
  obtain ⟨e₃⟩ := nonempty_pQuot_equiv_map_self (p := p) (ψ := π) (K := K₀)
    (by rw [hπ, QuotientGroup.ker_mk', inf_eq_left.2 hNK])
  let e₁ : PQuot p K ≃* ↥S := e₂.symm.trans e₃
  have hKperf : ⁅K, K⁆ = K := by
    have h : ⁅GLAPLayer p X, GLAPLayer p X⁆ = GLAPLayer p X := by
      apply le_antisymm
      · refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        rw [commutatorElement_def]
        exact (GLAPLayer p X).mul_mem ((GLAPLayer p X).mul_mem ((GLAPLayer p X).mul_mem ha hb)
          ((GLAPLayer p X).inv_mem ha)) ((GLAPLayer p X).inv_mem hb)
      · unfold GLAPLayer
        refine sSup_le fun J hJ => ?_
        have hJ' : GLAPComponent p X J := hJ
        calc J = ⁅J, J⁆ := (glaPComponent_perfect hJ').symm
          _ ≤ ⁅sSup {L : Subgroup G | GLAPComponent p X L}, sSup {L : Subgroup G | GLAPComponent p X L}⁆ :=
            Subgroup.commutator_mono (le_sSup hJ) (le_sSup hJ)
    rwa [hK] at h
  have hSq : ⁅S, S⁆ = S := by
    have hinj : Function.Injective H.subtype := H.subtype_injective
    have h1 : ⁅K₀, K₀⁆ = K₀ := by
      apply Subgroup.map_injective hinj
      rw [Subgroup.map_commutator, hK₀, Subgroup.map_subgroupOf_eq_of_le hKH, hKperf]
    rw [hS, ← Subgroup.map_commutator, h1]
  have hSp : GLAPPrimeCore p ↥S = ⊥ := by
    have h1 := map_glaPPrimeCoreOf hp π hker K₀
    have h2 : GLAPPrimeCoreOf p S = ⊥ := by
      rw [← h1]
      exact (Subgroup.map_eq_bot_iff _).2 (by rw [hπ, QuotientGroup.ker_mk'])
    exact (Subgroup.map_eq_bot_iff_of_injective _ S.subtype_injective).1 h2
  let eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  let eK : PQuot p K ≃* PQuot p S := e₁.trans eS.symm
  let eKS : PSimple p K ≃* PSimple p S := QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)
  have hChevS : IsChevSimple q (PSimple p S) := CFSG.LocalAnalysis.GLTheoremA.chev_isChevSimple_of_mulEquiv
    eKS.symm hChev
  have hKΩ : CFSG.Open.IsKGroup (↥H ⧸ N₀) :=
    (hX.of_injective (Subgroup.inclusion hHX) (Subgroup.inclusion_injective hHX)).quotient N₀
  have hSB : S ⊔ Bb = ⊤ := by
    have h1 : (K₀ ⊔ B₀).map H.subtype = H := by
      rw [Subgroup.map_sup, hK₀, hB₀, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hBH]
    have h2 : K₀ ⊔ B₀ = ⊤ := by
      apply Subgroup.map_injective H.subtype_injective
      rw [h1, Subgroup.map_top, Subgroup.range_subtype]
    rw [hS, hBb, ← Subgroup.map_sup, h2, Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective N₀)]
  have hH2 : p ^ GLATwoLocalRank p (↥H ⧸ N₀) ≤ Nat.card Bb := by
    rw [hcBb]
    refine le_trans (pow_le_pow_right₀ hp.one_lt.le ?_) hm2
    exact (glaTwoLocalRank_quotient_le hp hp2 N₀ hN).trans (S11.twoLocalRank_mono hp hHX)
  have hB4' : p ^ 4 ≤ Nat.card Bb := by rw [hcBb]; exact hB4
  have hBC' : Nat.card ↥(Bb ⊓ centModSubgroup p S) = p := by
    have hB₀K : B₀ ≤ Subgroup.normalizer (K₀ : Set ↥H) := by
      intro g _; rw [Subgroup.normalizer_eq_top_iff.2 hK₀n]; exact Subgroup.mem_top _
    have h1 := card_inf_centModSubgroup_map hp π hker hB₀p hB₀K
    have hinj : Function.Injective H.subtype := H.subtype_injective
    have hmapcm : (B₀ ⊓ centModSubgroup p K₀).map H.subtype = B ⊓ centModSubgroup p K := by
      have hh := map_inf_centModSubgroup hp H.subtype (show ¬ p ∣ Nat.card H.subtype.ker by
        rw [(MonoidHom.ker_eq_bot_iff H.subtype).2 hinj, Subgroup.card_bot]; exact hp.not_dvd_one) hB₀K
      rw [hh, hB₀, hK₀, Subgroup.map_subgroupOf_eq_of_le hBH, Subgroup.map_subgroupOf_eq_of_le hKH]
    have h2 : Nat.card ↥(B₀ ⊓ centModSubgroup p K₀) = p := by
      calc Nat.card ↥(B₀ ⊓ centModSubgroup p K₀)
          = Nat.card ↥((B₀ ⊓ centModSubgroup p K₀).map H.subtype) :=
            (Subgroup.card_map_of_injective hinj).symm
        _ = Nat.card ↥(B ⊓ centModSubgroup p K) := by rw [hmapcm]
        _ = p := hBC
    rw [hS, hBb, h1, h2]
  have hKm : K₀.map H.subtype = K := Subgroup.map_subgroupOf_eq_of_le hKH
  have hBm : B₀.map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
  by_cases hA : (CFSG.Open.pRank p B < GLATwoLocalRank q ↥X ∧ ¬ (p = 3 ∧ Nat.card B = 3 ^ 4))
  ·
    obtain ⟨hlt, hnot⟩ := hA
    have hnot' : ¬ (p = 3 ∧ Nat.card Bb = 3 ^ 4) := by rwa [hcBb]
    have h12 := hgen p q hp hp2 hq hq2 hqp _ hKΩ S Bb hSn hSq hSp hChevS hBbel hSB hH2 hB4' hBC' hnot'
    have h12' := conc267A12_of_quot hp hp2 N₀ hN K₀ B₀ hK₀n hB₀el h12
    have h12'' := gConcA12_of_amb hp H hHX K₀ B₀ h12'
    rw [hKm, hBm] at h12''
    obtain ⟨B', D, J, hB'el, hB'X, hIn, hcase, hcard⟩ := h12''
    exact Or.inl ⟨B', D, J, hB'el, hB'X, hIn, hcase, hcard, Or.inl hlt⟩
  ·
    have hdisj : S267ConcA p S Bb ∨ S267ConcBCDE p q S Bb := by
      by_cases h3 : p = 3 ∧ Nat.card B = 3 ^ 4
      · exact hp3 p q hp hp2 hq hq2 hqp _ hKΩ S Bb hSn hSq hSp hChevS hBbel hSB hH2 hB4' hBC' h3.1
          (by rw [hcBb]; exact h3.2)
      · have hnot' : ¬ (p = 3 ∧ Nat.card Bb = 3 ^ 4) := by rwa [hcBb]
        have hq' : ∃ (K' : Type) (_ : Group K') (_ : Finite K'),
            Nonempty (PQuot p (⊤ : Subgroup K') ≃* ↥S) ∧
              GLATwoLocalRank q K' ≤ CFSG.Open.pRank p Bb := by
          refine ⟨↥K, inferInstance, inferInstance, ?_, ?_⟩
          · obtain ⟨e₄⟩ := nonempty_pQuot_equiv_subgroupOf p (le_refl K)
            exact ⟨(by rw [← Subgroup.subgroupOf_self (H := K)]; exact e₄ :
              PQuot p (⊤ : Subgroup ↥K) ≃* PQuot p K).trans e₁⟩
          · have hle : GLATwoLocalRank q ↥X ≤ CFSG.Open.pRank p B := by
              by_contra hlt
              exact hA ⟨not_le.1 hlt, h3⟩
            refine (S11.twoLocalRank_mono hq hKX).trans (hle.trans ?_)
            obtain ⟨E, hEB, hEel, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt B
            have hEH : E ≤ H := hEB.trans hBH
            have hE₀ : IsElemAbelian p (E.subgroupOf H) := isElemAbelian_subgroupOf hEel H
            have hE₀B : E.subgroupOf H ≤ B₀ := fun x hx => hEB hx
            refine CFSG.SectionRank.le_pRank hp.one_lt (Subgroup.map_mono hE₀B)
              (CFSG.SectionRank.isElemAbelian_map hE₀ π) ?_
            rw [card_map_of_isPGroup hp π hker (isPGroup_of_isElemAbelian hE₀),
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hEc]
        by_cases hcl : catalogIs (PSimple p S) (onLie S267ClassicalIdx)
        · exact hcls p q hp hp2 hq hq2 hqp _ hKΩ S Bb hSn hSq hSp hChevS hcl hBbel hSB hH2 hB4' hBC'
            hnot' hq'
        · exact hexc p q hp hp2 hq hq2 hqp _ hKΩ S Bb hSn hSq hSp hChevS hcl hBbel hSB hH2 hB4' hBC'
            hnot' hq'
    rcases hdisj with hA' | hBCDE
    · have hA2 := conc267ACov_of_quot hp hp2 N₀ hN K₀ B₀ hNK hK₀n hB₀el hA'
      have hA3 := gConcACov_of_amb hp H hHX K₀ B₀ hA2
      rw [hKm, hBm] at hA3
      obtain ⟨B', D, J, hB'el, hB'X, hIn, hcase, hcard, T, hTX, hT0, hT2, hDT, hcov⟩ := hA3
      exact Or.inl ⟨B', D, J, hB'el, hB'X, hIn, hcase, hcard, Or.inr ⟨T, hTX, hT0, hT2, hDT, hcov⟩⟩
    · have h1 := concBCDE_of_quot hp N₀ hN K₀ B₀ hNK hK₀n hB₀el hBCDE
      have h2 := gConcBCDE_of_amb (p := p) (q := q) hp H K₀ B₀ h1
      rw [hKm, hBm] at h2
      exact Or.inr h2

end Main

end CFSG.LocalAnalysis.GLTheoremA.S267

end
