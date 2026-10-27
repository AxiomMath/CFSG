module

public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VBar
public import CFSG.HardMathSupport.Solomon.Coordinator.I11_2VSylow
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Timmesfeld.ComponentBalance

theorem lemma27_input11_2Four_of_tables (T : Tables112) (TL : TableL2) (TT : Tables112Types)
    (TM : Tables112More) : Lemma27Ns.Input11_2Four := by
  intro G _ _ m hS X B L hB hBX hr hL hnL hZne R
  obtain ⟨hp, -, -, hQK, hQcore, hBel, hrankQ, hLbar, hnLQ⟩ := i112v_bar hS hB hBX hr hL hnL
  obtain ⟨-, -, -, -, -, hcase⟩ :=
    i112v_core T TL TT TM hQK hp (by norm_num) hQcore hBel hrankQ hLbar hnLQ
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have hJ : barX 3 X (bClosure B L) = i112J (barX 3 X B) (barX 3 X L) :=
    i112f_barX_bClosure hBX hL.1
  rw [hJ] at hZne
  obtain ⟨hZ3', ht5⟩ : Nat.card (Subgroup.center ↥(barX 3 X L)) = 3 ∧
      (IsHatSix ↥(barX 3 X L) ∨ IsHatSeven ↥(barX 3 X L) ∨ IsHatMTwentyTwo ↥(barX 3 X L) ∨
        IsSLThreeExc ↥(barX 3 X L) ∨ IsSUThreeExc ↥(barX 3 X L)) := by
    rcases hcase with ⟨-, hZb, -, -⟩ | ⟨h3, ht5, -⟩
    · exfalso
      apply hZne
      have h1 : (Subgroup.center ↥(i112J (barX 3 X B) (barX 3 X L))).map
          (i112J (barX 3 X B) (barX 3 X L)).subtype = ⊥ := by
        rw [map_subtype_center]
        exact hZb
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h1
    · exact ⟨h3, ht5⟩
  have e : barOf 3 L ≃* ↥(barX 3 X L) := quotEquivBarX hp hL.1 hL.2.1
  have hq' : CFSG.Open.IsQuasisimple ↥(barX 3 X L) := i116e_isQuasisimple hQcore hLbar
  have hK' : CFSG.Open.IsKGroup ↥(barX 3 X L) := isKGroup_of_le hQK _
  have hsyl := i112v_sylow_facts_of_mulEquiv e (TM.T10_10S _ hq' hK' ht5)
  have hZ3 : Nat.card (Subgroup.center (barOf 3 L)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact hZ3'
  set f : ↥L →* barOf 3 L := QuotientGroup.mk' (GLAPPrimeCore 3 ↥L) with hfdef
  have hf : Function.Surjective f := QuotientGroup.mk'_surjective _
  set R' : Sylow 3 (barOf 3 L) := R.mapSurjective hf with hR'
  have hR'c : (R' : Subgroup (barOf 3 L)) = (R : Subgroup ↥L).map f := rfl
  obtain ⟨hc, hna, hexp⟩ := hsyl R'
  obtain ⟨hZR, hZeq⟩ := i112v_sylow_center hZ3 R' hc hna
  rw [hR'c] at hc hna hexp hZR
  have hker : Nat.Coprime 3 (Nat.card f.ker) := by
    rw [hfdef, QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card
  have hRp : IsPGroup 3 (R : Subgroup ↥L) := R.isPGroup'
  refine ⟨?_, ?_, ?_, hZR, ?_⟩
  · exact (i112v_card_map_eq f hker hRp).symm.trans hc
  · intro hcomm
    obtain ⟨r, hr, s, hs, hrs⟩ := hna
    obtain ⟨r₀, hr₀, rfl⟩ := hr
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    exact hrs (by rw [← map_mul, ← map_mul, hcomm r₀ hr₀ s₀ hs₀])
  · intro r hr
    have h3 := hexp (f r) ⟨r, hr, rfl⟩
    rw [← map_pow] at h3
    exact i112v_eq_one_of_mem_ker f hker hRp (Subgroup.pow_mem _ hr 3) h3
  · intro w hw hcw
    rw [← hZeq]
    rw [← hR'c] at hw hcw
    refine ⟨⟨w, hw⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (hcw g g.2).symm

end CFSG.HardMathSupport.Solomon.Coordinator
