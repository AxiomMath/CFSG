module

public import CFSG.HardMathSupport.Dickson.Bal207.Center
import CFSG.HardMathSupport.Dickson.Bal207.U62
import CFSG.Adapters.TauCetiLieModels
import CFSG.GH74.Uniqueness.SU.SU1Basic
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.PSUFour
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TwistedRank
import CFSG.HardMathSupport.Timmesfeld.FieldBonus.UntwistedRank
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.ExcTits
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ReeF4Target
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6LargeRee
public import CFSG.Adapters.TauCetiExceptional.EvenB1
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Orthogonal

public section

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.Open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

theorem rankSylAux_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (e : G ≃* H) (h : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup H)) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨E, -, hE, hc⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hp h
  exact ⟨E.map e.symm.toMonoidHom, hE.map _, by
    rw [Subgroup.card_map_of_injective e.symm.injective, hc]⟩

theorem rankSylAux_of_exists {G H : Type*} [Group G] [Group H] {p : ℕ} (e : G ≃* H)
    (h : ∃ E : Subgroup H, IsElemAbelian p E ∧ Nat.card E = p ^ 2) :
    ∃ E : Subgroup G, IsElemAbelian p E ∧ Nat.card E = p ^ 2 := by
  obtain ⟨E, hE, hc⟩ := h
  exact ⟨E.map e.symm.toMonoidHom, hE.map _, by
    rw [Subgroup.card_map_of_injective e.symm.injective, hc]⟩

section Certified


theorem bal207RankSyl_holds : Bal207RankSyl := by
  intro p d hd hsz
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | B r q =>
    obtain ⟨rfl, h⟩ := hd
    have hp2 : q.p = 2 := by rcases h with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    rcases CFSG.Models.lieModel_B r q hv (MulEquiv.refl _) with hL | hL
    · obtain ⟨⟨-, -, hr, -⟩, ⟨-, K, _, _, -, ⟨e⟩⟩ | ⟨h0, -⟩⟩ := hL
      · exact rankSylAux_of_mulEquiv Nat.prime_three e
          (CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_three_psp hr)
      · omega
    · rw [hp2] at hL
      exact absurd hL.1.2.2.2 (by simp)
  | twistedA r q =>
    obtain ⟨rfl, h⟩ := hd
    have hp2 : q.p = 2 := by rcases h with ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 := by
      rw [← hp2]
      exact TauCeti.LieTypeIndex.characteristic_twistedA r q
    have hL := CFSG.Models.lieModel_twistedA r q hv (MulEquiv.refl _)
    rw [hc] at hL
    obtain ⟨⟨-, -, hn, -⟩, hC | ⟨h0, -⟩⟩ := hL
    · have hn4 : 4 ≤ r + 1 := by
        rcases h with ⟨-, h3⟩ | ⟨-, rfl⟩
        · have : r + 1 ≠ 3 := fun h' => h3 ⟨1, by omega⟩
          omega
        · norm_num
      obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := id hC
      haveI := Finite.of_equiv _ e.symm.toEquiv
      exact rankSylAux_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
        (CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_psu_four hn4
          (by norm_num) hC)
    · omega
  | D r q =>
    obtain ⟨rfl, h⟩ := hd
    have hp2 : q.p = 2 := by
      rcases h with ⟨⟨h, -⟩ | ⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_D r q hv (MulEquiv.refl _)
    rw [hp2] at hL
    obtain ⟨⟨-, hf, hr⟩, ⟨-, K, _, _, hK, ⟨e⟩⟩ | ⟨h0, -⟩⟩ := hL
    · have : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two hf hK
      exact rankSylAux_of_mulEquiv Nat.prime_three e (le_trans (by norm_num)
        (CFSG.SectionRank.ClassicalEven.omegaPlus_three_le_pRank_three hr))
    · omega
  | twistedD r q =>
    obtain ⟨rfl, h, -⟩ := hd
    have hp2 : q.p = 2 := by rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h
    have hL := CFSG.Models.lieModel_twistedD r q hv (MulEquiv.refl _)
    rw [hp2] at hL
    obtain ⟨⟨-, hf, hr⟩, ⟨-, K, _, _, hK, b, c, -, ⟨e⟩⟩ | ⟨h0, -⟩⟩ := hL
    · have : CharP K 2 :=
        CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
          Nat.prime_two hf hK
      exact rankSylAux_of_mulEquiv Nat.prime_three e (le_trans (by norm_num)
        (CFSG.SectionRank.ClassicalEven.omegaMinus_three_le_pRank_three hr b c))
    · omega
  | trialityD4 q =>
    obtain ⟨rfl, hp2, -⟩ := hd
    obtain ⟨K, _, _, -, σ, -, ⟨e⟩⟩ := CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.trialityD4 q hv hp2 (by decide)
      (MulEquiv.refl _)
    haveI := CFSG.LieType.Chevalley.finite_modGL
      (τ := CFSG.Blueprint.Chevalley.TwistTag.D4.tag) (K := K)
    haveI := Finite.of_equiv _ e.symm.toEquiv
    exact rankSylAux_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
      (CFSG.HardMathSupport.Timmesfeld.FieldBonus.two_le_pRank_three_trialityD4
        (MulEquiv.refl _))
  | G2 q =>
    obtain ⟨rfl, hp2, -⟩ := hd
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.g2 q hv hp2 (MulEquiv.refl _)
    exact rankSylAux_of_mulEquiv Nat.prime_three e
      (CFSG.HardMathSupport.Timmesfeld.FieldBonus.Untw.two_le_pRank_three_adjointQuotient
        (Or.inl rfl))
  | F4 q =>
    obtain ⟨rfl, hp2, -⟩ := hd
    obtain ⟨K, _, _, -, ⟨e⟩⟩ := CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
      CFSG.TauCetiBridge.Even.chevalleyBridgesEven.f4 q hv hp2 (MulEquiv.refl _)
    exact rankSylAux_of_mulEquiv Nat.prime_three e
      (CFSG.HardMathSupport.Timmesfeld.FieldBonus.Untw.two_le_pRank_three_adjointQuotient
        (Or.inr (Or.inl rfl)))
  | tits =>
    have hT := CFSG.HardMathSupport.Timmesfeld.Tables.Census.reeTitsModel_tits_of_equiv
      (hv := hv) (MulEquiv.refl _)
    obtain ⟨K, _, _, _, hK, ⟨e⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hT
    rcases hd with rfl | rfl
    · haveI := CFSG.LieType.Chevalley.finite_modGL
        (τ := CFSG.LieType.Ree.ReeTag.F4.tag) (K := K)
      haveI := Finite.of_equiv _ e.symm.toEquiv
      exact rankSylAux_of_mulEquiv Nat.prime_three (MulEquiv.refl _)
        (CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_of_titsModel hT)
    · obtain ⟨x, y, -, hx, hy, hxy, hcard, -⟩ :=
        CFSG.SectionRank.Tits_sylow5_square_witness (K := K) hK
      exact rankSylAux_of_exists e
        ⟨_, CFSG.SectionRank.isElemAbelian_closure_pair hx hy hxy, hcard⟩
  | suzuki m => exact (hsz ⟨hd.1, hd.2⟩).elim
  | reeF4 m =>
    obtain ⟨rfl, rfl⟩ := hd
    have hX := CFSG.AGLEmbedding.reeTitsModel_of_catGroup_reeF4 (d := ⟨.reeF4 2, hv⟩) rfl
    obtain ⟨a, K, _, _, _, -, hfa, hK, ⟨e⟩⟩ :=
      CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hX
    obtain rfl : a = 2 := by omega
    exact rankSylAux_of_exists e
      (CFSG.AGLEmbedding.exists_elemAbelian_twentyfive_reeGamma (K := K) hK)
  | A r q => exact absurd hd (by simp [Bal207Index])
  | C r q => exact absurd hd (by simp [Bal207Index])
  | E6 q => exact absurd hd (by simp [Bal207Index])
  | E7 q => exact absurd hd (by simp [Bal207Index])
  | E8 q => exact absurd hd (by simp [Bal207Index])
  | twistedE6 q => exact absurd hd (by simp [Bal207Index])
  | reeG2 m => exact absurd hd (by simp [Bal207Index])

theorem bal207Rank_holds (hGA : GriessAllModelsStatement) : Bal207Rank :=
  bal207Rank_of_griess hGA bal207RankSyl_holds (bal207RankU62_of_griess hGA)

end Certified

end CFSG.HardMathSupport.Dickson.Bal207
