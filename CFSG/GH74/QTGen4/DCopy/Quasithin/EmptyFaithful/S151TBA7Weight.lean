module

public import CFSG.Quasithin.EmptyFaithful.S151TBA7Weight
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.C2Seven

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}

theorem input15120A7Weight_of_c27_F4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hC27 : ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G], ASC27Statement_F4 G) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
      Ctx15120 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → L ∈ cComp (g1_1516 Z₁) →
      ∀ α : ↥L →* alternatingGroup (Fin 7), IsAltBlockTypeWith L 7 α →
        ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
          (∀ x : ↥L, (x : G) ∈ s1516 T Z₁ → permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v) ∧
          ∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar hcomp α hα
  have hq := hc.hL.quasi

  have hQ : LStar L ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.quotientMulEquivOfEq hα.2.1.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (LStar L) := hQ.isSimpleGroup
  have hcen : Subgroup.center (LStar L) = ⊥ := center_eq_bot_of_simple hs hq
  have hD : ListD' L := Or.inl ⟨((QuotientGroup.quotientMulEquivOfEq hcen).trans
    QuotientGroup.quotientBot).trans hQ⟩
  have hN := g1_le_normalizer h37 h38 hc hcomp hD
  have hRN : q1_1516 Mc Z₁ ≤ Subgroup.normalizer (L : Set G) :=
    (q1_1516_le Mc Z₁).trans ((mZ1516_le_g1 Mc Z₁).trans hN)
  have hSN : s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) := (s1516_le_g1 T Z₁).trans hN
  have hMR : mZ1516 Mc Z₁ ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := fun x hx => by
    have : x ∈ g1_1516 Z₁ ⊓ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := hc.h18.five.2.1 ▸ hx
    exact this.2
  have hO2M := pCore_le_mZ hc hcomp hN
  have hcard7 : Nat.card (LStar L) = 2520 := by
    rw [Nat.card_congr hQ.toEquiv, CFSG.Quasithin.Vol2.Ch10.SecA.card_alt 7 (by norm_num)]
    decide
  obtain ⟨h1, -, h3⟩ := hC27 G (g1_1516 Z₁) (q1_1516 Mc Z₁) (mZ1516 Mc Z₁) L
    (omegaOneCenterOf (pCoreOf 2 (L ⊔ q1_1516 Mc Z₁))) hc.h18.five.2.2 hcomp hq hchar
    hc.hL.not_le hRN rfl
  suffices key : ∃ v : ↥(evenWeight 7), HasWeightTwo (v : Fin 7 → ZMod 2) ∧
      ∀ x : ↥L, (x : G) ∈ mZ1516 Mc Z₁ ↔ permWeight 7 (α x : Equiv.Perm (Fin 7)) v = v by
    obtain ⟨v, hv2, hv⟩ := key
    exact ⟨v, hv2, fun x hx => (hv x).1 (s_le_mZ hc hx), hv⟩
  rcases h3 with ⟨hchi, hcases⟩ | ⟨⟨n, α', hn5, hn8, hsh, hα', t, htR, htV, hRact, -, σ, hσ, hconj⟩,
    hMK⟩ | ⟨hHat, -⟩ | ⟨hexc, hidx⟩ | ⟨hAS, -⟩ | ⟨hg, -, -⟩ |
    ⟨⟨n, F, _, _, hn1, hF, ⟨e⟩⟩, -, -⟩ | ⟨hh, -, -⟩
  · rcases hcases with ⟨⟨n, hn, hlin⟩, -⟩ | ⟨hA5, -⟩ | ⟨-, hD8, e, P, hP, hMap⟩ |
      ⟨-, hE8, e, P, hP, hMap⟩
    · exact (listD'_false_of_lin2 hq hn hlin hD).elim
    · obtain ⟨α5, hα5⟩ := (isAltType_iff_exists_isAltBlockTypeWith (by decide)).1 hA5
      exact (listD'_false_of_alt hq (Or.inl rfl) hα5 hD).elim
    · exact (false_of_case_iii hMR hD8 e hP hMap).elim
    · obtain ⟨v, hv⟩ := stab_le_mZ hc hcomp hchi.1.1 hSN hα
      exact (false_of_case_iv hRN h1 hcen hα e hP hMap v hv).elim
  · have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    · exact (listD'_false_of_alt hq (Or.inl rfl) hα' hD).elim
    · exact (false_of_alt_six_seven hα' hα).elim
    · obtain ⟨p, q, hpq, rfl⟩ := hσ
      exact weight_two_of_case_b hRN h1 hcen hO2M hα hα' htR htV hRact hpq hconj hMK
    · exact (listD'_false_of_alt hq (Or.inr rfl) hα' hD).elim
  · have h3 := hHat.2.1.2.1
    rw [hcen] at h3
    simp at h3
  · exact (not_excA7_index hc hcomp hSN hexc hidx).elim
  · rcases hAS with ⟨-, α6, hα6⟩ | hsp4
    · exact (false_of_alt_six_seven hα6 hα).elim
    · exact (listD'_false_of_sp4 hq hsp4 hD).elim
  · have h6048 := CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three hg.2.1
    rw [hcard7] at h6048
    exact absurd h6048 (by norm_num)
  · obtain ⟨ψ₀, hψ₀, hO2, hker⟩ := exists_epi_autOn hRN h1
    exact (listD'_false_of_sl3 hq hn1 hF (e.toMonoidHom.comp ψ₀)
      (e.surjective.comp hψ₀) (fun x hx => by
        have := hO2 hx
        simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
        simpa using hx)) hD).elim
  · obtain ⟨ψ₀, hψ₀, hO2, hker⟩ := exists_epi_autOn hRN h1
    rcases hh with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (listD'_false_of_sl4 hq (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀)
        (fun x hx => by
          have := hO2 hx
          simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
          simpa using hx)) hD).elim
    · exact (listD'_false_of_sl5 hq (e.toMonoidHom.comp ψ₀) (e.surjective.comp hψ₀)
        (fun x hx => by
          have := hO2 hx
          simpa [MonoidHom.mem_ker] using this) (fun x hx => hker x (by
          simpa using hx)) hD).elim

end CFSG.Quasithin.S151TB
