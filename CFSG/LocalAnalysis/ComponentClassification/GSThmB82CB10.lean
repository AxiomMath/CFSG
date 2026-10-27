module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB9
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB7
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CB8

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Eight2

theorem gs82CaseB (hSy : CFL2Sylow) (hC : CFL2C) (hJ : CFL2J) (hRank : CFL2Rank)
    (hJo : CFSec8JOrder) (hComm : CF82L2Comm) (hCyc : CF82L2Cyc) (hAZ : CF82AZ) :
    ∀ (X : Type) [Group X] [Finite X] (s : Eight2.Setting3 X),
      ¬ normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X) →
      (Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10)) →
        Nat.card (s.h.secB0 s.y) = 2) →
      (Nat.card (s.h.secB0 s.y) = 2 →
        ∀ u ∈ normalizer (s.h.S : Set X), u * u ∈ s.h.S → u⁻¹ * s.h.a * u ∈ s.h.D →
          ∀ b ∈ s.h.secB0 s.y, ∀ d ∈ s.h.D, u⁻¹ * b * u * d = d * (u⁻¹ * b * u)) → False := by
  intro X _ _ s hNS hOS8 hOS9
  obtain ⟨Z⟩ := exists_zData hSy hC hJ hRank hJo s.case8 s.center_J
  have hD8 := card_D_ge_eight hJo s.case8
  have haS := a_mem_commutator s.secCond.mem_P s.lemma61
  have hzS' := z_mem_commutator Z hD8
  obtain ⟨u, hu, hua, huz, huu⟩ := exists_swap hComm Z s.S_sylow s.C_eq s.center_J
    s.eight_le_card_P haS hzS' hNS
  have hua' : u⁻¹ * s.h.a * u ≠ s.h.a := by
    rw [hua]
    exact fun h1 => Z.hzP (h1 ▸ s.h.a_mem_P)
  have hB2 : Nat.card (s.h.secB0 s.y) = 2 := by
    by_cases hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))
    · exact hOS8 hA
    · exact s.card_B0_eq_two hCyc hA hu hua'
  obtain ⟨⟨b, hbB0⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp s.B0_ne_bot
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hB0 : ∀ c ∈ s.h.secB0 s.y, c = 1 ∨ c = b := fun c hc =>
    eq_one_or_of_card_two hB2 hbB0 hc hb1'
  have hbb : b * b = 1 := by
    rcases hB0 (b * b) (mul_mem hbB0 hbB0) with h | h
    · exact h
    · exfalso
      apply hb1'
      calc b = b * b * b⁻¹ := by group
        _ = 1 := by rw [h, mul_inv_cancel]
  have hbP : b ∈ s.h.P := s.B0_le_P hbB0
  have hba : b ≠ s.h.a := by
    intro h
    have h1 : s.h.a ∈ s.h.B ⊓ zpowers s.h.a :=
      mem_inf.mpr ⟨h ▸ s.h.secB0_le_B s.y hbB0, mem_zpowers _⟩
    rw [s.NP_eq.2.1, mem_bot] at h1
    have h2 := s.h.orderOf_a
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hbD := hOS9 hB2 u hu huu (hua ▸ Z.hzD) b hbB0
  have hbuS : u⁻¹ * b * u ∈ s.h.S := by
    have := (mem_normalizer_iff.mp (inv_mem hu) b).mp (s.h.P_le_S hbP)
    rwa [inv_inv] at this
  obtain ⟨r, hrG, b₀, hb₀, hr⟩ := s.exists_r hAZ Z
  have hrb' : r⁻¹ * b * r = b := by
    have h1 : r⁻¹ * b * r ∈ s.h.secB0 s.y := by
      have := (mem_normalizer_iff.mp (inv_mem hrG) b).mp hbB0
      rwa [inv_inv] at this
    rcases hB0 _ h1 with h2 | h2
    · exfalso
      apply hb1'
      calc b = r * (r⁻¹ * b * r) * r⁻¹ := by group
        _ = 1 := by rw [h2]; group
    · exact h2
  have hrb : r * b = b * r := by
    calc r * b = r * (r⁻¹ * b * r) := by rw [hrb']
      _ = b * r := by group
  have hrab : r⁻¹ * (s.h.a * b) * r = Z.z ∨ r⁻¹ * (s.h.a * b) * r = Z.z * b := by
    have hsplit : r⁻¹ * (s.h.a * b) * r = (r⁻¹ * s.h.a * r) * (r⁻¹ * b * r) := by group
    rcases hB0 b₀ hb₀ with rfl | rfl
    · right
      rw [hsplit, hr, hrb', mul_one]
    · left
      rw [hsplit, hr, hrb', mul_assoc, hbb, mul_one]
  exact CtxB.elim
    { h := s.h
      hSa := s.S_sylow
      hJn := s.J_normal
      hC := s.C_eq
      hZJ := s.center_J
      z := Z.z
      u := u
      b := b
      r := r
      hzD := Z.hzD
      hzS := Z.hzS
      hzz := Z.hzz
      hz1 := Z.hz1
      hzP := Z.hzP
      hu := hu
      hua := hua
      huz := huz
      huu := huu
      hbP := hbP
      hbb := hbb
      hb1 := hb1'
      hba := hba
      hnaz := not_conj_a_az Z s.S_sylow s.C_eq s.center_J s.eight_le_card_P
      hrb := hrb
      hrab := hrab
      hInn := innOf_le_rhoImg Z s.C_eq hu hua huz huu hbP hbb hb1' hba hbD
      he := rhoE_b'_comm hbuS hbD
      hZD := Z.hZD
      hsq := Z.hsq
      hprod := Z.hprod
      hC4 := Z.hC4
      hJ8 := Z.hJ8
      hRk := Z.hRk }

end Eight2

end CFSG.ComponentClassification.GSThmB
