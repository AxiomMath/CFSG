module

public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7TrFi
public import CFSG.HardMathSupport.Solomon.Coordinator.I22_7TrSub

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs

section Cover

variable {K : Type} [Group K] [Finite K]

theorem i227m_primeCore_three_le_five
    (hK : FiCoverK K) :
    GLAPPrimeCore 3 K ≤ GLAPPrimeCore 5 K := by
  obtain ⟨hs, -, h3⟩ := i227m_fi22_facts hK.fi
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := GLAPPrimeCore 5 K with hR
  set Y := GLAPPrimeCore 3 K with hY
  have hn : (Y.map (QuotientGroup.mk' R)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective R)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map (QuotientGroup.mk' R)) with h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    have h1 : Nat.card (K ⧸ R) ∣ Nat.card Y := by
      have := Subgroup.card_map_dvd Y (QuotientGroup.mk' R)
      rw [h, Subgroup.card_top] at this
      exact this
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card)
      (h3.trans h1)

theorem i227m_fiCoverK_quotient (hK : FiCoverK K) (Y : Subgroup K) [Y.Normal]
    (hY : Y ≤ GLAPPrimeCore 5 K) : FiCoverK (K ⧸ Y) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set ψ : K →* K ⧸ Y := QuotientGroup.mk' Y with hψ
  have hsurj : Function.Surjective ψ := QuotientGroup.mk'_surjective Y
  have hcop : Nat.Coprime 5 (Nat.card ↥((⊤ : Subgroup K) ⊓ ψ.ker)) := by
    rw [hψ, QuotientGroup.ker_mk', top_inf_eq]
    exact CFSG.pPrimeCore_coprime_card.coprime_dvd_right (Subgroup.card_dvd_of_le hY)
  have hcore : (GLAPPrimeCore 5 K).map ψ = GLAPPrimeCore 5 (K ⧸ Y) := by
    refine glaPPrimeCore_map_of_surjective Nat.prime_five ψ hsurj ?_
    rw [hψ, QuotientGroup.ker_mk']
    exact CFSG.pPrimeCore_coprime_card.coprime_dvd_right (Subgroup.card_dvd_of_le hY)
  refine ⟨i227m_openKGroup_of_surjective hK.kgroup ψ hsurj, ?_, ?_, ?_⟩
  · have : Group.IsPerfect K := Group.isPerfect_def.2 hK.perfect
    exact (Group.IsPerfect.ofSurjective hsurj).commutator_eq_top
  · have h1 := i227m_glaPLayer_map Nat.prime_five ψ hcop
    rw [Subgroup.map_top_of_surjective ψ hsurj, hK.layer] at h1
    rw [h1, Subgroup.map_top_of_surjective ψ hsurj]
  · obtain ⟨e⟩ := hK.fi
    refine ⟨?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient Y _ hY)).trans e

theorem i227m_primeCore_three_quotient :
    ∀ (K : Type) [Group K] [Finite K], GLAPPrimeCore 3 (K ⧸ GLAPPrimeCore 3 K) = ⊥ := by
  intro K _ _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Y := GLAPPrimeCore 3 K with hY
  set Z := GLAPPrimeCore 3 (K ⧸ Y) with hZ
  have hcopZ : Nat.Coprime 3 (Nat.card Z) := CFSG.pPrimeCore_coprime_card
  have hcopY : Nat.Coprime 3 (Nat.card Y) := CFSG.pPrimeCore_coprime_card
  have hpre : Nat.Coprime 3 (Nat.card (Z.comap (QuotientGroup.mk' Y))) := by
    have h : Nat.card (Z.comap (QuotientGroup.mk' Y)) = Nat.card Y * Nat.card Z :=
      QuotientGroup.card_preimage_mk Y (Z : Set (K ⧸ Y))
    rw [h]
    exact hcopY.mul_right hcopZ
  have hnorm : (Z.comap (QuotientGroup.mk' Y)).Normal := Subgroup.Normal.comap inferInstance _
  have hle : Z.comap (QuotientGroup.mk' Y) ≤ Y := le_sSup ⟨hnorm, hpre⟩
  have h2 : Z ≤ Y.map (QuotientGroup.mk' Y) := by
    calc Z = (Z.comap (QuotientGroup.mk' Y)).map (QuotientGroup.mk' Y) :=
          (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Y) Z).symm
      _ ≤ _ := Subgroup.map_mono hle
  rw [(Subgroup.map_eq_bot_iff Y).2 (by rw [QuotientGroup.ker_mk'])] at h2
  exact le_bot_iff.1 h2

end Cover

end CFSG.HardMathSupport.Solomon.Coordinator
