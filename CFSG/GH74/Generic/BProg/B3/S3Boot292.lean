module

public import CFSG.GH74.Generic.BProg.B3.S3Boot172

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

section SD18

variable {G : Type} [Group G] [Finite G]

@[expose] def Lemma291 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x a : G) (K A D J : Subgroup G), B_B2_g4 → Ctx21 G x K A a D J →
    QShape3 (↥K ⧸ pPrimeCore 2 ↥K) → ∀ y₁ : G, y₁ ∈ A ⊓ K → y₁ ≠ 1 →
      ∃ Lb : Subgroup (CentralizerBar x), IsAdmPair x K A y₁ Lb ∧ ¬ NbhdSemisimple x y₁ Lb

@[expose] def Sec29Final (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (x a : G) (K A D J : Subgroup G), Ctx21 G x K A a D J →
    B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K) → 1 < pRank 2 ↥(CxK x K) →
    (∀ B : Subgroup G, IsExtSource2 x K A B → pRank 2 ↥B = 4 →
      ¬ (A7InGamma K A B ∧ IsKBal 3 B ∧ IsWeakKBal 2 B)) → False

theorem prop292_sd (hKG : BootKG G) (hB2 : B_B2_g4) (h291 : Lemma291 G) (hFin : Sec29Final G)
    {x a : G} {K A D J : Subgroup G} (hc : Ctx21 G x K A a D J)
    (hSD : B1.QShape3SD (↥K ⧸ pPrimeCore 2 ↥K)) : pRank 2 ↥(CxK x K) ≤ 1 := by
  by_contra hC
  push Not at hC
  have h3 : QShape3 (↥K ⧸ pPrimeCore 2 ↥K) := hSD.qShape3
  by_cases hex : ∃ B : Subgroup G, IsExtSource2 x K A B ∧ pRank 2 ↥B = 4 ∧
      (A7InGamma K A B ∧ IsKBal 3 B ∧ IsWeakKBal 2 B)
  · obtain ⟨B, hext, hB4, h8, hbal, hweak⟩ := hex
    have hZ := B1.PilotS3.center_trivial_of_shape3 hc.circ.1.1.1.2.2 h3
    obtain ⟨E, hEK, hAE, -, hEel, hE4⟩ := S3Theta52.exists_E_of_src hc.src hZ
    obtain ⟨y₁, hy₁E, hy₁1⟩ : ∃ e ∈ E, e ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 h
      rw [hbot, Subgroup.card_bot] at hE4
      omega
    have hy₁E' : y₁ ∈ A ⊓ K :=
      ⟨hAE ▸ Subgroup.mem_sup_left hy₁E, hEK hy₁E⟩
    obtain ⟨Lb, hadm, hns⟩ := h291 x a K A D J hB2 hc h3 y₁ hy₁E' hy₁1
    have hBadm : IsBAdmPair x K B y₁ Lb :=
      adm29E_of_ctx hc h3 hy₁E' hadm hext hB4
    exact prop172_p2 hKG hB2 hc h3 hext hB4 hBadm hns h8 ⟨hbal, hweak⟩
  · exact hFin x a K A D J hc hSD hC fun B hext hB4 hG => hex ⟨B, hext, hB4, hG⟩

end SD18

end CFSG.GH74.Generic.BProg.B3
