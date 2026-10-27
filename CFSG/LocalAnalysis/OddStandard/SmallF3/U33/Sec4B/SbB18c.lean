module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18b
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbE17a
public import CFSG.GroupTheory.CoprimeCentralizerCover

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G} {𝒮 : Subgroup G}

private lemma centralizer_zpowers_eq (rho : G) :
    Subgroup.centralizer (Subgroup.zpowers rho : Set G) =
      Subgroup.centralizer ({rho} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private lemma le_normalizer_of_normalIn {A B : Subgroup G} (h : NormalIn A B) :
    B ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => h.2 g hg a ha, fun ha => ?_⟩
  have hmem := h.2 g⁻¹ (B.inv_mem hg) (g * a * g⁻¹) ha
  have heq : g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a := by group
  rwa [heq] at hmem

private lemma cover (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) {X : Subgroup G}
    (hΞX : ctxXi t tau x₁ x₂ rho ≤ X)
    (hXN : NormalIn X (ctxK t tau x₁ x₂ rho))
    (hcomm : ⁅X, zpowers rho⁆ ≤ ctxXi t tau x₁ x₂ rho) :
    X ⊓ Subgroup.centralizer ({rho} : Set G) ⊔ ctxXi t tau x₁ x₂ rho = X := by
  have hXnorm : ctxK t tau x₁ x₂ rho ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_normalIn hXN
  have hΞnorm : ctxK t tau x₁ x₂ rho ≤
      Subgroup.normalizer (ctxXi t tau x₁ x₂ rho : Set G) :=
    le_normalizer_of_normalIn (l18_Xi_normal hc.toCtx13)
  have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc.toCtx13).2.2.2.2
  have hRX : zpowers rho ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (hXnorm hrhoK)
  have hRN : zpowers rho ≤ Subgroup.normalizer (ctxXi t tau x₁ x₂ rho : Set G) :=
    Subgroup.zpowers_le.mpr (hΞnorm hrhoK)
  have hR : IsPGroup 3 (zpowers rho) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.ord_rho]
    norm_num
  have hN : ¬ 3 ∣ Nat.card (ctxXi t tau x₁ x₂ rho) := by
    obtain ⟨n, hn⟩ := (l18_Xi_pgroup hc.toCtx13).exists_card_eq
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hmain := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) hΞX hRX hRN hR hN hcomm
  rwa [centralizer_zpowers_eq rho] at hmain

theorem l18_OK_eq_Xi_sup (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxOK t tau x₁ x₂ rho = ctxXi t tau x₁ x₂ rho ⊔ closure {t, om} := by
  have hcover := cover hc (X := ctxOK t tau x₁ x₂ rho)
    (l18_Xi_le_OK hc.toCtx13) l18_OK_normal le_rfl
  rw [l18_OK_cap_cent_rho hc.toCtx13] at hcover
  rw [← hcover]
  exact sup_comm _ _

theorem l18_C_eq_Xi_sup (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxCY t tau x₁ x₂ rho = ctxXi t tau x₁ x₂ rho ⊔ closure {tau, om} := by
  have hcomm : ⁅ctxCY t tau x₁ x₂ rho, zpowers rho⁆ ≤ ctxXi t tau x₁ x₂ rho := by
    have h := Subgroup.commutator_mono (l18_C_le_OK hc.toCtx13)
      (le_refl (zpowers rho))
    simpa only [ctxXi] using h
  have hcover := cover hc (X := ctxCY t tau x₁ x₂ rho)
    (l18_Xi_le_C hc) (l18_C_normal hc.toCtx13) hcomm
  rw [l18_C_cap_cent_rho hc.toCtx13] at hcover
  rw [← hcover]
  exact sup_comm _ _

theorem l18_Xi_cap_tom (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    ctxXi t tau x₁ x₂ rho ⊓ closure {t, om} = ⊥ := by
  have hle : closure ({t, om} : Set G) ≤ Subgroup.centralizer ({rho} : Set G) := by
    rw [← l18_OK_cap_cent_rho hc.toCtx13]
    exact inf_le_right
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_bot]
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [← l18_Xi_cap_cent_rho hc]
    exact ⟨hx.1, hle hx.2⟩
  exact Subgroup.mem_bot.mp hxbot

theorem l18_card_Xi (hc : Ctx18B t L S x₁ x₂ lam rho tau om 𝒮) :
    Nat.card (ctxXi t tau x₁ x₂ rho) = 2 ^ 8 := by
  have htomK : closure ({tau, om} : Set G) ≤ ctxK t tau x₁ x₂ rho := by
    rw [Subgroup.closure_le]
    rintro a (ha : a ∈ ({tau, om} : Set G))
    rcases ha with rfl | rfl
    · exact (l17_mem_K hc.toCtx13).2.1
    · exact (l17_mem_K hc.toCtx13).2.2.1
  have hnorm : ∀ k ∈ closure ({tau, om} : Set G), ∀ h ∈ ctxXi t tau x₁ x₂ rho,
      k * h * k⁻¹ ∈ ctxXi t tau x₁ x₂ rho := fun k hk h hh =>
    (l18_Xi_normal hc.toCtx13).2 k (htomK hk) h hh
  have hle : closure ({tau, om} : Set G) ≤ Subgroup.centralizer ({rho} : Set G) := by
    rw [← l18_C_cap_cent_rho hc.toCtx13]
    exact inf_le_right
  have hbot : ctxXi t tau x₁ x₂ rho ⊓ closure {tau, om} = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← l18_Xi_cap_cent_rho hc]
      exact ⟨hx.1, hle hx.2⟩
    exact Subgroup.mem_bot.mp hxbot
  have hcardmul := card_sup_eq_mul (H := ctxXi t tau x₁ x₂ rho)
    (K := closure ({tau, om} : Set G)) hnorm hbot
  rw [l17_card_tauom hc.toCtx13, ← l18_C_eq_Xi_sup hc, hc.card_C] at hcardmul
  have h1024 : Nat.card (ctxXi t tau x₁ x₂ rho) * 4 = 1024 := by
    rw [← hcardmul]
    norm_num
  have h256 : Nat.card (ctxXi t tau x₁ x₂ rho) = 256 := by omega
  rw [h256]
  norm_num

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
