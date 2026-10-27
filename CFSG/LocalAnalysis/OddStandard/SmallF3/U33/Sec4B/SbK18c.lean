module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbK18Cop
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbB18n
public import CFSG.GroupTheory.CoprimeCentralizerCover

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G}
  {x₁ x₂ lam rho tau om : G}

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

private lemma cover (hc : Ctx13 t L S x₁ x₂ lam rho tau om) {X : Subgroup G}
    (hΞX : ctxXi t tau x₁ x₂ rho ≤ X)
    (hXN : NormalIn X (ctxK t tau x₁ x₂ rho))
    (hcomm : ⁅X, zpowers rho⁆ ≤ ctxXi t tau x₁ x₂ rho) :
    X ⊓ Subgroup.centralizer ({rho} : Set G) ⊔ ctxXi t tau x₁ x₂ rho = X := by
  have hXnorm : ctxK t tau x₁ x₂ rho ≤ Subgroup.normalizer (X : Set G) :=
    le_normalizer_of_normalIn hXN
  have hΞnorm : ctxK t tau x₁ x₂ rho ≤
      Subgroup.normalizer (ctxXi t tau x₁ x₂ rho : Set G) :=
    le_normalizer_of_normalIn (l18_Xi_normal hc)
  have hrhoK : rho ∈ ctxK t tau x₁ x₂ rho := (l17_mem_K hc).2.2.2.2
  have hRX : zpowers rho ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (hXnorm hrhoK)
  have hRN : zpowers rho ≤ Subgroup.normalizer (ctxXi t tau x₁ x₂ rho : Set G) :=
    Subgroup.zpowers_le.mpr (hΞnorm hrhoK)
  have hR : IsPGroup 3 (zpowers rho) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hc.ord_rho]
    norm_num
  have hN : ¬ 3 ∣ Nat.card (ctxXi t tau x₁ x₂ rho) := by
    obtain ⟨n, hn⟩ := (l18_Xi_pgroup hc).exists_card_eq
    rw [hn]
    intro h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  have hmain := CFSG.GroupTheory.inf_centralizer_sup_eq_of_commutator_le
    (p := 3) hΞX hRX hRN hR hN hcomm
  rwa [centralizer_zpowers_eq rho] at hmain

theorem k18_Xi_idem (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ⁅ctxXi t tau x₁ x₂ rho, zpowers rho⁆ = ctxXi t tau x₁ x₂ rho := by
  have hρ3 : rho ^ 3 = 1 := by
    rw [← hc.ord_rho]
    exact pow_orderOf_eq_one rho
  have hρA : rho ∈ Subgroup.normalizer (ctxOK t tau x₁ x₂ rho : Set G) :=
    le_normalizer_of_normalIn l18_OK_normal (l17_mem_K hc).2.2.2.2
  unfold ctxXi
  exact commutator_commutator_zpowers_eq hρ3 l18_OK_pgroup hρA

theorem k18_OK_eq_Xi_tom (hc : Ctx13 t L S x₁ x₂ lam rho tau om) :
    ctxOK t tau x₁ x₂ rho = ctxXi t tau x₁ x₂ rho ⊔ closure ({t, om} : Set G) := by
  have hcover := cover hc (X := ctxOK t tau x₁ x₂ rho)
    (l18_Xi_le_OK hc) l18_OK_normal le_rfl
  rw [l18_OK_cap_cent_rho hc] at hcover
  rw [← hcover]
  exact sup_comm _ _

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
