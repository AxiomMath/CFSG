module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A7Module

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542 CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

theorem exists_offender_budget [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
    (hρ : Function.Injective ρ) {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 7))
    {A : Subgroup G} (hA2 : CFSG.IsElementaryAbelian 2 ↥A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hLA : ⁅L, A⁆ = L)
    (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ B : Subgroup G, B ≤ A ∧ ⁅L, B⁆ = L ∧ (∀ a ∈ B, ∀ c ∈ B, a * c = c * a) ∧
      (∀ b ∈ B, b ^ 2 = 1) ∧
      2 ^ secCod ρ B ⊥ (commOn ρ L ⊤) * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card B := by
  classical
  have : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have := isSimpleGroup_alt7
  have hsimpL : IsSimpleGroup ↥L := eL.isSimpleGroup
  obtain ⟨hq, hLL, -, hLnab⟩ := isQuasisimple_of_mulEquiv center_alt7 exists_ne_comm_alt7 eL
  have hKnt : ¬ L ≤ cenOn ρ L ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := hLnab
    apply hab
    have h1 : ∀ k : ↥L, k = 1 := fun k => by
      apply Subtype.ext
      apply hρ
      ext v
      rw [Subgroup.coe_one, map_one, Module.End.one_apply]
      exact (h k.2).2 v Submodule.mem_top
    rw [h1 a, h1 b]
  obtain ⟨B, hBA, hUinv, hLU, hBU, hbest, hquad, hmove, -⟩ :=
    exists_strictMin_moving (ρ := ρ) L A hA2 hAN hLA hKnt hb
  have hAc : ∀ a ∈ A, ∀ c ∈ A, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A) ⟨c, hc⟩)
  have hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a := fun a ha c hc => hAc a (hBA ha) c (hBA hc)
  have hB2 : ∀ b ∈ B, b ^ 2 = 1 := fun b hb =>
    CFSG.elemPow_eq_one_of_isElementaryAbelian (A := A) b (hBA hb)
  have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBA.trans hAN
  have hLB : ⁅L, B⁆ = L := by
    refine commutator_eq_of_ne_bot hq hBN fun hbot => ?_
    obtain ⟨b, hb, hbc⟩ := Set.not_subset.mp hBU
    obtain ⟨k, hk, u, -, hne⟩ := hmove b hb hbc
    apply hne
    have h1 : ⁅k, b⁆ ∈ ⁅L, B⁆ := Subgroup.commutator_mem_commutator hk hb
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    rw [← Module.End.mul_apply, ← map_mul, ← h1, map_mul, Module.End.mul_apply]
  have hUU : commOn ρ L (commOn ρ L ⊤) = commOn ρ L ⊤ := commOn_commOn_eq hA2 hAN hLA
  have hcen := ms24_comm ρ hBN hLB hUU hquad
  have hbudU := two_pow_secCod_le hbest hcen
  exact ⟨B, hBA, hLB, hBc, hB2, hbudU⟩

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
