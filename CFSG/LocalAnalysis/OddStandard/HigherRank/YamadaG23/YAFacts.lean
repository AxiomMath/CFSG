module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FactsS
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

private theorem card_sup_mul_card_inf_of_commute_aux {H : Type*} [Group H] [Finite H]
    (L R : Subgroup H) (hc : ∀ x ∈ L, ∀ y ∈ R, x * y = y * x) :
    Nat.card (L ⊔ R : Subgroup H) * Nat.card (L ⊓ R : Subgroup H) =
      Nat.card L * Nat.card R := by
  let μ : L × R →* H := MonoidHom.noncommCoprod L.subtype R.subtype fun x y => hc x x.2 y y.2
  have hμ : ∀ x : L × R, μ x = (x.1 : H) * x.2 := fun _ => rfl
  have hrange : μ.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [hμ]
      exact mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
    · refine sup_le (fun l hl => ⟨(⟨l, hl⟩, 1), by rw [hμ]; simp⟩)
        (fun r hr => ⟨(1, ⟨r, hr⟩), by rw [hμ]; simp⟩)
  have hker : Nat.card μ.ker = Nat.card (L ⊓ R : Subgroup H) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1.1 : H), x.1.1.2, ?_⟩
        invFun := fun z => ⟨(⟨z, z.2.1⟩, ⟨(z : H)⁻¹, inv_mem z.2.2⟩), ?_⟩
        left_inv := fun x => ?_
        right_inv := fun z => rfl }
    · have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_eq_inv] at h
      rw [h]
      exact R.inv_mem x.1.2.2
    · rw [MonoidHom.mem_ker, hμ]
      exact mul_inv_cancel _
    · apply Subtype.ext
      have h := x.2
      rw [MonoidHom.mem_ker, hμ, mul_eq_one_iff_inv_eq] at h
      exact Prod.ext rfl (Subtype.ext h)
  have := Subgroup.card_ker_mul_card_range μ
  rw [hrange, hker, Nat.card_prod] at this
  rw [mul_comm]
  exact this

theorem A_facts {Γ : Type} [Group Γ] [Finite Γ] (fr : Frame Γ) (h : fr.Fact14) :
    Nat.card ↥fr.A = 32 ∧ (∀ a ∈ fr.A, ∀ b ∈ fr.A, ⁅a, b⁆ ∈ fr.Z) ∧
      (∀ a ∈ fr.A, a ^ 2 ∈ fr.Z) ∧ (∃ a ∈ fr.A, ∃ b ∈ fr.A, a * b ≠ b * a) ∧ fr.z ∈ fr.A ∧
      orderOf fr.z = 2 ∧ cen fr.A = fr.Z := by
  obtain ⟨-, ⟨hU, hV, hcomm, hsup, hinf, hext, -⟩, -⟩ := h
  obtain ⟨hAcard, hcen2, hcommut, hsq⟩ := hext
  have hA32 : Nat.card ↥fr.A = 32 := by
    rw [hAcard]
    norm_num
  obtain ⟨eU⟩ := hU
  obtain ⟨eV⟩ := hV
  have hcardU : Nat.card ↥(closure {fr.a₁, fr.b₁} : Subgroup Γ) = 8 := by
    rw [Nat.card_congr eU.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hcardV : Nat.card ↥(closure {fr.a₂, fr.b₂} : Subgroup Γ) = 8 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hprod := card_sup_mul_card_inf_of_commute_aux
    (closure {fr.a₁, fr.b₁} : Subgroup Γ) (closure {fr.a₂, fr.b₂} : Subgroup Γ) hcomm
  have hZcard : Nat.card ↥fr.Z = 2 := by
    rw [hsup, hinf, hcardU, hcardV, hA32] at hprod
    norm_num at hprod
    omega
  have hb₁A : fr.b₁ ∈ fr.A := by
    show fr.b₁ ∈ closure ({fr.a₁, fr.b₁, fr.a₂, fr.b₂} : Set Γ)
    exact Subgroup.subset_closure (by simp)
  have hzA : fr.z ∈ fr.A := by
    rw [SFrame.z]
    exact Subgroup.pow_mem fr.A hb₁A 2
  have hz_cen : fr.z ∈ cen fr.A := by
    rw [SFrame.z]
    exact hsq fr.b₁ hb₁A
  have hZle : fr.Z ≤ cen fr.A := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr hz_cen
  have hZeq : fr.Z = cen fr.A := by
    refine Subgroup.eq_of_le_of_card_ge hZle ?_
    rw [hcen2, hZcard]
  refine ⟨hA32, ?_, ?_, ?_, hzA, ?_, hZeq.symm⟩
  · intro a ha b hb
    have hmem : ⁅a, b⁆ ∈ ⁅fr.A, fr.A⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [hcommut] at hmem
    rwa [hZeq]
  · intro a ha
    have hmem : a ^ 2 ∈ cen fr.A := hsq a ha
    rwa [hZeq]
  · by_contra hnab
    have hab : ∀ a ∈ fr.A, ∀ b ∈ fr.A, a * b = b * a := fun a ha b hb => by
      by_contra hne
      exact hnab ⟨a, ha, b, hb, hne⟩
    have hbot : ⁅fr.A, fr.A⁆ ≤ (⊥ : Subgroup Γ) := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hab a ha b hb
    have hcenbot : cen fr.A = ⊥ := bot_unique (hcommut ▸ hbot)
    have : Nat.card (cen fr.A) = 1 := by rw [hcenbot]; exact Subgroup.card_bot
    omega
  · have h1 : orderOf fr.z = Nat.card ↥fr.Z := by
      rw [SFrame.Z]
      exact (Nat.card_zpowers (a := fr.z)).symm
    exact h1.trans hZcard

end CFSG.OddStandard.HigherRank.YamadaG23
