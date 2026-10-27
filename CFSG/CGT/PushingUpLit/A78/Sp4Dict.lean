module

public import CFSG.CGT.PushingUpLit.A78.Sp4Count
public import CFSG.Timmesfeld.Transvection.Lines

public section

namespace CFSG.CGT.PushingUpLit.A78

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.Transvection

variable {G : Type} [Group G] {Z : Subgroup G} {e : ℕ}

section Generation

theorem Sp4Local.iSup_eq_top (h : Sp4Local G Z e) : ⨆ A ∈ zClass Z, A = ⊤ := by
  have := h.simple
  set N : Subgroup G := ⨆ A ∈ zClass Z, A with hN
  have hnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hle : N ≤ N.comap (MulAut.conj g).toMonoidHom := by
      refine iSup₂_le fun A hA => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_iSup₂_of_le (conjSub A g) (conjSub_mem_zClass hA g) le_rfl
    exact hle hn
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exfalso
    have hZ : Z ≤ N := le_iSup₂_of_le Z (self_mem_zClass Z) le_rfl
    rw [hbot, le_bot_iff] at hZ
    exact h.ne_bot_member (self_mem_zClass Z) hZ
  · exact htop

theorem Sp4Local.center_eq_bot (h : Sp4Local G Z e) : Subgroup.center G = ⊥ := by
  have := h.simple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨a, b, hab⟩ := h.nonabelian
    have ha : a ∈ Subgroup.center G := by rw [h1]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

end Generation

section Hyp

theorem Sp4Local.isRootClass (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2) :
    IsRootClass (zClass Z) where
  conj_class := ⟨Z, rfl⟩
  ne_bot := fun _ hA => h.ne_bot_member hA
  mul_self := fun _ hA => h.sq_member hA
  rel := fun A hA B hB _ => by
    by_cases hc : Commuting A B
    · exact Or.inl hc
    · exact Or.inr (Or.inl (h.opposite_of_not_commuting hL1 hA hB hc))
  gen := h.iSup_eq_top

theorem Sp4Local.noSpecial (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2) :
    ∀ A ∈ zClass Z, ∀ B ∈ zClass Z, ¬ Special (zClass Z) A B := by
  intro A hA B hB hsp
  have hR := h.isRootClass hL1
  exact hsp.not_opposite hR hA
    (h.opposite_of_not_commuting hL1 hA hB (hsp.not_commuting hR))

theorem Sp4Local.isTransvectionClass (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2) :
    IsTransvectionClass (zClass Z) :=
  ⟨h.isRootClass hL1, h.noSpecial hL1⟩

theorem Sp4Local.pointsDetermined (h : Sp4Local G Z e) : PointsDetermined (zClass Z) := by
  intro A hA B hB hAB
  by_contra hne
  have hc : Commuting A B := (hAB B hB).2 (h.commuting_self_member hB)
  have hBs : B ∈ sigmaSet (zClass Z) A := ⟨hB, fun e => hne e.symm, hc⟩
  have hex : ∃ D ∈ sigmaSet (zClass Z) A, ¬ Commuting B D := by
    by_contra hall
    push Not at hall
    have h1 := h.sigma_clique_at hA B hBs
    have h2 : Nat.card {C : Subgroup G // C ∈ sigmaSet (zClass Z) A ∧ Commuting B C} =
        Nat.card (sigmaSet (zClass Z) A) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun C =>
        ⟨fun hC => hC.1, fun hC => ⟨hC, hall C hC⟩⟩)
    rw [h1, h.sigma_card_at hA] at h2
    have hq : 4 ≤ 2 ^ e := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_le
    nlinarith
  obtain ⟨D, hD, hBD⟩ := hex
  exact hBD ((hAB D hD.1).1 hD.2.2)

theorem Sp4Local.exists_commuting (h : Sp4Local G Z e) :
    ∃ A ∈ zClass Z, ∃ B ∈ zClass Z, A ≠ B ∧ Commuting A B := by
  have hpos : 0 < Nat.card (sigmaSet (zClass Z) Z) := by
    rw [h.sigma_card_at (self_mem_zClass Z)]
    positivity
  obtain ⟨⟨B, hB⟩⟩ := (Nat.card_pos_iff.1 hpos).1
  exact ⟨Z, self_mem_zClass Z, B, hB.1, hB.2.1.symm, hB.2.2⟩

variable [Finite G]

theorem Sp4Local.transvectionHyp (h : Sp4Local G Z e) (hL1 : SylowOppositeSL2) :
    TransvectionHyp G (zClass Z) where
  finite := inferInstance
  cls := h.isTransvectionClass hL1
  points := h.pointsDetermined
  center := h.center_eq_bot
  rank := h.exists_commuting
  small := fun ⟨A, hA, hc⟩ => by
    have := h.four_le_card_member hA
    omega

end Hyp

section Lines

theorem Sp4Local.meetsLines [Finite G] (h : Sp4Local G Z e) (hS1 : SylowCountSL2) :
    MeetsLines (zClass Z) := by
  intro A hA B hB hAB hc C hC
  by_cases hCA : Commuting C A
  · exact ⟨A, left_mem_lineOf hA, hCA⟩
  · have hnc : ¬ Commuting A C := fun h' => hCA h'.symm
    have hBs : B ∈ sigmaSet (zClass Z) A := ⟨hB, hAB.symm, hc⟩
    obtain ⟨X, hXΔ, hXA, hXC, hXB⟩ := h.exists_common hS1 hA hC hnc B hBs
    refine ⟨X, ⟨hXΔ, ?_⟩, hXC.symm⟩
    intro Y hY hYA hYB
    by_cases hYeq : Y = A
    · subst hYeq
      exact hXA.symm
    · have hYs : Y ∈ sigmaSet (zClass Z) A := ⟨hY, hYeq, hYA.symm⟩
      have hXA' : X ≠ A := by
        rintro rfl
        exact hnc hXC
      have hXs : X ∈ sigmaSet (zClass Z) A := ⟨hXΔ, hXA', hXA.symm⟩
      exact h.sigma_trans_at hA Y hYs B hBs X hXs hYB hXB.symm

end Lines

end CFSG.CGT.PushingUpLit.A78
