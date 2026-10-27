module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Model
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU6Burg

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10GNeg

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10GU6


theorem label_A32_card {X : Type} [Group X] [Finite X]
    (h : HasLabel X (fun l : GLALabel => l = ⟨.A, 3, 2⟩)) :
    CFSG.Open.IsQuasisimple X ∧ Nat.card (X ⧸ Subgroup.center X) = 4 ^ 6 * (15 * 63 * 255) := by
  obtain ⟨-, hQ, hM⟩ := hasLabel_model h
  have hL : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSL 4 2 2 := hM
  refine ⟨hQ, ?_⟩
  rcases hL with ⟨-, hsc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, K, hKi, hKf, hKc, ⟨e⟩⟩ := hsc
    have hK4 : Nat.card K = 4 := by rw [hKc]; norm_num
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (K := K) (n := 4) (by norm_num),
      hK4]
    norm_num [Finset.prod_Icc_succ_top]
  · omega
  · omega
  · omega

theorem transport_twA52 {S : Type} [Group S] [Finite S]
    (h : HasLabel S (fun l : GLALabel => l = ⟨.twA, 5, 2⟩)) (hZ : Subgroup.center S = ⊥) :
    ∃ (F : Type) (_ : Field F) (_ : DecidableEq F) (_ : CharP F 2) (_ : Finite F),
      Nat.card F = (2 ^ 2) ^ 2 ∧ Nonempty (S ≃* ↥(CFSG.Open.StatedSU 6 (2 ^ 2) F)) := by
  classical
  obtain ⟨-, -, hM6⟩ := hasLabel_model h
  have hLM6 := i61_model_psu hM6 (lab := ⟨.twA, 5, 2⟩) rfl rfl
  have hsc6 : CFSG.Open.StatedClassicalModel (S ⧸ Subgroup.center S) .PSU 6 2 2 := by
    rcases hLM6 with ⟨-, h'⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h'
    all_goals omega
  obtain ⟨-, F, hFi, hFf, hF, ⟨e⟩⟩ := hsc6
  have hF' : Nat.card F = (2 ^ 2) ^ 2 := hF
  haveI : CharP F 2 := CFSG.LocalAnalysis.GLTheoremA.SFM12.charP_two_of_card hF'
  haveI : Finite F := hFf
  let Φ0 : S ≃* S ⧸ Subgroup.center S :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  exact ⟨F, hFi, inferInstance, inferInstance, hFf, hF',
    ⟨Φ0.trans (e.trans (CFSG.LocalAnalysis.GLTheoremA.Y10GU6.projIso hF'))⟩⟩

theorem subnormal_eq_top_of_top {S : Type} [Group S] (hS : IsSimpleGroup S) {H K : Subgroup S}
    (h : CFSG.Open.IsSubnormal H K) : K = ⊤ → H = ⊥ ∨ H = ⊤ := by
  induction h with
  | refl H => intro hK; exact Or.inr hK
  | @step H M K' hHM hnorm _ ih =>
      intro hK
      rcases ih hK with hM | hM
      · left
        rw [hM] at hHM
        exact le_bot_iff.1 hHM
      · subst hM
        have hHnorm : H.Normal := by
          have := (Subgroup.normal_subgroupOf_iff (le_top : H ≤ ⊤)).1 hnorm
          exact ⟨fun n hn g => this n g hn trivial⟩
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'

end CFSG.LocalAnalysis.GLTheoremA.Y10GNeg
