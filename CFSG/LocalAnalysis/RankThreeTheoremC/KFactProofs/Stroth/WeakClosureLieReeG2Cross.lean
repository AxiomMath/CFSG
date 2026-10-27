module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieCrossTags
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LieType.SeitzGeneration.ExcReeG2Rank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

theorem wcOn_of_no_plane {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hno : ∀ F : Subgroup K, CFSG.Open.IsElemAbelian p F → Nat.card F = p ^ 2 → False) :
    WCOn p K := by
  intro P _ hrank
  exfalso
  have hle : CFSG.Open.pRank p (P : Subgroup K) ≤ 1 := by
    unfold CFSG.Open.pRank
    apply csSup_le
    · refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩,
        fun x hx => ?_⟩, by simp⟩
      rw [Subgroup.mem_bot.1 hx, one_pow]
    · rintro k ⟨E, hEP, hE, hEc⟩
      by_contra hk
      push_neg at hk
      have hn : p ^ 2 ≤ Nat.card E := by
        rw [hEc]
        exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
      obtain ⟨F', hF'⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card
        (Fact.out : p.Prime) hE.isPGroup hn
      refine hno (F'.map E.subtype) (hE.mono (Subgroup.map_subtype_le F')) ?_
      rw [Subgroup.card_map_of_injective E.subtype_injective, hF']
  omega

theorem crossReeTits_twistedG2 :
    CrossReeTits .twistedG2 := by
  intro K _ _ ℓ f p _ _ hp2 hpℓ hmodel
  obtain ⟨-, -, hℓ, ⟨a', ha', hfa'⟩, hiso⟩ :=
    CFSG.LieType.Ree.small_Ree_model_Schreier K ℓ f hmodel
  subst hℓ
  obtain ⟨-, a, hfa, X, _, _, hXcard, ⟨e2⟩⟩ := hmodel
  have ha : 1 ≤ a := by omega
  have : Fintype X := Fintype.ofFinite X
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP X CFSG.LieType.Ree.ReeTag.G2.prime :=
    charP_of_card_eq_prime_pow (p := 3) (f := f) (by rw [← Nat.card_eq_fintype_card, hXcard])
  obtain ⟨E⟩ := hiso a X hfa hXcard ⟨e2⟩
  have hX : Nat.card X = 3 ^ (2 * a + 1) := by rw [← hfa]; exact hXcard
  have hp3 : 3 < p := by
    have := (Fact.out : p.Prime).two_le
    omega
  apply wcOn_of_no_plane
  intro F hF hFc
  have hF₁ : CFSG.Open.IsElemAbelian p (F.map E.toMonoidHom) := hF.map E.toMonoidHom
  have hF₂ : CFSG.Open.IsElemAbelian p ((F.map E.toMonoidHom).map
      (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype) := hF₁.map _
  refine CFSG.LieType.SeitzGeneration.no_plane_reeGamma_G2 ha hX (Fact.out : p.Prime) hp3
    (Subgroup.map_subtype_le _) hF₂.isElementaryAbelian ?_
  rw [Subgroup.card_map_of_injective (CFSG.LieType.Ree.ReeTag.G2.reeGamma X a).subtype_injective,
    Subgroup.card_map_of_injective E.injective, hFc]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
