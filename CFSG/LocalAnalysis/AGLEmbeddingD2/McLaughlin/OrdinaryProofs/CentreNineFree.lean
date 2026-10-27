module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.AGLEmbedding

theorem card_inf_centralizer_eq_card_center {Q : Type} [Group Q] (H : Subgroup Q) :
    Nat.card (H ⊓ Subgroup.centralizer (H : Set Q) : Subgroup Q) =
      Nat.card (Subgroup.center H) := by
  have hmap : (Subgroup.center H).map H.subtype = H ⊓ Subgroup.centralizer (H : Set Q) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, fun h hh => ?_⟩
      have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨h, hh⟩)
      simpa using hc
    · rintro ⟨hx, hc⟩
      refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
      simpa using hc g.1 g.2
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective]

theorem not_nine_dvd_card_center_of_griess {Q S : Type} [Group Q] [Finite Q] [Group S]
    (hQ : Group.IsPerfect Q) (e : Q ⧸ Subgroup.center Q ≃* S)
    (hS : ¬ 9 ∣ Nat.card (CFSG.Open.griessHopfMultiplier S)) :
    ¬ 9 ∣ Nat.card (Subgroup.center Q) :=
  fun h9 => hS (dvd_trans h9 (card_center_dvd_card_griessHopfMultiplier hQ e))

