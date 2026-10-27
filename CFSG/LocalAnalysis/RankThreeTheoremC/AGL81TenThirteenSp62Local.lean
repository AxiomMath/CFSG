module

public import CFSG.LocalAnalysis.AGLEmbedding.Sp62Data
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62KlingenLocal
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowFSp8
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.AGLEmbedding

@[expose] def KFactSp62CfgLocal : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K : Subgroup Y) (d : TauCeti.ValidLieTypeIndex),
    IsSpSixTwoIndex d → K.Normal → Nonempty (K ≃* CatGroup d) →
    (∃ E : Subgroup Y, E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3) ∧
    K ⊓ Subgroup.centralizer (K : Set Y) = ⊥ ∧
    (Subgroup.centralizer (K : Set Y) = ⊥ →
      K = ⊤ ∧ ∀ (T : Sylow 3 Y) (Y₀ : Subgroup Y), GLBWeakCore 3 (T : Subgroup Y) ≤ Y₀ →
        Y₀ ≠ ⊤ → 25920 ≤ Nat.card Y₀ → ∃ V₀ : Subgroup Y, Sp62InSitu (T : Subgroup Y) Y₀ V₀)

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs CFSG.AGLEmbedding.KFactProofs.Sp62Local
open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

theorem kFactSp62CfgLocal_holds :
    KFactSp62CfgLocal := by
  intro Y _ _ K d hd hKn ⟨e⟩
  obtain ⟨e₂⟩ := nonempty_catGroup_equiv_H6 d hd
  set e₃ : K ≃* H6 := e.trans e₂ with he₃
  refine ⟨?_, ?_, ?_⟩
  ·
    refine ⟨(B0.map e₃.symm.toMonoidHom).map K.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
    · exact CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3 B0_elemAbelian _) _
    · rw [Subgroup.card_map_of_injective K.subtype_injective,
        Subgroup.card_map_of_injective e₃.symm.injective, card_B0]
  ·
    have hZ6 : Subgroup.center H6 = ⊥ := by
      haveI : IsSimpleGroup H6 := CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.isSimpleGroup_H6
      obtain ⟨a, b, hab⟩ := CFSG.RankThree.PartTwo.Sec4.RonanK429F.Sp8.exists_not_comm_H6
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center H6) with h | h
      · exact h
      · exact absurd (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a) hab
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxC⟩
    have hcen : e₃ ⟨x, hxK⟩ ∈ Subgroup.center H6 := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨k, rfl⟩ := e₃.surjective g
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC k k.2)
    rw [hZ6, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hcen
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hcen
  ·
    intro hC
    refine ⟨top_of_centralizer_eq_bot K e₃ hC, ?_⟩
    intro T Y₀ hW hY₀ hcard
    obtain ⟨Ψ, hT⟩ := exists_equiv_H6_sylow K d hd e hC T
    have hmapsymm : ∀ A : Subgroup H6, (A.map Ψ.symm.toMonoidHom).map Ψ.toMonoidHom = A :=
      fun A => by
        rw [Subgroup.map_map]
        ext x
        simp
    have hN := N0_le_map_of_weakCore Ψ hT hW
    rcases eq_N0_or_W0 hN (sp62_map_ne_top Ψ hY₀) with h | h
    · exfalso
      have h1 : Nat.card (Y₀.map Ψ.toMonoidHom) = Nat.card Y₀ :=
        Subgroup.card_map_of_injective Ψ.injective
      rw [h, card_N0] at h1
      omega
    · refine ⟨V0.map Ψ.symm.toMonoidHom, Sp62InSitu.of_mulEquiv Ψ ?_⟩
      rw [hT, h, hmapsymm]
      exact sp62InSitu_W0

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
