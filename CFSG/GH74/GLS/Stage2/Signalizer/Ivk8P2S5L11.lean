module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Cases

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

theorem lemma18_11Q_of (hB12 : Bender12) (h171 : Prop17_1) (h183 : Lemma18_3a)
    (h184 : Lemma18_4ac) (h185 : Lemma18_5R) (hcl : Claim18Xd) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G) (p : ℕ) (E : Subgroup G)
      (t : G), Ctx18 G z k S M p E t → ∀ m : ℕ,
      (∀ X' ∈ XfamR z M (Vof M E), ∀ J' : Subgroup G, IsCompIn X' J' → ordq J' ≤ m) →
      ∀ X ∈ XfamR z M (Vof M E), ∀ J : Subgroup G, IsCompIn X J → ordq J = m →
      ∀ D : Subgroup G, D ≤ E → Nat.card ↥D = p ^ 2 → D ≤ centralizer (J : Set G) →
      ((∃ X' D' : Subgroup G, QTriple z M E p m X' D') → QTriple z M E p m X D) →
      XDR M D < ⊤ := by
  intro G _ _ z k S M p E t hctx m hmax X hX J hJ hJm D hDE hDc hDJ hQ
  have hy : S5Hyp := ⟨hB12, h171, h183, h184, h185, hcl⟩
  have hF := S5Facts.of_ctx h171 hctx
  have hnorm : ∀ d ∈ Dstar M D, XdR M d ≤ normalizer (J : Set G) := fun d hd =>
    le_normalizer_of_isCompIn h185 hctx
      (XdR_mem_XfamR hB12 h183 h171 hcl hctx (hDE hd.1) hd.2.1 hd.2.2)
      (isCompIn_XdR hy hctx hF hmax hX hJ hJm hDE hDc hDJ hQ hd)
  have hle : XDR M D ≤ normalizer (J : Set G) := iSup₂_le fun d hd => hnorm d hd
  have hsimple : IsSimpleGroup G := hF.hkps.1
  have hJbot : J ≠ ⊥ := ne_bot_of_isCompIn hJ
  have hJtop : J ≠ ⊤ := fun h => hX.2.1 (top_le_iff.1 (h ▸ hJ.1))
  have hNtop : normalizer (J : Set G) ≠ ⊤ := by
    intro h
    have hn : J.Normal := Subgroup.normalizer_eq_top_iff.1 h
    rcases hsimple.eq_bot_or_eq_top_of_normal J with h' | h'
    exacts [hJbot h', hJtop h']
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.2 hNtop)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
