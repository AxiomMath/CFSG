module

public import CFSG.CGT.Hall82.Model
public import CFSG.CGT.Hall82.W2
public import CFSG.CGT.Hall82.W4

public section

namespace CFSG.CGT.Hall82.Setting

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G}

theorem inCatalog_or_centralizer_eq_bot
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hSTT : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    (S : Setting G M L) :
    CFSG.Assembly.InCatalog G ∨ Subgroup.centralizer (L : Set G) = ⊥ := by
  obtain ⟨R, rep, hc⟩ := S.exists_hexaCoord
  have hF : ModelFacts := modelFacts
  rcases inCatalog_or_tight hNode hSTT S.simple S.nonab S.kProper S.charTwo S.maxLocal
      S.normalizer_eq S.uniq S.elemU (by rw [S.card_blockU]; norm_num) with
    h | h | ⟨-, hW2, hW, g, hgM, hgW⟩
  · exact Or.inl h
  · exact Or.inr h
  · have hcomm : IsMulCommutative
        ↥(CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G))) := by
      rcases hW with ⟨hcyc, -⟩ | hel
      · exact IsCyclic.isMulCommutative
      · exact hel.1
    have hWab : ∀ a ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)),
        ∀ b ∈ CFSG.Open.pCoreOf 2 (Subgroup.centralizer (L : Set G)), a * b = b * a :=
      fun a ha b hb => congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rcases S.card_eq_two_or_four hF hc hW2 hWab hgM hgW with h2 | ⟨h4, hel⟩
    · exact (S.false_of_card_eq_two hF hc hW2 h2 hgM hgW).elim
    · exact Or.inl (S.inCatalog_of_card_eq_four hNode hF hc hW2 h4 hel)

end CFSG.CGT.Hall82.Setting
