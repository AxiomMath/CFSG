module

public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.NaturalThree
public import CFSG.LocalAnalysis.SectionRank.QTK.Insp443.CentConfig
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4Perf
public import CFSG.Quasithin.Vol2.KGFactC31Hex
public import CFSG.Quasithin.Vol2.KGFactC31J4Gen

public section

namespace CFSG.SectionRank.QTK.Insp443

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.KGC31 CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSL)

theorem KConfig.conclK_of_e8 {G : Type} [Group G] [Finite G] {v : Fin 3 → G} (hv : EBasis v)
    {L MK : Subgroup G} (h : KConfig G L (eSub hv) MK)
    (hC2 : IsPGroup 2 ↥(Subgroup.centralizer (eSub hv : Set G))) :
    ConclK G L (eSub hv) MK := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : L ≤ eNorm hv := h.le_normalizer
  have hθ : ∀ l : ↥L, E16.eNHom hv hLN l = 1 ↔
      (l : G) ∈ Subgroup.centralizer (eSub hv : Set G) := fun l => E16.eNHom_eq_one_iff hv hLN l
  have : Group.IsPerfect ↥L := ⟨commutator_eq_top_of_perfect h.perfect⟩
  have hsl : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) := E8.isSimpleGroup_statedSL3
  have hsurj : Function.Surjective (E16.eNHom hv hLN) := by
    rw [← MonoidHom.range_eq_top]
    rcases CFSG.Quasithin.J4Fam.eq_bot_or_top_of_isPerfect
        (fun H hH => CFSG.Quasithin.J4Fam.solvable_of_ne_top_card168 E8.card_statedSL3 hH)
        (Group.IsPerfect.range (E16.eNHom hv hLN)) with hb | ht
    · exfalso
      have hLC : L ≤ Subgroup.centralizer (eSub hv : Set G) := fun l hl => (hθ ⟨l, hl⟩).mp (by
        have : E16.eNHom hv hLN ⟨l, hl⟩ ∈ (E16.eNHom hv hLN).range := ⟨_, rfl⟩
        rwa [hb, Subgroup.mem_bot] at this)
      have hL1 : L = ⊥ := eq_bot_of_perfect_of_isPGroup h.perfect (hC2.to_le hLC)
      apply h.ne_bot
      rw [eq_bot_iff]
      exact h.le_pCoreOf.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hL1.le)
    · exact ht
  have hpk : CFSG.pCore 2 ↥L = (E16.eNHom hv hLN).ker := by
    rw [← Hex.pCoreOf_subgroupOf' L]
    ext l
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hθ]
    constructor
    · intro hl
      exact h.pCoreOf_le hl
    · intro hl
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_left : L ⊓ Subgroup.centralizer (eSub hv : Set G) ≤ L)
        (fun m hm => mem_normalizer_inf (Subgroup.le_normalizer hm)
          (h.le_normalizer_centralizer hm)) (hC2.to_le inf_le_right) ⟨l.2, hl⟩
  exact conclK_of_natural3 hv hLN hsurj hpk MK

end CFSG.SectionRank.QTK.Insp443

end
