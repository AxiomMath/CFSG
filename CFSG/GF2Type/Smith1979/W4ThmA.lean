module

public import CFSG.GF2Type.Smith1979.W4ThmANorm
public import CFSG.LargeExtraspecial.S4FiveMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4ThmA

open Module CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

namespace ThmAData

variable {t : S.O}

theorem false (D : ThmAData S g t) : False := by
  obtain ⟨u, hum, hua, hau⟩ := S.exists_swap (g := g) rfl D.haQ D.hne
  have hu : Swap S g u := ⟨hum, hua, hau⟩
  obtain ⟨x, X⟩ := D.exists_XData hu
  exact (D.sigmaEnd4 hu X).false

end ThmAData

theorem false_of_transitive_four (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) (hw : S.width = 4)
    (hdim : finrank (ZMod 2) (Vt S g t) = 4)
    (htr : ∀ v : Vt S g t, v ≠ 0 → ∃ x ∈ RmodN S g t, x (aV ht) = v) : False :=
  (ThmAData.mk H C ht ht1 hVQ hw hdim htr).false

theorem not_pgl25Case (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    ¬ PGL25Case H C ht ht1 hVQ :=
  fun P => false_of_transitive_four H C ht ht1 hVQ hw P.finrank_eq P.transitive

theorem not_a6Case (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g) :
    ¬ A6Case H C ht ht1 hVQ :=
  fun P => false_of_transitive_four H C ht ht1 hVQ hw P.finrank_eq P.transitive

theorem not_spCase_four (hw : S.width = 4) (H : Hyp4 S g) (C : Cons311 S g) {t : S.O}
    (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
    (hdim : finrank (ZMod 2) (Vt S g t) = 4) : ¬ SpCase H C ht ht1 hVQ :=
  fun P => false_of_transitive_four H C ht ht1 hVQ hw hdim P.transitive

end CFSG.GF2Type.Smith1979.W4ThmA
