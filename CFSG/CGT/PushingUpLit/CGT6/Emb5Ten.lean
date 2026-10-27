module

public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenB
public import CFSG.CGT.PushingUpLit.CGT6.Emb5TenC

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit

section Ten

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem Emb5Cfg.five_ten (K5 : StellmacherSixOneThree) (cfg : Emb5Cfg G T Y)
    (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V))) (ht1 : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g ∈ G, CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t = G := by
  by_contra hno
  push Not at hno
  obtain ⟨L, hL⟩ := cfg.exists_layer' hV
  have hYL := cfg.le_layer_of_forall hV ht ht1 ht2 hno hL
  have hc : TenCfg G T Y t L := ⟨cfg, hV, ht, ht1, ht2, hno, hL, hYL⟩
  obtain ⟨N, hN5, e, c, hc3, hY⟩ := hc.exists_alt K5
  let A : TenAlt L Y N := ⟨e, c, hc3, hY⟩
  by_cases h5 : N = 5
  · subst h5
    exact hc.false_of_five A
  by_cases h8 : 8 ≤ N
  · exact hc.false_of_ge_eight h8 A
  · exact hc.false_of_six_seven (by omega) (by omega) A

end Ten

theorem emb5Ten_of_k5 (K5 : StellmacherSixOneThree) :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ G T Y : Subgroup (MulAut V), Emb5Cfg G T Y →
        ∀ t ∈ G ⊓ Subgroup.centralizer (Y : Set (MulAut V)), t ≠ 1 → t ^ 2 = 1 →
          ∃ g ∈ G, CGT6E.conjSub g Y ⊔ Y ⊔ Subgroup.zpowers t = G :=
  fun _ _ _ hV _ _ _ cfg _ ht ht1 ht2 => cfg.five_ten K5 hV ht ht1 ht2

end CFSG.CGT.PushingUpLit.CGT6
