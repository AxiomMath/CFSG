module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem9

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement IsMulCommutative

section Main

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem stmt12_2_9_one_F4 (h331 : Stmt3_3_1_F4) (hH : Hyp1223 G T L V)
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  set Z := quasithinOmegaOneCenter T with hZ
  set X := Z ⊓ Subgroup.centralizer (L : Set G) with hX
  have hXp : IsPGroup 2 X := hH.sylow.1.to_le (inf_le_left.trans (omegaOneCenter_le_self' T))
  obtain ⟨⟨-, -, huniq⟩, -⟩ :=
    (h331 G T hH.simple hH.nonabelian hH.qtke hH.sylow).2 L hH.maximal hH.quasisimple
  rw [hH.conjClosure_eq] at huniq
  obtain ⟨N, hNmax, hNle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (X : Set G))
    ⟨X, hZL, hXp, rfl⟩
  have hLX : L ≤ Subgroup.centralizer (X : Set G) := Subgroup.le_centralizer_iff.mp inf_le_right
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := fun t ht =>
    mem_normalizer_inf_centralizer
      (Subgroup.centralizer_le_normalizer _ (le_centralizer_omegaOneCenter' T ht))
      (hH.normalizes ht)
  have hLTN : L ⊔ T ≤ N := sup_le
    ((hLX.trans (Subgroup.centralizer_le_normalizer _)).trans hNle) (hTX.trans hNle)
  rw [← huniq N hNmax hLTN]
  exact (Subgroup.centralizer_le fun x hx => (inf_le_left : X ≤ Z) hx).trans
    ((Subgroup.centralizer_le_normalizer _).trans hNle)

end Main

end CFSG.Quasithin.H13
