module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Quot.Sub
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Transfer

public section

namespace CFSG.EvenSporadicStandard.Induction.Junction

open Subgroup CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
  CFSG.EvenSporadicStandard.Induction.Hyp
open scoped commutatorElement

variable {G : Type} [Group G] (M : Subgroup G) [M.Normal]

theorem map_sup_zpowers_cq (T : Subgroup G) (s : G) :
    (T ⊔ zpowers s).map (cq M) = T.map (cq M) ⊔ zpowers (cq M s) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]

theorem isCompIn_lf_sup_zpowers {Lp Tq : Subgroup (CQ M)} {T : Subgroup G} {s : G}
    (hT : T.map (cq M) = Tq) (hLp : Lp ≤ M.map (cq M)) (hq : CFSG.IsQuasisimple ↥Lp)
    (h : IsCompIn Lp (centralizer ((Tq ⊔ zpowers (cq M s) : Subgroup (CQ M)) : Set (CQ M)))) :
    IsCompIn (lf M Lp) (centralizer ((T ⊔ zpowers s : Subgroup G) : Set G)) := by
  refine isCompIn_lf M (T ⊔ zpowers s) hLp hq ?_
  rwa [map_sup_zpowers_cq, hT]

theorem isCompIn_lf_of_map {Li Tq : Subgroup (CQ M)} {T : Subgroup G} (hT : T.map (cq M) = Tq)
    (hLi : Li ≤ M.map (cq M)) (hq : CFSG.IsQuasisimple ↥Li)
    (h : IsCompIn Li (centralizer (Tq : Set (CQ M)))) :
    IsCompIn (lf M Li) (centralizer (T : Set G)) := by
  refine isCompIn_lf M T hLi hq ?_
  rwa [hT]

theorem map_conj_le_of_normal {A : Subgroup G} (hA : A ≤ M) (g : G) :
    A.map (MulAut.conj g).toMonoidHom ≤ M := by
  rintro _ ⟨x, hx, rfl⟩
  exact (inferInstance : M.Normal).conj_mem x (hA hx) g

theorem lf_sup_conj {Z : Subgroup (CQ M)} (hZp : ⁅Z, Z⁆ = Z) (hZM : Z ≤ M.map (cq M)) (g : G) :
    lf M Z ⊔ (lf M Z).map (MulAut.conj g).toMonoidHom =
      lf M (Z ⊔ Z.map (MulAut.conj (cq M g)).toMonoidHom) := by
  have hMq : (M.map (cq M)).Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have hcM : Z.map (MulAut.conj (cq M g)).toMonoidHom ≤ M.map (cq M) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hMq.conj_mem x (hZM hx) _
  have hZp' : ⁅Z.map (MulAut.conj (cq M g)).toMonoidHom, Z.map (MulAut.conj (cq M g)).toMonoidHom⁆ =
      Z.map (MulAut.conj (cq M g)).toMonoidHom := commutator_map_of_perfect _ hZp
  have hSp : ⁅Z ⊔ Z.map (MulAut.conj (cq M g)).toMonoidHom,
      Z ⊔ Z.map (MulAut.conj (cq M g)).toMonoidHom⁆ =
      Z ⊔ Z.map (MulAut.conj (cq M g)).toMonoidHom := commutator_sup_of_perfect hZp hZp'
  have hSM : Z ⊔ Z.map (MulAut.conj (cq M g)).toMonoidHom ≤ M.map (cq M) := sup_le hZM hcM
  refine eq_of_map_eq_cq M (sup_le (lf_le M Z) (map_conj_le_of_normal M (lf_le M Z) g))
    (lf_le M _) (commutator_sup_of_perfect (commutator_lf M hZp hZM)
      (commutator_map_of_perfect _ (commutator_lf M hZp hZM))) (commutator_lf M hSp hSM) ?_
  rw [Subgroup.map_sup, map_lf M hZp hZM, ← Hyp.map_map_conj, map_lf M hZp hZM,
    map_lf M hSp hSM]

theorem lf_le_lf_sup_conj {Lp Li : Subgroup (CQ M)} (hLp : ⁅Lp, Lp⁆ = Lp) (hLi : ⁅Li, Li⁆ = Li)
    (hLpM : Lp ≤ M.map (cq M)) (hLiM : Li ≤ M.map (cq M)) (s : G)
    (h : Lp ≤ Li ⊔ Li.map (MulAut.conj (cq M s)).toMonoidHom) :
    lf M Lp ≤ lf M Li ⊔ (lf M Li).map (MulAut.conj s).toMonoidHom := by
  have hMq : (M.map (cq M)).Normal := Subgroup.Normal.map ‹_› _ (QuotientGroup.mk'_surjective _)
  have hcM : Li.map (MulAut.conj (cq M s)).toMonoidHom ≤ M.map (cq M) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hMq.conj_mem x (hLiM hx) _
  rw [lf_sup_conj M hLi hLiM s]
  refine le_lf M (lf_le M Lp) (commutator_lf M hLp hLpM)
    (commutator_sup_of_perfect hLi (commutator_map_of_perfect _ hLi)) (sup_le hLiM hcM) ?_
  rw [map_lf M hLp hLpM]
  exact h

end CFSG.EvenSporadicStandard.Induction.Junction
