module

public import CFSG.CGT.PushingUpLit.CGT6K1.Cases
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34Main
public import CFSG.CGT.PushingUpLit.CGT6X.End3Cfg2
public import CFSG.CGT.PushingUpLit.CGT6X.End4L34
public import CFSG.CGT.PushingUpLit.CGT6X.End4Lin
public import CFSG.CGT.PushingUpLit.CGT6X.End4Uni

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.CGT6
  CFSG.CGT.PushingUpLit.CGT6X.End3 CFSG.CGT.PushingUpLit.CGT6X.End4
open CFSG.Open (StatedClassicalModel)

section Extract

variable {V : Type} [CommGroup V] [Finite V] {G T Y : Subgroup (MulAut V)}

theorem endcfg_extract' (cfg : EndCfg4 G T Y) (hT : OuterT G T Y) :
    ∃ (t : MulAut V) (htN : t ∈ Subgroup.normalizer (conjClosure Y G : Set (MulAut V))),
      t ^ 2 = 1 ∧ (∀ y ∈ Y, t * y = y * t) ∧
      ∀ x : ↥(conjClosure Y G) ⧸ Subgroup.center ↥(conjClosure Y G),
        CGT6X.K7a.centerAutHom ↥(conjClosure Y G) (conjOn (conjClosure Y G) t htN) ≠
          MulAut.conj x := by
  obtain ⟨t, htT, ht2, htL⟩ := hT
  have htG : t ∈ G := cfg.adm.hTG htT
  refine ⟨t, normalizer_conjClosure htG, ?_, ?_, centerAutHom_conjOn_ne cfg htG htL⟩
  · rw [← ht2]
    exact pow_orderOf_eq_one t
  · intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (cfg.adm.hYC hy).2) t htT

end Extract

section Cases

variable
  {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G T Y : Subgroup (MulAut V)}
  (cfg : EndCfg4 G T Y) {f : ℕ} (hY : YSL Y f) (hT : OuterT G T Y)

include hV cfg hY hT in
theorem end411_of_unitary' (hf : 2 ≤ f)
    (hmod : StatedClassicalModel (LayerQ G Y) .PSU 3 2 f) : False := by
  obtain ⟨t, htN, ht2, htY, hτout⟩ := endcfg_extract' cfg hT
  have hperf : Group.IsPerfect ↥(conjClosure Y G) := ⟨cfg.quasi.1⟩
  exact end411_unitary hV le_conjClosure (simpleQuot_of_cfg hV cfg)
    (commGen_of_perfect cfg.adm.hperf) htN ht2 htY hτout hf
    (GaloisField.card 2 f (by omega)) hY hmod

include hV cfg hY hT in
theorem end411_of_linear' (hf : 3 ≤ f)
    (hmod : StatedClassicalModel (LayerQ G Y) .PSL 3 2 f) : False := by
  obtain ⟨t, htN, ht2, htY, hτout⟩ := endcfg_extract' cfg hT
  have hperf : Group.IsPerfect ↥(conjClosure Y G) := ⟨cfg.quasi.1⟩
  exact end411_linear hV le_conjClosure (simpleQuot_of_cfg hV cfg)
    (commGen_of_perfect cfg.adm.hperf) htN ht2 htY hτout hf
    (GaloisField.card 2 f (by omega)) hY hmod

end Cases

@[expose] def End411L34' : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → YSL Y 2 → OuterT G T Y →
      StatedClassicalModel (LayerQ G Y) .PSL 3 2 2 → False

theorem end411_of'
    (hL34 : End411L34') : End411' := by
  intro V _ _ hV G T Y cfg f hf hY hT hmod
  rcases hmod with hPSL | hPSU
  · by_cases h2 : f = 2
    · subst h2
      exact hL34 V hV G T Y cfg hY hT hPSL
    · exact end411_of_linear' hV cfg hY hT (by omega) hPSL
  · exact end411_of_unitary' hV cfg hY hT hf hPSU

theorem end411L34_holds' :
    End411L34' := by
  intro V _ _ hV G T Y cfg hY hT hmod
  obtain ⟨t, htN, ht2, htY, hτout⟩ := endcfg_extract' cfg hT
  have hperf : Group.IsPerfect ↥(CGT6.conjClosure Y G) := ⟨cfg.quasi.1⟩
  exact end411_l34 hV CGT6.le_conjClosure (simpleQuot_of_cfg hV cfg)
    (commGen_of_perfect cfg.adm.hperf) CGT6.le_normalizer_conjClosure cfg.irr htN ht2 htY hτout
    cfg.oddZ (GaloisField.card 2 2 (by norm_num)) hY
    (card_commV_le_sixteen_l34 hV cfg.adm.hperf cfg.hcls2 hY) hmod

theorem end411_holds' :
    End411' :=
  end411_of' end411L34_holds'

end CFSG.CGT.PushingUpLit.CGT6K1
