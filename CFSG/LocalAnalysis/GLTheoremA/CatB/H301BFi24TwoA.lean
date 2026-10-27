module

import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi22Rank
public import CFSG.Sporadic.Fi24.Out
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open
open CFSG.Sporadic.Fi24 (J tJ tJ_mul_tJ tJ_ne_one)
open CFSG.Sporadic.Fi22 (idxPerm tauAut idxPerm_injective range_idxPerm_le card_range_idxPerm
  card_tauAut)

private theorem false_of_hom_index_two {Y X : Type} [Group Y] [Group X] {s : Y} {C : Subgroup Y}
    (hs2 : s * s = 1) (hs1 : s ≠ 1) (Φ : C →* X)
    (hker : ∀ c, Φ c = 1 → (c : Y) = 1 ∨ (c : Y) = s) {N : Subgroup X} (hN : N.index = 2)
    (hb : H1017.TwoLocalBoundPow 4 N) {E T : Subgroup Y} (hEC : E ≤ C)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 3 ^ 5) (hT : IsPGroup 2 T) (hTC : T ≤ C)
    (hET : E ≤ Subgroup.normalizer (T : Set Y)) (hTc : 8 ≤ Nat.card T) : False := by
  haveI := Subgroup.normal_of_index_eq_two hN
  set Eb := (E.subgroupOf C).map Φ with hEbdef
  set Tb := (T.subgroupOf C).map Φ with hTbdef
  have hEb : IsElemAbelian 3 Eb := (hE.subgroupOf C).map Φ
  have hTb : IsPGroup 2 Tb := hT.comap_subtype.map Φ
  have hEbc : Nat.card Eb = 3 ^ 5 := by
    have hinj : Function.Injective (Φ.comp (E.subgroupOf C).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx3 : ((x : C) : Y) ^ 3 = 1 := hE.2 _ (Subgroup.mem_subgroupOf.1 x.2)
      rcases hker (x : C) hx with h | h
      · exact Subtype.ext (Subtype.ext h)
      · rw [h, pow_succ, pow_two, hs2, one_mul] at hx3
        exact absurd hx3 hs1
    have e := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← hEbdef] at e
    rw [← e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEC).toEquiv, hEc]
  have hTbc : 4 ≤ Nat.card Tb := by
    set g := Φ.comp (T.subgroupOf C).subtype
    have hcard := Subgroup.card_mul_index g.ker
    rw [Subgroup.index_ker, MonoidHom.range_comp, Subgroup.range_subtype, ← hTbdef,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv] at hcard
    have hk : Nat.card g.ker ≤ 2 := by
      have hmem : ∀ k : g.ker, (((k : T.subgroupOf C) : C) : Y) ∈ ({1, s} : Set Y) := fun k =>
        hker ((k : T.subgroupOf C) : C) (MonoidHom.mem_ker.1 k.2)
      have hinj : Function.Injective fun k => (⟨_, hmem k⟩ : ({1, s} : Set Y)) := fun a b hab => by
        have e : (((a : T.subgroupOf C) : C) : Y) = (((b : T.subgroupOf C) : C) : Y) :=
          congrArg (Subtype.val : ({1, s} : Set Y) → Y) hab
        exact Subtype.ext (Subtype.ext (Subtype.ext e))
      refine (Nat.card_le_card_of_injective _ hinj).trans ?_
      rw [Nat.card_coe_set_eq, Set.ncard_pair hs1.symm]
    by_contra hlt
    have := Nat.mul_le_mul hk (Nat.le_of_lt_succ (not_le.1 hlt))
    omega
  have hTN : Tb ⊓ N ≠ ⊥ := fun h0 => by
    have h1 := Subgroup.relIndex_mul_card N Tb
    rw [inf_comm, h0, Subgroup.card_bot, mul_one] at h1
    have h2 := Nat.le_of_dvd (by norm_num) (hN ▸ Subgroup.relIndex_dvd_index_of_normal N Tb)
    omega
  have hEN : Eb ≤ N := fun e he => by
    have h := Subgroup.sq_mem_of_index_two hN (e ^ 2)
    rwa [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hEb.2 e he, one_mul] at h
  have hETb : Eb ≤ Subgroup.normalizer ((Tb ⊓ N : Subgroup X) : Set X) := by
    have h1 : E.subgroupOf C ≤ Subgroup.normalizer ((T.subgroupOf C : Subgroup C) : Set C) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hTC]
      exact Subgroup.subgroupOf_mono C hET
    refine le_trans (le_inf ((Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map Φ)) ?_)
      Subgroup.inf_normalizer_le_normalizer_inf
    rw [Subgroup.normalizer_eq_top N]
    exact le_top
  have hR : (Tb ⊓ N).subgroupOf N ≠ ⊥ := fun h0 => hTN (by
    rw [← Subgroup.card_eq_one,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : Tb ⊓ N ≤ N)).toEquiv, h0,
      Subgroup.card_bot])
  have h4 := hb _ _ hR (hTb.to_le inf_le_left).comap_subtype
    (by
      rw [← Subgroup.subgroupOf_normalizer_eq inf_le_right]
      exact Subgroup.subgroupOf_mono N hETb)
    (hEb.subgroupOf N)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEN).toEquiv, hEbc] at h4
  norm_num at h4


theorem isConj_fi24R2_of_elemAbelian {t : J} (ht2 : t * t = 1) (ht1 : t ≠ 1) {E T : Subgroup J}
    (hEt : E ≤ Subgroup.centralizer ({t} : Set J)) (hE : IsElemAbelian 3 E)
    (hEc : Nat.card E = 3 ^ 5) (hT : IsPGroup 2 T)
    (hTt : T ≤ Subgroup.centralizer ({t} : Set J))
    (hET : E ≤ Subgroup.normalizer (T : Set J)) (hTc : 8 ≤ Nat.card T) :
    IsConj t CFSG.Sporadic.FischerOddCore.fi24R2 := by
  rcases CFSG.HardMathSupport.Dickson.I271.TabMThreeA.fi24J_involutions.1 t ht2 ht1 with h | h
  · exfalso
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    obtain ⟨Φ, hΦ⟩ := H1017.exists_tJ_hom
    let eN : ↥(idxPerm.range.subgroupOf tauAut) ≃* ↥idxPerm.range :=
      Subgroup.subgroupOfEquivOfLe range_idxPerm_le
    have hN : (idxPerm.range.subgroupOf tauAut).index = 2 := by
      have h' := Subgroup.card_mul_index (idxPerm.range.subgroupOf tauAut)
      rw [Nat.card_congr eN.toEquiv, card_range_idxPerm, card_tauAut] at h'
      omega
    have hb : H1017.TwoLocalBoundPow 4 (idxPerm.range.subgroupOf tauAut) :=
      H1017.twoLocalBoundPow_of_mulEquiv
        (eN.trans ((MonoidHom.ofInjective idxPerm_injective).symm.trans
          CFSG.Sporadic.FischerOddCore.fi22PJ.symm)) H1017.Fi22Rank.twoLocalBoundPow_fi22P
    have hmap : ∀ {D : Subgroup J}, D ≤ Subgroup.centralizer ({t} : Set J) →
        D.map (MulAut.conj c).toMonoidHom ≤ Subgroup.centralizer ({tJ} : Set J) := fun hD => by
      have h' := H1017.map_conj_le_centralizer_singleton c hD
      rwa [hc] at h'
    have hinj : ∀ K : Subgroup J, Nat.card (K.map (MulAut.conj c).toMonoidHom) = Nat.card K :=
      fun K => Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
        (MulAut.conj c).injective
    exact false_of_hom_index_two (Y := J) (X := tauAut)
      (C := Subgroup.centralizer ({tJ} : Set J)) (s := tJ) (E := E.map (MulAut.conj c).toMonoidHom)
      (T := T.map (MulAut.conj c).toMonoidHom) tJ_mul_tJ tJ_ne_one Φ hΦ hN hb (hmap hEt)
      (hE.map _) (by rw [hinj, hEc]) (hT.map _) (hmap hTt)
      ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _)) (by rw [hinj]; exact hTc)
  · exact h

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
