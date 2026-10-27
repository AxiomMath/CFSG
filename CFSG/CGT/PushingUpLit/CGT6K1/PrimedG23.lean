module

public import CFSG.CGT.PushingUpLit.CGT6K1.Cases
public import CFSG.CGT.PushingUpLit.CGT6X.End3G23
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23Gen
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M5
public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.M2
public import CFSG.CGT.PushingUpLit.CGT6X.End3Mod

public section

namespace CFSG.CGT.PushingUpLit.CGT6K1

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoThree
  CFSG.CGT.PushingUpLit.CGT6X.End3
open scoped commutatorElement

theorem end412_of' (hM2 : H1NaturalSL2) (hM5 : G23NoSmallFaithful) (hGen : ∀ (V : Type) [CommGroup
    V] [Finite V], ∀ G T Y : Subgroup (MulAut V), EndCfg4 G T Y → YSL Y 3 → OuterT G T Y →
    Blueprint.ChevalleyExceptionalModel (LayerQ G Y) .G2 3 1 → ∀ S : Subgroup (MulAut V), S ≤ Y →
    Nat.card ↥S = 8 → ∃ g ∈ CGT6.conjClosure Y G, g ∈ Subgroup.normalizer (S : Set (MulAut V)) ∧ Y ⊔
    Y.map (MulAut.conj g).toMonoidHom = CGT6.conjClosure Y G) :
    End412' := by
  intro V _ _ hV G T Y cfg hY3 hout hQ
  have hperf : ⁅Y, Y⁆ = Y := cfg.adm.hperf
  have hX : InClassX ↥(yuHol Y) := by
    rcases cfg.hcls2 with h | ⟨n, hn, hΩ⟩
    · exact h
    · exfalso
      have := not_natOmegaMinus_of_ysl (f := 3) (n := n) (by norm_num) (by omega) hY3 hΩ
      omega
  have hnat : IsNatSectionBy (slAct 3) Y (commV Y) (commV Y ⊓ fixV Y) := by
    rcases natSection_of_classX hV hperf hX (f := 3) (by norm_num) hY3 with h | ⟨h, -⟩
    · exact h
    · omega
  have hSL2 := natSLTwo_of_classX hV hperf hX (f := 3) (by norm_num) hY3 hnat
  have : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hW : Nat.card ↥(commV Y ⊓ fixV Y) ≤ 2 ^ 3 :=
    emb_four_five_bound Y hM2 hV hX.1 (by norm_num) hSL2
  have hU : Nat.card ↥(commV Y) ≤ 2 ^ 9 := by
    rw [card_commV_of_natSection (by norm_num) hnat]
    calc Nat.card ↥(commV Y ⊓ fixV Y) * 2 ^ (2 * 3) ≤ 2 ^ 3 * 2 ^ (2 * 3) :=
          Nat.mul_le_mul_right _ hW
      _ = 2 ^ 9 := by norm_num
  have hcardY : Nat.card ↥Y = 2 ^ 3 * 63 := by
    rw [YSL.card_eq (by norm_num) hY3]
    norm_num
  obtain ⟨S, hSY, hS8⟩ : ∃ S : Subgroup (MulAut V), S ≤ Y ∧ Nat.card ↥S = 8 := by
    have hd : 2 ^ 3 ∣ Nat.card ↥Y := ⟨63, hcardY⟩
    obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 2 hd
    refine ⟨K.map Y.subtype, Subgroup.map_subtype_le K, ?_⟩
    rw [Subgroup.card_map_of_injective Y.subtype_injective, hK]
    norm_num
  obtain ⟨g, -, hgN, hgen⟩ := hGen V G T Y cfg hY3 hout hQ S hSY hS8
  have hgU : commV (Y.map (MulAut.conj g).toMonoidHom) = (commV Y).map g.toMonoidHom :=
    commV_map_conj g Y
  have hL1 : commV (CGT6.conjClosure Y G) ≤ commV Y ⊔ (commV Y).map g.toMonoidHom := by
    rw [← hgen]
    have := CGT6.commV_sup_le Y (Y.map (MulAut.conj g).toMonoidHom)
    rwa [hgU] at this
  have hSg : S ≤ Y.map (MulAut.conj g).toMonoidHom := by
    intro s hs
    refine ⟨g⁻¹ * s * g, ?_, ?_⟩
    · have h1 : g⁻¹ * s * g ∈ S := by
        have := (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.normalizer (S : Set (MulAut V))).inv_mem hgN) s).mp hs
        simpa using this
      exact hSY h1
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hSU : commV S ≤ commV Y ⊓ (commV Y).map g.toMonoidHom :=
    le_inf (CGT6.commV_mono hSY) (hgU ▸ CGT6.commV_mono hSg)
  have hU8 : Nat.card ↥(commV Y) ≤ Nat.card ↥(commV S) * 2 ^ 3 :=
    card_commV_le_sylow hV (n := 3) (by norm_num) hnat hSY (by rw [hS8]; norm_num)
  have hcard1 := card_sup_mul_card_le hSU
  have hgU'' : Nat.card ↥(commV Y) = Nat.card ↥((commV Y).map g.toMonoidHom) :=
    Nat.card_congr (Subgroup.equivMapOfInjective (commV Y) g.toMonoidHom g.injective).toEquiv
  have hc : 0 < Nat.card ↥(commV S) := Nat.card_pos
  have hx : Nat.card ↥(commV Y ⊔ (commV Y).map g.toMonoidHom) ≤ 8 * Nat.card ↥(commV Y) := by
    refine Nat.le_of_mul_le_mul_right (c := Nat.card ↥(commV S)) ?_ hc
    calc Nat.card ↥(commV Y ⊔ (commV Y).map g.toMonoidHom) * Nat.card ↥(commV S)
        ≤ Nat.card ↥(commV Y) * Nat.card ↥((commV Y).map g.toMonoidHom) := hcard1
      _ = Nat.card ↥(commV Y) * Nat.card ↥(commV Y) := by rw [← hgU'']
      _ ≤ Nat.card ↥(commV Y) * (Nat.card ↥(commV S) * 2 ^ 3) := Nat.mul_le_mul_left _ hU8
      _ = (8 * Nat.card ↥(commV Y)) * Nat.card ↥(commV S) := by ring
  have hVL : Nat.card ↥(commV (CGT6.conjClosure Y G)) ≤ 2 ^ 12 :=
    calc Nat.card ↥(commV (CGT6.conjClosure Y G))
        ≤ Nat.card ↥(commV Y ⊔ (commV Y).map g.toMonoidHom) := Subgroup.card_le_of_le hL1
      _ ≤ 8 * Nat.card ↥(commV Y) := hx
      _ ≤ 8 * 2 ^ 9 := Nat.mul_le_mul_left _ hU
      _ = 2 ^ 12 := by norm_num
  have hq : CFSG.Open.IsQuasisimple ↥(CGT6.conjClosure Y G) := cfg.quasi
  have hinj := resHom_injective_of_quasisimple hV hq cfg.oddZ
  have hM := hM5 ↥(CGT6.conjClosure Y G) hq hQ ↥(commV (CGT6.conjClosure Y G))
    (fun v => Subtype.ext (hV v)) (CGT6.resHom (CGT6.conjClosure Y G)) hinj
  have h14 : (2 : ℕ) ^ 14 ≤ 2 ^ 12 := hM.trans hVL
  norm_num at h14

section Final

theorem end412_holds' : End412' :=
  end412_of' h1NaturalSL2_holds g23NoSmallFaithful_holds
    (fun _ _ _ _ _ _ h hY hout hm S hSY hS8 => end412_generation h hY hout hm S hSY hS8)

end Final

end CFSG.CGT.PushingUpLit.CGT6K1
