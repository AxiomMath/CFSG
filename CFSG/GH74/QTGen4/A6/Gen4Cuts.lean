module

public import CFSG.GH74.QTGen4.OrderOverH
public import CFSG.Quasithin.Background.F9Basic
public import CFSG.Quasithin.H13.A6Inputs13_3
public import CFSG.Quasithin.H13.A6S4Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.GH74.QTGen4

open CFSG.GH74 CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.A6 CFSG.Open
open scoped IsMulCommutative

theorem card_alt6_gen4 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem card_quot_of_isHatA6 {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : IsHatA6 L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := by
  obtain ⟨-, hc, ⟨e⟩⟩ := h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
  rw [Nat.card_congr e.toEquiv, card_alt6_gen4, hc] at h1
  omega

theorem not_isHatA6_of_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G) {T L : Subgroup G}
    (hH : QTH13 G T L) : ¬ IsHatA6 L := by
  intro h
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo hH.sylow
  have hInH : CFSG.Quasithin.InH (P : Subgroup G) (L ⊔ P) :=
    ⟨le_sup_right, hH.faithful.1.2.2.2⟩
  have hd := modO2_dvd_of_inH hG hH.qtke.2.1 P hInH (le_sup_left : L ≤ L ⊔ P)
  rw [card_quot_of_isHatA6 h] at hd
  omega

theorem sq_P6_gen4 : ∀ x : P6, x * x = 1 := by decide

theorem setting4_elemAbelian {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting4 G T L V) : IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => S.frame.ψ.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩,
    fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : ↥V) ^ 2 = 1 := by
    apply S.frame.ψ.injective
    rw [map_pow, map_one, pow_two]
    exact Subtype.ext (sq_P6_gen4 _)
  simpa using congrArg Subtype.val h

theorem setting4_isTwoLocal_NV {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting4 G T L V) : IsTwoLocal (Subgroup.normalizer (V : Set G)) := by
  refine ⟨V, ?_, S.isPGroup_V, rfl⟩
  intro h
  have := S.card_V
  rw [h, Subgroup.card_bot] at this
  omega

theorem false_of_abelian_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {T L V : Subgroup G} (S : Setting4 G T L V)
    (hM : ¬ S.G1 ≤ Subgroup.normalizer (L : Set G))
    (hab : IsMulCommutative ↥(conjClosure V S.G1)) : False := by
  have hW : IsElemAbelian 2 (conjClosure V S.G1) := by
    refine HypF91.isElemAbelian_conjClosure_of_forall (setting4_elemAbelian S) fun k hk v hv => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (hab.is_comm.comm
      ⟨w, HypF91.conjSub_le_conjClosure hk hw⟩ ⟨v, le_conjClosure _ _ hv⟩)
  have hcard : Nat.card (conjClosure V S.G1) ≤ 2 ^ 4 :=
    SectionalTwoRankLE.card_le_of_elementary hG _ hW
  have hEq : conjClosure V S.G1 = V := by
    have hVW : V ≤ conjClosure V S.G1 := le_conjClosure V S.G1
    refine (Subgroup.eq_of_le_of_card_ge hVW ?_).symm
    rw [S.card_V]
    simpa using hcard
  have hGN : S.G1 ≤ Subgroup.normalizer (V : Set G) := by
    have h := le_normalizer_conjClosure V S.G1
    rwa [hEq] at h
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le S.frame.L_le S.frame.T_le
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge (setting4_isTwoLocal_NV S)
  have := S.uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
  exact hM (hGN.trans (this ▸ hM'le))

theorem setting134_elemAbelian {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting134 G T L V) : IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => S.frame.ψ.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩,
    fun x hx => ?_⟩
  have h : (⟨x, hx⟩ : ↥V) ^ 2 = 1 := by
    apply S.frame.ψ.injective
    rw [map_pow, map_one, pow_two]
    exact Subtype.ext (sq_P6_gen4 _)
  simpa using congrArg Subtype.val h

theorem false_of_setting134_gen4 {G : Type} [Group G] [Finite G] (hG : Gen4 G)
    {T L V : Subgroup G} (S : Setting134 G T L V) : False := by
  have h := SectionalTwoRankLE.card_le_of_elementary hG V (setting134_elemAbelian S)
  rw [S.card_V] at h
  norm_num at h

end CFSG.GH74.QTGen4
