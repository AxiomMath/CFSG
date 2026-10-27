module

public import CFSG.GH74.Generic.BProg.B3.S3KG31eDesc
public import CFSG.GH74.Generic.BProg.B3.S3KG31eObs
public import CFSG.GH74.Generic.BProg.B3.S3Sec29D1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29E1
public import CFSG.ClassicalInvolution.SolvableCase.SL2Three

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.Th2.Obs CFSG.GH74.GLS.Th2.Bal CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

namespace S3KG

theorem not_isPerfect_sl2_zmod3 : ¬ Group.IsPerfect SL(2, ZMod 3) := by
  intro hP
  have : (CFSG.ClassicalInvolution.sl2ThreeQ).Normal := CFSG.ClassicalInvolution.sl2ThreeQ_normal
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (SL(2, ZMod 3) ⧸ CFSG.ClassicalInvolution.sl2ThreeQ) :=
    isCyclic_of_prime_card (p := 3)
      (by rw [← Subgroup.index_eq_card]; exact CFSG.ClassicalInvolution.sl2ThreeQ_index)
  have hle := (Subgroup.Normal.quotient_commutative_iff_commutator_le
    (N := CFSG.ClassicalInvolution.sl2ThreeQ)).mp inferInstance
  rw [hP.commutator_eq_top, top_le_iff] at hle
  have h3 := CFSG.ClassicalInvolution.sl2ThreeQ_index
  rw [hle, Subgroup.index_top] at h3
  omega

theorem three_lt_card_of_isPerfect {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {X : Type*} [Group X] (ι : X ≃* SL(2, F)) (hP : Group.IsPerfect X) : 3 < Nat.card F := by
  have h2 : 1 < Nat.card F := Finite.one_lt_card
  by_contra h3
  have h3' : Nat.card F = 3 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  obtain ⟨e⟩ := CFSG.ClassicalInvolution.nonempty_mulEquiv_sl2Three_of_natCard_eq_three h3'
  exact not_isPerfect_sl2_zmod3
    (Group.IsPerfect.ofSurjective (f := (ι.trans e).toMonoidHom) (ι.trans e).surjective)

theorem mem_of_pRank_eq {G : Type} [Group G] [Finite G] (hG4 : pRank 2 G ≤ 4) {B : Subgroup G}
    (hBel : CFSG.IsElementaryAbelian 2 ↥B) (hB4 : pRank 2 ↥B = 4) {b : G} (hb2 : orderOf b = 2)
    (hbc : b ∈ centralizer (B : Set G)) : b ∈ B := by
  by_contra hbB
  have hcd : CommDisj (zpowers b) B := by
    refine ⟨fun p hp q hq => ?_, ?_⟩
    · obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
      exact (Commute.zpow_left (show Commute b q from (mem_centralizer_iff.mp hbc q hq).symm)
        m).eq
    · refine eq_bot_iff.2 fun z hz => ?_
      rcases mem_zpowers_two hb2 hz.1 with h0 | h0
      · simp [h0]
      · exact absurd (h0 ▸ hz.2) hbB
  have hrk := hcd.pRank_sup (Th2.isElementaryAbelian_zpowers_of_orderOf_two hb2) hBel le_rfl
    le_rfl
  rw [Th2.pRank_zpowers_of_orderOf_two hb2, hB4] at hrk
  have h4 := pRank_le_top' (zpowers b ⊔ B)
  omega

end S3KG

theorem kg31e_proved
    (G : Type) [Group G] [Finite G] : Kg31e G := by
  intro x K A B b D J hHyp _ _ _ _ hext hrk hobs hsl hBN
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := hext.2.2.2.1
  have hG4 : pRank 2 G ≤ 4 := Gen4.pRank_two_le hHyp.gen4
  have hbB : b ∈ B := S3KG.mem_of_pRank_eq hG4 hBel hrk hobs.b_ord hobs.b_cent
  obtain ⟨F, _, _, hodd, ⟨ι₀⟩⟩ := hsl
  let ι : kBar J ≃* SL(2, F) := ι₀.trans (specialLinearGroupEquivStatedSL 2 F).symm
  have h3 : 3 < Nat.card F :=
    S3KG.three_lt_card_of_isPerfect hodd ι (TwoThin.isQuasisimple_hat hobs.comp).1
  have hF : L2Field F := ⟨hodd, h3⟩
  have hF2 : ringChar F ≠ 2 := by
    have : Fintype F := Fintype.ofFinite F
    intro h2
    have h := FiniteField.even_card_iff_char_two.mp h2
    rw [← Nat.card_eq_fintype_card] at h
    obtain ⟨k, hk⟩ := hodd
    omega
  let e' : kBar J ⧸ center (kBar J) ≃* L2 F :=
    (QuotientGroup.congr (center (kBar J)) (center SL(2, F)) ι (Subgroup.map_center_eq ι)).trans
      (L2.equivPSL F).symm
  have hψ := S3KG.descendZ_injective hF2 ι
  have hloc : IsLocallyKBalanced 3 (kBar J) :=
    S3KG.isLocallyKBalanced_of_injective (S3KG.descendZ (kBar J)) hψ
      (fun k' => by
        obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective k'
        exact ⟨k₀, S3KG.descendZ_conj k₀⟩)
      (isLocallyKBalanced_three_of_l2 hF e')
  have hD := S3Sec29E1.toObsData hobs hBel hbB hloc
  have hInn : innAut (kBar J ⧸ center (kBar J)) ≤
      ((S3KG.descendZ (kBar J)).comp (barAct J)).range := by
    rintro _ ⟨k', rfl⟩
    obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective k'
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective k₁
    refine ⟨⟨(k : G), Subgroup.le_normalizer k.2⟩, ?_⟩
    rw [MonoidHom.comp_apply, barAct_of_mem k.2, S3KG.descendZ_conj]
  exact S3KG.obs_not_B_comp hD hBel (fun g hg => hBN hg) hF e' hψ hInn

end CFSG.GH74.Generic.BProg.B3
