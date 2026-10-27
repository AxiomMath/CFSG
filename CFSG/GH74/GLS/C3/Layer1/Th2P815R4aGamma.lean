module

public import CFSG.GH74.GLS.C3.Layer1.Th2ConnCentral
public import CFSG.GH74.GLS.C3.Layer1.Th2ConnRows
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.GH74.GLS.Th2

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS

variable {G : Type} [Group G]

theorem r4a_centralW [Finite G] {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r4a B) :
    ∃ W : Subgroup G,
      W ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) ∧
      W ≤ Subgroup.centralizer (((T ⊓ K) ⊔ (T ⊓ CxK x K) : Subgroup G) : Set G) ∧
      CFSG.IsElementaryAbelian 2 ↥W ∧ pRank 2 ↥W = 3 := by
  classical
  let P : Subgroup G := T ⊓ K
  let Q : Subgroup G := T ⊓ CxK x K
  let R : Subgroup G := P ⊔ Q
  obtain ⟨hL2, -⟩ := h2.row
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
  have hcen : CenterlessBar K := centerlessBar_of_hasL2Model hPr hL2
  have hPQ : CommDisj P Q := h2.std.commDisj hcen
  have hPshape : RankTwoShape P :=
    rankTwoShape_sylow_L2 h2.std.sylow_P (TwoThin.isQuasisimple_hat h2.std.comp) hPr hL2
  have hP4 : Nat.card ↥P = 4 := card_sylow_L2_five h2.std.sylow_P hL2
  obtain ⟨U, hU⟩ := exists_isFourSub_of_rankTwoShape hPshape
  have hUP : U = P := Subgroup.eq_of_le_of_card_ge hU.1 (by rw [hU.2.2, hP4])
  have hPel : CFSG.IsElementaryAbelian 2 ↥P := hUP ▸ hU.2.1
  have hPrank : pRank 2 ↥P = 2 := by rw [← hUP, pRank_of_isFourSub hU]
  have hxQ : x ∈ Q := ⟨h2.std.x_mem_T, h2.std.x_mem_CxK⟩
  have hx2 : orderOf x = 2 := h2.std.orderOf_x
  have hx2pow : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hxP : x ∉ P := by
    intro hxP
    have h1 : x = 1 := hPQ.eq_one_of_mem hxP hxQ
    have h2 : orderOf x = 1 := by rw [h1, orderOf_one]
    omega
  have hxel : CFSG.IsElementaryAbelian 2 ↥(zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hx2pow
  have hPxcomm : ∀ p ∈ P, ∀ b ∈ zpowers x, p * b = b * p := by
    have hxCent : x ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      exact hPQ.comm p hp x hxQ
    intro p hp b hb
    exact Subgroup.mem_centralizer_iff.1 (zpowers_le.2 hxCent hb) p hp
  have hPxinf : P ⊓ zpowers x = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rcases mem_zpowers_two hx2 hz.2 with rfl | rfl
    · exact one_mem _
    · exact False.elim (hxP hz.1)
  have hWel : CFSG.IsElementaryAbelian 2 ↥(P ⊔ zpowers x) :=
    isElementaryAbelian_sup (K := P) (L := zpowers x) hPel hxel hPxcomm
  have hWcard : Nat.card ↥(P ⊔ zpowers x) = 8 := by
    have hcd : CommDisj P (zpowers x) := ⟨hPxcomm, hPxinf⟩
    rw [hcd.card_sup le_rfl le_rfl, Nat.card_zpowers, hx2, hP4]
  have hWrank : pRank 2 ↥(P ⊔ zpowers x) = 3 := by
    have h := C3.Layer1.Back.card_eq_two_pow_pRank hWel
    rw [hWcard] at h
    exact Nat.pow_right_injective le_rfl (by simpa using h.symm)
  have hPcentR : P ≤ Subgroup.centralizer (R : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨p', hp', q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hPQ.comm hr
    have h1 : p * p' = p' * p := (C3.Layer1.Back.forall_of_isElementaryAbelian hPel).1 p hp p' hp'
    have h2 : p * q = q * p := hPQ.comm p hp q hq
    calc (p' * q) * p = p' * (q * p) := by group
      _ = p' * (p * q) := by rw [h2]
      _ = (p' * p) * q := by group
      _ = (p * p') * q := by rw [h1]
      _ = p * (p' * q) := by group
  have hxCentR : x ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_commute hPQ.comm hr
    have hxp : x * p = p * x := (hPQ.comm p hp x hxQ).symm
    have hxq : x * q = q * x := (Subgroup.mem_centralizer_singleton_iff.1 hq.2.1).symm
    calc (p * q) * x = p * (q * x) := by group
      _ = p * (x * q) := by rw [hxq]
      _ = (p * x) * q := by group
      _ = (x * p) * q := by rw [hxp]
      _ = x * (p * q) := by group
  have hWcR : P ⊔ zpowers x ≤ Subgroup.centralizer (R : Set G) :=
    sup_le hPcentR (zpowers_le.2 hxCentR)
  refine ⟨P ⊔ zpowers x, ?_, hWcR, hWel, hWrank⟩
  exact sup_le le_sup_left (zpowers_le.2 (Subgroup.mem_sup_right hxQ))

theorem b_thm2_l82_r4a [Finite G] {x y : G} {K T S M B : Subgroup G}
    (h2110 : B_IG_21_10) (h2 : Th2M2 x y K T S M .r4a B) :
    gammaK 2 (Th2Row.Tstar .r4a x K T S) 3 ≤ M ∧
      gammaK 2 (Th2Row.Tstar .r4a x K T S) 4 ≤ M ∧
      (∀ A : Subgroup G, IsE 4 (Th2Row.Tstar .r4a x K T S) A →
        gammaK 2 A 3 ≤ M) ∧
      gammaK 2 B 3 ≤ M := by
  obtain ⟨W, hWR, hWc, hWel, hW3⟩ := r4a_centralW h2
  have h74 : Th2Row.BT .r4a x K T S =
      {B' : Subgroup G | IsSn 4 (Th2Row.Tstar .r4a x K T S) B'} := by
    change {B' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'} =
      {B' : Subgroup G |
        IsSn 4 (⨆ B' ∈ {B' : Subgroup G |
          IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B'}, B') B'}
    exact Th2.isSn_tstar_eq ((T ⊓ K) ⊔ (T ⊓ CxK x K)) 4
  have hconn :
      (Th2Row.r4a ≠ .r4b → Th2Row.r4a ≠ .r4c →
        ∀ A : Subgroup G, IsE 3 (Th2Row.Tstar .r4a x K T S) A →
          RConnN 3 4 (Th2Row.Tstar .r4a x K T S) A B) ∧
      (∀ A : Subgroup G, IsE 4 (Th2Row.Tstar .r4a x K T S) A →
        RConnN 3 4 (Th2Row.Tstar .r4a x K T S) A B) := by
    constructor
    · intro _ _ A hA
      exact rConnN_three_four_of_central hWR (by simpa [Th2Row.Tstar] using hWc)
        hWel (by rw [hW3]) h2.mem A hA
    · intro A hA
      exact rConnN_three_four_of_central hWR (by simpa [Th2Row.Tstar] using hWc)
        hWel (by rw [hW3]) h2.mem A
        (isE_mono_rank hA (by norm_num : 3 ≤ 4))
  have hloc := b_thm2_l82_local h2110 h2 h74 hconn
  exact ⟨hloc.1 (by decide) (by decide), hloc.2.1, hloc.2.2.1, hloc.2.2.2⟩

end CFSG.GH74.GLS.Th2

