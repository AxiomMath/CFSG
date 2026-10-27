module

public import CFSG.GH74.GLS.C3.Layer1.Th2P73
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.C3.Layer1.Th2P61Strong

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Obstr52.false_of_image_le (hG4 : pRank 2 G ≤ 4) {B : Subgroup G} {b : G} {J : Subgroup G}
    (h : Obstr52 B b J) (hBel : CFSG.IsElementaryAbelian 2 ↥B) {A : Subgroup G}
    (hA4 : Nat.card ↥A ≤ 4) (hAN : A ≤ normalizer (J : Set G))
    (hA : ∀ g (hg : g ∈ B), ∃ (a : G) (ha : a ∈ A),
      barAct J ⟨g, h.normalizes hG4 hBel g hg⟩ = barAct J ⟨a, hAN ha⟩) : False := by
  classical
  have hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G) := h.normalizes hG4 hBel
  obtain ⟨e⟩ := h.nonempty_A7_of_rank_four hG4 hBel
  obtain ⟨D', hD'⟩ := h.exists_D
  obtain ⟨t, ht, hdis, hEBeq⟩ := (hD'.B_inv hBN).2 e
  have hF := hD'.D_root e
  set N : Subgroup G := normalizer (J : Set G) with hN
  set ψ : ↥N →* Perm (Fin 7) := a7Act J e with hψ
  set F' : Subgroup (Perm (Fin 7)) := (D'.subgroupOf N).map ψ with hF'
  set A' : Subgroup (Perm (Fin 7)) := (A.subgroupOf N).map ψ with hA'
  have hψB : ∀ g (hg : g ∈ B), ψ ⟨g, hBN g hg⟩ ∈ A' := by
    intro g hg
    obtain ⟨a, ha, hga⟩ := hA g hg
    refine ⟨⟨a, hAN ha⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
    have h1 : a7Act J e ⟨g, hBN g hg⟩ = a7Act J e ⟨a, hAN ha⟩ := by
      show (Th2.Bal.a7Theta e).symm (barAct J ⟨g, hBN g hg⟩) = (Th2.Bal.a7Theta e).symm (barAct J ⟨a, hAN ha⟩)
      rw [hga]
    exact h1.symm
  have hFA : F' ≤ A' := by
    rintro _ ⟨m, hm, rfl⟩
    exact hψB (m : G) (hD'.D_le (Subgroup.mem_subgroupOf.mp hm))
  have hA'4 : Nat.card ↥A' ≤ 4 := by
    have h1 : Nat.card ↥A' ∣ Nat.card ↥(A.subgroupOf N) := Subgroup.card_map_dvd _ _
    have h2 : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    rw [h2] at h1
    have hpos : 0 < Nat.card ↥A := Nat.card_pos
    exact (Nat.le_of_dvd hpos h1).trans hA4
  have hFeq : F' = A' :=
    Subgroup.eq_of_le_of_card_ge hFA (by rw [hF.2.1]; exact hA'4)
  obtain ⟨S₄, hS₄card, hS₄⟩ := hF.2.2.2
  have htE : t ∈ (B.subgroupOf N).map ψ := by
    rw [hEBeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨m, hm, hmt⟩ := htE
  have htA : t ∈ A' := by
    rw [← hmt]
    exact hψB (m : G) (Subgroup.mem_subgroupOf.mp hm)
  rw [← hFeq] at htA
  have ht1 : t ≠ 1 := (Equiv.Perm.IsSwap.isCycle ht).ne_one
  have hsupp := hS₄ t htA ht1
  have h2 : t.support.card = 2 := Equiv.Perm.card_support_eq_two.2 ht
  rw [hsupp, hS₄card] at h2
  omega

theorem Obstr52.ne_K (hG : C3Hyp G) {x y : G} {K T S : Subgroup G} (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B : Subgroup G} {b : G} {J : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) (hobs : Obstr52 B b J) : J ≠ K := by
  classical
  intro hJK
  obtain ⟨e7⟩ := h7
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hP : RankTwoShape (T ⊓ K) := rankTwoShape_sylow_A7 hs.sylow_P ⟨e7⟩
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel := hE.2.1
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hPQ := hs.commDisj hcen
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hPQ hP B).1 hB
  have hEqQ : E₁ ≤ T ⊓ CxK x K := hE₁S.1
  subst hJK
  have hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G) := hobs.normalizes hG4 hBel
  have hUN : U ≤ normalizer (J : Set G) := fun u hu => hBN u (hBdef ▸ Subgroup.mem_sup_left hu)
  refine hobs.false_of_image_le hG4 hBel (A := U) (by rw [hU.2.2]) hUN ?_
  intro g hg
  have hg' : g ∈ U ⊔ E₁ := hBdef ▸ hg
  obtain ⟨u, hu, q, hq, hgq⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hPQ.comm u (hU.1 hu) q (hEqQ hq)) hg'
  have hqs : q ∈ centralizerSection J (pPrimeCoreOf 2 J) := (hEqQ hq).2.2
  have hqN : q ∈ normalizer (J : Set G) := hBN q (hBdef ▸ Subgroup.mem_sup_right hq)
  refine ⟨u, hu, ?_⟩
  have h1 : barAct J ⟨q, hqN⟩ = 1 := (barAct_eq_one_iff _).2 hqs
  have : (⟨g, hBN g hg⟩ : ↥(normalizer (J : Set G))) = ⟨u, hUN hu⟩ * ⟨q, hqN⟩ :=
    Subtype.ext hgq
  rw [this, map_mul, h1, mul_one]

theorem Obstr52.ne_x (hG : C3Hyp G) {x y : G} {K T S : Subgroup G} (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B : Subgroup G} {b : G} {J : Subgroup G}
    (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B) (hobs : Obstr52 B b J) : b ≠ x := by
  classical
  intro hbx
  rw [hbx] at hobs
  have hJK : J ≠ K := hobs.ne_K hG hs h7 hB
  obtain ⟨e7⟩ := h7
  have hcen : CenterlessBar K := centerlessBar_of_A7 ⟨e7⟩
  have hP : RankTwoShape (T ⊓ K) := rankTwoShape_sylow_A7 hs.sylow_P ⟨e7⟩
  have hE : IsE 4 ⊤ B := isE_of_isSn le_top hB le_rfl
  have hBel := hE.2.1
  have hG4 : pRank 2 G ≤ 4 := hG.pRank_eq_four.le
  have hPQ := hs.commDisj hcen
  obtain ⟨U, hU, E₁, hE₁S, hE₁2, hBdef⟩ := (isS_sup_iff hPQ hP B).1 hB
  have hEqQ : E₁ ≤ T ⊓ CxK x K := hE₁S.1
  have hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G) := hobs.normalizes hG4 hBel
  have hE₁N : E₁ ≤ normalizer (J : Set G) := fun q hq => hBN q (hBdef ▸ Subgroup.mem_sup_right hq)
  have hKJ : K ≤ centralizerSection J (pPrimeCoreOf 2 J) :=
    Stage1.Thm2.Recip.le_cSec_of_ne hs.comp hobs.comp hJK.symm
  have hE₁card : Nat.card ↥E₁ ≤ 4 := by
    have h1 := C3.Layer1.Back.card_eq_two_pow_pRank hE₁S.2.1
    have h2 : pRank 2 ↥E₁ ≤ 2 := by
      have hrk := hPQ.pRank_sup hU.2.1 hE₁S.2.1 hU.1 hEqQ
      have hUr : pRank 2 ↥U = 2 := pRank_of_isFourSub hU
      have hle : pRank 2 ↥(U ⊔ E₁) ≤ pRank 2 G := pRank_le_top' _
      omega
    rw [h1]
    calc 2 ^ pRank 2 ↥E₁ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h2
      _ = 4 := by norm_num
  refine hobs.false_of_image_le hG4 hBel (A := E₁) hE₁card hE₁N ?_
  intro g hg
  have hg' : g ∈ U ⊔ E₁ := hBdef ▸ hg
  obtain ⟨u, hu, q, hq, hgq⟩ := exists_mul_of_mem_sup_of_commute
    (fun u hu q hq => hPQ.comm u (hU.1 hu) q (hEqQ hq)) hg'
  have huK : u ∈ K := (hU.1 hu).2
  have hus : u ∈ centralizerSection J (pPrimeCoreOf 2 J) := hKJ huK
  have huN : u ∈ normalizer (J : Set G) := hus.1
  have hqN : q ∈ normalizer (J : Set G) := hE₁N hq
  refine ⟨q, hq, ?_⟩
  have h1 : barAct J ⟨u, huN⟩ = 1 := (barAct_eq_one_iff _).2 hus
  have : (⟨g, hBN g hg⟩ : ↥(normalizer (J : Set G))) = ⟨u, huN⟩ * ⟨q, hqN⟩ :=
    Subtype.ext hgq
  rw [this, map_mul, h1, one_mul]

end CFSG.GH74.GLS.Th2.Obs
