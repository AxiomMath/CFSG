module

public import CFSG.LocalAnalysis.EvenBN.G2.QMain
public import CFSG.LocalAnalysis.EvenBN.G2.LocalN60
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple
public import CFSG.Yardstones.M41b0c98b3153.Definitions

public section

namespace CFSG.LocalAnalysis.EvenBN.G2

open Subgroup CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase.ProductN1SylowAux
  (conj_inf conj_eq_of_mem_normalizer)
open scoped CFSG.LocalAnalysis.EvenBN.TrialityD4.ProductCase


namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {K : Type} [Field K]
  [Finite K] [CharP K 2]

theorem complement₂_of_eight (hW : CFSG.Walter.WalterOrderForm) (h : Setup G L f t)
    (d : G2Data L K) (hK : Nat.card K = 2 ^ f) (h8 : 8 ≤ Nat.card K) :
    Complement₂ d t (yamadaN₂ d t ⊓ centralizer (d.J₄ : Set G)) := by
  have hQ := h.qFacts_of_eight d hK h8
  obtain ⟨hsup, hlevi⟩ := h.yamada_5_60_2 hW d hK hQ
  have htN₂ : t ∈ normalizer (yamadaN₂ d t : Set G) :=
    ProductK2Aux.t_mem_normalizer_N₂_aux hW h d hK hQ
  have hJ₄ : ∀ j ∈ (d.J₄ : Subgroup G), j * t = t * j := fun j hj =>
    mem_centralizer_singleton_iff.1
      (Subgroup.mem_inf.1 (h.J_le_centralizer_inf_normalizer_S d (J₄_le_J d hj))).1
  refine ⟨le_rfl, h.yamada_5_60_3 hW d hK h8, hsup, ?_, hlevi⟩
  rw [conj_inf, conj_eq_of_mem_normalizer htN₂, ProductN3Aux.conj_centralizer_of_commute hJ₄]

end Setup

theorem g2LargeCenterlessExclusion_holds :
    CFSG.Yardstones.M41b0c98b3153.G2LargeCenterlessExclusion := by
  intro G _ _ _ hnonab hK L hL hZ hcore hcyc f hf hm
  have hW : CFSG.Walter.WalterOrderForm := fun G _ _ _ hnonab P hP =>
    CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple G hnonab P hP
  obtain ⟨t, h⟩ := exists_setup hnonab hK hL hZ hcore hcyc (by omega) hm
  obtain ⟨K, _, _, _, hKc, ⟨d⟩⟩ := h.exists_data
  have h8 : 8 ≤ Nat.card K := by
    rw [hKc]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  exact h.false_of_qFacts hW d hKc (h.qFacts_of_eight d hKc h8)
    ⟨_, h.complement₂_of_eight hW d hKc h8⟩

end CFSG.LocalAnalysis.EvenBN.G2
