module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAElement
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoPropTwelveN3

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G]

@[expose] def Wof {z : G} (fr : JankoFrame G z) (m s : G) : Subgroup G :=
  fr.U ⊓ centralizer ({s} : Set G) ⊔ zpowers m

variable [Finite G] {z : G} {fr : JankoFrame G z} {m s : G} (h : Hyp fr) (p12 : JankoProp12 fr)
  (hm : JankoChoiceM fr m) (hs : fr.E ⊓ centralizer ({m} : Set G) = zpowers s)
  (hs3 : orderOf s = 3)

include h p12 hs hs3 in
theorem card_U_inf_s : Nat.card (fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) = 3 ^ 7 :=
  card_U_inf_centralizer_E h p12 (s_mem_E hs) (s_ne_one hs hs3)

include p12 hm hs in
theorem m_mem_normalizer : m ∈ normalizer ((fr.U ⊓ centralizer ({s} : Set G) : Subgroup G) :
    Set G) :=
  inf_mem_normalizer (p12.K_le_normalizer_U hm.mem_K)
    (mem_normalizer_centralizer_singleton (m_mul_s hs))

include h hm in
theorem zpowers_inf_U_inf : zpowers m ⊓ (fr.U ⊓ centralizer ({s} : Set G)) = ⊥ :=
  eq_bot_iff.mpr ((inf_le_inf_left _ inf_le_left).trans (h.zpowers_m_inf_U hm.mem_K).le)

include h p12 hm hs hs3 in
theorem card_W : Nat.card (Wof fr m s) = 3 ^ 8 := by
  rw [Wof, sup_comm, card_sup_of_inf_eq_bot (zpowers_le.mpr (m_mem_normalizer p12 hm hs))
    (zpowers_inf_U_inf h hm), Nat.card_zpowers, hm.orderOf_m, card_U_inf_s h p12 hs hs3]
  norm_num

include h p12 hm hs in
theorem W_inf_U : Wof fr m s ⊓ fr.U = fr.U ⊓ centralizer ({s} : Set G) := by
  refine le_antisymm (fun w hw => ?_) (le_inf le_sup_left inf_le_left)
  have hw1 := hw.1
  rw [Wof, sup_comm] at hw1
  obtain ⟨y, hy, x, hx, rfl⟩ :=
    exists_mul_of_mem_sup (zpowers_le.mpr (m_mem_normalizer p12 hm hs)) hw1
  have hyU : y ∈ fr.U := by
    have := fr.U.mul_mem hw.2 (fr.U.inv_mem hx.1)
    rwa [mul_inv_cancel_right] at this
  have hy1 : y = 1 := by
    have : y ∈ zpowers m ⊓ fr.U := ⟨hy, hyU⟩
    rwa [h.zpowers_m_inf_U hm.mem_K, mem_bot] at this
  rwa [hy1, one_mul]

include h p12 hm hs hs3 in
theorem W_inf_N : Wof fr m s ⊓ fr.N = fr.I := by
  have hI : fr.N ⊓ centralizer ({s} : Set G) = fr.I :=
    N_inf_centralizer_eq_I h (s_mem_E hs) (s_not_mem_P₁ h hm hs hs3)
  refine le_antisymm ?_ ?_
  · rw [← hI]
    intro w hw
    have hwU : w ∈ Wof fr m s ⊓ fr.U := ⟨hw.1, h.N_le_U hw.2⟩
    rw [W_inf_U h p12 hm hs] at hwU
    exact ⟨hw.2, hwU.2⟩
  · rw [← hI]
    exact le_inf ((inf_le_inf_right _ h.N_le_U).trans
      (le_sup_left : fr.U ⊓ centralizer ({s} : Set G) ≤ Wof fr m s)) inf_le_left

omit [Finite G] in
theorem W_sup_U : Wof fr m s ⊔ fr.U = fr.R m :=
  le_antisymm (sup_le (sup_le (inf_le_left.trans le_sup_left) le_sup_right) le_sup_left)
    (sup_le le_sup_right (le_sup_right.trans le_sup_left))

omit [Finite G] in
theorem W_le_R : Wof fr m s ≤ fr.R m :=
  le_sup_left.trans (W_sup_U (fr := fr) (m := m) (s := s)).le

omit [Finite G] in
include hs in
theorem W_le_centralizer : Wof fr m s ≤ centralizer ({s} : Set G) :=
  sup_le inf_le_right (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (m_mul_s hs)))

include h p12 hm hs hs3 in
theorem R_inf_centralizer : fr.R m ⊓ centralizer ({s} : Set G) = Wof fr m s := by
  have hle : Wof fr m s ≤ fr.R m ⊓ centralizer ({s} : Set G) :=
    le_inf W_le_R (W_le_centralizer hs)
  refine (eq_of_le_of_card_ge hle ?_).symm
  have hRU : fr.R m ⊓ centralizer ({s} : Set G) ≤ normalizer (fr.U : Set G) :=
    inf_le_left.trans (sup_le le_normalizer (zpowers_le.mpr (p12.K_le_normalizer_U hm.mem_K)))
  have h1 := card_sup_mul_card_inf hRU
  have hinf : fr.R m ⊓ centralizer ({s} : Set G) ⊓ fr.U = fr.U ⊓ centralizer ({s} : Set G) := by
    rw [inf_right_comm, inf_eq_right.mpr (h.U_le_R (m := m))]
  rw [hinf, card_U_inf_s h p12 hs hs3, p12.card_U] at h1
  have h2 : Nat.card (fr.R m ⊓ centralizer ({s} : Set G) ⊔ fr.U : Subgroup G) ≤ 3 ^ 10 := by
    rw [← hm.card_R]
    exact card_le_of_le (sup_le inf_le_left le_sup_left)
  rw [card_W h p12 hm hs hs3]
  nlinarith

omit [Finite G] in
theorem mem_normalizer_zpowers_of_comm {g a : G} (hga : g * a = a * g) :
    g ∈ normalizer (zpowers a : Set G) :=
  le_normalizer_of_commute (fun x hx y hy => by
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hy
    exact (Commute.zpow_zpow hga i j).eq) (mem_zpowers g)

include h hm hs in
theorem z_mem_normalizer_W : z ∈ normalizer (Wof fr m s : Set G) := by
  have hzs : z * s = s * z := (mem_centralizer_singleton_iff.mp (fr.E_le (s_mem_E hs))).symm
  have hzm : z * m = m * z := (mem_centralizer_singleton_iff.mp (fr.K_le hm.mem_K)).symm
  exact mem_normalizer_sup (inf_mem_normalizer h.z_mem_normalizer_U
    (mem_normalizer_centralizer_singleton hzs)) (mem_normalizer_zpowers_of_comm hzm)

include h hm hs hs3 in
theorem t_mem_normalizer_W : fr.t ∈ normalizer (Wof fr m s : Set G) :=
  mem_normalizer_sup (inf_mem_normalizer h.t_mem_normalizer_U
    (mem_normalizer_centralizer_of_inv (t_mul_s h hm hs hs3)))
    (h.t_mem_normalizer_zpowers hm.t_mul_m)

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
