module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalAUK

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal

open Subgroup JankoTwelve

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z} (h : Hyp fr)
  (p12 : JankoProp12 fr)

omit [Finite G] in
theorem card_E_sup_of_mem_K {k : G} (hk : k ∈ fr.K) (hk3 : orderOf k = 3) :
    Nat.card (fr.E ⊔ zpowers k : Subgroup G) = 81 := by
  have hle : zpowers k ≤ normalizer (fr.E : Set G) := zpowers_le.mpr (fr.K_le_normalizer hk)
  have hbot : zpowers k ⊓ fr.E = ⊥ := by
    rw [eq_bot_iff, ← fr.E_inf_K, inf_comm]
    exact inf_le_inf_left _ (zpowers_le.mpr hk)
  rw [sup_comm, card_sup_of_inf_eq_bot hle hbot, Nat.card_zpowers, hk3, fr.card_E]

include h p12 in
theorem isConj_of_le_UK {e : G} (he : e ∈ fr.E) (he1 : e ≠ 1) {B : Subgroup G}
    (hB : B ≤ (fr.U ⊔ fr.K) ⊓ centralizer ({e} : Set G)) (hcard : Nat.card B = 3 ^ 8) :
    IsConj e fr.s₃ := by
  have hle : fr.K ⊓ centralizer ({e} : Set G) ≤
      normalizer ((fr.U ⊓ centralizer ({e} : Set G) : Subgroup G) : Set G) := fun k hk =>
    inf_mem_normalizer (p12.K_le_normalizer_U hk.1)
      (mem_normalizer_centralizer_singleton (mem_centralizer_singleton_iff.mp hk.2))
  have hbot : fr.K ⊓ centralizer ({e} : Set G) ⊓ (fr.U ⊓ centralizer ({e} : Set G)) = ⊥ := by
    rw [eq_bot_iff, ← p12.U_inf_K]
    exact le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_left)
  have hdvd := card_dvd_of_le ((hB.trans (UK_inf_le_of_mem h p12 he)))
  rw [hcard, card_sup_of_inf_eq_bot hle hbot, card_U_inf_centralizer_E h p12 he he1,
    pow_succ', mul_comm] at hdvd
  have h3 : 3 ∣ Nat.card (fr.K ⊓ centralizer ({e} : Set G) : Subgroup G) :=
    Nat.dvd_of_mul_dvd_mul_right (by norm_num) hdvd
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hk3 : orderOf (k : G) = 3 := by rw [orderOf_coe]; exact hk
  have h81 : 81 ∣ Nat.card (centralizer ({e} : Set G) ⊓ centralizer ({z} : Set G) :
      Subgroup G) := by
    rw [← card_E_sup_of_mem_K k.2.1 hk3]
    refine card_dvd_of_le (sup_le (le_inf (fun x hx => ?_) fr.E_le) (zpowers_le.mpr
      ⟨?_, fr.K_le k.2.1⟩))
    · exact mem_centralizer_singleton_iff.mpr (fr.E_comm x hx e he)
    · exact k.2.2
  exact (h.p7.isConj_s₃_iff z h.set.orderOf_z e (fr.E_le he) (fr.E_pow_three e he)).mpr
    (card_eq_of_dvd h (fr.E_le he) (fr.E_pow_three e he) he1 h81)

include h in
theorem S_inf_centralizer_W {m s : G} (hm : JankoChoiceM fr m) :
    fr.S ⊓ centralizer (Wof fr m s : Set G) = fr.P3bar := by
  have hmW : m ∈ Wof fr m s := mem_sup_right (mem_zpowers m)
  refine le_antisymm ?_ (le_inf le_sup_left ?_)
  · rw [← h.S_inf_centralizer_m hm.mem_K hm.orderOf_m hm.mem_centralizer]
    exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hmW))
  · have hZ : fr.P3bar ≤ centralizer (fr.R m : Set G) := by
      rw [← hm.center_R]
      exact inf_le_right
    exact hZ.trans (centralizer_le (SetLike.coe_subset_coe.mpr W_le_R))

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinal
