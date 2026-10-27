module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F5Sq
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Wc
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F7Syl

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G]

private lemma local_t84_zpowers_inf_eq_bot_of_notMem {t : G} {C : Subgroup G}
    (ht : t ∉ C) (hcard : Nat.card ↥(zpowers t) = 2) : zpowers t ⊓ C = ⊥ := by
  haveI : Fact (Nat.card ↥(zpowers t)).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (C.subgroupOf (zpowers t)) with h | h
  · have hd : Disjoint C (zpowers t) := Subgroup.subgroupOf_eq_bot.mp h
    rw [Subgroup.disjoint_def] at hd
    refine le_antisymm ?_ bot_le
    intro x hx
    rw [Subgroup.mem_bot]
    exact hd hx.2 hx.1
  · exact absurd ((Subgroup.subgroupOf_eq_top.mp h) (Subgroup.mem_zpowers t)) ht

theorem sec8t84_S_card (F : Sec8T84Base) (hI : Asc82Step84IK)
    (hKP : CFSG.Assembly.KProper Catalog G) {t : G} {L S : Subgroup G} {z g : G}
    {B E T T1 T2 V1 V2 F1 F2 : Subgroup G} (hE : Sec8E G t L S z g B E)
    (hgood : S ⊓ L ≤ normalizer (E : Set G)) (hST : S ⊓ normalizer (E : Set G) ≤ T)
    (D : Sec8T84TData G t E T T1 T2 V1 V2 F1 F2) {c : G}
    (hcC : c ∈ centralizer ({t} : Set G)) (hcT : c ∉ T) (hcN : c ∈ normalizer (T : Set G))
    (hc2 : IsPGroup 2 ↥((T ⊓ centralizer ({t} : Set G)) ⊔ zpowers c)) :
    S ⊓ normalizer (E : Set G) = T ⊓ centralizer ({t} : Set G) ∧
      T ⊓ centralizer ({t} : Set G) = zpowers t ⊔ (S ⊓ L) ∧ Nat.card S = 2 ^ 9 ∧
      Nat.card ↥((T ⊓ centralizer ({t} : Set G)) ⊔ zpowers c) = 2 ^ 9 := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hE.ctx.involution]
    exact pow_orderOf_eq_one t
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htS : t ∈ S := sec4_t_mem_S hE.ctx.sylow hE.ctx.involution
  have htN : t ∈ normalizer (E : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact hE.t_norm e he
    · intro he
      have h := hE.t_norm (t * e * t⁻¹) he
      have hkey : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [hinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
          _ = e := by rw [ht2]; group
      rwa [hkey] at h
  have htT : t ∈ T := hST (Subgroup.mem_inf.mpr ⟨htS, htN⟩)
  have hSleC : S ≤ centralizer ({t} : Set G) := hE.ctx.sylow.1
  have hSLC : S ⊓ L ≤ centralizer ({t} : Set G) := fun x hx => hSleC hx.1
  have hSLT : S ⊓ L ≤ T := by
    have hle : S ⊓ L ≤ S ⊓ normalizer (E : Set G) :=
      fun x hx => Subgroup.mem_inf.mpr ⟨hx.1, hgood hx⟩
    exact hle.trans hST
  set M0 : Subgroup G := T ⊓ centralizer ({t} : Set G) with hM0
  have hM0card : Nat.card M0 = 2 ^ 8 := by
    rw [hM0]
    exact sec8t84_card_cent_t D
  have hM0C : M0 ≤ centralizer ({t} : Set G) := by
    rw [hM0]
    exact inf_le_right
  have hzpT : zpowers t ≤ T := Subgroup.zpowers_le.mpr htT
  have hzpC : zpowers t ≤ centralizer ({t} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hsupM0 : zpowers t ⊔ (S ⊓ L) ≤ M0 := by
    rw [hM0]
    exact sup_le (le_inf hzpT hzpC) (le_inf hSLT hSLC)
  have htnotL : t ∉ L := sec8t84_t_not_mem_L F hE.ctx
  have htnotSL : t ∉ S ⊓ L := fun hx => htnotL hx.2
  have h2 : Nat.card ↥(zpowers t) = 2 := by
    rw [Nat.card_zpowers, hE.ctx.involution]
  have hdisj : zpowers t ⊓ (S ⊓ L) = ⊥ :=
    local_t84_zpowers_inf_eq_bot_of_notMem htnotSL h2
  have hcomm : ∀ a ∈ zpowers t, ∀ b ∈ S ⊓ L, a * b = b * a := by
    intro a ha b hb
    have hbC : b ∈ centralizer ({t} : Set G) := hSLC hb
    have hbt : b * t = t * b := Subgroup.mem_centralizer_singleton_iff.mp hbC
    have hle : zpowers t ≤ centralizer ({b} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hbt.symm)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)
  have hcardSup : Nat.card ↥(zpowers t ⊔ (S ⊓ L)) = 2 * Nat.card ↥(S ⊓ L) := by
    rw [sec124_card_sup hcomm hdisj, h2]
  have hcardSL_le : Nat.card ↥(S ⊓ L) ≤ 2 ^ 7 := by
    have hle := Subgroup.card_le_of_le hsupM0
    rw [hcardSup, hM0card] at hle
    omega
  obtain ⟨γ, hγS, hγout, hSeq, hγsq, hS_le⟩ := sec8t84_gamma0 F hI hKP hE.ctx
  have hS_le_29 : Nat.card S ≤ 2 ^ 9 := by
    calc Nat.card S ≤ 4 * Nat.card ↥(S ⊓ L) := hS_le
      _ ≤ 4 * 2 ^ 7 := Nat.mul_le_mul_left 4 hcardSL_le
      _ = 2 ^ 9 := by norm_num
  set S' : Subgroup G := M0 ⊔ zpowers c with hS'
  have hM0S' : M0 ≤ S' := by
    rw [hS']
    exact le_sup_left
  have hcS' : c ∈ S' := by
    rw [hS']
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hcM0 : c ∉ M0 := by
    intro h
    apply hcT
    rw [hM0] at h
    exact h.1
  have hS'C : S' ≤ centralizer ({t} : Set G) := by
    rw [hS']
    exact sup_le hM0C (Subgroup.zpowers_le.mpr hcC)
  have hc2' : IsPGroup 2 S' := by
    rw [hS', hM0]
    exact hc2
  have hdvd : Nat.card M0 ∣ Nat.card S' := Subgroup.card_dvd_of_le hM0S'
  have hne : Nat.card S' ≠ Nat.card M0 := by
    intro heq
    have hEq : M0 = S' := Subgroup.eq_of_le_of_card_ge hM0S' (le_of_eq heq)
    exact hcM0 (hEq.symm ▸ hcS')
  have h9le : 2 ^ 9 ≤ Nat.card S' := by
    obtain ⟨k, hk⟩ := hdvd
    have hS'pos : 0 < Nat.card S' := Nat.card_pos
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with hk0 | hpos
      · rw [hk, hk0, Nat.mul_zero] at hS'pos
        omega
      · exact hpos
    have hkne : k ≠ 1 := by
      intro hk1
      exact hne (by rw [hk, hk1, Nat.mul_one])
    have hk2 : 2 ≤ k := by omega
    rw [hk, hM0card]
    calc 2 ^ 9 = 2 ^ 8 * 2 := by norm_num
      _ ≤ 2 ^ 8 * k := Nat.mul_le_mul_left _ hk2
  have hS'leS : Nat.card S' ≤ Nat.card S :=
    sec8t84_card_le_of_sylow hE.ctx.sylow hS'C hc2'
  have h9leS : 2 ^ 9 ≤ Nat.card S := h9le.trans hS'leS
  have hcardS : Nat.card S = 2 ^ 9 := le_antisymm hS_le_29 h9leS
  have hcardS' : Nat.card S' = 2 ^ 9 := by
    refine le_antisymm ?_ h9le
    rw [hcardS] at hS'leS
    exact hS'leS
  have hcardSL : Nat.card ↥(S ⊓ L) = 2 ^ 7 := by
    have hge : 2 ^ 7 ≤ Nat.card ↥(S ⊓ L) := by
      have h := hS_le
      rw [hcardS] at h
      omega
    omega
  have hcardSupM0 : Nat.card ↥(zpowers t ⊔ (S ⊓ L)) = Nat.card M0 := by
    rw [hcardSup, hcardSL, hM0card]
    norm_num
  have hEqSup : zpowers t ⊔ (S ⊓ L) = M0 :=
    Subgroup.eq_of_le_of_card_ge hsupM0 (le_of_eq hcardSupM0.symm)
  have hfirst : S ⊓ normalizer (E : Set G) = M0 := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp hx
      rw [hM0]
      exact Subgroup.mem_inf.mpr
        ⟨hST (Subgroup.mem_inf.mpr ⟨hxS, hxN⟩), hSleC hxS⟩
    · rw [← hEqSup]
      refine sup_le ?_ ?_
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨htS, htN⟩)
      · intro x hx
        exact Subgroup.mem_inf.mpr ⟨hx.1, hgood hx⟩
  refine ⟨?_, ?_, hcardS, ?_⟩
  · rw [hfirst, hM0]
  · exact hM0.symm.trans hEqSup.symm
  · simpa [hM0, hS'] using hcardS'

end CFSG.OddStandard.SmallF3.Omega
