module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84EDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec79BA
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {E Y1 Y2 : Subgroup G}

private theorem pow_eq_self_of_sq_eq_one_of_odd {x : G} (hx : x ^ 2 = 1) {m : ℕ}
    (hm : Odd m) : x ^ m = x := by
  obtain ⟨k, rfl⟩ := hm
  calc x ^ (2 * k + 1) = x ^ (2 * k) * x := by rw [pow_succ]
    _ = (x ^ 2) ^ k * x := by rw [pow_mul]
    _ = 1 ^ k * x := by rw [hx]
    _ = x := by simp

private theorem inf_le_normalizer_oddCoreIn (hc : Sec8T84XCore G t E Y1 Y2) :
    E ⊓ Y1 ≤ normalizer (oddCoreIn (normalizer (E : Set G)) : Set G) := by
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_oddCoreIn (K := normalizer (E : Set G))
      (Subgroup.le_normalizer (hc.le1 he.2)) hx
  · intro hx
    have he' : e⁻¹ ∈ normalizer (normalizer (E : Set G) : Set G) :=
      Subgroup.le_normalizer ((normalizer (E : Set G)).inv_mem (hc.le1 he.2))
    have h := conj_mem_oddCoreIn (K := normalizer (E : Set G)) he' hx
    have hx' : x = e⁻¹ * (e * x * e⁻¹) * (e⁻¹)⁻¹ := by group
    rw [hx']
    exact h

private theorem inf_subgroupOf_Y1_normal (hc : Sec8T84XCore G t E Y1 Y2) :
    ((E ⊓ Y1).subgroupOf Y1).Normal := by
  rw [Subgroup.inf_subgroupOf_right]
  exact Subgroup.normal_subgroupOf_of_le_normalizer hc.le1

private theorem oddCoreIn_subgroupOf_sup_normal (hc : Sec8T84XCore G t E Y1 Y2) :
    ((oddCoreIn (normalizer (E : Set G))).subgroupOf
      ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right)).mpr ?_
  exact sup_le (inf_le_normalizer_oddCoreIn hc) Subgroup.le_normalizer

private theorem isComplement'_subgroupOf_sup_oddCoreIn (hc : Sec8T84XCore G t E Y1 Y2) :
    ((E ⊓ Y1).subgroupOf ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))).IsComplement'
      ((oddCoreIn (normalizer (E : Set G))).subgroupOf
        ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) := by
  haveI : ((oddCoreIn (normalizer (E : Set G))).subgroupOf
      ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))).Normal :=
    oddCoreIn_subgroupOf_sup_normal hc
  have hinf_bot : E ⊓ Y1 ⊓ oddCoreIn (normalizer (E : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx2 : x ^ 2 = 1 := hc.e16_1.1.2 x hx.1
    have hxodd : Odd (orderOf x) := odd_orderOf_of_mem_oddCoreIn hx.2
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hxodd.coprime_two_right hdvd)
  have hdisj : Disjoint ((E ⊓ Y1).subgroupOf ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))))
      ((oddCoreIn (normalizer (E : Set G))).subgroupOf
        ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) := by
    rw [disjoint_iff]
    have hsub : ((E ⊓ Y1).subgroupOf ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) ⊓
        ((oddCoreIn (normalizer (E : Set G))).subgroupOf
          ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) =
        ((E ⊓ Y1) ⊓ oddCoreIn (normalizer (E : Set G))).subgroupOf
          ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) :=
      (Subgroup.comap_inf (E ⊓ Y1) (oddCoreIn (normalizer (E : Set G)))
        ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))).subtype).symm
    rw [hsub, hinf_bot, Subgroup.bot_subgroupOf]
  have hsup : ((E ⊓ Y1).subgroupOf ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) ⊔
      ((oddCoreIn (normalizer (E : Set G))).subgroupOf
        ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup
        (le_sup_left : E ⊓ Y1 ≤ (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))
        (le_sup_right : oddCoreIn (normalizer (E : Set G)) ≤
          (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))),
      Subgroup.subgroupOf_self]
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj ?_
  rw [← Subgroup.mul_normal ((E ⊓ Y1).subgroupOf ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))))
    ((oddCoreIn (normalizer (E : Set G))).subgroupOf
      ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))), hsup]
  rfl

theorem sec8t84d5_core_symm (h : Sec8T84XCore G t E Y1 Y2) : Sec8T84XCore G t E Y2 Y1 := by
  refine ⟨h.o_le2, h.o_le1, h.le2, h.le1, ?_, ?_, ?_, ?_, h.swap2, h.swap1, ?_, h.e16_2, h.e16_1,
    h.quot2, h.quot1, h.cent2, h.cent1, h.trans2, h.trans1⟩
  · intro a ha b hb
    have h' := h.comm b hb a ha
    have : a * b * a⁻¹ * b⁻¹ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by group
    rw [this]
    exact (oddCoreIn (normalizer (E : Set G))).inv_mem h'
  · rw [inf_comm]
    exact h.inf
  · rw [sup_comm Y2 Y1]
    exact h.sup
  · rw [sup_comm Y2 Y1]
    exact h.t_not
  · rw [sup_comm (E ⊓ Y2) (E ⊓ Y1)]
    exact h.E_sup

theorem sec8t84d5_card_sylow (hc : Sec8T84XCore G t E Y1 Y2) {S1 : Subgroup G}
    (hS : IsSylow2Of S1 Y1) : Nat.card ↥S1 = 2 ^ 7 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcompl := isComplement'_subgroupOf_sup_oddCoreIn hc
  have hcardE1sub : Nat.card
      ↥((E ⊓ Y1).subgroupOf ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : E ⊓ Y1 ≤ (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))).toEquiv,
      hc.e16_1.2]
    norm_num
  have hcardOsub : Nat.card
      ↥((oddCoreIn (normalizer (E : Set G))).subgroupOf
        ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))) =
      Nat.card ↥(oddCoreIn (normalizer (E : Set G))) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : oddCoreIn (normalizer (E : Set G)) ≤
        (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)))).toEquiv
  have hcardK : Nat.card ↥((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) =
      16 * Nat.card ↥(oddCoreIn (normalizer (E : Set G))) := by
    have h := hcompl.card_mul_card
    rw [hcardE1sub, hcardOsub] at h
    exact h.symm
  have hYcard : Nat.card ↥Y1 = Nat.card ↥((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) *
      Nat.card (alternatingGroup (Fin 6)) := by
    obtain ⟨φ, hsurj, hker⟩ := hc.quot1
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker] at h1
    have h2 : Nat.card ↥(((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))).subgroupOf Y1) =
        Nat.card ↥((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (sup_le inf_le_right hc.o_le1 : (E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G)) ≤ Y1)).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hYfac : (Nat.card ↥Y1).factorization 2 = 7 := by
    have hOodd : Odd (Nat.card ↥(oddCoreIn (normalizer (E : Set G)))) :=
      odd_card_oddCoreIn _
    rw [hYcard, hcardK, hA6]
    have hrewrite : 16 * Nat.card ↥(oddCoreIn (normalizer (E : Set G))) * 360 =
        2 ^ 7 * (Nat.card ↥(oddCoreIn (normalizer (E : Set G))) * 45) := by ring
    rw [hrewrite]
    have hoddm : Odd (Nat.card ↥(oddCoreIn (normalizer (E : Set G))) * 45) :=
      hOodd.mul ⟨22, by norm_num⟩
    have hcop : Nat.Coprime (2 ^ 7) (Nat.card ↥(oddCoreIn (normalizer (E : Set G))) * 45) :=
      (Nat.coprime_two_left.mpr hoddm).pow_left 7
    have h0 : (Nat.card ↥(oddCoreIn (normalizer (E : Set G))) * 45).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd
        (Nat.prime_two.coprime_iff_not_dvd.mp (Nat.coprime_two_left.mpr hoddm))
    rw [Nat.factorization_mul_apply_of_coprime hcop, Nat.factorization_pow_self Nat.prime_two, h0,
      add_zero]
  obtain ⟨P, hPmap⟩ := hS.exists_sylow
  have hcardS1 : Nat.card ↥S1 = Nat.card ↥(P : Subgroup ↥Y1) := by
    rw [← hPmap]
    exact Subgroup.card_map_of_injective Y1.subtype_injective
  rw [hcardS1, Sylow.card_eq_multiplicity P, hYfac]

theorem sec8t84d5_complement (hc : Sec8T84XCore G t E Y1 Y2) {S1 : Subgroup G}
    (hS : IsSylow2Of S1 Y1)
    (hK : ∃ K : Subgroup G, K ≤ S1 ∧ (E ⊓ Y1) ⊓ K = ⊥ ∧ (E ⊓ Y1) ⊔ K = S1) :
    ∃ H : Subgroup G, H ≤ Y1 ∧ (E ⊓ Y1) ⊓ H = ⊥ ∧ (E ⊓ Y1) ⊔ H = Y1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ((E ⊓ Y1).subgroupOf Y1).Normal := inf_subgroupOf_Y1_normal hc
  haveI : IsMulCommutative ((E ⊓ Y1).subgroupOf Y1) := by
    haveI : IsMulCommutative ↥(E ⊓ Y1) := hc.e16_1.1.1
    exact IsMulCommutative.of_comm fun a b =>
      (Subgroup.subgroupOfEquivOfLe inf_le_right).injective (by
        rw [map_mul, map_mul, mul_comm'])
  have hVp : IsPGroup 2 ((E ⊓ Y1).subgroupOf Y1) :=
    (IsPGroup.iff_card.mpr ⟨4, hc.e16_1.2⟩).of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  obtain ⟨P, hPmap⟩ := hS.exists_sylow
  obtain ⟨K0, hK0S1, hK0inf, hK0sup⟩ := hK
  have hK0Y : K0 ≤ Y1 := hK0S1.trans hS.1
  have hK'P : K0.subgroupOf Y1 ≤ P := by
    intro x hx
    have hxK0 : (x : G) ∈ K0 := hx
    have hxS1 : (x : G) ∈ S1 := hK0S1 hxK0
    rw [← hPmap] at hxS1
    obtain ⟨y, hyP, hyx⟩ := Subgroup.mem_map.mp hxS1
    have hyx' : y = x := Subtype.ext hyx
    rwa [← hyx']
  have hK'inf : ((E ⊓ Y1).subgroupOf Y1) ⊓ (K0.subgroupOf Y1) = ⊥ := by
    have hsub : ((E ⊓ Y1).subgroupOf Y1) ⊓ (K0.subgroupOf Y1) =
        ((E ⊓ Y1) ⊓ K0).subgroupOf Y1 :=
      (Subgroup.comap_inf (E ⊓ Y1) K0 Y1.subtype).symm
    rw [hsub, hK0inf, Subgroup.bot_subgroupOf]
  have hK'sup : ((E ⊓ Y1).subgroupOf Y1) ⊔ (K0.subgroupOf Y1) = P := by
    have hS1sub : S1.subgroupOf Y1 = P := by
      rw [← hPmap]
      exact Subgroup.comap_map_eq_self_of_injective Y1.subtype_injective P
    rw [← Subgroup.subgroupOf_sup inf_le_right hK0Y, hK0sup, hS1sub]
  obtain ⟨K'', hK''inf, hK''sup⟩ :=
    (CFSG.Quasithin.gaschutz (G := ↥Y1) (p := 2) (V := (E ⊓ Y1).subgroupOf Y1) hVp P).mpr
      ⟨K0.subgroupOf Y1, hK'P, hK'inf, hK'sup⟩
  refine ⟨K''.map Y1.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h1 : (((E ⊓ Y1).subgroupOf Y1) ⊓ K'').map Y1.subtype = ⊥ := by
      rw [hK''inf, Subgroup.map_bot]
    rw [Subgroup.map_inf _ _ Y1.subtype Y1.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    exact h1
  · have h1 : (((E ⊓ Y1).subgroupOf Y1) ⊔ K'').map Y1.subtype = Y1 := by
      rw [hK''sup, Subgroup.map_top, Subgroup.range_subtype]
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    exact h1

theorem sec8t84d5_split_of_complement
    (hO : oddCoreIn (normalizer (E : Set G)) ≤ centralizer (E : Set G))
    (hc : Sec8T84XCore G t E Y1 Y2) {H : Subgroup G} (hHY : H ≤ Y1) (hinf : (E ⊓ Y1) ⊓ H = ⊥)
    (hsup : (E ⊓ Y1) ⊔ H = Y1) : Sec8T84SplitFor G E Y1 := by
  classical
  haveI : ((E ⊓ Y1).subgroupOf Y1).Normal := inf_subgroupOf_Y1_normal hc
  have hO_le_H : oddCoreIn (normalizer (E : Set G)) ≤ H := by
    intro o ho
    have hoY : o ∈ Y1 := hc.o_le1 ho
    have hsup' : (E ⊓ Y1).subgroupOf Y1 ⊔ H.subgroupOf Y1 = ⊤ := by
      rw [← Subgroup.subgroupOf_sup inf_le_right hHY, hsup, Subgroup.subgroupOf_self]
    have hmem : (⟨o, hoY⟩ : ↥Y1) ∈ (E ⊓ Y1).subgroupOf Y1 ⊔ H.subgroupOf Y1 := by
      rw [hsup']; trivial
    obtain ⟨e', he', h', hh', heh⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
    have he'E1 : (e' : G) ∈ E ⊓ Y1 := Subgroup.mem_subgroupOf.mp he'
    have hh'H : (h' : G) ∈ H := Subgroup.mem_subgroupOf.mp hh'
    have hehG : (e' : G) * (h' : G) = o := by
      have := congrArg (fun z : ↥Y1 => (z : G)) heh
      simpa using this
    have heo : (e' : G) * o = o * (e' : G) :=
      (Subgroup.mem_centralizer_iff.mp (hO ho)) (e' : G) he'E1.1
    have he2 : (e' : G) ^ 2 = 1 := hc.e16_1.1.2 _ he'E1
    have hodd : Odd (orderOf o) := odd_orderOf_of_mem_oddCoreIn ho
    have hh_eq : (h' : G) = (e' : G)⁻¹ * o := by rw [← hehG]; group
    have hpow : (h' : G) ^ (orderOf o) = (e' : G) := by
      have hinv : (e' : G)⁻¹ = (e' : G) :=
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact he2)
      rw [hh_eq, (Commute.inv_left heo).mul_pow (orderOf o), inv_pow,
        pow_eq_self_of_sq_eq_one_of_odd he2 hodd, pow_orderOf_eq_one, mul_one, hinv]
    have he'H : (e' : G) ∈ H := by
      rw [← hpow]
      exact H.pow_mem hh'H (orderOf o)
    have he'one : (e' : G) = 1 := by
      have : (e' : G) ∈ (⊥ : Subgroup G) := by rw [← hinf]; exact ⟨he'E1, he'H⟩
      simpa using this
    have hxo : o = (h' : G) := by rw [← hehG, he'one, one_mul]
    rw [hxo]
    exact hh'H
  have hcompl := isComplement'_subgroupOf_sup_oddCoreIn hc
  refine ⟨H, hHY, ?_, ?_⟩
  · intro x hx
    have hxH : x ∈ H := hx.1
    obtain ⟨⟨e', o'⟩, heo⟩ :=
      hcompl.2 (⟨x, hx.2⟩ : ↥((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))))
    have heoG : (e' : G) * (o' : G) = x := by
      have := congrArg (fun z : ↥((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) => (z : G)) heo
      simpa using this
    have he'E1 : (e' : G) ∈ E ⊓ Y1 := e'.2
    have ho'O : (o' : G) ∈ oddCoreIn (normalizer (E : Set G)) := o'.2
    have ho'H : (o' : G) ∈ H := hO_le_H ho'O
    have he'H : (e' : G) ∈ H := by
      have hx' : (e' : G) = x * (o' : G)⁻¹ := by rw [← heoG]; group
      rw [hx']
      exact H.mul_mem hxH (H.inv_mem ho'H)
    have he'one : (e' : G) = 1 := by
      have : (e' : G) ∈ (⊥ : Subgroup G) := by rw [← hinf]; exact ⟨he'E1, he'H⟩
      simpa using this
    have hxo : x = (o' : G) := by rw [← heoG, he'one, one_mul]
    rw [hxo]
    exact ho'O
  · apply le_antisymm
    · exact sup_le hHY (sup_le inf_le_right hc.o_le1)
    · calc Y1 = (E ⊓ Y1) ⊔ H := hsup.symm
        _ ≤ ((E ⊓ Y1) ⊔ H) ⊔ oddCoreIn (normalizer (E : Set G)) := le_sup_left
        _ = H ⊔ ((E ⊓ Y1) ⊔ oddCoreIn (normalizer (E : Set G))) := by
              rw [sup_assoc, sup_left_comm]

end CFSG.OddStandard.SmallF3.Omega
