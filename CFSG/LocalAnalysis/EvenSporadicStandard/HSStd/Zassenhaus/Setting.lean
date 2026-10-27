module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5Steps
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

theorem mem_of_isPGroup_of_odd_relIndex {S : Subgroup G} (hle : S ≤ centralizer ({t} : Set G))
    (h2 : IsPGroup 2 S) (hidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G)))
    (ht2 : orderOf t = 2) : t ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have hBS : zpowers t ≤ centralizer (S : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun s hs => mem_centralizer_singleton_iff.1 (hle hs)
  have hP := isPGroup_sup_of_le_centralizer h2 hB hBS
  have hPC : S ⊔ zpowers t ≤ centralizer ({t} : Set G) :=
    sup_le hle (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hmul := relIndex_mul_relIndex S (S ⊔ zpowers t) _ le_sup_left hPC
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hP
  have hdvd : S.relIndex (S ⊔ zpowers t) ∣ 2 ^ k := hk ▸ relIndex_dvd_card S (S ⊔ zpowers t)
  obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rcases j with _ | j
  · rw [pow_zero] at hjeq
    exact relIndex_eq_one.1 hjeq (mem_sup_right (mem_zpowers t))
  · exfalso
    apply hidx
    rw [← hmul, hjeq]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero j)) _

omit [Finite G] in
theorem disjoint_zpowers (htL : t ∈ centralizer (L : Set G))
    (hLC : L ⊓ centralizer (L : Set G) = ⊥) : Disjoint L (zpowers t) := by
  rw [disjoint_iff, eq_bot_iff]
  rintro x ⟨hxL, hxt⟩
  have : x ∈ L ⊓ centralizer (L : Set G) := ⟨hxL, (zpowers_le.2 htL) hxt⟩
  rwa [hLC] at this

omit [Finite G] in
theorem card_sup_zpowers (htL : t ∈ centralizer (L : Set G))
    (hLC : L ⊓ centralizer (L : Set G) = ⊥) (ht2 : orderOf t = 2) :
    Nat.card (L ⊔ zpowers t : Subgroup G) = 2 * Nat.card L := by
  have e := mulEquivProdSup (zpowers_le.2 htL) (disjoint_zpowers htL hLC)
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_zpowers, ht2, mul_comm]

theorem two_lt_card_inf {S : Subgroup G} (hin : centralizer ({t} : Set G) = L ⊔ zpowers t)
    (htL : t ∈ centralizer (L : Set G)) (hLC : L ⊓ centralizer (L : Set G) = ⊥)
    (ht2 : orderOf t = 2) (hle : S ≤ centralizer ({t} : Set G)) (h2 : IsPGroup 2 S)
    (hidx : ¬ 2 ∣ S.relIndex (centralizer ({t} : Set G))) (hL4 : 4 ∣ Nat.card L) :
    2 < Nat.card (S ⊓ L : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := card_sup_zpowers htL hLC ht2
  rw [← hin] at hC
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 h2
  have hSC := relIndex_mul_card (H := S) (K := centralizer ({t} : Set G))
  rw [inf_of_le_left hle, hk, hC] at hSC
  have hk3 : 3 ≤ k := by
    by_contra hk3
    have hk3' : k < 3 := Nat.lt_of_not_le hk3
    obtain ⟨m, hm⟩ := hL4
    interval_cases k <;> omega
  have hLC2 : L.relIndex (centralizer ({t} : Set G)) = 2 := by
    have h := relIndex_mul_card (H := L) (K := centralizer ({t} : Set G))
    have hLle : L ≤ centralizer ({t} : Set G) := hin ▸ le_sup_left
    rw [inf_of_le_left hLle, hC] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hrel : L.relIndex S ≤ 2 := by
    rw [← hLC2]
    exact relIndex_le_of_le_right hle (by rw [hLC2]; norm_num)
  have h3 := relIndex_mul_card (H := L) (K := S)
  rw [inf_comm, hk] at h3
  have hpow : 8 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk3)
  by_contra hle2
  have hle2' : Nat.card (S ⊓ L : Subgroup G) ≤ 2 := Nat.le_of_not_lt hle2
  have : L.relIndex S * Nat.card (S ⊓ L : Subgroup G) ≤ 2 * 2 :=
    Nat.mul_le_mul hrel hle2'
  omega

theorem card_of_isSporadic_hs {Y : Type} [Group Y]
    (h : IsSporadic Y .HS) : Nat.card Y = 44352000 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr (e : Y ≃* NativeSporadic.HS).toEquiv]
  exact CFSG.Sporadic.HS.card_HS

omit [Finite G] in
theorem inf_centralizer_eq_bot_hs (hL : IsSporadic L .HS) :
    L ⊓ centralizer (L : Set G) = ⊥ := by
  rw [← map_center_eq_inf_centralizer, center_eq_bot_of_isSporadic_hs hL, Subgroup.map_bot]

section FusionData

variable {S : Subgroup G} {z n : G}

theorem fusionData_t_mem (hf : HSFusionData L t S z n) (ht2 : orderOf t = 2) : t ∈ S :=
  mem_of_isPGroup_of_odd_relIndex hf.le hf.pgroup hf.index ht2

theorem fusionData_conj_z (hf : HSFusionData L t S z n)
    (hL : IsSporadic L .HS) (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) : n * z * n⁻¹ = z := by
  have hLC := inf_centralizer_eq_bot_hs hL
  have hL4 : 4 ∣ Nat.card L := by rw [card_of_isSporadic_hs hL]; norm_num
  exact conj_eq_self_of_normalizer htL (hin ▸ hf.le) (fusionData_t_mem hf ht2) hf.pgroup hf.z2 hf.zc hf.nS
    (two_lt_card_inf hin htL hLC ht2 hf.le hf.pgroup hf.index hL4)

theorem fusionData_conj_ne_z (hf : HSFusionData L t S z n)
    (hL : IsSporadic L .HS) (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) (g : G) : g * t * g⁻¹ ≠ z := by
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht2
    omega
  exact conj_ne_of_inner hin htL (inf_centralizer_eq_bot_hs hL) ht1 hf.zL
    (fusionData_conj_z hf hL htL ht2 hin) hf.nt g

theorem fusionData_relIndex_odd (hf : HSFusionData L t S z n)
    (hL : IsSporadic L .HS) (htL : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hin : centralizer ({t} : Set G) = L ⊔ zpowers t) : ¬ 2 ∣ (S ⊓ L).relIndex L := by
  have hLC := inf_centralizer_eq_bot_hs hL
  have hC := card_sup_zpowers htL hLC ht2
  rw [← hin] at hC
  have htS : t ∈ S := fusionData_t_mem hf ht2
  have htnL : t ∉ L := by
    intro h
    have h1 : t ∈ L ⊓ centralizer (L : Set G) := ⟨h, htL⟩
    rw [hLC] at h1
    have ht1 : t = 1 := h1
    rw [ht1, orderOf_one] at ht2
    omega
  have hLle : L ≤ centralizer ({t} : Set G) := hin ▸ le_sup_left
  have hLC2 : L.relIndex (centralizer ({t} : Set G)) = 2 := by
    have h := relIndex_mul_card (H := L) (K := centralizer ({t} : Set G))
    rw [inf_of_le_left hLle, hC] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hCS := relIndex_mul_card (H := S) (K := centralizer ({t} : Set G))
  rw [inf_of_le_left hf.le] at hCS
  have hSL := relIndex_mul_card (H := L) (K := S)
  rw [inf_comm] at hSL
  have hLS := relIndex_mul_card (H := S ⊓ L) (K := L)
  rw [inf_of_le_left (inf_le_right : S ⊓ L ≤ L)] at hLS
  have hrel : L.relIndex S ≤ 2 := by
    rw [← hLC2]
    exact relIndex_le_of_le_right hf.le (by rw [hLC2]; norm_num)
  have hne0 : L.relIndex S ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hSL
    exact absurd hSL.symm (Nat.card_pos).ne'
  have hne1 : L.relIndex S ≠ 1 := fun h => htnL (relIndex_eq_one.1 h htS)
  have h2 : L.relIndex S = 2 := by omega
  rw [h2] at hSL
  have hpos : 0 < Nat.card (S ⊓ L : Subgroup G) := Nat.card_pos
  have key : (S ⊓ L).relIndex L = S.relIndex (centralizer ({t} : Set G)) := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [hLS]
    have h3 : 2 * Nat.card L =
        S.relIndex (centralizer ({t} : Set G)) * (2 * Nat.card (S ⊓ L : Subgroup G)) := by
      rw [← hC, ← hCS, hSL]
    have h4 : 2 * Nat.card L =
        2 * (S.relIndex (centralizer ({t} : Set G)) * Nat.card (S ⊓ L : Subgroup G)) := by
      rw [h3]
      ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  rw [key]
  exact hf.index

end FusionData

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus

