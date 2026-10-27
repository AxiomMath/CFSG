module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4SlcProj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4Struct
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec4_slc_decomp [Finite G] {t : G} {L S : Subgroup G} (hL : IsOmega7Group L)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G))
    (hS : IsSylow2Of S (centralizer ({t} : Set G))) {x : G} (hx : x ∈ SLC S L) :
    ∃ p ∈ S ⊓ L, ∃ c ∈ S ⊓ centralizer (L : Set G), x = p * c := by
  let C := centralizer (L : Set G)
  let P := S ⊓ L
  let R := SLC S L
  change x ∈ S ⊓ (L ⊔ C) at hx
  have hcomm : ∀ a ∈ L, ∀ b ∈ C, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp hb a ha
  have hZC : centerIn L ≤ C := by
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (((sec4_mem_centerIn_iff z).mp hz).2 k hk).symm
  obtain ⟨π, hker, hinc⟩ := sec4_exists_proj_center_quotient (L := L) (C := C) hcomm hZC
  have hP : IsSylow2Of P L := sec4_isSylow2Of_inf hLt hN hS
  obtain ⟨T, hT⟩ := IsSylow2Of.exists_sylow hP
  let q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let TQ : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
    Sylow.mapSurjective (f := q) (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) T
  have hTQ : (TQ : Subgroup (↥L ⧸ Subgroup.center ↥L)) = (T : Subgroup ↥L).map q := rfl
  have hmap : (P.subgroupOf (L ⊔ C)).map π = (T : Subgroup ↥L).map q := by
    ext y
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hj' : (j : G) ∈ (T : Subgroup ↥L).map L.subtype := by
        rw [hT]; exact Subgroup.mem_subgroupOf.mp hj
      rw [Subgroup.mem_map] at hj'
      obtain ⟨s, hs, hsj⟩ := hj'
      refine Subgroup.mem_map.mpr ⟨s, hs, ?_⟩
      have hjs : j = Subgroup.inclusion le_sup_left s := Subtype.ext (by simpa using hsj.symm)
      rw [hjs]
      exact (hinc s).symm
    · rintro ⟨s, hs, rfl⟩
      refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion le_sup_left s, ?_, hinc s⟩
      rw [Subgroup.mem_subgroupOf, ← hT]
      exact Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
  have hPR : P ≤ R := le_inf inf_le_left (inf_le_right.trans le_sup_left)
  have hR2 : IsPGroup 2 ((R.subgroupOf (L ⊔ C)).map π) := by
    have hR : IsPGroup 2 R := hS.2.1.to_le (inf_le_left : R ≤ S)
    have hR' : IsPGroup 2 (R.subgroupOf (L ⊔ C)) :=
      hR.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : R ≤ L ⊔ C)).symm
    exact hR'.map π
  have hπR : (R.subgroupOf (L ⊔ C)).map π = (T : Subgroup ↥L).map q := by
    rw [← hTQ]
    exact TQ.is_maximal' hR2 (by
      rw [hTQ, ← hmap]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono (L ⊔ C) hPR))
  have hxR : x ∈ R := hx
  have hxR' : (⟨x, hx.2⟩ : ↥(L ⊔ C)) ∈ R.subgroupOf (L ⊔ C) :=
    Subgroup.mem_subgroupOf.mpr hxR
  have hxπ : π ⟨x, hx.2⟩ ∈ (R.subgroupOf (L ⊔ C)).map π := Subgroup.mem_map_of_mem π hxR'
  rw [hπR, ← hmap] at hxπ
  obtain ⟨j, hj, hjx⟩ := Subgroup.mem_map.mp hxπ
  have hm : (j : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.mp hj
  have hcC : (j : G)⁻¹ * x ∈ C := by
    have h1 : π (j⁻¹ * ⟨x, hx.2⟩) = 1 := by
      rw [map_mul, map_inv, hjx]
      group
    have h2 := (hker (j⁻¹ * ⟨x, hx.2⟩)).mp h1
    simpa using h2
  exact ⟨(j : G), hm, (j : G)⁻¹ * x,
    ⟨S.mul_mem (S.inv_mem hm.1) hx.1, hcC⟩, by group⟩

theorem sec4_elemAbelian_slc [Finite G] {t : G} {L S B : Subgroup G} (hL : IsOmega7Group L)
    (hLt : L ≤ centralizer ({t} : Set G))
    (hN : ∀ c ∈ centralizer ({t} : Set G), c ∈ normalizer (L : Set G))
    (hS : IsSylow2Of S (centralizer ({t} : Set G)))
    (h42 : ∀ P : Sylow 2 (centralizer (L : Set G)),
      IsCyclic (P : Subgroup (centralizer (L : Set G))))
    (hB : IsMaxElemAbelianIn (S ⊓ L) B) (hBu : ∀ B' : Subgroup G, IsMaxElemAbelianIn (S ⊓ L) B' →
      B' = B) (hBc : Nat.card B = 2 ^ 6) (ht : orderOf t = 2)
    (htC : t ∈ centralizer (L : Set G)) (htL : t ∉ L) {E : Subgroup G} (hE : E ≤ SLC S L)
    (hEa : CFSG.Open.IsElemAbelian 2 E) :
    Nat.card E ≤ 2 ^ 7 ∧ (Nat.card E = 2 ^ 7 → E = B ⊔ zpowers t) := by
  let C := centralizer (L : Set G)
  let P := S ⊓ L
  have ht2 : t * t = 1 := by
    have h : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
    simpa [pow_two] using h
  have hdec : ∀ x ∈ E, ∃ p ∈ P, p * p = 1 ∧ (x = p ∨ x = p * t) := by
    intro x hx
    obtain ⟨p, hp, c, hc, hxpc⟩ := sec4_slc_decomp hL hLt hN hS (hE hx)
    have hpc : p * c = c * p := Subgroup.mem_centralizer_iff.mp hc.2 p hp.2
    have hx2 : x * x = 1 := CFSG.Open.IsElemAbelian.mul_self_eq_one hEa hx
    have h1 : (p * c) * (p * c) = (p * p) * (c * c) := by
      calc (p * c) * (p * c) = p * (c * (p * c)) := mul_assoc p c (p * c)
        _ = p * ((c * p) * c) := by rw [mul_assoc c p c]
        _ = p * ((p * c) * c) := by rw [hpc.symm]
        _ = p * (p * (c * c)) := by rw [mul_assoc p c c]
        _ = (p * p) * (c * c) := by rw [mul_assoc p p (c * c)]
    have hp2c2 : (p * p) * (c * c) = 1 := by rw [hxpc, h1] at hx2; exact hx2
    have hp2C : p * p ∈ C := by
      rw [eq_inv_of_mul_eq_one_left hp2c2]
      exact C.inv_mem (C.mul_mem hc.2 hc.2)
    have hp2one : p * p = 1 := by
      have hmem : p * p ∈ (L ⊓ C) ⊓ S :=
        ⟨⟨L.mul_mem hp.2 hp.2, hp2C⟩, S.mul_mem hp.1 hp.1⟩
      have hbot := sec4_isPGroup_inf_eq_bot_of_odd_orderOf (H := L ⊓ C) (K := S)
        (fun x hx => sec4_odd_orderOf_of_mem_centralizer hL hx.1 hx.2) hS.2.1
      rwa [hbot, Subgroup.mem_bot] at hmem
    have hc2 : c * c = 1 := by rw [hp2one, one_mul] at hp2c2; exact hp2c2
    have hct : c * t = t * c :=
      (Subgroup.mem_centralizer_iff.mp (hS.1 hc.1) t (Set.mem_singleton t)).symm
    rcases sec4_eq_of_commute h42 hc.2 htC hc2 ht hct with hc1 | hct'
    · exact ⟨p, hp, hp2one, Or.inl (by rw [hxpc, hc1, mul_one])⟩
    · exact ⟨p, hp, hp2one, Or.inr (by rw [hxpc, hct'])⟩
  let E' := E ⊔ zpowers t
  have htC' : t ∈ C := htC
  have hztC : Subgroup.zpowers t ≤ C := Subgroup.zpowers_le.mpr htC'
  have htS : t ∈ S := sec4_t_mem_S hS ht
  have hE'eleb : CFSG.Open.IsElemAbelian 2 E' := by
    refine CFSG.Open.IsElemAbelian.sup_of_commute hEa
      (CFSG.Open.isElemAbelian_zpowers (by rw [pow_two]; exact ht2)) ?_
    intro a ha b hb
    obtain ⟨p, hp, hp2, ha'⟩ := hdec a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    rcases ha' with hpa | hpa
    · rw [hpa]
      exact ((show Commute p t from
        Subgroup.mem_centralizer_iff.mp htC' p hp.2).zpow_right k).eq
    · rw [hpa]
      have hpt : p * t = t * p := Subgroup.mem_centralizer_iff.mp htC' p hp.2
      have hcommpt : Commute (p * t) t := by
        show (p * t) * t = t * (p * t)
        calc (p * t) * t = p * (t * t) := by rw [mul_assoc]
          _ = p := by rw [ht2, mul_one]
          _ = (t * p) * t := by rw [← hpt, mul_assoc, ht2, mul_one]
          _ = t * (p * t) := by rw [mul_assoc]
      exact (hcommpt.zpow_right k).eq
  have hE'le : E' ≤ SLC S L := by
    refine sup_le hE ?_
    rw [Subgroup.zpowers_le]
    exact ⟨htS, Subgroup.mem_sup_right htC'⟩
  let E₁ := E' ⊓ L
  have hE1P : E₁ ≤ P := le_inf ((inf_le_left.trans hE'le).trans inf_le_left) inf_le_right
  have hE1eleb : CFSG.Open.IsElemAbelian 2 E₁ := hE'eleb.mono inf_le_left
  have hE1cardB : Nat.card E₁ ≤ Nat.card B := hB.2.2 E₁ hE1P hE1eleb
  have hE'eq : E' = E₁ ⊔ zpowers t := by
    refine le_antisymm ?_ (sup_le inf_le_left le_sup_right)
    rw [show E' = E ⊔ zpowers t from rfl, sup_le_iff]
    refine ⟨?_, le_sup_right⟩
    intro x hx
    obtain ⟨p, hp, hp2, hxp⟩ := hdec x hx
    have hpE' : p ∈ E' := by
      rcases hxp with hxp | hxp
      · rw [← hxp]; exact Subgroup.mem_sup_left hx
      · have hpt : p = x * t := by rw [hxp, mul_assoc, ht2, mul_one]
        rw [hpt]
        exact E'.mul_mem (Subgroup.mem_sup_left hx)
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩))
    have hpE1 : p ∈ E₁ := ⟨hpE', hp.2⟩
    rcases hxp with hxp | hxp
    · rw [hxp]; exact Subgroup.mem_sup_left hpE1
    · rw [hxp]
      exact Subgroup.mul_mem_sup hpE1 (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
  have hE1zt : E₁ ⊓ zpowers t = ⊥ := by
    refine le_antisymm (fun x hx => ?_) bot_le
    rw [Subgroup.mem_bot]
    have hxE' : x ∈ E' := (inf_le_left : E₁ ≤ E') hx.1
    have hodd : Odd (orderOf x) :=
      sec4_odd_orderOf_of_mem_centralizer hL hx.1.2 (hztC hx.2)
    have hx2 : x * x = 1 := hE'eleb.mul_self_eq_one hxE'
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd; exact absurd hodd (by decide)
  have hE'card : Nat.card E' = 2 * Nat.card E₁ := by
    rw [hE'eq, sec4_natCard_sup_of_commute_of_inf_bot (fun a ha b hb =>
      hE'eleb.comm ((inf_le_left : E₁ ≤ E') ha) ((le_sup_right : zpowers t ≤ E') hb)) hE1zt,
      Nat.card_zpowers, ht, Nat.mul_comm (Nat.card E₁) 2]
  have hE'le7 : Nat.card E' ≤ 2 ^ 7 := by
    calc Nat.card E' = 2 * Nat.card E₁ := hE'card
      _ ≤ 2 * 2 ^ 6 := by rw [← hBc]; exact Nat.mul_le_mul_left 2 hE1cardB
      _ = 2 ^ 7 := by norm_num
  refine ⟨?_, ?_⟩
  · calc Nat.card E ≤ Nat.card E' := Subgroup.card_le_of_le le_sup_left
      _ ≤ 2 ^ 7 := hE'le7
  · intro hcard
    have hEeq : E = E' :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard]; exact hE'le7)
    have hE1card6 : Nat.card E₁ = 2 ^ 6 := by
      have h2 : 2 * Nat.card E₁ = 2 * 2 ^ 6 := by
        rw [← hE'card, ← hEeq, hcard]; norm_num
      omega
    have hE1A : IsMaxElemAbelianIn P E₁ :=
      ⟨hE1P, hE1eleb, fun B' hB'P hB'eleb => by
        rw [hE1card6, ← hBc]
        exact hB.2.2 B' hB'P hB'eleb⟩
    have hE1B : E₁ = B := hBu E₁ hE1A
    rw [hEeq, hE'eq, hE1B]

end CFSG.OddStandard.SmallF3.Omega
