
module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelGenBase
import all CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelGenBase

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorelFpf

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem pow_four_of_ker'
    {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    {l : Cover →* E} (h : IsQSetting q l) {z : E} (hz : z ∈ q.ker) : z ^ 4 = 1 := by
  obtain ⟨d, rfl⟩ := h.exists_psi hz
  rw [← map_pow, D4_pow_four, map_one]

theorem l34BorelGenerationFact :
    L34BorelGenerationFact := by
  intro G _ _ J P C hJ hL hP hcyc hCP hCe hC16 hCZ
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hJ hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  have hEY : ∀ E : Subgroup G, E ≤ C → IsEightGroup E → J ⊓ normalizer (E : Set G) ≤
      oddIn J ⊔ ⨆ (E' : Subgroup G) (_ : E' ≤ C) (_ : IsEightGroup E'),
        J ⊓ normalizer (E' : Set G) :=
    fun E hE h8 => le_sup_of_le_right (le_iSup₂_of_le E hE (le_iSup_of_le h8 le_rfl))
  have hCZP : C ⊔ P ⊓ zStarIn J ≤ P := sup_le hCP inf_le_left
  have hmulP : ∀ {u v : G} (hu : u ∈ P) (hv : v ∈ P),
      jq J ⟨u * v, hP.1 (P.mul_mem hu hv)⟩ = jq J ⟨u, hP.1 hu⟩ * jq J ⟨v, hP.1 hv⟩ :=
    fun hu hv => by rw [← map_mul]; rfl
  have hCZ0 : ∀ {y : G} (hy : y ∈ C ⊔ P ⊓ zStarIn J),
      q (jq J ⟨y, hP.1 (hCZP hy)⟩) ∈ Z0 := fun {y} hy =>
    (mem_Z0_iff_comm hP hqsurj hqker hT (hCZP hy)).2 ((hCZ y (hCZP hy)).2 hy)
  have hZ0CZ : ∀ {y : G} (hy : y ∈ P), q (jq J ⟨y, hP.1 hy⟩) ∈ Z0 → y ∈ C ⊔ P ⊓ zStarIn J :=
    fun {y} hy h => (hCZ y hy).1 ((mem_Z0_iff_comm hP hqsurj hqker hT hy).1 h)
  have hCZcomm : ∀ x ∈ C ⊔ P ⊓ zStarIn J, ∀ y ∈ C ⊔ P ⊓ zStarIn J, x * y = y * x := by
    refine commute_sup_left (commute_sup_right hCe.1 ?_) (commute_sup_right ?_ ?_)
    · intro x hx y hy
      exact (comm_of_mem_Z hP hy (hCP hx)).symm
    · intro x hx y hy
      exact comm_of_mem_Z hP hx (hCP hy)
    · intro x hx y hy
      exact comm_of_mem_Z hP hx (mem_inf.mp hy).1
  have hinvC : ∀ v ∈ C ⊔ P ⊓ zStarIn J, v * v = 1 → v ∈ C := by
    intro v hv hv2
    by_contra hvC
    have hvc : ∀ y ∈ C, v * y = y * v := fun y hy => hCZcomm v hv y (mem_sup_left hy)
    have hD := (isElemTwo_zpowers hv2).sup hCe (commute_zpowers_left hvc)
    have hcard := card_zpowers_sup_eq hv2 (mem_normalizer_of_commute hvc) hvC
    rw [hC16] at hcard
    have hDle : zpowers v ⊔ C ≤ C ⊔ P ⊓ zStarIn J := sup_le (zpowers_le.2 hv) le_sup_left
    have := card_le_sixteen hQ hP (hDle.trans hCZP) hD fun hd => hCZ0 (hDle hd)
    omega
  have hK2 : ∀ z ∈ P ⊓ zStarIn J, z * z = 1 → z ∈ C ⊓ (P ⊓ zStarIn J) :=
    fun z hz hz2 => ⟨hinvC z (mem_sup_right hz) hz2, hz⟩
  have hKe : IsElemTwo (C ⊓ (P ⊓ zStarIn J)) := hCe.mono inf_le_left
  have hKle : Nat.card ↥(C ⊓ (P ⊓ zStarIn J)) ≤ 4 := by
    refine le_trans (Nat.card_le_card_of_injective
      (fun k => (⟨jq J ⟨k.1, hP.1 (hCP k.2.1)⟩, ?_, ?_⟩ :
        {e : Jhat J // e ∈ q.ker ∧ e * e = 1})) fun a b hab => ?_) hQ.card_omega_ker_le
    · rw [hqker]
      exact (mem_zStarIn_iff _).1 (mem_inf.mp k.2.2).2
    · rw [← hmulP (hCP k.2.1) (hCP k.2.1)]
      have : (⟨k.1 * k.1, hP.1 (P.mul_mem (hCP k.2.1) (hCP k.2.1))⟩ : J) = 1 :=
        Subtype.ext (hKe.2 _ k.2)
      rw [this, map_one]
    · exact Subtype.ext (eq_of_jq_eq hP.1 hP2 (hCP a.2.1) (hCP b.2.1)
        (congrArg Subtype.val hab))
  have hKge : 2 < Nat.card ↥(C ⊓ (P ⊓ zStarIn J)) := by
    by_contra hle
    push Not at hle
    obtain ⟨ζ, -⟩ := exists_zeta hP hqker
    set T : Subgroup (Jhat J) := ((C ⊓ (P ⊓ zStarIn J)).subgroupOf P).map
      ((jq J).comp (Subgroup.inclusion hP.1)) with hTd
    have hTmem : ∀ e, e ∈ T ↔ e ∈ q.ker ∧ e * e = 1 := by
      intro e
      constructor
      · rintro ⟨k, hk, rfl⟩
        have hk : (k : G) ∈ C ⊓ (P ⊓ zStarIn J) := hk
        refine ⟨?_, ?_⟩
        · rw [hqker]
          exact (mem_zStarIn_iff _).1 (mem_inf.mp (mem_inf.mp hk).2).2
        · show jq J (Subgroup.inclusion hP.1 k) * jq J (Subgroup.inclusion hP.1 k) = 1
          rw [← map_mul]
          have : Subgroup.inclusion hP.1 k * Subgroup.inclusion hP.1 k = 1 :=
            Subtype.ext (hKe.2 _ hk)
          rw [this, map_one]
      · rintro ⟨he, he2⟩
        have he' := he
        rw [hqker] at he'
        obtain ⟨z, hzP, hzJ, rfl⟩ := exists_mem_of_mem_center hP he'
        have hzZ : z ∈ P ⊓ zStarIn J := mem_inf.mpr ⟨hzP, (mem_zStarIn_iff hzJ).2 he'⟩
        have hz2 : z * z = 1 := eq_one_of_jq_eq_one hP.1 hP2 (P.mul_mem hzP hzP)
          (by rw [hmulP hzP hzP]; exact he2)
        exact ⟨⟨z, hzP⟩, mem_subgroupOf.mpr (hK2 z hzZ hz2), rfl⟩
    have hTcard : Nat.card T = Nat.card ↥(C ⊓ (P ⊓ zStarIn J)) := by
      rw [hTd, Subgroup.card_map_of_injective]
      · exact Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hCP)).toEquiv
      · intro a b hab
        exact Subtype.ext (eq_of_jq_eq hP.1 hP2 a.2 b.2 hab)
    have hcyc' := isCyclic_of_card_le_two hQ.ker_le (fun z hz => pow_four_of_ker' hQ hz) hTmem
      (hTcard ▸ hle)
    exact hcyc (isCyclic_of_surjective ζ.symm.toMonoidHom ζ.symm.surjective)
  have hK4 : Nat.card ↥(C ⊓ (P ⊓ zStarIn J)) = 4 := by
    have hd : Nat.card ↥(C ⊓ (P ⊓ zStarIn J)) ∣ 16 := hC16 ▸ card_dvd_of_le inf_le_left
    interval_cases h : Nat.card ↥(C ⊓ (P ⊓ zStarIn J)) <;> omega
  have hTP : ∀ {u : G} (hu : u ∈ P), q (jq J ⟨u, hP.1 hu⟩) ∈ T0 := fun hu =>
    (hT _).2 ⟨_, hu, _, rfl⟩
  have hconjq : ∀ {n u : G} (hn : n ∈ J) (hu : u ∈ J), q (jq J ⟨n * u * n⁻¹,
      J.mul_mem (J.mul_mem hn hu) (J.inv_mem hn)⟩) =
        q (jq J ⟨n, hn⟩) * q (jq J ⟨u, hu⟩) * (q (jq J ⟨n, hn⟩))⁻¹ := by
    intro n u hn hu
    have e : (⟨n * u * n⁻¹, J.mul_mem (J.mul_mem hn hu) (J.inv_mem hn)⟩ : J) =
        ⟨n, hn⟩ * ⟨u, hu⟩ * (⟨n, hn⟩ : J)⁻¹ := rfl
    rw [e]
    simp only [map_mul, map_inv]
  have hCK : ¬ C ≤ C ⊓ (P ⊓ zStarIn J) := fun h => by
    have := Subgroup.card_le_of_le h
    rw [hC16, hK4] at this
    omega
  obtain ⟨c₀, hc₀C, hc₀K⟩ := Set.not_subset.mp hCK
  have hc₀2 := hCe.2 c₀ hc₀C
  have hc₀P := hCP hc₀C
  have hc₀comm : ∀ y ∈ C ⊓ (P ⊓ zStarIn J), c₀ * y = y * c₀ :=
    fun y hy => hCe.1 c₀ hc₀C y (mem_inf.mp hy).1
  have hEPC : zpowers c₀ ⊔ C ⊓ (P ⊓ zStarIn J) ≤ C := sup_le (zpowers_le.2 hc₀C) inf_le_left
  have hEP8 : IsEightGroup (zpowers c₀ ⊔ C ⊓ (P ⊓ zStarIn J)) := by
    refine ⟨hCe.mono hEPC, ?_⟩
    rw [card_zpowers_sup_eq hc₀2 (mem_normalizer_of_commute hc₀comm) hc₀K, hK4]
  have hconjP : ∀ p ∈ P, ∀ g ∈ zpowers c₀ ⊔ C ⊓ (P ⊓ zStarIn J),
      p * g * p⁻¹ ∈ zpowers c₀ ⊔ C ⊓ (P ⊓ zStarIn J) := by
    intro p hp
    have hle : zpowers c₀ ⊔ C ⊓ (P ⊓ zStarIn J) ≤
        (zpowers c₀ ⊔ C ⊓ (P ⊓ zStarIn J)).comap (MulAut.conj p).toMonoidHom := by
      refine sup_le (zpowers_le.2 ?_) fun k hk => ?_
      · have hwP : p * c₀ * p⁻¹ * c₀⁻¹ ∈ P :=
          P.mul_mem (P.mul_mem (P.mul_mem hp hc₀P) (P.inv_mem hp)) (P.inv_mem hc₀P)
        have hwZ : p * c₀ * p⁻¹ * c₀⁻¹ ∈ zStarIn J := by
          rw [mem_zStarIn_iff (hP.1 hwP), ← hqker, MonoidHom.mem_ker]
          have e : (⟨p * c₀ * p⁻¹ * c₀⁻¹, hP.1 hwP⟩ : J) = ⟨p, hP.1 hp⟩ * ⟨c₀, hP.1 hc₀P⟩ *
              (⟨p, hP.1 hp⟩ : J)⁻¹ * (⟨c₀, hP.1 hc₀P⟩ : J)⁻¹ := rfl
          rw [e]
          simp only [map_mul, map_inv]
          have hc := (mem_centralizer_iff.mp (hCZ0 (mem_sup_left hc₀C)).1) _ (hTP hp)
          rw [hc]
          group
        have hwc := comm_of_mem_Z hP (mem_inf.mpr ⟨hwP, hwZ⟩) hc₀P
        have hw2 : p * c₀ * p⁻¹ * c₀⁻¹ * (p * c₀ * p⁻¹ * c₀⁻¹) = 1 := by
          generalize hwd : p * c₀ * p⁻¹ * c₀⁻¹ = w at hwc
          have hwc0 : w * c₀ = p * c₀ * p⁻¹ := by rw [← hwd]; group
          calc w * w = w * w * (c₀ * c₀) := by rw [hc₀2, mul_one]
            _ = w * (w * c₀) * c₀ := by group
            _ = w * (c₀ * w) * c₀ := by rw [hwc]
            _ = (w * c₀) * (w * c₀) := by group
            _ = p * (c₀ * c₀) * p⁻¹ := by rw [hwc0]; group
            _ = 1 := by rw [hc₀2]; group
        have hwK := hK2 _ (mem_inf.mpr ⟨hwP, hwZ⟩) hw2
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show p * c₀ * p⁻¹ = (p * c₀ * p⁻¹ * c₀⁻¹) * c₀ by group]
        exact mul_mem (mem_sup_right hwK) (mem_sup_left (mem_zpowers c₀))
      · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          ← comm_of_mem_Z hP (mem_inf.mp hk).2 hp, mul_inv_cancel_right]
        exact mem_sup_right hk
    exact fun g hg => hle hg
  have hPY : ∀ p ∈ P, p ∈ oddIn J ⊔ ⨆ (E' : Subgroup G) (_ : E' ≤ C) (_ : IsEightGroup E'),
      J ⊓ normalizer (E' : Set G) := fun p hp =>
    hEY _ hEPC hEP8 ⟨hP.1 hp, mem_normalizer_of_conj (hconjP p hp) fun g hg => by
      have := hconjP p⁻¹ (P.inv_mem hp) g hg
      rwa [inv_inv] at this⟩
  intro n hn
  obtain ⟨hnJ, hnP⟩ := mem_inf.mp hn
  have hsT : ∀ t ∈ T0, q (jq J ⟨n, hnJ⟩) * t * (q (jq J ⟨n, hnJ⟩))⁻¹ ∈ T0 := by
    intro t ht
    obtain ⟨e, he⟩ := hqsurj t (T0_le_S ht)
    obtain ⟨p, hpP, hpJ, rfl⟩ := (hT e).1 (he ▸ ht)
    rw [← he, ← hconjq hnJ hpJ]
    exact hTP ((mem_normalizer_iff.mp hnP p).mp hpP)
  have hsB := normalizer_T0_le (hqS _) hsT
  have hsN := B0_le_normalizer hsB
  by_cases hsT0 : q (jq J ⟨n, hnJ⟩) ∈ T0
  · obtain ⟨p, hpP, hpJ, hpe⟩ := (hT _).1 hsT0
    have ho : p⁻¹ * n ∈ oddIn J := by
      rw [mem_oddIn_iff (J.mul_mem (J.inv_mem hpJ) hnJ)]
      have e : (⟨p⁻¹ * n, J.mul_mem (J.inv_mem hpJ) hnJ⟩ : J) = (⟨p, hpJ⟩ : J)⁻¹ * ⟨n, hnJ⟩ :=
        rfl
      rw [e, map_mul, map_inv, hpe, inv_mul_cancel]
    rw [show n = p * (p⁻¹ * n) by group]
    exact mul_mem (hPY p hpP) (mem_sup_left ho)
  have hfp : ∀ t ∈ Z0, q (jq J ⟨n, hnJ⟩) * t = t * q (jq J ⟨n, hnJ⟩) → t = 1 := by
    intro t ht hst
    obtain ⟨k, hk, rfl⟩ := mem_Z0.1 ht
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact wordPerm_tg_zero
    · exact absurd hst (borelFpf hsB hsT0 (by decide))
    · exact absurd hst (borelFpf hsB hsT0 (by decide))
    · exact absurd hst (borelFpf hsB hsT0 (by decide))
  have hnC : ∀ {m : G} (hm : m ∈ J), m ∈ normalizer (P : Set G) →
      q (jq J ⟨m, hm⟩) ∈ normalizer (T0 : Set (Equiv.Perm (Fin 42))) →
      ∀ c ∈ C, m * c * m⁻¹ ∈ C := by
    intro m hm hmP hmT c hc
    have hmc : m * c * m⁻¹ ∈ P := (mem_normalizer_iff.mp hmP c).mp (hCP hc)
    refine hinvC _ (hZ0CZ hmc ?_) ?_
    · rw [hconjq hm (hP.1 (hCP hc))]
      exact conj_mem_Z0 hmT (hCZ0 (mem_sup_left hc))
    · rw [show m * c * m⁻¹ * (m * c * m⁻¹) = m * (c * c) * m⁻¹ by group, hCe.2 c hc]
      group
  have hn' : n⁻¹ ∈ J := J.inv_mem hnJ
  have hnC1 := hnC hnJ hnP hsN
  have hnC2 : ∀ c ∈ C, n⁻¹ * c * n ∈ C := fun c hc => by
    have h1 := hnC hn' (inv_mem hnP) (by
      have : (⟨n⁻¹, hn'⟩ : J) = (⟨n, hnJ⟩ : J)⁻¹ := rfl
      rw [this, map_inv, map_inv]
      exact inv_mem hsN) c hc
    rwa [inv_inv] at h1
  have hnK : ∀ k ∈ C ⊓ (P ⊓ zStarIn J), n * k * n⁻¹ = k := by
    intro k hk
    obtain ⟨-, hkP, hkZ⟩ := hk
    have hnk : n * k * n⁻¹ ∈ P := (mem_normalizer_iff.mp hnP k).mp hkP
    apply eq_of_jq_eq hP.1 hP2 hnk hkP
    have e : (⟨n * k * n⁻¹, hP.1 hnk⟩ : J) = ⟨n, hnJ⟩ * ⟨k, hP.1 hkP⟩ * (⟨n, hnJ⟩ : J)⁻¹ := rfl
    have hc := mem_center_iff.mp ((mem_zStarIn_iff (hP.1 hkP)).1 hkZ)
    rw [e, map_mul, map_mul, map_inv, hc (jq J ⟨n, hnJ⟩), mul_inv_cancel_right]
  have hfpC : ∀ c ∈ C, n * c * n⁻¹ * c⁻¹ ∈ P ⊓ zStarIn J → c ∈ C ⊓ (P ⊓ zStarIn J) := by
    intro c hc hcz
    obtain ⟨hcP', hcZ'⟩ := mem_inf.mp hcz
    have hcP := hCP hc
    have h1 : q (jq J ⟨n * c * n⁻¹ * c⁻¹, hP.1 hcP'⟩) = 1 := by
      have := (mem_zStarIn_iff (hP.1 hcP')).1 hcZ'
      rw [← hqker] at this
      exact this
    have e : (⟨n * c * n⁻¹ * c⁻¹, hP.1 hcP'⟩ : J) = ⟨n, hnJ⟩ * ⟨c, hP.1 hcP⟩ *
        (⟨n, hnJ⟩ : J)⁻¹ * (⟨c, hP.1 hcP⟩ : J)⁻¹ := rfl
    rw [e] at h1
    simp only [map_mul, map_inv] at h1
    have hcomm : q (jq J ⟨n, hnJ⟩) * q (jq J ⟨c, hP.1 hcP⟩) =
        q (jq J ⟨c, hP.1 hcP⟩) * q (jq J ⟨n, hnJ⟩) := by
      generalize q (jq J ⟨n, hnJ⟩) = a at h1 ⊢
      generalize q (jq J ⟨c, hP.1 hcP⟩) = b at h1 ⊢
      calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
        _ = b * a := by rw [h1, one_mul]
    have hq1 := hfp _ (hCZ0 (mem_sup_left hc)) hcomm
    refine mem_inf.mpr ⟨hc, mem_inf.mpr ⟨hcP, ?_⟩⟩
    rw [mem_zStarIn_iff (hP.1 hcP), ← hqker]
    exact hq1
  have hCcomm := hCe.1
  let δ : C →* C := MonoidHom.mk' (fun c => ⟨(c : G)⁻¹ * (n * c * n⁻¹),
      C.mul_mem (C.inv_mem c.2) (hnC1 c c.2)⟩) fun a b => by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h1 := hCcomm _ (C.inv_mem b.2) _ (C.inv_mem a.2)
    have h2 := hCcomm _ (C.inv_mem b.2) _ (hnC1 a a.2)
    calc ((a : G) * b)⁻¹ * (n * (a * b) * n⁻¹) =
        (b : G)⁻¹ * (a : G)⁻¹ * (n * a * n⁻¹) * (n * b * n⁻¹) := by group
      _ = (a : G)⁻¹ * (b : G)⁻¹ * (n * a * n⁻¹) * (n * b * n⁻¹) := by rw [h1]
      _ = (a : G)⁻¹ * ((b : G)⁻¹ * (n * a * n⁻¹)) * (n * b * n⁻¹) := by group
      _ = (a : G)⁻¹ * ((n * a * n⁻¹) * (b : G)⁻¹) * (n * b * n⁻¹) := by rw [h2]
      _ = (a : G)⁻¹ * (n * a * n⁻¹) * ((b : G)⁻¹ * (n * b * n⁻¹)) := by group
  have hker : ∀ c : C, δ c = 1 ↔ (c : G) ∈ C ⊓ (P ⊓ zStarIn J) := by
    intro c
    constructor
    · intro h
      have h1 : (c : G)⁻¹ * (n * c * n⁻¹) = 1 := congrArg Subtype.val h
      apply hfpC c c.2
      have e : n * c * n⁻¹ = c := by
        calc n * ↑c * n⁻¹ = c * ((c : G)⁻¹ * (n * c * n⁻¹)) := by group
          _ = c := by rw [h1, mul_one]
      rw [e, mul_inv_cancel]
      exact one_mem _
    · intro hk
      apply Subtype.ext
      show (c : G)⁻¹ * (n * c * n⁻¹) = 1
      rw [hnK c hk, inv_mul_cancel]
  have hkerC : Nat.card δ.ker = 4 := by
    rw [← hK4]
    exact Nat.card_congr
      { toFun := fun c => ⟨c.1.1, (hker c.1).1 c.2⟩
        invFun := fun k => ⟨⟨k.1, (mem_inf.mp k.2).1⟩, (hker _).2 k.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hrange : Nat.card δ.range = 4 := by
    have h1 := Subgroup.card_ker_mul_card_range δ
    rw [hkerC, hC16] at h1
    omega
  set V := δ.range.map C.subtype with hVd
  have hV4 : Nat.card V = 4 := by
    rw [hVd, Subgroup.card_map_of_injective Subtype.val_injective, hrange]
  have hVC : V ≤ C := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hVmem : ∀ v ∈ V, ∃ c ∈ C, v = c⁻¹ * (n * c * n⁻¹) := by
    rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨c, c.2, rfl⟩
  have hδV : ∀ c ∈ C, c⁻¹ * (n * c * n⁻¹) ∈ V := fun c hc =>
    ⟨δ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩, rfl⟩
  have hVK : ∀ v ∈ V, v ∈ C ⊓ (P ⊓ zStarIn J) → v = 1 := by
    intro v hv hvK
    obtain ⟨c, hc, rfl⟩ := hVmem v hv
    have hcomm := hCcomm _ hc _ (hnC1 c hc)
    have e : n * c * n⁻¹ * c⁻¹ = c⁻¹ * (n * c * n⁻¹) := by
      calc n * c * n⁻¹ * c⁻¹ = c⁻¹ * (c * (n * c * n⁻¹)) * c⁻¹ := by group
        _ = c⁻¹ * ((n * c * n⁻¹) * c) * c⁻¹ := by rw [hcomm]
        _ = c⁻¹ * (n * c * n⁻¹) := by group
    have hcK := hfpC c hc (by rw [e]; exact (mem_inf.mp hvK).2)
    rw [hnK c hcK, inv_mul_cancel]
  obtain ⟨⟨z₀, hz₀K⟩, hz₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    ((one_lt_card_iff_ne_bot _).mp (by rw [hK4]; norm_num))
  have hz₀1' : z₀ ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hz₀C := (mem_inf.mp hz₀K).1
  have hz₀2 := hCe.2 z₀ hz₀C
  have hz₀V : z₀ ∉ V := fun h => hz₀1' (hVK z₀ h hz₀K)
  have hz₀comm : ∀ y ∈ V, z₀ * y = y * z₀ := fun y hy => hCcomm z₀ hz₀C y (hVC hy)
  have hEC : zpowers z₀ ⊔ V ≤ C := sup_le (zpowers_le.2 hz₀C) hVC
  have hE8 : IsEightGroup (zpowers z₀ ⊔ V) := ⟨hCe.mono hEC, by
    rw [card_zpowers_sup_eq hz₀2 (mem_normalizer_of_commute hz₀comm) hz₀V, hV4]⟩
  have hz₀n : n * z₀ * n⁻¹ = z₀ := hnK z₀ hz₀K
  have hz₀n' : n⁻¹ * z₀ * n = z₀ := by
    calc n⁻¹ * z₀ * n = n⁻¹ * (n * z₀ * n⁻¹) * n := by rw [hz₀n]
      _ = z₀ := by group
  have hnE : n ∈ normalizer ((zpowers z₀ ⊔ V : Subgroup G) : Set G) := by
    refine mem_normalizer_of_conj (fun g hg => ?_) (fun g hg => ?_)
    · have hle : zpowers z₀ ⊔ V ≤ (zpowers z₀ ⊔ V).comap (MulAut.conj n).toMonoidHom := by
        refine sup_le (zpowers_le.2 ?_) fun v hv => ?_
        · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hz₀n]
          exact mem_sup_left (mem_zpowers z₀)
        · obtain ⟨c, hc, rfl⟩ := hVmem v hv
          rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            show n * (c⁻¹ * (n * c * n⁻¹)) * n⁻¹ =
              (n * c * n⁻¹)⁻¹ * (n * (n * c * n⁻¹) * n⁻¹) by group]
          exact mem_sup_right (hδV _ (hnC1 c hc))
      exact hle hg
    · have hle : zpowers z₀ ⊔ V ≤ (zpowers z₀ ⊔ V).comap (MulAut.conj n⁻¹).toMonoidHom := by
        refine sup_le (zpowers_le.2 ?_) fun v hv => ?_
        · rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hz₀n']
          exact mem_sup_left (mem_zpowers z₀)
        · obtain ⟨c, hc, rfl⟩ := hVmem v hv
          rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
            show n⁻¹ * (c⁻¹ * (n * c * n⁻¹)) * n =
              (n⁻¹ * c * n)⁻¹ * (n * (n⁻¹ * c * n) * n⁻¹) by group]
          exact mem_sup_right (hδV _ (hnC2 c hc))
      have := hle hg
      rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at this
  exact hEY _ hEC hE8 (mem_inf.mpr ⟨hnJ, hnE⟩)

end CFSG.ComponentClassification.GrSLit.L34Facts
